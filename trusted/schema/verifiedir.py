"""VerifiedIR v1 JSON schema and strict validator. TRUSTED.

The JSON form is a one-to-one serialisation of `BendVerify.Prog`
(trusted/spec/lean/BendVerify/Syntax.lean). Any document that fails
`validate` is rejected before anything else looks at it.

    Prog  = {"format": "verifiedir-v1", "adts": [Adt], "fns": [Fn]}
    Adt   = {"name": Name | "Name & Name", "ctors": [{"name": Name, "fields": [Ty]}]}
    Fn    = {"name": Name, "params": [Ty], "ret": Ty, "body": Expr}
    Ty    = "u32" | "nat" | ["adt", int]
    Expr  = ["var", i] | ["u32", k] | ["nat", k]
          | ["prim", PrimName, [Expr]]
          | ["ctr", adt, tag, [Expr]]
          | ["call", f, [Expr]]
          | ["let", Expr, Expr]
          | ["par", Expr, Expr, Expr]
          | ["mat", adt, Expr, [[arity, Expr]]]
          | ["natcase", Expr, Expr, Expr]

Well-formedness enforced here (beyond the shape):
  * names match NAME_RE, function names are unique, ADT names are unique;
  * every ADT / constructor / function index is in range;
  * constructor and call arity match the declarations; a primitive has its
    fixed arity; a match has exactly one arm per constructor, each with the
    constructor's field count;
  * variables are in scope (de Bruijn index < number of enclosing binders);
  * literal ranges: u32 < 2^32, nat < 2^48 (the compiled runtime's Nat cap);
  * size limits (MAX_*).
"""

from __future__ import annotations

import re

NAME_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*(\.[A-Za-z0-9_]+)*$")
# datatype names may also denote a monomorphic pair instance, e.g. "Mode & U32"
ADT_NAME_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_.]*( & [A-Za-z_][A-Za-z0-9_.]*)?$")
MAX_NAME = 64
MAX_ADTS = 256
MAX_CTORS = 256
MAX_FIELDS = 64
MAX_FNS = 4096
MAX_PARAMS = 64
MAX_NODES = 500_000
MAX_DEPTH = 2000
U32_LIMIT = 2 ** 32
NAT_LIMIT = 2 ** 48

# name -> arity; order is the order of constructors in BendVerify.Prim
PRIMS = {
    "u32_add": 2, "u32_sub": 2, "u32_mul": 2, "u32_div": 2, "u32_mod": 2,
    "u32_and": 2, "u32_or": 2, "u32_xor": 2, "u32_not": 1,
    "u32_shl": 1, "u32_shr": 1, "u32_shln": 2, "u32_shrn": 2,
    "u32_inc": 1,
    "u32_is_eq": 2, "u32_is_ne": 2, "u32_is_lt": 2, "u32_is_le": 2, "u32_is_gt": 2, "u32_is_ge": 2,
    "u32_is_zero": 1,
    "u32_to_nat": 1, "u32_from_nat": 1,
    "nat_add": 2, "nat_sub": 2, "nat_mul": 2, "nat_div": 2, "nat_mod": 2,
    "nat_is_eq": 2, "nat_is_ne": 2, "nat_is_lt": 2, "nat_is_le": 2, "nat_is_gt": 2, "nat_is_ge": 2,
    "bool_and": 2, "bool_or": 2, "bool_not": 1,
}


class IRError(Exception):
    pass


def _is_int(x) -> bool:
    return isinstance(x, int) and not isinstance(x, bool)


def _name(x, what, regex=NAME_RE, limit=MAX_NAME):
    if not isinstance(x, str) or len(x) > limit or not regex.match(x):
        raise IRError(f"{what}: invalid name {x!r}")
    return x


def _keys(obj, keys, what):
    if not isinstance(obj, dict) or set(obj.keys()) != set(keys):
        raise IRError(f"{what}: expected exactly the fields {sorted(keys)}")


def _ty(t, nadts, what):
    if t == "u32" or t == "nat":
        return
    if (isinstance(t, list) and len(t) == 2 and t[0] == "adt" and _is_int(t[1])
            and 0 <= t[1] < nadts):
        return
    raise IRError(f"{what}: invalid type {t!r}")


class _Walker:
    def __init__(self, prog):
        self.prog = prog
        self.nodes = 0

    def expr(self, e, scope, depth, where):
        self.nodes += 1
        if self.nodes > MAX_NODES:
            raise IRError("program too large")
        if depth > MAX_DEPTH:
            raise IRError(f"{where}: expression too deep")
        if not isinstance(e, list) or not e or not isinstance(e[0], str):
            raise IRError(f"{where}: malformed expression")
        tag, n = e[0], len(e)
        adts, fns = self.prog["adts"], self.prog["fns"]
        if tag == "var" and n == 2 and _is_int(e[1]):
            if not 0 <= e[1] < scope:
                raise IRError(f"{where}: variable {e[1]} out of scope ({scope} bound)")
        elif tag == "u32" and n == 2 and _is_int(e[1]):
            if not 0 <= e[1] < U32_LIMIT:
                raise IRError(f"{where}: u32 literal out of range")
        elif tag == "nat" and n == 2 and _is_int(e[1]):
            if not 0 <= e[1] < NAT_LIMIT:
                raise IRError(f"{where}: nat literal out of range")
        elif tag == "prim" and n == 3 and isinstance(e[2], list):
            if e[1] not in PRIMS:
                raise IRError(f"{where}: unknown primitive {e[1]!r}")
            if len(e[2]) != PRIMS[e[1]]:
                raise IRError(f"{where}: primitive {e[1]} arity")
            for a in e[2]:
                self.expr(a, scope, depth + 1, where)
        elif tag == "ctr" and n == 4 and _is_int(e[1]) and _is_int(e[2]) and isinstance(e[3], list):
            if not 0 <= e[1] < len(adts):
                raise IRError(f"{where}: ADT index out of range")
            ctors = adts[e[1]]["ctors"]
            if not 0 <= e[2] < len(ctors):
                raise IRError(f"{where}: constructor index out of range")
            if len(e[3]) != len(ctors[e[2]]["fields"]):
                raise IRError(f"{where}: constructor arity")
            for a in e[3]:
                self.expr(a, scope, depth + 1, where)
        elif tag == "call" and n == 3 and _is_int(e[1]) and isinstance(e[2], list):
            if not 0 <= e[1] < len(fns):
                raise IRError(f"{where}: function index out of range")
            if len(e[2]) != len(fns[e[1]]["params"]):
                raise IRError(f"{where}: call arity")
            for a in e[2]:
                self.expr(a, scope, depth + 1, where)
        elif tag == "let" and n == 3:
            self.expr(e[1], scope, depth + 1, where)
            self.expr(e[2], scope + 1, depth + 1, where)
        elif tag == "par" and n == 4:
            self.expr(e[1], scope, depth + 1, where)
            self.expr(e[2], scope, depth + 1, where)
            self.expr(e[3], scope + 2, depth + 1, where)
        elif tag == "mat" and n == 4 and _is_int(e[1]) and isinstance(e[3], list):
            if not 0 <= e[1] < len(adts):
                raise IRError(f"{where}: ADT index out of range")
            ctors = adts[e[1]]["ctors"]
            self.expr(e[2], scope, depth + 1, where)
            if len(e[3]) != len(ctors):
                raise IRError(f"{where}: match must have one arm per constructor")
            for t, arm in enumerate(e[3]):
                if (not isinstance(arm, list) or len(arm) != 2 or not _is_int(arm[0])
                        or arm[0] != len(ctors[t]["fields"])):
                    raise IRError(f"{where}: arm {t} arity")
                self.expr(arm[1], scope + arm[0], depth + 1, where)
        elif tag == "natcase" and n == 4:
            self.expr(e[1], scope, depth + 1, where)
            self.expr(e[2], scope, depth + 1, where)
            self.expr(e[3], scope + 1, depth + 1, where)
        else:
            raise IRError(f"{where}: malformed expression with tag {tag!r}")


def validate(prog) -> dict:
    """Validate a parsed VerifiedIR document; return it unchanged or raise IRError."""
    _keys(prog, ["format", "adts", "fns"], "program")
    if prog["format"] != "verifiedir-v1":
        raise IRError("program: unsupported format")
    adts, fns = prog["adts"], prog["fns"]
    if not isinstance(adts, list) or len(adts) > MAX_ADTS:
        raise IRError("program: adts")
    if not isinstance(fns, list) or len(fns) > MAX_FNS:
        raise IRError("program: fns")
    seen = set()
    for i, a in enumerate(adts):
        _keys(a, ["name", "ctors"], f"adt {i}")
        if _name(a["name"], f"adt {i}", ADT_NAME_RE, 2 * MAX_NAME + 3) in seen:
            raise IRError(f"adt {i}: duplicate name")
        seen.add(a["name"])
        if not isinstance(a["ctors"], list) or len(a["ctors"]) > MAX_CTORS:
            raise IRError(f"adt {i}: ctors")
        for j, c in enumerate(a["ctors"]):
            _keys(c, ["name", "fields"], f"adt {i} ctor {j}")
            _name(c["name"], f"adt {i} ctor {j}")
            if not isinstance(c["fields"], list) or len(c["fields"]) > MAX_FIELDS:
                raise IRError(f"adt {i} ctor {j}: fields")
            for t in c["fields"]:
                _ty(t, len(adts), f"adt {i} ctor {j}")
    seen = set()
    for i, f in enumerate(fns):
        _keys(f, ["name", "params", "ret", "body"], f"fn {i}")
        if _name(f["name"], f"fn {i}") in seen:
            raise IRError(f"fn {i}: duplicate name {f['name']}")
        seen.add(f["name"])
        if not isinstance(f["params"], list) or len(f["params"]) > MAX_PARAMS:
            raise IRError(f"fn {i}: params")
        for t in f["params"]:
            _ty(t, len(adts), f"fn {i} param")
        _ty(f["ret"], len(adts), f"fn {i} ret")
    w = _Walker(prog)
    for i, f in enumerate(fns):
        w.expr(f["body"], len(f["params"]), 0, f"fn {f['name']}")
    return prog


def find_fn(prog, name):
    for i, f in enumerate(prog["fns"]):
        if f["name"] == name:
            return i
    return None
