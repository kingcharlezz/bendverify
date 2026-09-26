"""VerifiedIR -> Bend source lowering (competition v1). TRUSTED.

A deliberately small, direct printer. It does not optimise, reorder, or
introduce helper functions: each IR construct becomes the Bend construct with
the same meaning. IR that has no direct Bend spelling is REJECTED
("not lowerable"); the competitor's optimiser must emit lowerable IR.

  * let / par / mat / natcase may appear only in statement position (a
    function body, a let/par body, a match arm); expression positions hold
    only var / literal / prim / ctr / call;
  * a match scrutinee must be a variable (Bend matches only parameters and
    pattern-bound fields; the reference checker rejects anything else);
  * a variable bound by a parallel let may be used at most once per path;
  * names may not collide with Base or with the harness (`main`, `harness.*`).

The fixed harness `main` parses the entry arguments from IO.args(), calls the
entry and prints the result. It is identical for the reference and for every
candidate. The lowered program is then checked by the pinned reference Bend
checker (bend.ts) and compiled by the pinned reference compiler (comp.ts).
"""

from __future__ import annotations

PRIM_BEND = {
    "u32_add": "U32.add", "u32_sub": "U32.sub", "u32_mul": "U32.mul", "u32_div": "U32.div",
    "u32_mod": "U32.mod", "u32_and": "U32.and", "u32_or": "U32.or", "u32_xor": "U32.xor",
    "u32_not": "U32.not", "u32_shl": "U32.shl", "u32_shr": "U32.shr", "u32_shln": "U32.shln",
    "u32_shrn": "U32.shrn", "u32_inc": "U32.inc", "u32_is_eq": "U32.is_eq", "u32_is_ne": "U32.is_ne",
    "u32_is_lt": "U32.is_lt", "u32_is_le": "U32.is_le", "u32_is_gt": "U32.is_gt",
    "u32_is_ge": "U32.is_ge", "u32_is_zero": "U32.is_zero", "u32_to_nat": "U32.to_nat",
    "u32_from_nat": "U32.from_nat",
    "nat_add": "Nat.add", "nat_sub": "Nat.sub", "nat_mul": "Nat.mul", "nat_div": "Nat.div",
    "nat_mod": "Nat.mod", "nat_is_eq": "Nat.is_eq", "nat_is_ne": "Nat.is_ne", "nat_is_lt": "Nat.is_lt",
    "nat_is_le": "Nat.is_le", "nat_is_gt": "Nat.is_gt", "nat_is_ge": "Nat.is_ge",
    "bool_and": "Bool.and", "bool_or": "Bool.or", "bool_not": "Bool.not",
}

# Base datatypes a program may use, with their exact shapes (field types by name)
BASE_ADTS = {"Bool": [("False", []), ("True", [])],
             "Char": [("Chr", ["U32"])],
             "String": [("SNil", []), ("SCon", ["Char", "String"])]}
PRINTABLE = set(range(0x20, 0x7F)) - {ord('"'), ord("\\")}
RESERVED_FN_PREFIXES = ("harness.",)
RESERVED_FN_NAMES = {"main"}


class LowerError(Exception):
    pass


class _Binder:
    __slots__ = ("name", "kind", "plus", "fields_plus")

    def __init__(self, name, kind):
        self.name = name
        self.kind = kind          # "param" | "let" | "par" | "field" | "pred"
        self.plus = False


def _max_merge(a: dict, b: dict) -> dict:
    out = dict(a)
    for k, v in b.items():
        out[k] = max(out.get(k, 0), v)
    return out


def _sum_merge(a: dict, b: dict) -> dict:
    out = dict(a)
    for k, v in b.items():
        out[k] = out.get(k, 0) + v
    return out


class Lowerer:
    def __init__(self, prog, base_names: set[str]):
        self.prog = prog
        self.base_names = base_names
        self.counter = 0

    # ------------------------------------------------------------ usage analysis
    def uses(self, e, env) -> dict:
        """Max-over-paths use count of each binder (identified by id())."""
        tag = e[0]
        if tag == "var":
            return {id(env[-1 - e[1]]): 1}
        if tag in ("u32", "nat"):
            return {}
        if tag in ("prim", "call"):
            acc: dict = {}
            for a in e[2]:
                acc = _sum_merge(acc, self.uses(a, env))
            return acc
        if tag == "ctr":
            acc = {}
            for a in e[3]:
                acc = _sum_merge(acc, self.uses(a, env))
            return acc
        if tag == "let":
            b = _Binder("_", "let")
            return _sum_merge(self.uses(e[1], env), self.uses(e[2], env + [b]))
        if tag == "par":
            b1, b2 = _Binder("_", "par"), _Binder("_", "par")
            return _sum_merge(_sum_merge(self.uses(e[1], env), self.uses(e[2], env)),
                              self.uses(e[3], env + [b1, b2]))
        if tag == "mat":
            acc = {}
            for k, body in e[3]:
                acc = _max_merge(acc, self.uses(body, env + [_Binder("_", "field") for _ in range(k)]))
            return _sum_merge(self.uses(e[2], env), acc)
        if tag == "natcase":
            arms = _max_merge(self.uses(e[2], env), self.uses(e[3], env + [_Binder("_", "pred")]))
            return _sum_merge(self.uses(e[1], env), arms)
        raise LowerError(f"unknown tag {tag}")

    # ------------------------------------------------------------ printing
    def fresh(self, kind):
        self.counter += 1
        return f"{kind[0]}{self.counter}"

    def ty(self, t) -> str:
        if t == "u32":
            return "U32"
        if t == "nat":
            return "Nat"
        return self.prog["adts"][t[1]]["name"]

    def expr(self, e, env) -> str:
        tag = e[0]
        if tag == "var":
            return env[-1 - e[1]].name
        if tag == "u32":
            return str(e[1])
        if tag == "nat":
            return f"{e[1]}n"
        if tag == "prim":
            return f"{PRIM_BEND[e[1]]}({', '.join(self.expr(a, env) for a in e[2])})"
        if tag == "ctr":
            adt = self.prog["adts"][e[1]]
            if adt["name"] == "String":
                lit = self.string_lit(e)
                if lit is not None:
                    return lit
            if " & " in adt["name"]:
                return f"({', '.join(self.expr(a, env) for a in e[3])})"
            c = adt["ctors"][e[2]]["name"]
            return f"{c}{{{', '.join(self.expr(a, env) for a in e[3])}}}"
        if tag == "call":
            f = self.prog["fns"][e[1]]["name"]
            return f"{f}({', '.join(self.expr(a, env) for a in e[2])})"
        raise LowerError(f"not lowerable: '{tag}' in expression position")

    def string_lit(self, e):
        """A closed String constructor chain of printable characters, as a literal."""
        adts = self.prog["adts"]
        chars = []
        while True:
            if e[0] != "ctr" or adts[e[1]]["name"] != "String":
                return None
            if e[2] == 0 and not e[3]:
                break
            head, e = e[3]
            if (head[0] != "ctr" or adts[head[1]]["name"] != "Char" or head[3][0][0] != "u32"
                    or head[3][0][1] not in PRINTABLE):
                return None
            chars.append(chr(head[3][0][1]))
        return '"' + "".join(chars) + '"'

    def stmt(self, e, env, ind: str, out: list[str]) -> None:
        tag = e[0]
        if tag == "let":
            b = _Binder(self.fresh("let"), "let")
            val = self.expr(e[1], env)
            u = self.uses(e[2], env + [b]).get(id(b), 0)
            out.append(f"{ind}{'+' if u > 1 else ''}{b.name} = {val}")
            self.stmt(e[2], env + [b], ind, out)
            return
        if tag == "par":
            b1, b2 = _Binder(self.fresh("par"), "par"), _Binder(self.fresh("par"), "par")
            u = self.uses(e[3], env + [b1, b2])
            if u.get(id(b1), 0) > 1 or u.get(id(b2), 0) > 1:
                raise LowerError("not lowerable: a parallel-let variable is used more than once")
            out.append(f"{ind}{b1.name} {b2.name} = {self.expr(e[1], env)} {self.expr(e[2], env)}")
            self.stmt(e[3], env + [b1, b2], ind, out)
            return
        if tag == "mat":
            if e[2][0] != "var":
                raise LowerError("not lowerable: match on a computed value")
            scrut = env[-1 - e[2][1]]
            if scrut.kind in ("let", "par"):
                raise LowerError("not lowerable: match on a let-bound variable")
            out.append(f"{ind}match {scrut.name}:")
            adt = self.prog["adts"][e[1]]
            for (k, body), ctor in zip(e[3], adt["ctors"]):
                fields = [_Binder(self.fresh("field"), "field") for _ in range(k)]
                arm: list[str] = []
                self.stmt(body, env + fields, ind + "    ", arm)   # may set f.plus (natcase)
                u = self.uses(body, env + fields)
                pat = ", ".join(("+" if (f.plus or u.get(id(f), 0) > 1) else "") + f.name
                                for f in fields)
                out.append(f"{ind}  case {ctor['name']}{{{pat}}}:")
                out.extend(arm)
            return
        if tag == "natcase":
            if e[1][0] != "var":
                raise LowerError("not lowerable: match on a computed value")
            scrut = env[-1 - e[1][1]]
            if scrut.kind in ("let", "par"):
                raise LowerError("not lowerable: match on a let-bound variable")
            p = _Binder(self.fresh("pred"), "pred")
            if self.uses(e[3], env + [p]).get(id(p), 0) > 1:
                scrut.plus = True          # a `+` Nat hands out a `+` predecessor
            out.append(f"{ind}match {scrut.name}:")
            out.append(f"{ind}  case 0n:")
            self.stmt(e[2], env, ind + "    ", out)
            out.append(f"{ind}  case 1n+{p.name}:")
            self.stmt(e[3], env + [p], ind + "    ", out)
            return
        out.append(ind + self.expr(e, env))

    # ------------------------------------------------------------ program
    def callees(self, e, acc: set) -> set:
        tag = e[0]
        if tag == "call":
            acc.add(e[1])
            for a in e[2]:
                self.callees(a, acc)
        elif tag in ("prim",):
            for a in e[2]:
                self.callees(a, acc)
        elif tag == "ctr":
            for a in e[3]:
                self.callees(a, acc)
        elif tag == "let":
            self.callees(e[1], acc); self.callees(e[2], acc)
        elif tag in ("par", "natcase"):
            self.callees(e[1], acc); self.callees(e[2], acc); self.callees(e[3], acc)
        elif tag == "mat":
            self.callees(e[2], acc)
            for _, b in e[3]:
                self.callees(b, acc)
        return acc

    def order(self) -> list[int]:
        """Callees before callers (Bend forbids forward references). Self-recursion
        is allowed; any other cycle is mutual recursion, which Bend rejects."""
        n = len(self.prog["fns"])
        deps = [self.callees(f["body"], set()) - {i} for i, f in enumerate(self.prog["fns"])]
        placed: list[int] = []
        done = [False] * n
        while len(placed) < n:
            progress = False
            for i in range(n):
                if not done[i] and all(done[d] for d in deps[i]):
                    done[i] = True
                    placed.append(i)
                    progress = True
            if not progress:
                raise LowerError("not lowerable: mutual recursion")
        return placed

    def program(self) -> list[str]:
        out: list[str] = []
        for a in self.prog["adts"]:
            if a["name"] in BASE_ADTS:
                expect = BASE_ADTS[a["name"]]
                got = [(c["name"], [self.ty(t) for t in c["fields"]]) for c in a["ctors"]]
                if got != expect:
                    raise LowerError(f"datatype {a['name']} must match Base's declaration")
                continue
            if " & " in a["name"]:
                cs = a["ctors"]
                if (len(cs) != 1 or cs[0]["name"] != "Tuple" or len(cs[0]["fields"]) != 2
                        or a["name"] != f"{self.ty(cs[0]['fields'][0])} & {self.ty(cs[0]['fields'][1])}"):
                    raise LowerError(f"pair datatype {a['name']} must be Tuple{{A, B}} named 'A & B'")
                continue
            if a["name"] in self.base_names:
                raise LowerError(f"datatype name {a['name']} collides with Base")
            out.append(f"type {a['name']} is Data:")
            for c in a["ctors"]:
                if c["name"] in self.base_names:
                    raise LowerError(f"constructor name {c['name']} collides with Base")
                fs = ", ".join(f"f{j}: {self.ty(t)}" for j, t in enumerate(c["fields"]))
                out.append(f"  {c['name']}{{{fs}}}")
            out.append("")
        for fi in self.order():
            f = self.prog["fns"][fi]
            name = f["name"]
            if name in RESERVED_FN_NAMES or name.startswith(RESERVED_FN_PREFIXES) or name in self.base_names:
                raise LowerError(f"function name {name} is reserved or collides with Base")
            params = [_Binder(self.fresh("x"), "param") for _ in f["params"]]
            body: list[str] = []
            self.stmt(f["body"], params, "  ", body)
            u = self.uses(f["body"], params)
            for b in params:
                if u.get(id(b), 0) > 1:
                    b.plus = True   # (natcase may also have set it)
            ps = ", ".join(("+" if b.plus else "") + f"{b.name}: {self.ty(t)}"
                           for b, t in zip(params, f["params"]))
            out.append(f"def {name}({ps}) -> {self.ty(f['ret'])}:")
            out.extend(body)
            out.append("")
        return out


def harness(prog, entry: str) -> list[str]:
    """The fixed BendVerify harness for an entry with U32/Nat params and result.

    Arguments are parsed as decimal digits by small AFFINE parsers (each string is
    consumed once). Base's `U32.read`/`Nat.read` share (`+`) their input strings,
    which makes `String` a "hot" (reference-sealed) type in the whole compiled
    program and slows down any workload that builds strings (measured: lexer
    2.3 s -> 4.0 s). The inputs are supplied by the trusted benchmark harness;
    non-digit characters are not validated."""
    fn = next(f for f in prog["fns"] if f["name"] == entry)
    params = fn["params"]
    if any(t not in ("u32", "nat") for t in params) or fn["ret"] not in ("u32", "nat"):
        raise LowerError("v1 harness supports U32/Nat entry parameters and results only")
    n = len(params)
    show = {"u32": "U32.show", "nat": "Nat.show"}[fn["ret"]]
    parse = {"u32": "harness.u32(s{j}, 0)", "nat": "harness.nat(s{j}, 0n)"}
    pat = "Nil{}"
    for j in reversed(range(n)):
        pat = f"Con{{s{j}, {pat}}}"
    call = f"{entry}!({', '.join(parse[t].format(j=j) for j, t in enumerate(params))})"
    # `!` runs the entry on Bend's parallel lane; the build is CPU-only and every
    # run passes `--gpu off`, so this lane executes on CPU threads.
    return [
        "# ---- BendVerify v1 harness (trusted, identical for every candidate) ----",
        "def harness.u32(s: String, acc: U32) -> U32:",
        "  match s:",
        "    case SNil{}:",
        "      acc",
        "    case SCon{Chr{c}, t}:",
        "      harness.u32(t, U32.add(U32.mul(acc, 10), U32.sub(c, 48)))",
        "",
        "def harness.nat(s: String, acc: Nat) -> Nat:",
        "  match s:",
        "    case SNil{}:",
        "      acc",
        "    case SCon{Chr{c}, t}:",
        "      harness.nat(t, Nat.add(Nat.mul(acc, 10n), U32.to_nat(U32.sub(c, 48))))",
        "",
        "def harness.args(xs: List<String>) -> String:",
        "  match xs:",
        f"    case {pat}:",
        f"      {show}({call})",
        "    case _:",
        '      "harness: bad arguments"',
        "",
        "def main() -> IO(Unit):",
        "  do IO<Unit>:",
        "    xs : List<String> <- IO.args()",
        "    IO.print(harness.args(xs))",
        "",
    ]


def lower(prog, entry: str, base_names: set[str]) -> str:
    lw = Lowerer(prog, base_names)
    lines = ["# GENERATED by trusted/verifier/bend/lower.py from VerifiedIR. DO NOT EDIT.",
             "import Base", ""]
    lines += lw.program()
    lines += harness(prog, entry)
    return "\n".join(lines)
