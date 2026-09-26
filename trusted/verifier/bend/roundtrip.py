"""Translation validation of the lowering. TRUSTED.

After a candidate IR `Q` is lowered to Bend, the lowered file is re-extracted
with the trusted extractor. The result must be `Q` itself up to renumbering of
functions and datatypes by name (the extractor numbers them in discovery
order). This makes the Python printer in lower.py untrusted-in-effect: any
printing bug that changes meaning changes the re-extracted IR and is caught.
"""

from __future__ import annotations


class RoundTripError(Exception):
    pass


def _renumber(prog):
    adt_names = [a["name"] for a in prog["adts"]]
    fn_names = [f["name"] for f in prog["fns"]]

    def ty(t):
        return t if isinstance(t, str) else ["adt", adt_names[t[1]]]

    def ex(e):
        tag = e[0]
        if tag in ("var", "u32", "nat"):
            return list(e)
        if tag == "prim":
            return ["prim", e[1], [ex(a) for a in e[2]]]
        if tag == "ctr":
            return ["ctr", adt_names[e[1]], e[2], [ex(a) for a in e[3]]]
        if tag == "call":
            return ["call", fn_names[e[1]], [ex(a) for a in e[2]]]
        if tag == "let":
            return ["let", ex(e[1]), ex(e[2])]
        if tag == "par":
            return ["par", ex(e[1]), ex(e[2]), ex(e[3])]
        if tag == "mat":
            return ["mat", adt_names[e[1]], ex(e[2]), [[k, ex(b)] for k, b in e[3]]]
        if tag == "natcase":
            return ["natcase", ex(e[1]), ex(e[2]), ex(e[3])]
        raise RoundTripError(f"unknown tag {tag}")

    adts = {a["name"]: [(c["name"], [ty(t) for t in c["fields"]]) for c in a["ctors"]]
            for a in prog["adts"]}
    fns = {f["name"]: ([ty(t) for t in f["params"]], ty(f["ret"]), ex(f["body"])) for f in prog["fns"]}
    return adts, fns


def reachable(prog, entry):
    idx = {f["name"]: i for i, f in enumerate(prog["fns"])}
    seen, stack = set(), [idx[entry]]
    while stack:
        i = stack.pop()
        if i in seen:
            continue
        seen.add(i)

        def walk(e):
            if e[0] == "call":
                stack.append(e[1])
            for x in e[1:]:
                if isinstance(x, list):
                    if x and isinstance(x[0], str):
                        walk(x)
                    else:
                        for y in x:
                            if isinstance(y, list) and y and isinstance(y[0], str):
                                walk(y)
                            elif isinstance(y, list) and len(y) == 2 and isinstance(y[1], list):
                                walk(y[1])
        walk(prog["fns"][i]["body"])
    return {prog["fns"][i]["name"] for i in seen}


def check(q, q_rt, entry):
    """q: the proven IR; q_rt: re-extraction of its lowering. The re-extraction
    contains exactly the functions reachable from the entry."""
    qa, qf = _renumber(q)
    ra, rf = _renumber(q_rt)
    live = reachable(q, entry)
    if set(rf) != live:
        raise RoundTripError(f"function sets differ: {sorted(set(rf) ^ live)}")
    for name in live:
        if qf[name] != rf[name]:
            raise RoundTripError(f"function {name} changed through lowering")
    for name, ctors in ra.items():
        if qa.get(name) != ctors:
            raise RoundTripError(f"datatype {name} changed through lowering")
