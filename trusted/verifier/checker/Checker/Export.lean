/-
BendVerify proof-export format `bendverify-export-v1` — the decoder.

TRUSTED (part of the replay checker). A proof certificate is NOT Lean source:
it is a list of kernel declarations in a flat JSON encoding. The checker never
elaborates, compiles or `#eval`s anything a competitor wrote; it decodes the
declarations with the strict decoder below and hands each one to the Lean
kernel (`Lean.Environment.replay`).

Encoding (all references point strictly backwards, so decoding is a single
pass and cannot loop):

  names  : [ ["s", parent, "str"] | ["n", parent, nat] ]      index 0 = anonymous (implicit)
  levels : [ ["z"] | ["s", l] | ["m", l, l] | ["i", l, l] | ["p", name] ]
  exprs  : [ ["bv", i] | ["so", l] | ["c", name, [l..]] | ["ap", e, e]
           | ["lm", name, e, e, bi] | ["pi", name, e, e, bi]
           | ["lt", name, e, e, e, nondep] | ["ln", "digits"] | ["ls", str]
           | ["pj", name, idx, e] ]
  decls  : [ {"k": "thm", "n": name, "lp": [name..], "t": e, "v": e}
           | {"k": "def", "n": name, "lp": [name..], "t": e, "v": e, "h": "o"|"a"|nat}
           | {"k": "ind", "lp": [name..], "np": nat,
              "types": [{"n": name, "t": e, "ctors": [{"n": name, "t": e}, ..]}, ..]} ]

Declarations are sent to the kernel IN THE GIVEN ORDER (dependencies first).
For an inductive block only the types and constructor signatures are
transmitted: the kernel checks them (positivity, universes) and generates the
constructors and recursors itself; nothing kernel-generated is taken from the
competitor.

`bi` ∈ "d" (default), "i" (implicit), "s" (strict implicit), "c" (instance).
Only theorems, safe definitions and (safe) inductive types can be expressed:
axioms, opaque constants, quotients, unsafe and partial definitions are
unrepresentable by construction.
-/
import Lean

open Lean

namespace Checker

abbrev DecodeM := Except String

structure Tables where
  names : Array Name := #[Name.anonymous]
  levels : Array Level := #[]
  exprs : Array Expr := #[]

def getArr (j : Json) (what : String) : DecodeM (Array Json) :=
  match j with
  | .arr a => pure a
  | _ => throw s!"{what}: expected array"

def getStr (j : Json) (what : String) : DecodeM String :=
  match j with
  | .str s => pure s
  | _ => throw s!"{what}: expected string"

def getNat (j : Json) (what : String) : DecodeM Nat :=
  match j.getNat? with
  | .ok n => pure n
  | .error _ => throw s!"{what}: expected natural number"

def idx {α : Type} [Inhabited α] (a : Array α) (i : Nat) (bound : Nat) (what : String) : DecodeM α :=
  if i < bound ∧ i < a.size then pure a[i]! else throw s!"{what}: reference {i} out of range"

def decodeNames (js : Array Json) : DecodeM (Array Name) := do
  let mut out : Array Name := #[Name.anonymous]
  for j in js do
    let a ← getArr j "name"
    if a.size != 3 then throw "name: arity"
    let tag ← getStr a[0]! "name tag"
    let p ← getNat a[1]! "name parent"
    let parent ← idx out p out.size "name parent"
    match tag with
    | "s" => out := out.push (Name.str parent (← getStr a[2]! "name string"))
    | "n" => out := out.push (Name.num parent (← getNat a[2]! "name number"))
    | _ => throw s!"name: unknown tag {tag}"
  return out

def decodeLevels (names : Array Name) (js : Array Json) : DecodeM (Array Level) := do
  let mut out : Array Level := #[]
  for j in js do
    let a ← getArr j "level"
    if a.size == 0 then throw "level: empty"
    let tag ← getStr a[0]! "level tag"
    let lv ← match tag, a.size with
      | "z", 1 => pure Level.zero
      | "s", 2 => do pure (Level.succ (← idx out (← getNat a[1]! "l") out.size "level"))
      | "m", 3 => do
        pure (Level.max (← idx out (← getNat a[1]! "l") out.size "level")
                        (← idx out (← getNat a[2]! "l") out.size "level"))
      | "i", 3 => do
        pure (Level.imax (← idx out (← getNat a[1]! "l") out.size "level")
                         (← idx out (← getNat a[2]! "l") out.size "level"))
      | "p", 2 => do pure (Level.param (← idx names (← getNat a[1]! "n") names.size "level param"))
      | _, _ => throw s!"level: bad tag/arity {tag}"
    out := out.push lv
  return out

def decodeBI (j : Json) : DecodeM BinderInfo := do
  match ← getStr j "binder info" with
  | "d" => pure .default
  | "i" => pure .implicit
  | "s" => pure .strictImplicit
  | "c" => pure .instImplicit
  | s => throw s!"binder info: {s}"

def decodeExprs (names : Array Name) (levels : Array Level) (js : Array Json) :
    DecodeM (Array Expr) := do
  let mut out : Array Expr := #[]
  for j in js do
    let a ← getArr j "expr"
    if a.size == 0 then throw "expr: empty"
    let tag ← getStr a[0]! "expr tag"
    let n := out.size
    let E (k : Nat) : DecodeM Expr := do idx out (← getNat a[k]! "expr ref") n "expr"
    let N (k : Nat) : DecodeM Name := do idx names (← getNat a[k]! "name ref") names.size "name"
    let e ← match tag, a.size with
      | "bv", 2 => do pure (Expr.bvar (← getNat a[1]! "bvar"))
      | "so", 2 => do pure (Expr.sort (← idx levels (← getNat a[1]! "l") levels.size "level"))
      | "c", 3 => do
        let ls ← getArr a[2]! "const levels"
        let ls ← ls.mapM fun l => do idx levels (← getNat l "l") levels.size "level"
        pure (Expr.const (← N 1) ls.toList)
      | "ap", 3 => do pure (Expr.app (← E 1) (← E 2))
      | "lm", 5 => do pure (Expr.lam (← N 1) (← E 2) (← E 3) (← decodeBI a[4]!))
      | "pi", 5 => do pure (Expr.forallE (← N 1) (← E 2) (← E 3) (← decodeBI a[4]!))
      | "lt", 6 => do
        let nd ← match a[5]! with
          | .bool b => pure b
          | _ => throw "let: nondep flag"
        pure (Expr.letE (← N 1) (← E 2) (← E 3) (← E 4) nd)
      | "ln", 2 => do
        let s ← getStr a[1]! "nat literal"
        if s.isEmpty || s.length > 100000 || !s.all Char.isDigit then throw "nat literal: digits"
        pure (Expr.lit (.natVal s.toNat!))
      | "ls", 2 => do pure (Expr.lit (.strVal (← getStr a[1]! "string literal")))
      | "pj", 4 => do pure (Expr.proj (← N 1) (← getNat a[2]! "proj idx") (← E 3))
      | _, _ => throw s!"expr: bad tag/arity {tag}"
    out := out.push e
  return out

def getField (j : Json) (k : String) : DecodeM Json :=
  match j.getObjVal? k with
  | .ok v => pure v
  | .error _ => throw s!"decl: missing field {k}"

/-- Decode the declarations of an export, in order. -/
def decodeDecls (t : Tables) (js : Array Json) : DecodeM (Array Declaration) := do
  let E (j : Json) (what : String) : DecodeM Expr := do
    idx t.exprs (← getNat j what) t.exprs.size what
  let N (j : Json) (what : String) : DecodeM Name := do
    idx t.names (← getNat j what) t.names.size what
  let mut out : Array Declaration := #[]
  for j in js do
    let kind ← getStr (← getField j "k") "decl kind"
    let allowed := match kind with
      | "thm" => ["k", "n", "lp", "t", "v"]
      | "def" => ["k", "n", "lp", "t", "v", "h"]
      | "ind" => ["k", "lp", "np", "types"]
      | _ => []
    if allowed.isEmpty then throw s!"decl: forbidden declaration kind '{kind}' (only thm/def/ind are admissible)"
    match j with
    | .obj kvs =>
      for (k, _) in kvs.toArray do
        unless k ∈ allowed do throw s!"decl: unexpected field {k}"
    | _ => throw "decl: expected object"
    let lps ← (← getArr (← getField j "lp") "level params").mapM fun l => N l "level param"
    match kind with
    | "thm" =>
      let name ← N (← getField j "n") "decl name"
      out := out.push (.thmDecl { name, levelParams := lps.toList, type := ← E (← getField j "t") "type",
                                  value := ← E (← getField j "v") "value", all := [name] })
    | "def" =>
      let name ← N (← getField j "n") "decl name"
      let hints ← match ← getField j "h" with
        | .str "o" => pure ReducibilityHints.opaque
        | .str "a" => pure ReducibilityHints.abbrev
        | h => do
          let n ← getNat h "hints"
          if n ≥ 2 ^ 32 then throw "hints: too large"
          pure (ReducibilityHints.regular n.toUInt32)
      out := out.push (.defnDecl { name, levelParams := lps.toList, type := ← E (← getField j "t") "type",
                                   value := ← E (← getField j "v") "value", hints, safety := .safe,
                                   all := [name] })
    | _ =>
      let np ← getNat (← getField j "np") "numParams"
      let types ← (← getArr (← getField j "types") "types").mapM fun ty => do
        let ctors ← (← getArr (← getField ty "ctors") "ctors").mapM fun c => do
          pure ({ name := ← N (← getField c "n") "ctor name", type := ← E (← getField c "t") "ctor type" }
            : Constructor)
        pure ({ name := ← N (← getField ty "n") "type name", type := ← E (← getField ty "t") "type",
                ctors := ctors.toList } : InductiveType)
      if types.isEmpty then throw "ind: empty block"
      out := out.push (.inductDecl lps.toList np types.toList false)
  return out

def decodeExport (j : Json) : DecodeM (Tables × Array Declaration × Array Name) := do
  match j with
  | .obj kvs =>
    for (k, _) in kvs.toArray do
      unless k ∈ ["format", "names", "levels", "exprs", "decls", "imports"] do
        throw s!"export: unexpected field {k}"
  | _ => throw "export: expected object"
  let fmt ← getStr (← getField j "format") "format"
  if fmt != "bendverify-export-v1" then throw s!"export: unsupported format {fmt}"
  let names ← decodeNames (← getArr (← getField j "names") "names")
  let levels ← decodeLevels names (← getArr (← getField j "levels") "levels")
  let exprs ← decodeExprs names levels (← getArr (← getField j "exprs") "exprs")
  let t : Tables := { names, levels, exprs }
  let decls ← decodeDecls t (← getArr (← getField j "decls") "decls")
  let imports ← (← getArr (← getField j "imports") "imports").mapM fun i => do
    pure (String.toName (← getStr i "import"))
  return (t, decls, imports)

end Checker
