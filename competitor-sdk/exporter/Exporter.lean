/-
bendverify-export — competitor-side tool (UNTRUSTED).

Serialises the kernel declarations a proof depends on into the
`bendverify-export-v1` JSON format that the verifier's checker replays.

    bendverify-export <out.json> <Module> <root> [<root> ...]

Every constant reachable from the roots that is not defined in a trusted
module (Init, BendVerify, Contest.*) is exported. Nothing about this tool is
trusted: the verifier decodes the file with its own decoder and re-checks
every declaration in the Lean kernel. A modified exporter can only produce
declarations, which the kernel then accepts or rejects.
-/
import Lean

open Lean

namespace Exporter

structure St where
  names : Std.HashMap Name Nat := {}
  nameOut : Array Json := #[]
  levels : Std.HashMap Level Nat := {}
  levelOut : Array Json := #[]
  exprs : Std.HashMap Expr Nat := {}
  exprOut : Array Json := #[]

abbrev M := StateT St IO

partial def name (n : Name) : M Nat := do
  if n.isAnonymous then return 0
  if let some i := (← get).names[n]? then return i
  let j ← match n with
    | .str p s => do pure (Json.arr #["s", toJson (← name p), toJson s])
    | .num p k => do pure (Json.arr #["n", toJson (← name p), toJson k])
    | .anonymous => unreachable!
  modifyGet fun s =>
    let i := s.nameOut.size + 1
    (i, { s with names := s.names.insert n i, nameOut := s.nameOut.push j })

partial def level (l : Level) : M Nat := do
  if let some i := (← get).levels[l]? then return i
  let j ← match l with
    | .zero => pure (Json.arr #["z"])
    | .succ a => do pure (Json.arr #["s", toJson (← level a)])
    | .max a b => do pure (Json.arr #["m", toJson (← level a), toJson (← level b)])
    | .imax a b => do pure (Json.arr #["i", toJson (← level a), toJson (← level b)])
    | .param n => do pure (Json.arr #["p", toJson (← name n)])
    | .mvar _ => throw (IO.userError "level metavariable in declaration")
  modifyGet fun s =>
    let i := s.levelOut.size
    (i, { s with levels := s.levels.insert l i, levelOut := s.levelOut.push j })

def bi : BinderInfo → Json
  | .default => "d" | .implicit => "i" | .strictImplicit => "s" | .instImplicit => "c"

partial def expr (e : Expr) : M Nat := do
  -- metadata is irrelevant to the kernel: export the annotated expression
  if let .mdata _ x := e then return (← expr x)
  if let some i := (← get).exprs[e]? then return i
  let j ← match e with
    | .bvar i => pure (Json.arr #["bv", toJson i])
    | .sort l => do pure (Json.arr #["so", toJson (← level l)])
    | .const n ls => do pure (Json.arr #["c", toJson (← name n), toJson (← ls.toArray.mapM level)])
    | .app f a => do pure (Json.arr #["ap", toJson (← expr f), toJson (← expr a)])
    | .lam n t b i => do pure (Json.arr #["lm", toJson (← name n), toJson (← expr t), toJson (← expr b), bi i])
    | .forallE n t b i => do pure (Json.arr #["pi", toJson (← name n), toJson (← expr t), toJson (← expr b), bi i])
    | .letE n t v b nd => do
      pure (Json.arr #["lt", toJson (← name n), toJson (← expr t), toJson (← expr v), toJson (← expr b), toJson nd])
    | .lit (.natVal k) => pure (Json.arr #["ln", toJson (toString k)])
    | .lit (.strVal s) => pure (Json.arr #["ls", toJson s])
    | .proj s i x => do pure (Json.arr #["pj", toJson (← name s), toJson i, toJson (← expr x)])
    | .mdata _ _ => throw (IO.userError "unreachable: mdata")
    | .fvar _ => throw (IO.userError "free variable in declaration")
    | .mvar _ => throw (IO.userError "metavariable in declaration")
  modifyGet fun s =>
    let i := s.exprOut.size
    (i, { s with exprs := s.exprs.insert e i, exprOut := s.exprOut.push j })

def trusted (mod : Name) : Bool :=
  mod.getRoot == `Init || mod.getRoot == `BendVerify || mod.getRoot == `Contest

inductive Item where
  | const (n : Name)
  | block (types : List Name)

/-- Post-order walk: every emitted item comes after everything it uses. -/
partial def visit (env : Environment) (skip : Name → Bool) (n : Name) :
    StateT (NameSet × Array Item) IO Unit := do
  if (← get).1.contains n || skip n then return
  let some ci := env.find? n | throw (IO.userError s!"unknown constant {n}")
  match ci with
  | .ctorInfo v => visit env skip v.induct
  | .recInfo v => visit env skip (v.all.headD n)
  | .inductInfo v =>
    -- the whole mutual block at once
    let blockNames := v.all
    let mut members : List Name := []
    for t in blockNames do
      members := members ++ [t] ++ (match env.find? t with
        | some (.inductInfo tv) => tv.ctors
        | _ => [])
    modify fun (vs, is) => (members.foldl (·.insert ·) vs, is)
    for t in blockNames do
      let some (.inductInfo tv) := env.find? t | throw (IO.userError s!"bad block {t}")
      for m in tv.type.getUsedConstants do visit env skip m
      for c in tv.ctors do
        let some cc := env.find? c | throw (IO.userError s!"bad ctor {c}")
        for m in cc.type.getUsedConstants do
          unless members.contains m do visit env skip m
    modify fun (vs, is) => (vs, is.push (.block blockNames))
  | .defnInfo _ | .thmInfo _ =>
    modify fun (vs, is) => (vs.insert n, is)
    for m in ci.getUsedConstantsAsSet do visit env skip m
    modify fun (vs, is) => (vs, is.push (.const n))
  | _ => throw (IO.userError s!"{n}: only theorems, definitions and inductive types can be exported")

def main (args : List String) : IO UInt32 := do
  let out :: modName :: roots := args
    | IO.eprintln "usage: bendverify-export <out.json> <Module> <root>..."; return 2
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := modName.toName }] {} (loadExts := false)
  let modOf (n : Name) : Name :=
    match env.getModuleIdxFor? n with
    | some i => env.header.moduleNames[i.toNat]!
    | none => Name.anonymous
  let skip (n : Name) : Bool := trusted (modOf n)
  let ((), (_, items)) ← (roots.forM fun r => visit env skip r.toName).run ({}, #[])
  let mut imports : Array Json := #[]
  for m in env.header.moduleNames do
    if trusted m && m.getRoot != `Init then imports := imports.push (toJson m.toString)
  let act : M (Array Json) := items.mapM fun it => do
    match it with
    | .const n =>
      let some ci := env.find? n | throw (IO.userError s!"unknown constant {n}")
      let lp ← ci.levelParams.toArray.mapM name
      match ci with
      | .thmInfo v =>
        pure (Json.mkObj [("k", "thm"), ("n", toJson (← name n)), ("lp", toJson lp),
          ("t", toJson (← expr v.type)), ("v", toJson (← expr v.value))])
      | .defnInfo v =>
        let h : Json := match v.hints with
          | .opaque => "o" | .abbrev => "a" | .regular k => toJson k.toNat
        pure (Json.mkObj [("k", "def"), ("n", toJson (← name n)), ("lp", toJson lp),
          ("t", toJson (← expr v.type)), ("v", toJson (← expr v.value)), ("h", h)])
      | _ => throw (IO.userError s!"{n}: unexpected constant kind")
    | .block ts =>
      let some (.inductInfo v0) := env.find? ts.head! | throw (IO.userError "bad block")
      let lp ← v0.levelParams.toArray.mapM name
      let types ← ts.toArray.mapM fun t => do
        let some (.inductInfo v) := env.find? t | throw (IO.userError s!"bad block {t}")
        let ctors ← v.ctors.toArray.mapM fun c => do
          let some cc := env.find? c | throw (IO.userError s!"bad ctor {c}")
          pure (Json.mkObj [("n", toJson (← name c)), ("t", toJson (← expr cc.type))])
        pure (Json.mkObj [("n", toJson (← name t)), ("t", toJson (← expr v.type)), ("ctors", Json.arr ctors)])
      pure (Json.mkObj [("k", "ind"), ("lp", toJson lp), ("np", toJson v0.numParams), ("types", Json.arr types)])
  let (decls, st) ← act.run {}
  let j := Json.mkObj [("format", "bendverify-export-v1"), ("imports", Json.arr imports),
    ("names", Json.arr st.nameOut), ("levels", Json.arr st.levelOut),
    ("exprs", Json.arr st.exprOut), ("decls", Json.arr decls)]
  IO.FS.writeFile out j.compress
  IO.eprintln s!"exported {decls.size} declarations, {st.exprOut.size} expression nodes"
  return 0

end Exporter

def main (args : List String) : IO UInt32 := Exporter.main args
