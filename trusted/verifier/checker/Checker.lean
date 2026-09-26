/-
bendverify-check — the independent root proof checker.

TRUSTED. Usage:

    bendverify-check <request.json>

`request.json` is written by the trusted verifier (never by a competitor):

    { "lean_sysroot": "/path/to/pinned/toolchain",
      "imports": ["BendVerify", "Contest.Obligation"],       -- trusted modules only
      "export": "/path/to/proof/export.json",              -- competitor data
      "goals": [ {"goal": "Contest.Obligation.goal_1", "proof": "Submission.step_1"}, ... ],
      "compose": {"name": "Contest.Certified.root",
                  "type": "Contest.Obligation.RootGoal",
                  "fn":   "Contest.Obligation.root_of_steps"},
      "allowed_axioms": ["propext", "Quot.sound", "Classical.choice"],
      "reserved_prefixes": ["Contest"] }

Steps:
 1. Build the trusted environment by importing ONLY the listed trusted modules
    (compiled by the verifier from trusted sources and generated obligations).
 2. Decode the competitor export (Checker/Export.lean). Reject any declaration
    whose name is already in the environment (no redeclaration, so no trusted
    constant can be shadowed) or lies under a reserved prefix (`Contest`, the
    namespace the verifier generates into).
 3. Send every declaration to the kernel, in the export's order.
 4. For every goal, require the named proof to be a theorem, without universe
    parameters, whose type is *syntactically* the trusted goal constant.
 5. Compose the certified root theorem (`fn goal-proofs...`) and add it through
    the kernel with the trusted root type.
 6. Compute the axiom closure of the root; require it ⊆ allowed axioms.
 7. Print a single JSON object on stdout. The caller parses it structurally and
    re-checks the fields; the process exit code is NOT the verdict.
-/
import Lean
import Checker.Export

open Lean

namespace Checker

def fail (msg : String) : IO α := throw (IO.userError msg)

def jsonGetStr (j : Json) (k : String) : IO String :=
  match j.getObjValAs? String k with
  | .ok s => pure s
  | .error e => fail s!"request: {k}: {e}"

def jsonGetArr (j : Json) (k : String) : IO (Array Json) :=
  match j.getObjVal? k with
  | .ok (.arr a) => pure a
  | _ => fail s!"request: {k}: expected array"

def strArr (a : Array Json) (what : String) : IO (Array String) :=
  a.mapM fun j => match j with
    | .str s => pure s
    | _ => fail s!"request: {what}: expected strings"

/-- Axioms (and any other non-definitional leaves) reachable from `root`. -/
def axiomClosure (env : Environment) (root : Name) : IO (Array Name × Array Name) := do
  let mut seen : NameSet := {}
  let mut stack : Array Name := #[root]
  let mut axioms : Array Name := #[]
  let mut suspicious : Array Name := #[]
  while h : stack.size > 0 do
    let n := stack.back
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    match env.find? n with
    | none => suspicious := suspicious.push n
    | some ci =>
      match ci with
      | .axiomInfo _ => axioms := axioms.push n
      | .opaqueInfo v => if v.isUnsafe then suspicious := suspicious.push n
      | .defnInfo v => if v.safety != .safe then suspicious := suspicious.push n
      | _ => pure ()
      if ci.isUnsafe then suspicious := suspicious.push n
      for m in ci.getUsedConstantsAsSet do
        unless seen.contains m do stack := stack.push m
  return (axioms.qsort (·.toString < ·.toString), suspicious)

def run (reqPath : String) : IO Json := do
  let req ← match Json.parse (← IO.FS.readFile reqPath) with
    | .ok j => pure j
    | .error e => fail s!"request: {e}"
  let imports ← strArr (← jsonGetArr req "imports") "imports"
  let allowed ← strArr (← jsonGetArr req "allowed_axioms") "allowed_axioms"
  let reserved ← strArr (← jsonGetArr req "reserved_prefixes") "reserved_prefixes"
  let exportPath ← jsonGetStr req "export"
  -- 1. trusted environment (the Lean sysroot is pinned by the request, never
  --    discovered from PATH)
  let sysroot ← jsonGetStr req "lean_sysroot"
  initSearchPath sysroot
  let env ← importModules (imports.map fun m => { module := m.toName }) {} (loadExts := false)
  -- 2. decode competitor data
  let raw ← IO.FS.readFile exportPath
  let ej ← match Json.parse raw with
    | .ok j => pure j
    | .error e => fail s!"export: not JSON: {e}"
  let (_, decls, exportImports) ← match decodeExport ej with
    | .ok r => pure r
    | .error e => fail s!"export: {e}"
  -- the proof's declared import graph must lie inside the trusted environment
  let trustedMods := env.header.moduleNames
  for i in exportImports do
    unless trustedMods.contains i do
      fail s!"export: declares import {i} outside the trusted import graph"
  -- names introduced by the export (types, constructors, generated recursors)
  let declNames (d : Declaration) : List Name :=
    match d with
    | .inductDecl _ _ tys _ => tys.flatMap fun ty => ty.name :: (ty.name ++ `rec) :: ty.ctors.map (·.name)
    | .thmDecl v => [v.name]
    | .defnDecl v => [v.name]
    | _ => []
  let mut introduced : NameSet := {}
  for d in decls do
    for n in declNames d do
      if n.isAnonymous then fail "export: anonymous declaration"
      if env.contains n then fail s!"export: redeclares existing constant {n}"
      if introduced.contains n then fail s!"export: duplicate declaration {n}"
      for p in reserved do
        if (p.toName).isPrefixOf n then fail s!"export: declaration {n} is in reserved namespace {p}"
      introduced := introduced.insert n
  -- 3. kernel: every declaration, in the given order (dependencies first)
  let mut env := env
  for d in decls do
    match env.addDeclCore 0 d none with
    | .ok e => env := e
    | .error ex =>
      fail s!"kernel rejected a declaration ({declNames d |>.headD Name.anonymous}): {← (ex.toMessageData {}).toString}"
  let exported (n : Name) : Bool := introduced.contains n
  -- 4. goals
  let mut goalOut : Array Json := #[]
  let mut proofs : Array Name := #[]
  for g in ← jsonGetArr req "goals" do
    let goal := (← jsonGetStr g "goal").toName
    let proof := (← jsonGetStr g "proof").toName
    unless exported proof do fail s!"goal {goal}: proof {proof} is not in the export"
    let some gci := env.find? goal | fail s!"goal {goal}: not in trusted environment"
    unless gci.levelParams.isEmpty do fail s!"goal {goal}: unexpected universe parameters"
    match env.find? proof with
    | some (.thmInfo tv) =>
      unless tv.levelParams.isEmpty do fail s!"{proof}: must not have universe parameters"
      unless tv.type == Expr.const goal [] do
        fail s!"{proof}: proves a different statement than {goal}"
    | _ => fail s!"{proof}: is not a theorem"
    let (axs, sus) ← axiomClosure env proof
    unless sus.isEmpty do fail s!"{proof}: depends on unsafe/unknown constants {sus}"
    for a in axs do
      unless allowed.contains a.toString do fail s!"{proof}: uses non-allowlisted axiom {a}"
    proofs := proofs.push proof
    goalOut := goalOut.push (Json.mkObj [("goal", toJson goal.toString), ("proof", toJson proof.toString),
      ("axioms", toJson (axs.map (·.toString)))])
  -- 5. compose the root
  let comp ← match req.getObjVal? "compose" with
    | .ok c => pure c
    | .error _ => fail "request: compose"
  let rootName := (← jsonGetStr comp "name").toName
  let rootType := (← jsonGetStr comp "type").toName
  let rootFn := (← jsonGetStr comp "fn").toName
  let value := mkAppN (Expr.const rootFn []) (proofs.map fun p => Expr.const p [])
  let decl := Declaration.thmDecl { name := rootName, levelParams := [], type := Expr.const rootType [],
                                    value, all := [rootName] }
  let envRoot ← match env.addDeclCore 0 decl none with
    | .ok e => pure e
    | .error ex => fail s!"root composition rejected by kernel: {← (ex.toMessageData {}).toString}"
  -- 6. axiom audit of the root
  let (axs, sus) ← axiomClosure envRoot rootName
  unless sus.isEmpty do fail s!"root depends on unsafe/unknown constants {sus}"
  for a in axs do
    unless allowed.contains a.toString do fail s!"root uses non-allowlisted axiom {a}"
  return Json.mkObj [
    ("result", "PASS"),
    ("kernel_replayed", toJson decls.size),
    ("goals", Json.arr goalOut),
    ("root", Json.mkObj [("name", toJson rootName.toString), ("type", toJson rootType.toString),
                         ("axioms", toJson (axs.map (·.toString)))])]

end Checker

def main (args : List String) : IO UInt32 := do
  match args with
  | [req] =>
    try
      let out ← Checker.run req
      IO.println out.compress
      return 0
    catch e =>
      IO.println (Json.mkObj [("result", "FAIL"), ("reason", toJson (toString e))]).compress
      return 1
  | _ =>
    IO.eprintln "usage: bendverify-check <request.json>"
    return 2
