import CompletedProof
open Lean Elab Command Meta
set_option pp.universes true
set_option pp.explicit true
#print BareModelCompletion.completed_theorem_1
#print axioms BareModelCompletion.completed_theorem_1
#print axioms BareModelCompletion.completed_exact_solution_exists
#print axioms BareModelCompletion.completed_exact_solution_iff
#print axioms BareModelCompletion.completed_exact_solution_unique
run_cmd do
  let env ← getEnv
  let isProject := fun (n : Name) => n.toString.startsWith "KdV." || n.toString.startsWith "BareModelCompletion."
  let namesIn := fun (e : Expr) => e.getUsedConstants.toList.filter isProject
  let mut pending := namesIn (env.find? ``BareModelCompletion.completed_theorem_1).get!.type
  let mut seen : List Name := []
  while !pending.isEmpty do
    let n := pending.head!
    pending := pending.tail!
    if seen.contains n then continue
    seen := n :: seen
    let some ci := env.find? n | continue
    logInfo m!"RECURSIVE_DECL {n}
TYPE {ci.type}"
    pending := namesIn ci.type ++ pending
    match ci with
    | .defnInfo d =>
      logInfo m!"DEFINITION {d.value}"
      pending := namesIn d.value ++ pending
    | .inductInfo i =>
      for ctor in i.ctors do
        let some cc := env.find? ctor | continue
        logInfo m!"CONSTRUCTOR {ctor}
FIELDS {cc.type}"
        pending := namesIn cc.type ++ pending
    | _ => pure ()
  logInfo m!"RECURSIVE_PROJECT_DECLARATION_COUNT {seen.length}"
run_cmd do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    if !(n.toString.startsWith "KdV." || n.toString.startsWith "BareModelCompletion." || n == ``theorem_1) then continue
    match ci with
    | .axiomInfo a => logInfo m!"PROJECT_AXIOM {n} : {a.type}"
    | .opaqueInfo o => logInfo m!"PROJECT_OPAQUE {n} unsafe={o.isUnsafe} : {o.type}"
    | .defnInfo d =>
      if d.safety != .safe then logInfo m!"PROJECT_NONSAFE {n} {repr d.safety}"
    | _ => pure ()
