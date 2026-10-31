import Mathlib
set_option pp.universes true
set_option pp.explicit false
open Lean Elab Command in
run_elab do
  let name ← resolveGlobalConstNoOverloadCore `ENNReal.tsum_eq_iSup_sum
  let info ← getConstInfo name
  match info with
  | .thmInfo _ => pure ()
  | _ => throwError "This source is not a proved theorem declaration"
  let actual ← findModuleOf? name
  IO.println s!"RESOLVED_NAME:M015:{name}"
  match actual with
  | some source => IO.println s!"RESOLVED_MODULE:M015:{source}"
  | none => throwError "This source has no imported module"
  IO.println "BEGIN_SIGNATURE:M015"
  let printed ← Meta.ppExpr info.type
  IO.println s!"@{name} : {printed}"
#eval IO.println "BEGIN_AXIOMS:M015"
#print axioms ENNReal.tsum_eq_iSup_sum
#eval IO.println "END_SOURCE:M015"
