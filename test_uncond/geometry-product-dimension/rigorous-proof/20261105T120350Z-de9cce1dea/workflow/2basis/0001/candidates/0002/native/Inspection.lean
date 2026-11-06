import Mathlib
open scoped ENNReal NNReal Topology
open Set MeasureTheory
namespace BasisObjects
abbrev Rn (n : ℕ) := EuclideanSpace ℝ (Fin n)
noncomputable def content {X : Type*} [EMetricSpace X]
    (s : ℝ) (r : ℝ≥0∞) (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)
    (_ : ∀ i, Metric.ediam (U i) ≤ r),
      ∑' i, ⨆ (_ : (U i).Nonempty), (Metric.ediam (U i)) ^ s
def euclideanLift (n : ℕ) : Rn n × ℝ → WithLp 2 (Rn n × ℝ) :=
  WithLp.toLp 2
end BasisObjects

namespace YuiBasis
set_option autoImplicit false
set_option Elab.async false in
theorem B001 : ∀ (X : Type) [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (a : ℝ) (A : Set X),
  MeasureTheory.Measure.hausdorffMeasure a A =
    ⨆ (r : ℝ≥0∞) (_ : 0 < r), BasisObjects.content a r A := by
  intro X _ _ _ a A
  exact MeasureTheory.Measure.hausdorffMeasure_apply a A
set_option Elab.async false in
theorem B002 : ∀ (X : Type) [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (A : Set X) (d : ℝ≥0),
  (((d : ℝ≥0∞) < dimH A) → MeasureTheory.Measure.hausdorffMeasure (d : ℝ) A = ⊤) ∧
  ((dimH A < (d : ℝ≥0∞)) → MeasureTheory.Measure.hausdorffMeasure (d : ℝ) A = 0) ∧
  ((MeasureTheory.Measure.hausdorffMeasure (d : ℝ) A ≠ ⊤) → dimH A ≤ (d : ℝ≥0∞)) ∧
  ((MeasureTheory.Measure.hausdorffMeasure (d : ℝ) A = ⊤) → (d : ℝ≥0∞) ≤ dimH A) := by
  intro X _ _ _ A d
  exact ⟨hausdorffMeasure_of_lt_dimH,
    hausdorffMeasure_of_dimH_lt,
    dimH_le_of_hausdorffMeasure_ne_top,
    le_dimH_of_hausdorffMeasure_eq_top⟩
set_option Elab.async false in
theorem B003 : ∀ (X : Type) [EMetricSpace X] (A B : Set X), A ⊆ B → dimH A ≤ dimH B := by
  intro X _ A B h
  exact dimH_mono h
set_option Elab.async false in
theorem B004 : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X],
  dimH (Set.univ : Set X) = (Module.finrank ℝ X : ℝ≥0∞) := by
  intro X _ _ _
  exact Real.dimH_univ_eq_finrank X
set_option Elab.async false in
theorem B005 : ∀ (X Y : Type) [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] (e : X ≃L[ℝ] Y) (A : Set X),
  dimH (e '' A) = dimH A := by
  intro X Y _ _ _ _ e A
  exact e.dimH_image A
set_option Elab.async false in
theorem B006 : ∀ (X Y : Type) [EMetricSpace X] [EMetricSpace Y] (f : X → Y),
  Isometry f → ∀ A : Set X, dimH (f '' A) = dimH A := by
  intro X Y _ _ f hf A
  exact hf.dimH_image A
set_option Elab.async false in
theorem B007 : ∀ a b : ℝ, MeasureTheory.volume (Set.Icc a b) = ENNReal.ofReal (b - a) := by
  intro a b
  exact Real.volume_Icc
set_option Elab.async false in
theorem B008 : ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (f : ℕ → X → ℝ≥0∞),
  (∀ i, AEMeasurable (f i) μ) →
  (∫⁻ x, ∑' i, f i x ∂μ) = ∑' i, ∫⁻ x, f i x ∂μ := by
  intro X _ μ f hf
  exact MeasureTheory.lintegral_tsum hf
set_option Elab.async false in
theorem B009 : ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (f g : X → ℝ≥0∞),
  (∀ x, f x ≤ g x) → (∫⁻ x, f x ∂μ) ≤ ∫⁻ x, g x ∂μ := by
  intro X _ μ f g h
  exact MeasureTheory.lintegral_mono h
set_option Elab.async false in
theorem B010 : ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (S : Set X) (c : ℝ≥0∞),
  MeasurableSet S → (∫⁻ x, S.indicator (fun _ => c) x ∂μ) = c * μ S := by
  intro X _ μ S c hS
  exact MeasureTheory.lintegral_indicator_const hS c
set_option Elab.async false in
theorem B011 : ∀ (n : ℕ) (S : Set (BasisObjects.Rn n × ℝ)),
  dimH (BasisObjects.euclideanLift n '' S) = dimH S := by
  intro n S
  exact YuiBasis.B005 (BasisObjects.Rn n × ℝ) (WithLp 2 (BasisObjects.Rn n × ℝ))
    (WithLp.prodContinuousLinearEquiv 2 ℝ (BasisObjects.Rn n) ℝ).symm S
set_option Elab.async false in
theorem B012 : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  (A : Set X), (interior A).Nonempty → dimH A = (Module.finrank ℝ X : ℝ≥0∞) := by
  intro X _ _ _ A h
  exact Real.dimH_of_nonempty_interior h
set_option Elab.async false in
theorem B013 : ∀ (n : ℕ) (p : WithLp 2 (BasisObjects.Rn n × ℝ)),
  ‖p‖ ^ 2 = ‖p.fst‖ ^ 2 + ‖p.snd‖ ^ 2 := by
  intro n p
  exact WithLp.prod_norm_sq_eq_of_L2 p

end YuiBasis

/- Trusted inspector appended after the generated proof, never a worker tool.
   Its only substitution is an array of escaped (id, selector, expected type) strings. -/
namespace NL2LeanAuditProbe
open Lean Meta Elab Command Term

private def nameOf (parts : Array String) : Name :=
  parts.foldl Name.str .anonymous

private def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quotient"

private def binderKind : BinderInfo → String
  | .default => "explicit"
  | .implicit => "implicit"
  | .strictImplicit => "strict_implicit"
  | .instImplicit => "instance"

private def showType (e : Expr) : MetaM String := do
  return (← ppExpr e).pretty

private def binderInventory (type : Expr) : MetaM Json :=
  forallTelescope type fun xs body => do
    let mut rows : Array Json := #[]
    for x in xs do
      let d ← getFVarLocalDecl x
      rows := rows.push <| Json.mkObj [
        ("name", toJson d.userName.toString), ("kind", toJson (binderKind d.binderInfo)),
        ("type", toJson (← showType d.type)), ("proof_valued", toJson (← isProp d.type))]
    return Json.mkObj [("binders", toJson rows), ("result", toJson (← showType body))]

private def record (name : Name) : MetaM Json := do
  let info ← getConstInfo name
  let env ← getEnv
  let imported := env.isImportedConst name
  let moduleName := match env.getModuleIdxFor? name with
    | some idx => (env.header.moduleNames[idx.toNat]!).toString
    | none => env.mainModule.toString
  return Json.mkObj [
    ("name", toJson name.toString), ("kind", toJson (kindOf info)),
    ("imported", toJson imported), ("module", toJson moduleName),
    ("proof_valued", toJson (← isProp info.type)),
    ("instance_declaration", toJson (isInstanceCore env name)),
    ("type", toJson (← showType info.type)),
    ("signature", ← binderInventory info.type),
    ("levels", toJson (info.levelParams.map Name.toString)),
    ("direct_constants", toJson ((info.getUsedConstantsAsSet.toArray.qsort Name.lt).map Name.toString)),
    ("axioms", toJson ((← collectAxioms name).map Name.toString))]

private def inspect (roots : Array Name) : MetaM Json := do
  let mut pending := roots
  let mut seen : NameSet := {}
  let mut rows : Array Json := #[]
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let info ← getConstInfo name
    rows := rows.push (← record name)
    if !(← getEnv).isImportedConst name then
      pending := pending ++ info.getUsedConstantsAsSet.toArray
      if let .inductInfo value := info then
        pending := pending ++ value.ctors.toArray
  return Json.mkObj [("declarations", toJson rows), ("truncated", toJson (!pending.isEmpty))]

private def actualType (selector : String) (parts : Array String) : TermElabM Expr := do
  if selector.startsWith "decl:" then
    return (← getConstInfo (nameOf parts)).type
  if selector.startsWith "value:" then
    let .defnInfo decl ← getConstInfo (nameOf parts) | throwError "Expected a defined proposition"
    return decl.value
  if selector.startsWith "premise:" then
    let wanted := "h_" ++ (selector.drop 8).toString
    let root ← getConstInfo `AuditBExport.P
    return ← forallTelescope root.type fun xs _ => do
      let mut context : Array Expr := #[]
      for x in xs do
        let binder ← getFVarLocalDecl x
        if binder.userName.toString == wanted then
          return ← mkForallFVars context binder.type
        context := context.push x
      throwError "Missing actual root premise {wanted}"
  throwError "Unsupported selector {selector}"

/- Universe parameter names belong to each declaration's binder scope.
   Rename them bijectively, retaining repetitions and all level expressions.
   This is alpha-equivalence, not a proof of logical equivalence. -/
private def sameSignature (actual expected : Expr) : MetaM (Bool × String) := do
  if ← withoutModifyingState <| isDefEq actual expected then
    return (true, "definitional")
  let actualParams := (collectLevelParams {} actual).params.toList
  let expectedParams := (collectLevelParams {} expected).params.toList
  if actualParams.length != expectedParams.length then
    return (false, "different_universe_binders")
  let levels := (List.range actualParams.length).map fun i =>
    Level.param (Name.mkSimple ("_yuiAuditLevel" ++ toString i))
  let equal ← withoutModifyingState <| isDefEq
    (actual.instantiateLevelParams actualParams levels)
    (expected.instantiateLevelParams expectedParams levels)
  return (equal, "bijective_universe_renaming")

elab "#nl2lean_audit_probe" : command => do
  let result ← liftTermElabM <| withOptions
      (fun o => (o.setBool `pp.all true).setBool `pp.universes true) do
    let checks : Array (String × String × String × Array String) := #[("B001", "decl:YuiBasis.B001", "∀ (X : Type) [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (a : ℝ) (A : Set X),\n  MeasureTheory.Measure.hausdorffMeasure a A =\n    ⨆ (r : ℝ≥0∞) (_ : 0 < r), BasisObjects.content a r A", #["YuiBasis", "B001"]), ("B002", "decl:YuiBasis.B002", "∀ (X : Type) [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (A : Set X) (d : ℝ≥0),\n  (((d : ℝ≥0∞) < dimH A) → MeasureTheory.Measure.hausdorffMeasure (d : ℝ) A = ⊤) ∧\n  ((dimH A < (d : ℝ≥0∞)) → MeasureTheory.Measure.hausdorffMeasure (d : ℝ) A = 0) ∧\n  ((MeasureTheory.Measure.hausdorffMeasure (d : ℝ) A ≠ ⊤) → dimH A ≤ (d : ℝ≥0∞)) ∧\n  ((MeasureTheory.Measure.hausdorffMeasure (d : ℝ) A = ⊤) → (d : ℝ≥0∞) ≤ dimH A)", #["YuiBasis", "B002"]), ("B003", "decl:YuiBasis.B003", "∀ (X : Type) [EMetricSpace X] (A B : Set X), A ⊆ B → dimH A ≤ dimH B", #["YuiBasis", "B003"]), ("B004", "decl:YuiBasis.B004", "∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X],\n  dimH (Set.univ : Set X) = (Module.finrank ℝ X : ℝ≥0∞)", #["YuiBasis", "B004"]), ("B005", "decl:YuiBasis.B005", "∀ (X Y : Type) [NormedAddCommGroup X] [NormedSpace ℝ X]\n  [NormedAddCommGroup Y] [NormedSpace ℝ Y] (e : X ≃L[ℝ] Y) (A : Set X),\n  dimH (e '' A) = dimH A", #["YuiBasis", "B005"]), ("B006", "decl:YuiBasis.B006", "∀ (X Y : Type) [EMetricSpace X] [EMetricSpace Y] (f : X → Y),\n  Isometry f → ∀ A : Set X, dimH (f '' A) = dimH A", #["YuiBasis", "B006"]), ("B007", "decl:YuiBasis.B007", "∀ a b : ℝ, MeasureTheory.volume (Set.Icc a b) = ENNReal.ofReal (b - a)", #["YuiBasis", "B007"]), ("B008", "decl:YuiBasis.B008", "∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (f : ℕ → X → ℝ≥0∞),\n  (∀ i, AEMeasurable (f i) μ) →\n  (∫⁻ x, ∑' i, f i x ∂μ) = ∑' i, ∫⁻ x, f i x ∂μ", #["YuiBasis", "B008"]), ("B009", "decl:YuiBasis.B009", "∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (f g : X → ℝ≥0∞),\n  (∀ x, f x ≤ g x) → (∫⁻ x, f x ∂μ) ≤ ∫⁻ x, g x ∂μ", #["YuiBasis", "B009"]), ("B010", "decl:YuiBasis.B010", "∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (S : Set X) (c : ℝ≥0∞),\n  MeasurableSet S → (∫⁻ x, S.indicator (fun _ => c) x ∂μ) = c * μ S", #["YuiBasis", "B010"]), ("B011", "decl:YuiBasis.B011", "∀ (n : ℕ) (S : Set (BasisObjects.Rn n × ℝ)),\n  dimH (BasisObjects.euclideanLift n '' S) = dimH S", #["YuiBasis", "B011"]), ("B012", "decl:YuiBasis.B012", "∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]\n  (A : Set X), (interior A).Nonempty → dimH A = (Module.finrank ℝ X : ℝ≥0∞)", #["YuiBasis", "B012"]), ("B013", "decl:YuiBasis.B013", "∀ (n : ℕ) (p : WithLp 2 (BasisObjects.Rn n × ℝ)),\n  ‖p‖ ^ 2 = ‖p.fst‖ ^ 2 + ‖p.snd‖ ^ 2", #["YuiBasis", "B013"])]
    let mut comparisons : Array Json := #[]
    let mut frozenComparisons : Array Json := #[]
    let mut roots : Array Name := #[`YuiBasis.B001, `YuiBasis.B002, `YuiBasis.B003, `YuiBasis.B004, `YuiBasis.B005, `YuiBasis.B006, `YuiBasis.B007, `YuiBasis.B008, `YuiBasis.B009, `YuiBasis.B010, `YuiBasis.B011, `YuiBasis.B012, `YuiBasis.B013]
    for (id, selector, expectedText, parts) in checks do
      let stx ← ofExcept <| Parser.runParserCategory (← getEnv) `term expectedText
      let expected ← Term.elabTerm stx none
      Term.synthesizeSyntheticMVarsNoPostponing
      let expected ← instantiateMVars expected
      let actual ← actualType selector parts
      let (equal, method) ← sameSignature actual expected
      let row := Json.mkObj [
        ("id", toJson id), ("selector", toJson selector),
        ("expected_type", toJson (← showType expected)),
        ("actual_type", toJson (← showType actual)), ("definitionally_equal", toJson equal),
        ("comparison_method", toJson method)]
      if id.startsWith "__frozen__" then
        frozenComparisons := frozenComparisons.push row
      else
        comparisons := comparisons.push row
      if selector.startsWith "decl:" then
        roots := roots.push (nameOf parts)
    let dependencies ← inspect roots
    return Json.mkObj [("comparisons", toJson comparisons),
      ("frozen_comparisons", toJson frozenComparisons), ("dependencies", dependencies)]
  logInfo m!"NL2LEAN_AUDIT_JSON:{result.compress}"

#nl2lean_audit_probe
end NL2LeanAuditProbe
