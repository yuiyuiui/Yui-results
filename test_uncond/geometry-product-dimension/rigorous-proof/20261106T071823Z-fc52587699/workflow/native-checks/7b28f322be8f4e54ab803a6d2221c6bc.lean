import Mathlib
open scoped ENNReal NNReal MeasureTheory
open MeasureTheory Set

noncomputable def YuiContent {X : Type} [MetricSpace X] (p : ℝ) (r : ℝ≥0∞) (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i) (_ : ∀ i, Metric.ediam (U i) ≤ r),
    ∑' i, ⨆ (_ : (U i).Nonempty), (Metric.ediam (U i)) ^ p

namespace YuiBasis
set_option autoImplicit false
set_option Elab.async false in
theorem B001 : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (p : ℝ) (A : Set X), MeasureTheory.Measure.hausdorffMeasure p A = ⨆ (r : ℝ≥0∞) (_ : 0 < r), YuiContent p r A := by
  intro X _ _ _ p A
  simpa only [YuiContent] using MeasureTheory.Measure.hausdorffMeasure_apply p A
set_option Elab.async false in
theorem B002 : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (A : Set X) (a : ℝ≥0), (((a : ℝ≥0∞) < dimH A) → MeasureTheory.Measure.hausdorffMeasure (a : ℝ) A = ⊤) ∧ ((dimH A < (a : ℝ≥0∞)) → MeasureTheory.Measure.hausdorffMeasure (a : ℝ) A = 0) ∧ ((MeasureTheory.Measure.hausdorffMeasure (a : ℝ) A ≠ ⊤) → dimH A ≤ (a : ℝ≥0∞)) ∧ ((MeasureTheory.Measure.hausdorffMeasure (a : ℝ) A = ⊤) → (a : ℝ≥0∞) ≤ dimH A) := by
  intro X _ _ _ A a
  exact ⟨hausdorffMeasure_of_lt_dimH, hausdorffMeasure_of_dimH_lt, dimH_le_of_hausdorffMeasure_ne_top, le_dimH_of_hausdorffMeasure_eq_top⟩
set_option Elab.async false in
theorem B003 : ∀ (X Y : Type) [MetricSpace X] [MetricSpace Y], (∀ (A B : Set X), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (K : ℝ≥0) (f : X → Y) (A : Set X), LipschitzWith K f → dimH (f '' A) ≤ dimH A) ∧ (∀ (f : X → Y) (A : Set X), Isometry f → dimH (f '' A) = dimH A) := by
  intro X Y _ _
  exact ⟨fun A B h => dimH_mono h, fun K f A h => h.dimH_image_le A, fun f A h => h.dimH_image A⟩
set_option Elab.async false in
theorem B004 : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (A : Set V), dimH A ≤ (Module.finrank ℝ V : ℝ≥0∞) := by
  intro V _ _ _ A
  exact (dimH_mono (Set.subset_univ A)).trans_eq (Real.dimH_univ_eq_finrank V)
set_option Elab.async false in
theorem B005 : dimH (Set.Icc (0 : ℝ) 1) = 1 := by
  have h : (interior (Set.Icc (0 : ℝ) 1)).Nonempty := by
    rw [interior_Icc]
    exact ⟨(1 / 2 : ℝ), by norm_num, by norm_num⟩
  simpa using Real.dimH_of_nonempty_interior h
set_option Elab.async false in
theorem B006 : ∀ (X : Type) [MeasurableSpace X] (μ : MeasureTheory.Measure X), (∀ (f : ℕ → X → ℝ≥0∞), (∀ i, AEMeasurable (f i) μ) → (∫⁻ x, ∑' i, f i x ∂μ) = ∑' i, ∫⁻ x, f i x ∂μ) ∧ (∀ (S : Set X) (c : ℝ≥0∞), MeasurableSet S → (∫⁻ x, S.indicator (fun _ => c) x ∂μ) = c * μ S) ∧ (∀ (f g : X → ℝ≥0∞), (∀ x, f x ≤ g x) → (∫⁻ x, f x ∂μ) ≤ ∫⁻ x, g x ∂μ) ∧ (∀ (S : Set X) (c : ℝ≥0∞), (∫⁻ x in S, c ∂μ) = c * μ S) := by
  intro X _ μ
  exact ⟨fun f h => MeasureTheory.lintegral_tsum h, fun S c h => MeasureTheory.lintegral_indicator_const h c, fun f g h => MeasureTheory.lintegral_mono h, fun S c => MeasureTheory.setLIntegral_const S c⟩
set_option Elab.async false in
theorem B007 : ∀ (a b : ℝ), MeasureTheory.volume (Set.Icc a b) = ENNReal.ofReal (b - a) ∧ MeasureTheory.volume (Set.Ioo a b) = ENNReal.ofReal (b - a) := by
  intro a b
  exact ⟨Real.volume_Icc, Real.volume_Ioo⟩
set_option Elab.async false in
theorem B008 : ∀ (V W : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (e : V ≃ₗ[ℝ] W) (A : Set V), dimH (e '' A) = dimH A := by
  intro V W _ _ _ _ _ _ e A
  exact e.toContinuousLinearEquiv.dimH_image A
set_option Elab.async false in
theorem B009 : ∀ (X Y : Type) [MetricSpace X] [MetricSpace Y] (K : ℝ≥0) (f : X → Y) (A : Set X), LipschitzWith K f → Metric.ediam (f '' A) ≤ (K : ℝ≥0∞) * Metric.ediam A := by
  intro X Y _ _ K f A h
  exact h.ediam_image_le A

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
    let checks : Array (String × String × String × Array String) := #[("B001", "decl:YuiBasis.B001", "∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (p : ℝ) (A : Set X), MeasureTheory.Measure.hausdorffMeasure p A = ⨆ (r : ℝ≥0∞) (_ : 0 < r), YuiContent p r A", #["YuiBasis", "B001"]), ("B002", "decl:YuiBasis.B002", "∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (A : Set X) (a : ℝ≥0), (((a : ℝ≥0∞) < dimH A) → MeasureTheory.Measure.hausdorffMeasure (a : ℝ) A = ⊤) ∧ ((dimH A < (a : ℝ≥0∞)) → MeasureTheory.Measure.hausdorffMeasure (a : ℝ) A = 0) ∧ ((MeasureTheory.Measure.hausdorffMeasure (a : ℝ) A ≠ ⊤) → dimH A ≤ (a : ℝ≥0∞)) ∧ ((MeasureTheory.Measure.hausdorffMeasure (a : ℝ) A = ⊤) → (a : ℝ≥0∞) ≤ dimH A)", #["YuiBasis", "B002"]), ("B003", "decl:YuiBasis.B003", "∀ (X Y : Type) [MetricSpace X] [MetricSpace Y], (∀ (A B : Set X), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (K : ℝ≥0) (f : X → Y) (A : Set X), LipschitzWith K f → dimH (f '' A) ≤ dimH A) ∧ (∀ (f : X → Y) (A : Set X), Isometry f → dimH (f '' A) = dimH A)", #["YuiBasis", "B003"]), ("B004", "decl:YuiBasis.B004", "∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (A : Set V), dimH A ≤ (Module.finrank ℝ V : ℝ≥0∞)", #["YuiBasis", "B004"]), ("B005", "decl:YuiBasis.B005", "dimH (Set.Icc (0 : ℝ) 1) = 1", #["YuiBasis", "B005"]), ("B006", "decl:YuiBasis.B006", "∀ (X : Type) [MeasurableSpace X] (μ : MeasureTheory.Measure X), (∀ (f : ℕ → X → ℝ≥0∞), (∀ i, AEMeasurable (f i) μ) → (∫⁻ x, ∑' i, f i x ∂μ) = ∑' i, ∫⁻ x, f i x ∂μ) ∧ (∀ (S : Set X) (c : ℝ≥0∞), MeasurableSet S → (∫⁻ x, S.indicator (fun _ => c) x ∂μ) = c * μ S) ∧ (∀ (f g : X → ℝ≥0∞), (∀ x, f x ≤ g x) → (∫⁻ x, f x ∂μ) ≤ ∫⁻ x, g x ∂μ) ∧ (∀ (S : Set X) (c : ℝ≥0∞), (∫⁻ x in S, c ∂μ) = c * μ S)", #["YuiBasis", "B006"]), ("B007", "decl:YuiBasis.B007", "∀ (a b : ℝ), MeasureTheory.volume (Set.Icc a b) = ENNReal.ofReal (b - a) ∧ MeasureTheory.volume (Set.Ioo a b) = ENNReal.ofReal (b - a)", #["YuiBasis", "B007"]), ("B008", "decl:YuiBasis.B008", "∀ (V W : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (e : V ≃ₗ[ℝ] W) (A : Set V), dimH (e '' A) = dimH A", #["YuiBasis", "B008"]), ("B009", "decl:YuiBasis.B009", "∀ (X Y : Type) [MetricSpace X] [MetricSpace Y] (K : ℝ≥0) (f : X → Y) (A : Set X), LipschitzWith K f → Metric.ediam (f '' A) ≤ (K : ℝ≥0∞) * Metric.ediam A", #["YuiBasis", "B009"])]
    let mut comparisons : Array Json := #[]
    let mut frozenComparisons : Array Json := #[]
    let mut roots : Array Name := #[`YuiBasis.B001, `YuiBasis.B002, `YuiBasis.B003, `YuiBasis.B004, `YuiBasis.B005, `YuiBasis.B006, `YuiBasis.B007, `YuiBasis.B008, `YuiBasis.B009]
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
