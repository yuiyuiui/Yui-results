import Mathlib
open scoped ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric
namespace YuiBasis
noncomputable def Content {X : Type*} [EMetricSpace X]
    (s : ℝ) (δ : ℝ≥0∞) (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i) (_ : ∀ i, Metric.ediam (U i) ≤ δ),
    ∑' i, ⨆ (_ : (U i).Nonempty), Metric.ediam (U i) ^ s
abbrev Ambient (n : ℕ) := EuclideanSpace ℝ (Fin n)
def unitInterval : Set ℝ := Set.Icc 0 1
noncomputable def appendCoord (n : ℕ) (p : Ambient n × ℝ) : Ambient (n + 1) :=
  WithLp.toLp 2 (Fin.lastCases p.2 (fun i => p.1 i))
end YuiBasis

namespace YuiBasis
set_option autoImplicit false
set_option Elab.async false in
theorem B001 : ∀ (X : Type*) [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (s : ℝ) (A : Set X),
  hausdorffMeasure s A = ⨆ (δ : ℝ≥0∞) (_ : 0 < δ), YuiBasis.Content s δ A := by
  intro X _ _ _ s A
  exact hausdorffMeasure_apply s A
set_option Elab.async false in
theorem B002 : ∀ (X : Type*) [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (A : Set X) (d : ℝ≥0),
  ((d : ℝ≥0∞) < dimH A → hausdorffMeasure (d : ℝ) A = ⊤) ∧
  (dimH A < (d : ℝ≥0∞) → hausdorffMeasure (d : ℝ) A = 0) ∧
  (hausdorffMeasure (d : ℝ) A ≠ ⊤ → dimH A ≤ (d : ℝ≥0∞)) ∧
  (hausdorffMeasure (d : ℝ) A = ⊤ → (d : ℝ≥0∞) ≤ dimH A) := by
  intro X _ _ _ A d
  exact ⟨hausdorffMeasure_of_lt_dimH, hausdorffMeasure_of_dimH_lt,
    dimH_le_of_hausdorffMeasure_ne_top, le_dimH_of_hausdorffMeasure_eq_top⟩
set_option Elab.async false in
theorem B003 : ∀ (X Y : Type*) [EMetricSpace X] [EMetricSpace Y] (K L : ℝ≥0) (f : X → Y)
  (hf : LipschitzWith K f) (hg : AntilipschitzWith L f) (A : Set X),
  (dimH (f '' A) ≤ dimH A ∧ dimH A ≤ dimH (f '' A)) ∧
  (∀ B : Set X, A ⊆ B → dimH A ≤ dimH B) := by
  intro X Y _ _ K L f hf hg A
  exact ⟨⟨hf.dimH_image_le A, hg.le_dimH_image A⟩, fun B h => dimH_mono h⟩
set_option Elab.async false in
theorem B004 : ∀ (n : ℕ) (A : Set (YuiBasis.Ambient n)), dimH A ≤ (n : ℝ≥0∞) ∧ dimH A ≠ ⊤ := by
  intro n A
  constructor
  · calc
      dimH A ≤ dimH (Set.univ : Set (YuiBasis.Ambient n)) := dimH_mono (Set.subset_univ A)
      _ = (n : ℝ≥0∞) := by rw [Real.dimH_univ_eq_finrank]; simp [YuiBasis.Ambient]
  · exact Real.dimH_ne_top A
set_option Elab.async false in
theorem B005 : dimH (Set.Icc (0 : ℝ) 1) = 1 := by
  simpa only [segment_eq_Icc (by norm_num : (0 : ℝ) ≤ 1)] using
    (Real.dimH_segment (by norm_num : (0 : ℝ) ≠ 1))
set_option Elab.async false in
theorem B006 : ∀ (X : Type*) [MeasurableSpace X] (μ : Measure X) (f : ℕ → X → ℝ≥0∞),
  (∀ i, AEMeasurable (f i) μ) →
  (∫⁻ x, ∑' i, f i x ∂μ) = ∑' i, ∫⁻ x, f i x ∂μ := by
  intro X _ μ f hf
  exact lintegral_tsum hf
set_option Elab.async false in
theorem B007 : ∀ (X : Type*) [MeasurableSpace X] (μ : Measure X) (S : Set X),
  MeasurableSet S → ∀ c : ℝ≥0∞,
  (∫⁻ x, S.indicator (fun _ => c) x ∂μ) = c * μ S := by
  intro X _ μ S hS c
  exact lintegral_indicator_const hS c
set_option Elab.async false in
theorem B008 : ∀ (X : Type*) [MeasurableSpace X] (μ : Measure X),
  (∀ f g : X → ℝ≥0∞, (∀ x, f x ≤ g x) →
    (∫⁻ x, f x ∂μ) ≤ ∫⁻ x, g x ∂μ) ∧
  (∀ c : ℝ≥0∞, (∫⁻ _x : X, c ∂μ) = c * μ Set.univ) := by
  intro X _ μ
  exact ⟨fun f g h => lintegral_mono h, fun c => lintegral_const c⟩
set_option Elab.async false in
theorem B009 : (∀ B : Set ℝ, Bornology.IsBounded B →
  B ⊆ Set.Icc (sInf B) (sSup B) ∧
  volume (Set.Icc (sInf B) (sSup B)) = Metric.ediam B) ∧
  (∀ a b : ℝ, volume (Set.Icc a b) = ENNReal.ofReal (b - a)) ∧
  volume (Set.Icc (0 : ℝ) 1) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro B hB
    exact ⟨hB.subset_Icc_sInf_sSup, Real.volume_Icc.trans (Real.ediam_eq hB).symm⟩
  · intro a b
    exact Real.volume_Icc
  · simp
set_option Elab.async false in
theorem B010 : ∀ q : ℝ, 0 ≤ q → Continuous (fun x : ℝ => x ^ q) := by
  intro q hq
  exact Real.continuous_rpow_const hq
set_option Elab.async false in
theorem B011 : ∀ (X Y : Type*) [EMetricSpace X] [EMetricSpace Y] (K : ℝ≥0) (f : X → Y),
  LipschitzWith K f → ∀ A : Set X,
  Metric.ediam (f '' A) ≤ (K : ℝ≥0∞) * Metric.ediam A := by
  intro X Y _ _ K f hf A
  exact hf.ediam_image_le A

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
    let checks : Array (String × String × String × Array String) := #[("B001", "decl:YuiBasis.B001", "∀ (X : Type*) [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (s : ℝ) (A : Set X),\n  hausdorffMeasure s A = ⨆ (δ : ℝ≥0∞) (_ : 0 < δ), YuiBasis.Content s δ A", #["YuiBasis", "B001"]), ("B002", "decl:YuiBasis.B002", "∀ (X : Type*) [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (A : Set X) (d : ℝ≥0),\n  ((d : ℝ≥0∞) < dimH A → hausdorffMeasure (d : ℝ) A = ⊤) ∧\n  (dimH A < (d : ℝ≥0∞) → hausdorffMeasure (d : ℝ) A = 0) ∧\n  (hausdorffMeasure (d : ℝ) A ≠ ⊤ → dimH A ≤ (d : ℝ≥0∞)) ∧\n  (hausdorffMeasure (d : ℝ) A = ⊤ → (d : ℝ≥0∞) ≤ dimH A)", #["YuiBasis", "B002"]), ("B003", "decl:YuiBasis.B003", "∀ (X Y : Type*) [EMetricSpace X] [EMetricSpace Y] (K L : ℝ≥0) (f : X → Y)\n  (hf : LipschitzWith K f) (hg : AntilipschitzWith L f) (A : Set X),\n  (dimH (f '' A) ≤ dimH A ∧ dimH A ≤ dimH (f '' A)) ∧\n  (∀ B : Set X, A ⊆ B → dimH A ≤ dimH B)", #["YuiBasis", "B003"]), ("B004", "decl:YuiBasis.B004", "∀ (n : ℕ) (A : Set (YuiBasis.Ambient n)), dimH A ≤ (n : ℝ≥0∞) ∧ dimH A ≠ ⊤", #["YuiBasis", "B004"]), ("B005", "decl:YuiBasis.B005", "dimH (Set.Icc (0 : ℝ) 1) = 1", #["YuiBasis", "B005"]), ("B006", "decl:YuiBasis.B006", "∀ (X : Type*) [MeasurableSpace X] (μ : Measure X) (f : ℕ → X → ℝ≥0∞),\n  (∀ i, AEMeasurable (f i) μ) →\n  (∫⁻ x, ∑' i, f i x ∂μ) = ∑' i, ∫⁻ x, f i x ∂μ", #["YuiBasis", "B006"]), ("B007", "decl:YuiBasis.B007", "∀ (X : Type*) [MeasurableSpace X] (μ : Measure X) (S : Set X),\n  MeasurableSet S → ∀ c : ℝ≥0∞,\n  (∫⁻ x, S.indicator (fun _ => c) x ∂μ) = c * μ S", #["YuiBasis", "B007"]), ("B008", "decl:YuiBasis.B008", "∀ (X : Type*) [MeasurableSpace X] (μ : Measure X),\n  (∀ f g : X → ℝ≥0∞, (∀ x, f x ≤ g x) →\n    (∫⁻ x, f x ∂μ) ≤ ∫⁻ x, g x ∂μ) ∧\n  (∀ c : ℝ≥0∞, (∫⁻ _x : X, c ∂μ) = c * μ Set.univ)", #["YuiBasis", "B008"]), ("B009", "decl:YuiBasis.B009", "(∀ B : Set ℝ, Bornology.IsBounded B →\n  B ⊆ Set.Icc (sInf B) (sSup B) ∧\n  volume (Set.Icc (sInf B) (sSup B)) = Metric.ediam B) ∧\n  (∀ a b : ℝ, volume (Set.Icc a b) = ENNReal.ofReal (b - a)) ∧\n  volume (Set.Icc (0 : ℝ) 1) = 1", #["YuiBasis", "B009"]), ("B010", "decl:YuiBasis.B010", "∀ q : ℝ, 0 ≤ q → Continuous (fun x : ℝ => x ^ q)", #["YuiBasis", "B010"]), ("B011", "decl:YuiBasis.B011", "∀ (X Y : Type*) [EMetricSpace X] [EMetricSpace Y] (K : ℝ≥0) (f : X → Y),\n  LipschitzWith K f → ∀ A : Set X,\n  Metric.ediam (f '' A) ≤ (K : ℝ≥0∞) * Metric.ediam A", #["YuiBasis", "B011"])]
    let mut comparisons : Array Json := #[]
    let mut frozenComparisons : Array Json := #[]
    let mut roots : Array Name := #[`YuiBasis.B001, `YuiBasis.B002, `YuiBasis.B003, `YuiBasis.B004, `YuiBasis.B005, `YuiBasis.B006, `YuiBasis.B007, `YuiBasis.B008, `YuiBasis.B009, `YuiBasis.B010, `YuiBasis.B011]
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
