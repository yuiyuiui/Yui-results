import Mathlib
open scoped Topology ContDiff
open MeasureTheory Filter
namespace WaveMapEnergy
abbrev Space (n : ℕ) := Fin n → ℝ
abbrev Value (m : ℕ) := Fin m → ℝ
def dot {m : ℕ} (v w : Value m) : ℝ := ∑ k, v k * w k
def normSq {m : ℕ} (v : Value m) : ℝ := dot v v
noncomputable def velocity {n m : ℕ} (u : Space n × ℝ → Value m)
    (x : Space n) (t : ℝ) : Value m :=
  fun k => deriv (fun r => u (x, r) k) t
noncomputable def acceleration {n m : ℕ} (u : Space n × ℝ → Value m)
    (x : Space n) (t : ℝ) : Value m :=
  fun k => deriv (fun r => velocity u x r k) t
noncomputable def spatial {n m : ℕ} (u : Space n × ℝ → Value m)
    (j : Fin n) (x : Space n) (t : ℝ) : Value m :=
  fun k => fderiv ℝ (fun y => u (y, t) k) x (Pi.single j 1)
noncomputable def spatialSecond {n m : ℕ} (u : Space n × ℝ → Value m)
    (j : Fin n) (x : Space n) (t : ℝ) : Value m :=
  fun k => fderiv ℝ (fun y => spatial u j y t k) x (Pi.single j 1)
noncomputable def laplacian {n m : ℕ} (u : Space n × ℝ → Value m)
    (x : Space n) (t : ℝ) : Value m := ∑ j, spatialSecond u j x t
noncomputable def density {n m : ℕ} (u : Space n × ℝ → Value m)
    (x : Space n) (t : ℝ) : ℝ :=
  normSq (velocity u x t) + ∑ j, normSq (spatial u j x t)
noncomputable def energy {n m : ℕ} (u : Space n × ℝ → Value m) (t : ℝ) : ℝ :=
  ∫ x, density u x t
def Smooth {n m : ℕ} (u : Space n × ℝ → Value m) : Prop :=
  ContDiffOn ℝ ∞ u {p | 0 < p.2}
def UnitValued {n m : ℕ} (u : Space n × ℝ → Value m) : Prop :=
  ∀ x t, 0 < t → normSq (u (x, t)) = 1
def Normal {n m : ℕ} (u : Space n × ℝ → Value m) : Prop :=
  ∀ x t, 0 < t → ∃ a : ℝ, acceleration u x t - laplacian u x t = a • u (x, t)
def CompactPerturbation {n m : ℕ} (u : Space n × ℝ → Value m) (q : Value m) : Prop :=
  ∀ s t : ℝ, 0 < s → s < t → ∃ C : Set (Space n), IsCompact C ∧
    ∀ x r, x ∉ C → r ∈ Set.Icc s t → u (x, r) = q
end WaveMapEnergy

namespace YuiBasis
set_option autoImplicit false
set_option Elab.async false in
theorem B001 : ∀ (n : ℕ) (f : (Fin n → ℝ) → ℝ), Continuous f → HasCompactSupport f → Integrable f := by
  intro n f hf hc
  exact hf.integrable_of_hasCompactSupport hc
set_option Elab.async false in
theorem B002 : ∀ (n : ℕ) (F F' : ℝ → (Fin n → ℝ) → ℝ)
  (b : (Fin n → ℝ) → ℝ) (t₀ : ℝ) (s : Set ℝ),
  s ∈ 𝓝 t₀ →
  (∀ᶠ t in 𝓝 t₀, AEStronglyMeasurable (F t) volume) →
  Integrable (F t₀) →
  AEStronglyMeasurable (F' t₀) volume →
  (∀ᵐ x ∂volume, ∀ t ∈ s, ‖F' t x‖ ≤ b x) →
  Integrable b →
  (∀ᵐ x ∂volume, ∀ t ∈ s, HasDerivAt (fun r => F r x) (F' t x) t) →
  Integrable (F' t₀) ∧
    HasDerivAt (fun t => ∫ x, F t x) (∫ x, F' t₀ x) t₀ := by
  intro n F F' b t₀ s hs hm hi hm' hb hbi hd
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hm hi hm' hb hbi hd
set_option Elab.async false in
theorem B003 : ∀ (n : ℕ) (f g : (Fin n → ℝ) → ℝ) (v : Fin n → ℝ),
  Integrable (fun x => fderiv ℝ f x v * g x) →
  Integrable (fun x => f x * fderiv ℝ g x v) →
  Integrable (fun x => f x * g x) →
  (∀ x ∈ tsupport g, DifferentiableAt ℝ f x) →
  (∀ x ∈ tsupport f, DifferentiableAt ℝ g x) →
  (∫ x, f x * fderiv ℝ g x v) = -(∫ x, fderiv ℝ f x v * g x) := by
  intro n f g v h1 h2 h3 hf hg
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h1 h2 h3 hf hg
set_option Elab.async false in
theorem B004 : ∀ (f g : ℝ → ℝ) (f' g' t : ℝ), HasDerivAt f f' t → HasDerivAt g g' t →
  HasDerivAt (fun r => f r * g r) (f' * g t + f t * g') t := by
  intro f g f' g' t hf hg
  exact hf.mul hg
set_option Elab.async false in
theorem B005 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (x : E),
  ContDiffAt ℝ 2 f x →
  ∀ v w : E, fderiv ℝ (fderiv ℝ f) x v w = fderiv ℝ (fderiv ℝ f) x w v := by
  intro E F _ _ _ _ f x hf v w
  exact hf.isSymmSndFDerivAt (by simp) v w
set_option Elab.async false in
theorem B006 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (U : Set E),
  IsOpen U → ContDiffOn ℝ ∞ f U → ContDiffOn ℝ ∞ (fderiv ℝ f) U := by
  intro E F _ _ _ _ f U hU hf
  exact hf.fderiv_of_isOpen hU (by simp)
set_option Elab.async false in
theorem B007 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (c : F) (x : E),
  (f =ᶠ[𝓝 x] fun _ => c) → fderiv ℝ f x = 0 := by
  intro E F _ _ _ _ f c x h
  rw [h.fderiv_eq]
  simp
set_option Elab.async false in
theorem B008 : ∀ (n : ℕ) (K : Set ((Fin n → ℝ) × ℝ)) (f : ((Fin n → ℝ) × ℝ) → ℝ),
  IsCompact K → ContinuousOn f K → ∃ B : ℝ, ∀ p ∈ K, ‖f p‖ ≤ B := by
  intro n K f hK hf
  exact hK.exists_bound_of_continuousOn hf
set_option Elab.async false in
theorem B009 : ∀ (n : ℕ) (K : Set (Fin n → ℝ)) (B : ℝ),
  IsCompact K → Integrable (K.indicator (fun _ => B)) := by
  intro n K B hK
  rw [integrable_indicator_iff hK.measurableSet]
  exact integrableOn_const hK.measure_ne_top

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
    let checks : Array (String × String × String × Array String) := #[("B001", "decl:YuiBasis.B001", "∀ (n : ℕ) (f : (Fin n → ℝ) → ℝ), Continuous f → HasCompactSupport f → Integrable f", #["YuiBasis", "B001"]), ("B002", "decl:YuiBasis.B002", "∀ (n : ℕ) (F F' : ℝ → (Fin n → ℝ) → ℝ)\n  (b : (Fin n → ℝ) → ℝ) (t₀ : ℝ) (s : Set ℝ),\n  s ∈ 𝓝 t₀ →\n  (∀ᶠ t in 𝓝 t₀, AEStronglyMeasurable (F t) volume) →\n  Integrable (F t₀) →\n  AEStronglyMeasurable (F' t₀) volume →\n  (∀ᵐ x ∂volume, ∀ t ∈ s, ‖F' t x‖ ≤ b x) →\n  Integrable b →\n  (∀ᵐ x ∂volume, ∀ t ∈ s, HasDerivAt (fun r => F r x) (F' t x) t) →\n  Integrable (F' t₀) ∧\n    HasDerivAt (fun t => ∫ x, F t x) (∫ x, F' t₀ x) t₀", #["YuiBasis", "B002"]), ("B003", "decl:YuiBasis.B003", "∀ (n : ℕ) (f g : (Fin n → ℝ) → ℝ) (v : Fin n → ℝ),\n  Integrable (fun x => fderiv ℝ f x v * g x) →\n  Integrable (fun x => f x * fderiv ℝ g x v) →\n  Integrable (fun x => f x * g x) →\n  (∀ x ∈ tsupport g, DifferentiableAt ℝ f x) →\n  (∀ x ∈ tsupport f, DifferentiableAt ℝ g x) →\n  (∫ x, f x * fderiv ℝ g x v) = -(∫ x, fderiv ℝ f x v * g x)", #["YuiBasis", "B003"]), ("B004", "decl:YuiBasis.B004", "∀ (f g : ℝ → ℝ) (f' g' t : ℝ), HasDerivAt f f' t → HasDerivAt g g' t →\n  HasDerivAt (fun r => f r * g r) (f' * g t + f t * g') t", #["YuiBasis", "B004"]), ("B005", "decl:YuiBasis.B005", "∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]\n  [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (x : E),\n  ContDiffAt ℝ 2 f x →\n  ∀ v w : E, fderiv ℝ (fderiv ℝ f) x v w = fderiv ℝ (fderiv ℝ f) x w v", #["YuiBasis", "B005"]), ("B006", "decl:YuiBasis.B006", "∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]\n  [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (U : Set E),\n  IsOpen U → ContDiffOn ℝ ∞ f U → ContDiffOn ℝ ∞ (fderiv ℝ f) U", #["YuiBasis", "B006"]), ("B007", "decl:YuiBasis.B007", "∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]\n  [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (c : F) (x : E),\n  (f =ᶠ[𝓝 x] fun _ => c) → fderiv ℝ f x = 0", #["YuiBasis", "B007"]), ("B008", "decl:YuiBasis.B008", "∀ (n : ℕ) (K : Set ((Fin n → ℝ) × ℝ)) (f : ((Fin n → ℝ) × ℝ) → ℝ),\n  IsCompact K → ContinuousOn f K → ∃ B : ℝ, ∀ p ∈ K, ‖f p‖ ≤ B", #["YuiBasis", "B008"]), ("B009", "decl:YuiBasis.B009", "∀ (n : ℕ) (K : Set (Fin n → ℝ)) (B : ℝ),\n  IsCompact K → Integrable (K.indicator (fun _ => B))", #["YuiBasis", "B009"])]
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
