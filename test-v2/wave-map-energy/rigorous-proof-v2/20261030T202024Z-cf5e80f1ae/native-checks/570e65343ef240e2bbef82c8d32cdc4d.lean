import Mathlib
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
namespace WaveEnergy
abbrev X (n : ℕ) := Fin n → ℝ
abbrev V (m : ℕ) := EuclideanSpace ℝ (Fin m)
def domain (n : ℕ) : Set (X n × ℝ) := {p | 0 < p.2}
noncomputable def mu (n : ℕ) : Measure (X n) := Measure.pi (fun _ : Fin n => (volume : Measure ℝ))
noncomputable def dt {n : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : X n × ℝ → F) (p : X n × ℝ) : F := deriv (fun r : ℝ => f (p.1, r)) p.2
noncomputable def dx {n : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : X n × ℝ → F) (j : Fin n) (p : X n × ℝ) : F :=
  fderiv ℝ (fun y : X n => f (y, p.2)) p.1 (Pi.single j 1)
noncomputable def lap {n m : ℕ} (u : X n × ℝ → V m) (p : X n × ℝ) : V m :=
  ∑ j : Fin n, dx (dx u j) j p
noncomputable def density {n m : ℕ} (u : X n × ℝ → V m) (p : X n × ℝ) : ℝ :=
  ‖dt u p‖ ^ 2 + ∑ j : Fin n, ‖dx u j p‖ ^ 2
noncomputable def energy {n m : ℕ} (u : X n × ℝ → V m) (t : ℝ) : ℝ :=
  ∫ x : X n, density u (x, t) ∂mu n
noncomputable def kinetic {n m : ℕ} (u : X n × ℝ → V m) (p : X n × ℝ) : ℝ :=
  inner ℝ (dt u p) (dt (dt u) p)
noncomputable def mixed {n m : ℕ} (u : X n × ℝ → V m) (j : Fin n) (p : X n × ℝ) : ℝ :=
  inner ℝ (dx u j p) (dx (dt u) j p)
noncomputable def lapTerm {n m : ℕ} (u : X n × ℝ → V m) (j : Fin n) (p : X n × ℝ) : ℝ :=
  inner ℝ (dt u p) (dx (dx u j) j p)
noncomputable def flux {n m : ℕ} (u : X n × ℝ → V m) (j : Fin n) (p : X n × ℝ) : ℝ :=
  inner ℝ (dt u p) (dx u j p)
def box {n : ℕ} (R : ℝ) : Set (X n) := {x | ∀ j, x j ∈ Icc (-R) R}
def scalarTerms {n m : ℕ} (u : X n × ℝ → V m) : Set (X n × ℝ → ℝ) :=
  {f | f = density u ∨ f = dt (density u) ∨ f = kinetic u ∨
    ∃ j : Fin n, f = mixed u j ∨ f = lapTerm u j ∨ f = flux u j ∨ f = dx (flux u j) j}
structure Window {n m : ℕ} (u : X n × ℝ → V m) (q : V m)
    (t0 : ℝ) (C : Set (X n)) (R : ℝ) : Prop where
  compact : IsCompact C
  radius_pos : 0 < R
  inside : ∀ x ∈ C, ∀ j : Fin n, x j ∈ Ioo (-R) R
  constant : ∀ x, x ∉ C → ∀ r ∈ Icc (t0 / 2) (3 * t0 / 2), u (x, r) = q
  box_volume : mu n (box R) = ENNReal.ofReal ((2 * R) ^ n)
  box_finite : mu n (box R) < ⊤
  derivatives_zero : ∀ k : ℕ, 0 < k → ∀ x, x ∉ C →
    ∀ r ∈ Ioo (t0 / 2) (3 * t0 / 2), iteratedFDeriv ℝ k u (x, r) = 0
  sections : ∀ f ∈ scalarTerms u, ∀ r ∈ Ioo (t0 / 2) (3 * t0 / 2),
    Continuous (fun x => f (x, r)) ∧ (∀ x, x ∉ C → f (x, r) = 0) ∧
    Integrable (fun x => f (x, r)) (mu n)
  uniform : ∀ f ∈ scalarTerms u, ∀ a b : ℝ,
    Icc a b ⊆ Ioo (t0 / 2) (3 * t0 / 2) →
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ box R, ∀ r ∈ Icc a b, |f (x, r)| ≤ B
abbrev Other (n : ℕ) (j : Fin n) := {i : Fin n // i ≠ j} → ℝ
noncomputable def otherMu {n : ℕ} (j : Fin n) : Measure (Other n j) :=
  Measure.pi (fun _ : {i : Fin n // i ≠ j} => (volume : Measure ℝ))
def otherBox {n : ℕ} (j : Fin n) (R : ℝ) : Set (Other n j) :=
  {y | ∀ i, y i ∈ Icc (-R) R}
def insert {n : ℕ} (j : Fin n) (p : Other n j × ℝ) : X n :=
  fun i => if h : i = j then p.2 else p.1 ⟨i,h⟩
end WaveEnergy
open WaveEnergy

namespace Translation
set_option autoImplicit false

theorem T011 (n : ℕ) (m : ℕ) (u : X n × ℝ → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ u (domain n)) (h_T004 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (X n), ∃ R : ℝ, Window u q t0 C R) ∧
  ContDiffOn ℝ ∞ (density u) (domain n) ∧
  ContDiffOn ℝ ∞ (dt (density u)) (domain n) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : X n => density u (x,t)) (mu n))) (h_T009 : ∀ t0 : ℝ, 0 < t0 → ∀ j : Fin n,
  ContDiff ℝ ∞ (fun x : X n => flux u j (x,t0)) ∧
  (∀ x : X n, dx (flux u j) j (x,t0) =
    inner ℝ (dx (dt u) j (x,t0)) (dx u j (x,t0)) + lapTerm u j (x,t0)) ∧
  (∀ x : X n, HasDerivAt (fun z : ℝ => flux u j (Function.update x j z,t0))
    (dx (flux u j) j (x,t0)) (x j)) ∧
  (∀ C : Set (X n), ∀ R : ℝ, Window u q t0 C R →
    ∀ x : X n, x j = -R ∨ x j = R → flux u j (x,t0) = 0)) (h_T010 : ∀ t0 : ℝ, 0 < t0 → ∀ j : Fin n,
  ∀ C : Set (X n), ∀ R : ℝ, Window u q t0 C R →
  ∀ x : X n, (∫ z in (-R)..R,
    dx (flux u j) j (Function.update x j z,t0)) = 0) :
    ∀ t0 : ℝ, 0 < t0 → ∀ j : Fin n,
  ∀ C : Set (X n), ∀ R : ℝ, Window u q t0 C R →
  MeasurePreserving (insert j)
    (((otherMu j).restrict (otherBox j R)).prod (volume.restrict (Icc (-R) R)))
    ((mu n).restrict (box R)) ∧
  (∫ x in box R, dx (flux u j) j (x,t0) ∂mu n) = 0 := by
  classical
  have hcoord : ∀ j : Fin n, MeasurableEmbedding (WaveEnergy.insert j) ∧
      MeasurePreserving (WaveEnergy.insert j) ((otherMu j).prod volume) (mu n) := by
      intro j
      classical
      have hmeas : Measurable (WaveEnergy.insert j) := by
        apply measurable_pi_lambda
        intro i
        by_cases h : i = j
        · simpa [WaveEnergy.insert, h] using (measurable_snd : Measurable (fun p : Other n j × ℝ => p.2))
        · simp only [WaveEnergy.insert, dif_neg h]
          exact (measurable_pi_apply (⟨i,h⟩ : {k : Fin n // k ≠ j})).comp (measurable_fst : Measurable (fun p : Other n j × ℝ => p.1))
      let e : (Other n j × ℝ) ≃ᵐ X n :=
        { toFun := WaveEnergy.insert j
          invFun := fun x => (fun i => x i, x j)
          left_inv := by
            intro p
            apply Prod.ext
            · funext i
              simp [WaveEnergy.insert, i.property]
            · simp [WaveEnergy.insert]
          right_inv := by
            intro x
            funext i
            by_cases h : i = j <;> simp [WaveEnergy.insert, h]
          measurable_toFun := hmeas
          measurable_invFun := (measurable_pi_lambda _ (fun i => measurable_pi_apply i.val)).prodMk (measurable_pi_apply j) }
      refine ⟨e.measurableEmbedding, hmeas, ?_⟩
      apply Eq.symm
      apply Measure.pi_eq
      intro s hs
      have hp : WaveEnergy.insert j ⁻¹' (Set.univ.pi s) =
          (Set.univ.pi (fun i : {i : Fin n // i ≠ j} => s i.val)) ×ˢ s j := by
        ext p
        simp only [mem_preimage, mem_univ_pi, mem_prod]
        constructor
        · intro h
          exact ⟨fun i => by simpa [WaveEnergy.insert, i.property] using h i.val,
            by simpa [WaveEnergy.insert] using h j⟩
        · rintro ⟨hy,hz⟩ i
          by_cases h : i = j
          · subst i
            simpa [WaveEnergy.insert] using hz
          · simpa [WaveEnergy.insert, h] using hy ⟨i,h⟩
      rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs), hp,
        Measure.prod_prod, otherMu, Measure.pi_pi]
      rw [Fintype.prod_eq_mul_prod_subtype_ne (fun i => volume (s i)) j, mul_comm]
  intro t0 ht0 j C R hW
  obtain ⟨hemb, hmp⟩ := hcoord j
  letI : SigmaFinite (otherMu j) := by unfold otherMu; infer_instance
  letI : IsFiniteMeasureOnCompacts (otherMu j) := by unfold otherMu; infer_instance
  have hbox : MeasurableSet (box (n := n) R) := by
    have heq : box (n := n) R = Set.univ.pi (fun _ : Fin n => Icc (-R) R) := by
      ext x
      simp only [box, mem_setOf_eq, mem_univ_pi]
    rw [heq]
    exact MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  have hpre : WaveEnergy.insert j ⁻¹' box R = otherBox j R ×ˢ Icc (-R) R := by
    ext p
    change (∀ i, WaveEnergy.insert j p i ∈ Icc (-R) R) ↔
      (∀ i : {i : Fin n // i ≠ j}, p.1 i ∈ Icc (-R) R) ∧ p.2 ∈ Icc (-R) R
    constructor
    · intro h
      exact ⟨fun i => by simpa [WaveEnergy.insert, i.property] using h i.val,
        by simpa [WaveEnergy.insert] using h j⟩
    · rintro ⟨hy,hz⟩ i
      by_cases h : i = j
      · simpa [WaveEnergy.insert, h] using hz
      · simpa [WaveEnergy.insert, h] using hy ⟨i,h⟩
  have hrestricted : MeasurePreserving (WaveEnergy.insert j)
      (((otherMu j).restrict (otherBox j R)).prod (volume.restrict (Icc (-R) R)))
      ((mu n).restrict (box R)) := by
    rw [Measure.prod_restrict, ← hpre]
    exact hmp.restrict_preimage hbox
  refine ⟨hrestricted, ?_⟩
  have htwin : t0 ∈ Ioo (t0 / 2) (3 * t0 / 2) := by constructor <;> linarith
  have hfmem : dx (flux u j) j ∈ scalarTerms u := by
    exact Or.inr (Or.inr (Or.inr ⟨j, Or.inr (Or.inr (Or.inr rfl))⟩))
  have hf : Continuous (fun x : X n => dx (flux u j) j (x,t0)) :=
    (hW.sections _ hfmem t0 htwin).1
  have hins : Continuous (WaveEnergy.insert j) := by
    apply continuous_pi
    intro i
    by_cases h : i = j
    · simpa [WaveEnergy.insert, h] using (continuous_snd : Continuous (fun p : Other n j × ℝ => p.2))
    · simp only [WaveEnergy.insert, dif_neg h]
      exact (continuous_apply (⟨i,h⟩ : {k : Fin n // k ≠ j})).comp
        (continuous_fst : Continuous (fun p : Other n j × ℝ => p.1))
  have hcompact : IsCompact (otherBox j R) := by
    have heq : otherBox j R = Set.univ.pi (fun _ : {i : Fin n // i ≠ j} => Icc (-R) R) := by
      ext x
      simp only [otherBox, mem_setOf_eq, mem_univ_pi]
    rw [heq]
    exact isCompact_univ_pi (fun _ => isCompact_Icc)
  have hv : Integrable (fun p : Other n j × ℝ =>
      dx (flux u j) j (WaveEnergy.insert j p,t0))
      (((otherMu j).restrict (otherBox j R)).prod (volume.restrict (Icc (-R) R))) := by
    rw [Measure.prod_restrict]
    exact (hf.comp hins).continuousOn.integrableOn_compact (hcompact.prod isCompact_Icc)
  rw [← hrestricted.integral_comp hemb (fun x => dx (flux u j) j (x,t0)),
    integral_prod _ hv]
  have hinner : ∀ y : Other n j, (∫ z in Icc (-R) R,
      dx (flux u j) j (WaveEnergy.insert j (y,z),t0)) = 0 := by
    intro y
    have hup : ∀ z : ℝ, WaveEnergy.insert j (y,z) =
        Function.update (WaveEnergy.insert j (y,0)) j z := by
      intro z
      funext i
      by_cases h : i = j
      · subst i
        simp [WaveEnergy.insert]
      · simp [WaveEnergy.insert, h, Function.update_of_ne h]
    simp_rw [hup]
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith [hW.radius_pos] : -R ≤ R)]
    exact h_T010 t0 ht0 j C R hW (WaveEnergy.insert j (y,0))
  simp only [hinner, integral_zero]

#check @T011
#print axioms T011

end Translation
