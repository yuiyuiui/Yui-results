import Mathlib
open scoped ENNReal NNReal BigOperators
open Set MeasureTheory
abbrev YEuclid (m : ℕ) := EuclideanSpace ℝ (Fin m)
noncomputable def yContent {X : Type*} [EMetricSpace X] (s δ : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i) (_ : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ),
    ∑' i, (Metric.ediam (U i)) ^ s
noncomputable def yHaus {X : Type*} [EMetricSpace X] (s : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨆ (δ : ℝ) (_ : 0 < δ), yContent s δ A
def yI : Set ℝ := Set.Icc 0 1
def yHoriz {n : ℕ} (z : YEuclid (n+1)) : YEuclid n :=
  WithLp.toLp 2 (fun i : Fin n => z i.castSucc)
def yVert {n : ℕ} (z : YEuclid (n+1)) : ℝ := z (Fin.last n)
def yJoin {n : ℕ} (x : YEuclid n) (t : ℝ) : YEuclid (n+1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x i) t)
def yProd {n : ℕ} (E : Set (YEuclid n)) : Set (YEuclid (n+1)) :=
  {z | yHoriz z ∈ E ∧ yVert z ∈ yI}
def yCritical (X : Type*) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] : Prop :=
  (∀ A : Set X, 0 ≤ dimH A) ∧
  ∀ (A : Set X) (s : ℝ), 0 < s →
    yHaus s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (dimH A < ENNReal.ofReal s → yHaus s A = 0) ∧
    (ENNReal.ofReal s < dimH A → yHaus s A = ⊤) ∧
    (yHaus s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (yHaus s A = ⊤ → ENNReal.ofReal s ≤ dimH A)
def yCover {X : Type*} [EMetricSpace X] (δ : ℝ) (A : Set X) (U : ℕ → Set X) : Prop :=
  A ⊆ ⋃ i, U i ∧ ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ
noncomputable def yCost {X : Type*} [EMetricSpace X] (s : ℝ) (U : ℕ → Set X) : ℝ≥0∞ :=
  ∑' i, (Metric.ediam (U i)) ^ s

namespace Translation
set_option autoImplicit false

theorem T006 (n : ℕ) (E : Set (YEuclid n)) (h_T001 : (∀ m : ℕ, yCritical (YEuclid m)) ∧ yCritical ℝ) (h_T002 : dimH E < ⊤ ∧ 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ (n = 0 → E = Set.univ ∧ (∃ x : YEuclid n, E = {x}) ∧ dimH E = 0) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → yContent s δ E < ⊤)) (h_T005 : dimH yI = 1 ∧ (∀ a : ℝ, 1 < a → yHaus a yI = 0) ∧ (∀ s : ℝ, 0 < s → s < 1 → yHaus s yI = ⊤)) :
    n = 0 → dimH (yProd E) ≤ dimH E + 1 := by
  intro hn
  subst n
  rcases h_T002.2.2.2.1 rfl with ⟨hE, ⟨x, hx⟩, hD⟩
  rw [hD, zero_add]
  have hlast (t : ℝ) : yJoin x t (Fin.last 0) = t := by
    exact Fin.snoc_last (α := fun _ : Fin 1 => ℝ) (x := t) (p := fun i => x i)
  have hf : Isometry (yJoin x) := by
    apply Isometry.of_dist_eq
    intro t u
    have hsq : dist (yJoin x t) (yJoin x u) ^ 2 = dist t u ^ 2 := by
      rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_one]
      change dist (yJoin x t (Fin.last 0)) (yJoin x u (Fin.last 0)) ^ 2 = _
      rw [hlast, hlast]
    have h₁ : 0 ≤ dist (yJoin x t) (yJoin x u) := dist_nonneg
    have h₂ : 0 ≤ dist t u := dist_nonneg
    nlinarith
  have himg : yJoin x '' yI = yProd E := by
    apply Set.Subset.antisymm
    · rintro z ⟨t, ht, rfl⟩
      constructor
      · rw [hE]
        trivial
      · change yJoin x t (Fin.last 0) ∈ yI
        rwa [hlast]
    · intro z hz
      refine ⟨yVert z, hz.2, ?_⟩
      ext i
      have hi : i = Fin.last 0 := by
        apply Fin.ext
        have hi' := i.isLt
        simp only [Fin.val_last]
        omega
      rw [hi, hlast]
      rfl
  have hcontent (s δ : ℝ) : yContent s δ (yProd E) ≤ yContent s δ yI := by
    rw [← himg]
    unfold yContent
    refine le_iInf fun U => le_iInf fun hU => le_iInf fun hd => ?_
    refine iInf_le_of_le (fun i => yJoin x '' U i) ?_
    have hcover : yJoin x '' yI ⊆ ⋃ i, yJoin x '' U i := by
      rintro z ⟨t, ht, rfl⟩
      rcases Set.mem_iUnion.mp (hU ht) with ⟨i, hi⟩
      exact Set.mem_iUnion.mpr ⟨i, ⟨t, hi, rfl⟩⟩
    refine iInf_le_of_le hcover ?_
    have hdiam : ∀ i, Metric.ediam (yJoin x '' U i) ≤ ENNReal.ofReal δ := by
      intro i
      rw [hf.ediam_image]
      exact hd i
    refine iInf_le_of_le hdiam ?_
    simp only [hf.ediam_image, le_refl]
  have hbound (a : ℝ) (ha : 1 < a) : dimH (yProd E) ≤ ENNReal.ofReal a := by
    have hapos : 0 < a := lt_trans zero_lt_one ha
    have hzero : yHaus a (yProd E) = 0 := by
      apply le_antisymm ?_ bot_le
      calc
        yHaus a (yProd E) ≤ yHaus a yI := by
          unfold yHaus
          refine iSup_le fun δ => iSup_le fun hδ => ?_
          exact (hcontent a δ).trans (le_iSup_of_le δ (le_iSup_of_le hδ le_rfl))
        _ = 0 := h_T005.2.1 a ha
    exact ((h_T001.1 (0+1)).2 (yProd E) a hapos).2.2.2.1 hzero
  by_contra hn
  have hd : (1 : ℝ≥0∞) < dimH (yProd E) := lt_of_not_ge hn
  rcases ENNReal.lt_iff_exists_real_btwn.mp hd with ⟨a, ha0, ha, had⟩
  have hreal : 1 < a := ENNReal.one_lt_ofReal.mp ha
  exact (not_lt_of_ge (hbound a hreal)) had

#check @T006
#print axioms T006

end Translation
