import Mathlib
open scoped ENNReal NNReal
noncomputable section
abbrev YEucl (m : ℕ) := EuclideanSpace ℝ (Fin m)
def YI : Set ℝ := Set.Icc 0 1
def YJoin {m : ℕ} (x : YEucl m) (t : ℝ) : YEucl (m + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x i) t)
def YBase {m : ℕ} (z : YEucl (m + 1)) : YEucl m :=
  WithLp.toLp 2 (fun i => z i.castSucc)
def YLast {m : ℕ} (z : YEucl (m + 1)) : ℝ := z (Fin.last m)
def YF {m : ℕ} (A : Set (YEucl m)) : Set (YEucl (m + 1)) :=
  {z | ∃ x ∈ A, ∃ t ∈ YI, z = YJoin x t}
def YLine (t : ℝ) : YEucl 1 := WithLp.toLp 2 (fun _ => t)
def YCover {X : Type*} [PseudoEMetricSpace X]
    (δ : ℝ) (A : Set X) (U : ℕ → Set X) : Prop :=
  A ⊆ ⋃ i, U i ∧ ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ
def YCost {X : Type*} [PseudoEMetricSpace X]
    (s : ℝ) (U : ℕ → Set X) : ℝ≥0∞ :=
  ∑' i, (Metric.ediam (U i)) ^ s
def YContent {X : Type*} [PseudoEMetricSpace X]
    (s δ : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : YCover δ A U), YCost s U
def YHaus {X : Type*} [PseudoEMetricSpace X]
    (s : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨆ (δ : ℝ) (_ : 0 < δ), YContent s δ A
def YCritical {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (A : Set X) : Prop :=
  0 ≤ dimH A ∧ ∀ s : ℝ, 0 < s →
    YHaus s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (dimH A < ENNReal.ofReal s → YHaus s A = 0) ∧
    (ENNReal.ofReal s < dimH A → YHaus s A = ⊤) ∧
    (YHaus s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (YHaus s A = ⊤ → ENNReal.ofReal s ≤ dimH A)

namespace Translation
set_option autoImplicit false

theorem T011 (n : ℕ) (E : Set (YEucl n)) (h_T002 : ∀ (m : ℕ) (A : Set (YEucl m)), YCritical A) (h_T003 : (∀ (m : ℕ) (x y : YEucl m) (t u : ℝ), dist (YJoin x t) (YJoin y u) = Real.sqrt (dist x y ^ 2 + |t-u| ^ 2)) ∧ (∀ (m : ℕ) (z : YEucl (m+1)), YJoin (YBase z) (YLast z) = z) ∧ (∀ (m : ℕ) (x : YEucl m) (t : ℝ), YBase (YJoin x t) = x ∧ YLast (YJoin x t) = t) ∧ (∀ m : ℕ, LipschitzWith 1 (@YBase m) ∧ LipschitzWith 1 (@YLast m)) ∧ Isometry YLine ∧ Function.Surjective YLine) (h_T006 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤) ∧ (n = 0 → E = Set.univ ∧ E.Subsingleton ∧ dimH E = 0) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → YContent s δ E < ⊤)) (h_T010 : dimH YI = 1 ∧ (∀ a : ℝ, 1 < a → YHaus a YI = 0) ∧ (∀ (s δ : ℝ), 0 < s → s < 1 → 0 < δ → ∀ U : ℕ → Set ℝ, YCover δ YI U → (1 : ℝ≥0∞) ≤ ∑' i, Metric.ediam (U i) ∧ (ENNReal.ofReal δ) ^ (s-1) ≤ YCost s U) ∧ (∀ s : ℝ, 0 < s → s < 1 → YHaus s YI = ⊤)) :
    n = 0 → dimH (YF E) ≤ dimH E + 1 := by
  intro hn
  rcases h_T006.2.1 hn with ⟨hE, hsub, hD⟩
  let f : ℝ → YEucl (n + 1) := fun t => YJoin (0 : YEucl n) t
  have h0 : (0 : YEucl n) ∈ E := by rw [hE]; trivial
  have hf : Isometry f := by
    apply Isometry.of_dist_eq
    intro t u
    dsimp [f]
    rw [h_T003.1 n 0 0 t u]
    simp [Real.sqrt_sq_eq_abs, Real.dist_eq]
  have hF : YF E = f '' YI := by
    ext z
    constructor
    · rintro ⟨x, hx, t, ht, hz⟩
      have hx0 : x = 0 := hsub hx h0
      exact ⟨t, ht, by simpa [f, hx0] using hz.symm⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨0, h0, t, ht, rfl⟩
  have hcontent : ∀ (a δ : ℝ), 0 < a →
      YContent a δ (YF E) ≤ YContent a δ YI := by
    intro a δ ha
    unfold YContent
    refine le_iInf fun U => le_iInf fun hU => ?_
    let V : ℕ → Set (YEucl (n + 1)) := fun i => f '' (U i ∩ YI)
    have hd : ∀ i, Metric.ediam (V i) ≤ Metric.ediam (U i) := by
      intro i
      dsimp [V]
      rw [hf.ediam_image]
      exact Metric.ediam_mono Set.inter_subset_left
    have hV : YCover δ (YF E) V := by
      constructor
      · intro z hz
        rw [hF] at hz
        rcases hz with ⟨t, ht, rfl⟩
        rcases Set.mem_iUnion.mp (hU.1 ht) with ⟨i, hi⟩
        exact Set.mem_iUnion.mpr ⟨i, t, ⟨hi, ht⟩, rfl⟩
      · intro i
        exact (hd i).trans (hU.2 i)
    have hbound : YContent a δ (YF E) ≤ YCost a V :=
      iInf_le_of_le V (iInf_le_of_le hV le_rfl)
    refine hbound.trans ?_
    exact ENNReal.tsum_le_tsum fun i => ENNReal.rpow_le_rpow (hd i) ha.le
  have hhaus : ∀ a : ℝ, 1 < a → YHaus a (YF E) = 0 := by
    intro a ha
    apply le_antisymm _ zero_le
    rw [← h_T010.2.1 a ha]
    unfold YHaus
    refine iSup_le fun δ => iSup_le fun hδ => ?_
    exact (hcontent a δ (lt_trans zero_lt_one ha)).trans
      (le_iSup_of_le δ (le_iSup_of_le hδ le_rfl))
  have hdim : ∀ a : ℝ, 1 < a → dimH (YF E) ≤ ENNReal.ofReal a := by
    intro a ha
    exact ((h_T002 (n + 1) (YF E)).2 a (lt_trans zero_lt_one ha)).2.2.2.1 (hhaus a ha)
  rw [hD, zero_add]
  by_contra h
  have hlt : (1 : ℝ≥0∞) < dimH (YF E) := lt_of_not_ge h
  rcases ENNReal.lt_iff_exists_real_btwn.mp hlt with ⟨a, ha0, ha1, haD⟩
  exact (not_lt_of_ge (hdim a (ENNReal.one_lt_ofReal.mp ha1))) haD

#check @T011
#print axioms T011

end Translation
