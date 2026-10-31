import Mathlib
open scoped ENNReal NNReal
namespace GP
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)
def unitInterval : Set ℝ := Set.Icc 0 1
def join {n : ℕ} (x : Space n) (t : ℝ) : Space (n + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x i) t)
def horizontal {n : ℕ} (z : Space (n + 1)) : Space n :=
  WithLp.toLp 2 (fun i => z i.castSucc)
def vertical {n : ℕ} (z : Space (n + 1)) : ℝ := z (Fin.last n)
def cylinder {n : ℕ} (E : Set (Space n)) : Set (Space (n + 1)) :=
  {z | horizontal z ∈ E ∧ vertical z ∈ unitInterval}
def Cover {X : Type*} [EMetricSpace X] (A : Set X) (δ : ℝ)
    (U : ℕ → Set X) : Prop :=
  A ⊆ ⋃ i, U i ∧ ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ
noncomputable def cost {X : Type*} [EMetricSpace X] (s : ℝ)
    (U : ℕ → Set X) : ℝ≥0∞ :=
  ∑' i, ⨆ (_ : (U i).Nonempty), (Metric.ediam (U i)) ^ s
noncomputable def content {X : Type*} [EMetricSpace X] (s δ : ℝ)
    (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : Cover A δ U), cost s U
noncomputable def hausdorff {X : Type*} [EMetricSpace X] (s : ℝ)
    (A : Set X) : ℝ≥0∞ :=
  ⨆ (δ : ℝ) (_ : 0 < δ), content s δ A
end GP

namespace Translation
set_option autoImplicit false

theorem T007 (n : ℕ) (E : Set (GP.Space n)) (h_T002 : dimH E < ⊤ ∧ 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧
  (n = 0 → E = Set.univ ∧ (∃ x : GP.Space n, E = {x}) ∧ dimH E = 0) ∧
  ∀ (s δ : ℝ), 0 < s → 0 < δ → GP.content s δ E < ⊤) :
    ∀ (s δ : ℝ), 0 < s → 0 < δ →
  ∀ (V : ℕ → Set (GP.Space (n + 1))), GP.Cover (GP.cylinder E) δ V →
  ∀ ε : ℝ, 0 < ε → ∃ J : ℕ → Set ℝ,
    (∀ i, IsOpen (J i)) ∧
    (∀ i, GP.vertical '' (V i) ⊆ J i) ∧
    (∀ i, MeasureTheory.volume (J i) ≤ Metric.ediam (V i) +
      ENNReal.ofReal (ε * (1 / 2 : ℝ) ^ (i + 1) /
        (1 + (Metric.diam (V i)) ^ s))) ∧
    (∀ t ∈ GP.unitInterval,
      GP.content s δ E ≤
        ∑' i, (J i).indicator (fun _ => (Metric.ediam (V i)) ^ s) t) := by
  classical
  have hproj : LipschitzWith 1 (@GP.horizontal n) ∧ LipschitzWith 1 (@GP.vertical n) := by
    have hsplit (x y : GP.Space (n+1)) : dist x y ^ 2 =
        dist (GP.horizontal x) (GP.horizontal y) ^ 2 +
          dist (GP.vertical x) (GP.vertical y) ^ 2 := by
      simp only [EuclideanSpace.dist_sq_eq, Fin.sum_univ_castSucc, GP.horizontal, GP.vertical]
    constructor
    · apply LipschitzWith.of_dist_le_mul
      intro x y
      simp only [NNReal.coe_one, one_mul]
      nlinarith [hsplit x y, sq_nonneg (dist (GP.vertical x) (GP.vertical y)),
        dist_nonneg (x := GP.horizontal x) (y := GP.horizontal y),
        dist_nonneg (x := x) (y := y)]
    · apply LipschitzWith.of_dist_le_mul
      intro x y
      simp only [NNReal.coe_one, one_mul]
      nlinarith [hsplit x y, sq_nonneg (dist (GP.horizontal x) (GP.horizontal y)),
        dist_nonneg (x := GP.vertical x) (y := GP.vertical y),
        dist_nonneg (x := x) (y := y)]
  rcases hproj with ⟨hh, hv⟩
  have hinterval : ∀ (V : Set (GP.Space (n+1))), Bornology.IsBounded V →
      ∀ η : ℝ, 0 < η → ∃ J : Set ℝ, IsOpen J ∧ GP.vertical '' V ⊆ J ∧
        MeasureTheory.volume J ≤ Metric.ediam V + ENNReal.ofReal η := by
    classical
    intro V hV η hη
    let B : Set ℝ := GP.vertical '' V
    have hB : Bornology.IsBounded B := hv.isBounded_image hV
    have hd : Metric.diam B ≤ Metric.diam V := by
      simpa only [NNReal.coe_one, one_mul] using hv.diam_image_le V hV
    have hconv : ENNReal.ofReal (Metric.diam V) = Metric.ediam V :=
      ENNReal.ofReal_toReal hV.ediam_ne_top
    by_cases hne : V.Nonempty
    · refine ⟨Set.Ioo (sInf B - η / 2) (sSup B + η / 2), isOpen_Ioo, ?_, ?_⟩
      · intro t ht
        have ht' := hB.subset_Icc_sInf_sSup ht
        constructor <;> linarith [ht'.1, ht'.2]
      · rw [Real.volume_Ioo]
        have hh : sSup B + η / 2 - (sInf B - η / 2) = Metric.diam B + η := by
          rw [Real.diam_eq hB]
          ring
        rw [hh]
        calc
          ENNReal.ofReal (Metric.diam B + η) ≤ ENNReal.ofReal (Metric.diam V + η) :=
            ENNReal.ofReal_le_ofReal (by linarith)
          _ = Metric.ediam V + ENNReal.ofReal η := by
            rw [ENNReal.ofReal_add Metric.diam_nonneg hη.le, hconv]
    · have hem : V = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      refine ⟨∅, isOpen_empty, ?_, ?_⟩ <;> simp [hem]
  intro s δ hs hδ V hV ε hε
  have hcfinite : GP.content s δ E < ⊤ := h_T002.2.2.2.2 s δ hs hδ
  have hb (i : ℕ) : Bornology.IsBounded (V i) :=
    Metric.isBounded_iff_ediam_ne_top.mpr
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hV.2 i))
  let η : ℕ → ℝ := fun i => ε * (1 / 2 : ℝ) ^ (i + 1) /
      (1 + (Metric.diam (V i)) ^ s)
  have hη (i : ℕ) : 0 < η i := by
    dsimp [η]
    have hp : 0 ≤ (Metric.diam (V i)) ^ s := Real.rpow_nonneg Metric.diam_nonneg s
    positivity
  choose J hopen hsub hvol using fun i => hinterval (V i) (hb i) (η i) (hη i)
  refine ⟨J, hopen, hsub, hvol, ?_⟩
  intro t ht
  let W : ℕ → Set (GP.Space n) := fun i =>
    if t ∈ J i then GP.horizontal '' (V i) else ∅
  have hd (i : ℕ) : Metric.ediam (GP.horizontal '' V i) ≤ Metric.ediam (V i) := by
    simpa only [ENNReal.coe_one, one_mul] using hh.ediam_image_le (V i)
  have hW : GP.Cover E δ W := by
    constructor
    · intro x hx
      have hz : GP.join x t ∈ GP.cylinder E := by
        change GP.horizontal (GP.join x t) ∈ E ∧ GP.vertical (GP.join x t) ∈ GP.unitInterval
        simpa [GP.horizontal, GP.vertical, GP.join] using And.intro hx ht
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hV.1 hz)
      have hti : t ∈ J i := by
        apply hsub i
        exact ⟨GP.join x t, hi, by simp [GP.vertical, GP.join]⟩
      apply Set.mem_iUnion.mpr
      refine ⟨i, ?_⟩
      simp only [W, if_pos hti]
      exact ⟨GP.join x t, hi, by simp [GP.horizontal, GP.join]⟩
    · intro i
      dsimp [W]
      split_ifs
      · exact (hd i).trans (hV.2 i)
      · simp
  have hc : GP.content s δ E ≤ GP.cost s W := by
    exact iInf_le_of_le W (iInf_le_of_le hW le_rfl)
  apply hc.trans
  unfold GP.cost
  apply ENNReal.tsum_le_tsum
  intro i
  by_cases hti : t ∈ J i
  · simp only [Set.indicator_of_mem hti]
    apply iSup_le
    intro hne
    apply ENNReal.rpow_le_rpow _ hs.le
    simpa only [W, if_pos hti] using hd i
  · simp [W, hti, Set.indicator_of_notMem hti]

#check @T007
#print axioms T007

end Translation
