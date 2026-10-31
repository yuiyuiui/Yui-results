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

theorem T010 (n : ℕ) (E : Set (YEuclid n)) (h_T002 : dimH E < ⊤ ∧ 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ (n = 0 → E = Set.univ ∧ (∃ x : YEuclid n, E = {x}) ∧ dimH E = 0) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → yContent s δ E < ⊤)) :
    ∀ (s δ : ℝ), 0 < s → 0 < δ → ∀ V : ℕ → Set (YEuclid (n+1)), yCover δ (yProd E) V → ∀ ε : ℝ, 0 < ε → yContent s δ E ≤ yCost (s+1) V + ENNReal.ofReal ε := by
  classical
  have hproj : ∀ z w : YEuclid (n+1),
      edist (yHoriz z) (yHoriz w) ≤ edist z w ∧
      edist (yVert z) (yVert w) ≤ edist z w := by
      intro z w
      have hd : dist z w ^ 2 =
          dist (yHoriz z) (yHoriz w) ^ 2 + dist (yVert z) (yVert w) ^ 2 := by
        rw [EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq, Fin.sum_univ_castSucc]
        rfl
      constructor <;>
        simp only [edist_dist, ENNReal.ofReal_le_ofReal_iff (dist_nonneg)] <;>
        nlinarith [sq_nonneg (dist (yHoriz z) (yHoriz w)), sq_nonneg (dist (yVert z) (yVert w)),
          dist_nonneg (x := z) (y := w), dist_nonneg (x := yHoriz z) (y := yHoriz w),
          dist_nonneg (x := yVert z) (y := yVert w)]

  have hinter : ∀ (B : Set ℝ) (d : ℝ≥0∞), d ≠ ⊤ → Metric.ediam B ≤ d →
      ∀ η : ℝ, 0 < η → ∃ J : Set ℝ, IsOpen J ∧ B ⊆ J ∧ volume J ≤ d + ENNReal.ofReal η := by
      intro B d hd hB η hη
      classical
      by_cases hne : B.Nonempty
      · have hb : Bornology.IsBounded B :=
          Metric.isBounded_iff_ediam_ne_top.mpr (ne_top_of_le_ne_top hd hB)
        refine ⟨Ioo (sInf B - η/2) (sSup B + η/2), isOpen_Ioo, ?_, ?_⟩
        · intro t ht
          have ht' := hb.subset_Icc_sInf_sSup ht
          constructor <;> dsimp at * <;> linarith [ht'.1, ht'.2]
        · rw [Real.volume_Ioo]
          have he : sSup B + η/2 - (sInf B - η/2) = (sSup B - sInf B) + η := by ring
          rw [he]
          exact (ENNReal.ofReal_add_le).trans (add_le_add (by simpa [Real.ediam_eq hb] using hB) le_rfl)
      · refine ⟨∅, isOpen_empty, ?_, ?_⟩
        · simpa [Set.not_nonempty_iff_eq_empty.mp hne]
        · simp
  have hnum : ∀ (a : ℝ≥0∞), a ≠ ⊤ → ∀ e : ℝ, 0 ≤ e →
      a * ENNReal.ofReal (e / (1 + a.toReal)) ≤ ENNReal.ofReal e := by
      intro a ha e he
      have hn : 0 ≤ a.toReal := ENNReal.toReal_nonneg
      have hd : 0 < 1 + a.toReal := by positivity
      calc
        a * ENNReal.ofReal (e / (1 + a.toReal)) =
            ENNReal.ofReal (a.toReal * (e / (1 + a.toReal))) := by
          rw [ENNReal.ofReal_mul hn, ENNReal.ofReal_toReal ha]
        _ ≤ ENNReal.ofReal e := ENNReal.ofReal_le_ofReal (by
          rw [← mul_div_assoc]
          apply (div_le_iff₀ hd).mpr
          nlinarith)

  have hjoin : ∀ (x : YEuclid n) (t : ℝ),
      yHoriz (yJoin x t) = x ∧ yVert (yJoin x t) = t := by
    intro x t
    constructor
    · ext i
      simp [yHoriz, yJoin]
    · simp [yVert, yJoin]
  have hrejoin : ∀ z : YEuclid (n+1), yJoin (yHoriz z) (yVert z) = z := by
    intro z
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [yJoin, yVert]
    · simp [yJoin, yHoriz]
  intro s δ hs hδ V hV ε hε
  let ρ : ℕ → ℝ≥0∞ := fun i => Metric.ediam (V i)
  let A : ℕ → Set (YEuclid n) := fun i => yHoriz '' V i
  let B : ℕ → Set ℝ := fun i => yVert '' V i
  let c := yContent s δ E
  have hc : c < ⊤ := h_T002.2.2.2.2 s δ hs hδ
  have hρ : ∀ i, ρ i ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hV.2 i)
  have hA : ∀ i, Metric.ediam (A i) ≤ ρ i := by
    intro i
    exact Metric.ediam_image_le_iff.mpr (fun z hz w hw =>
      (hproj z w).1.trans (Metric.edist_le_ediam_of_mem hz hw))
  have hB : ∀ i, Metric.ediam (B i) ≤ ρ i := by
    intro i
    exact Metric.ediam_image_le_iff.mpr (fun z hz w hw =>
      (hproj z w).2.trans (Metric.edist_le_ediam_of_mem hz hw))
  let a : ℕ → ℝ≥0∞ := fun i => ρ i ^ s
  have ha : ∀ i, a i ≠ ⊤ := fun i => ENNReal.rpow_ne_top_of_nonneg hs.le (hρ i)
  let e : ℕ → ℝ := fun i => ε / 2 / 2 ^ i
  let η : ℕ → ℝ := fun i => e i / (1 + (a i).toReal)
  have he : ∀ i, 0 < e i := by intro i; dsimp [e]; positivity
  have hη : ∀ i, 0 < η i := by intro i; dsimp [η]; exact div_pos (he i) (by positivity)
  choose J hJopen hJsub hJvol using fun i => hinter (B i) (ρ i) (hρ i) (hB i) (η i) (hη i)
  let f : ℕ → ℝ → ℝ≥0∞ := fun i => (J i).indicator (fun _ => a i)
  have hf : ∀ i, Measurable (f i) := fun i => measurable_const.indicator (hJopen i).measurableSet
  have hslice : ∀ t ∈ yI, c ≤ ∑' i, f i t := by
    intro t ht
    let W : ℕ → Set (YEuclid n) := fun i => if t ∈ J i then A i else ∅
    have hcov : E ⊆ ⋃ i, W i := by
      intro x hx
      have hxt : yJoin x t ∈ yProd E := by
        change yHoriz (yJoin x t) ∈ E ∧ yVert (yJoin x t) ∈ yI
        simpa only [(hjoin x t).1, (hjoin x t).2] using And.intro hx ht
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hV.1 hxt)
      have htJ : t ∈ J i := hJsub i ⟨yJoin x t, hi, (hjoin x t).2⟩
      apply Set.mem_iUnion.mpr
      refine ⟨i, ?_⟩
      simpa only [W, if_pos htJ] using
        (show x ∈ A i from ⟨yJoin x t, hi, (hjoin x t).1⟩)
    have hdiam : ∀ i, Metric.ediam (W i) ≤ ENNReal.ofReal δ := by
      intro i
      dsimp [W]
      split_ifs
      · exact (hA i).trans (hV.2 i)
      · simp
    calc
      c ≤ ∑' i, Metric.ediam (W i) ^ s := by
        exact iInf_le_of_le W (iInf_le_of_le hcov (iInf_le _ hdiam))
      _ ≤ ∑' i, f i t := by
        apply ENNReal.tsum_le_tsum
        intro i
        by_cases htJ : t ∈ J i
        · simpa only [W, if_pos htJ, f, Set.indicator_of_mem htJ, a] using
            ENNReal.rpow_le_rpow (hA i) hs.le
        · simp [W, htJ, f, ENNReal.zero_rpow_of_pos hs]
  let μ : Measure ℝ := volume.restrict yI
  have hμ : μ Set.univ = 1 := by simp [μ, yI]
  have hlower : c ≤ ∫⁻ t, ∑' i, f i t ∂μ := by
    calc
      c = ∫⁻ _ : ℝ, c ∂μ := by rw [lintegral_const, hμ, mul_one]
      _ ≤ ∫⁻ t, ∑' i, f i t ∂μ := by
        apply lintegral_mono_ae
        exact (ae_restrict_mem (show MeasurableSet yI from measurableSet_Icc)).mono hslice
  have hint : ∀ i, (∫⁻ t, f i t ∂μ) ≤ ρ i ^ (s+1) + ENNReal.ofReal (e i) := by
    intro i
    calc
      (∫⁻ t, f i t ∂μ) = a i * μ (J i) :=
        lintegral_indicator_const (hJopen i).measurableSet (a i)
      _ ≤ a i * (ρ i + ENNReal.ofReal (η i)) := by
        apply mul_le_mul_left'
        exact (Measure.restrict_apply_le yI (J i)).trans (hJvol i)
      _ = ρ i ^ (s+1) + a i * ENNReal.ofReal (η i) := by
        dsimp [a]
        rw [ENNReal.rpow_add_of_nonneg s 1 hs.le zero_le_one, ENNReal.rpow_one, mul_add]
      _ ≤ ρ i ^ (s+1) + ENNReal.ofReal (e i) :=
        add_le_add_left (hnum (a i) (ha i) (e i) (he i).le) _
  have hsum : (∑' i, ENNReal.ofReal (e i)) = ENNReal.ofReal ε := by
    dsimp [e]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => (he i).le) (summable_geometric_two' ε),
      tsum_geometric_two']
  calc
    yContent s δ E ≤ ∫⁻ t, ∑' i, f i t ∂μ := hlower
    _ = ∑' i, ∫⁻ t, f i t ∂μ :=
      MeasureTheory.lintegral_tsum (α := ℝ) (β := ℕ) (μ := μ) (f := f) (fun i => (hf i).aemeasurable)
    _ ≤ ∑' i, (ρ i ^ (s+1) + ENNReal.ofReal (e i)) := ENNReal.tsum_le_tsum hint
    _ = yCost (s+1) V + ENNReal.ofReal ε := by rw [ENNReal.tsum_add, hsum]; rfl

#check @T010
#print axioms T010

end Translation
