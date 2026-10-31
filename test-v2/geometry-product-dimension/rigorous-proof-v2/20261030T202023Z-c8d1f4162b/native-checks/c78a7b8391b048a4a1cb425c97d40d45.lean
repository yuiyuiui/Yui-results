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

theorem T008 (n : ℕ) (E : Set (YEucl n))  :
    ∀ (δ : ℝ), 0 < δ → ∀ U : ℕ → Set ℝ, YCover δ YI U → (1 : ℝ≥0∞) ≤ ∑' i, Metric.ediam (U i) := by
  classical
  intro δ hδ U hU
  have hbdd (i : ℕ) : Bornology.IsBounded (U i) :=
    Metric.isBounded_iff_ediam_ne_top.mpr
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hU.2 i))
  let K : Set ℕ := {i | (U i).Nonempty}
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε hfinite
  have hεR : 0 < (ε : ℝ) := hε
  let b : ℕ → ℝ := fun i => (ε : ℝ) / 2 / 2 ^ i
  have hbpos (i : ℕ) : 0 < b i := by dsimp [b]; positivity
  have hbsum : (∑' i : ℕ, ENNReal.ofReal (b i)) = (ε : ℝ≥0∞) := by
    dsimp [b]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity)
      (summable_geometric_two' (ε : ℝ)), tsum_geometric_two']
    simp
  let J : K → Set ℝ := fun i =>
    Set.Ioo (sInf (U i) - b i / 2) (sSup (U i) + b i / 2)
  have hsub (i : K) : U i ⊆ J i := by
    intro x hx
    have hb := (hbdd i).subset_Icc_sInf_sSup hx
    change sInf (U i) - b i / 2 < x ∧ x < sSup (U i) + b i / 2
    constructor <;> linarith [hbpos i, hb.1, hb.2]
  have hvol (i : K) : MeasureTheory.volume (J i) =
      Metric.ediam (U i) + ENNReal.ofReal (b i) := by
    dsimp [J]
    rw [Real.volume_Ioo, Real.ediam_eq (hbdd i)]
    have hd : 0 ≤ sSup (U i) - sInf (U i) := by
      rw [← Real.diam_eq (hbdd i)]
      exact Metric.diam_nonneg
    have he : sSup (U i) + b i / 2 - (sInf (U i) - b i / 2) =
        (sSup (U i) - sInf (U i)) + b i := by ring
    rw [he, ENNReal.ofReal_add hd (hbpos i).le]
  have hcover : YI ⊆ ⋃ i : K, J i := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hU.1 hx)
    exact Set.mem_iUnion.mpr ⟨⟨i, ⟨x, hi⟩⟩, hsub ⟨i, ⟨x, hi⟩⟩ hi⟩
  calc
    (1 : ℝ≥0∞) = MeasureTheory.volume YI := by simp [YI, Real.volume_Icc]
    _ ≤ MeasureTheory.volume (⋃ i : K, J i) := MeasureTheory.measure_mono hcover
    _ ≤ ∑' i : K, MeasureTheory.volume (J i) := MeasureTheory.measure_iUnion_le J
    _ = ∑' i : K, (Metric.ediam (U i) + ENNReal.ofReal (b i)) := tsum_congr hvol
    _ = (∑' i : K, Metric.ediam (U i)) + ∑' i : K, ENNReal.ofReal (b i) := ENNReal.tsum_add
    _ ≤ (∑' i : ℕ, Metric.ediam (U i)) + ∑' i : ℕ, ENNReal.ofReal (b i) :=
      add_le_add
        (ENNReal.tsum_comp_le_tsum_of_injective
          (f := fun i : K => (i : ℕ)) Subtype.coe_injective (fun i => Metric.ediam (U i)))
        (ENNReal.tsum_comp_le_tsum_of_injective
          (f := fun i : K => (i : ℕ)) Subtype.coe_injective (fun i => ENNReal.ofReal (b i)))
    _ = (∑' i : ℕ, Metric.ediam (U i)) + ε := by rw [hbsum]

#check @T008
#print axioms T008

end Translation
