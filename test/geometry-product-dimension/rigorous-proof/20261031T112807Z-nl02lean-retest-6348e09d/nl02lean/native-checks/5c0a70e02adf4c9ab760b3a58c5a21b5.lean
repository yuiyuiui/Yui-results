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

theorem T007 (n : ℕ) (E : Set (YEuclid n)) (h_T001 : (∀ m : ℕ, yCritical (YEuclid m)) ∧ yCritical ℝ) (h_T002 : dimH E < ⊤ ∧ 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ (n = 0 → E = Set.univ ∧ (∃ x : YEuclid n, E = {x}) ∧ dimH E = 0) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → yContent s δ E < ⊤)) :
    1 ≤ n → ∀ (q r ε : ℝ), 0 < q → dimH E < ENNReal.ofReal q → 0 < r → r ≤ 1 → 0 < ε → ∃ U : ℕ → Set (YEuclid n), yCover r E U ∧ (∀ i, (U i).Nonempty → 0 < Metric.ediam (U i)) ∧ yCost q U < ENNReal.ofReal ε := by
  classical
  intro hn q r ε hq hdim hr hr1 hε
  have hz : yHaus q E = 0 := ((h_T001.1 n).2 E q hq).2.1 hdim
  have hle : yContent q r E ≤ yHaus q E := by
    unfold yHaus
    exact le_iSup_of_le r (le_iSup_of_le hr le_rfl)
  have hc : yContent q r E = 0 := le_antisymm (hle.trans_eq hz) zero_le
  have hl : yContent q r E < ENNReal.ofReal (ε / 2) := by
    rw [hc]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  have hex : ∃ W : ℕ → Set (YEuclid n),
      yCover r E W ∧ yCost q W < ENNReal.ofReal (ε / 2) := by
    simpa only [yContent, iInf_lt_iff, yCover, yCost,
      exists_prop, exists_and_left, and_assoc] using hl
  obtain ⟨W, hW, hcost⟩ := hex
  let a : ℕ → ℝ := fun i => ε / 8 * (1 / 2 : ℝ) ^ i
  have ha : ∀ i, 0 < a i := fun i => by dsimp [a]; positivity
  have hsmall : ∀ i : ℕ, ∃ b : ℝ, 0 < b ∧ b ≤ r ∧
      (ENNReal.ofReal b) ^ q ≤ ENNReal.ofReal (a i) := by
    intro i
    let b := min (r / 2) ((a i) ^ q⁻¹)
    have hb : 0 < b := lt_min (by positivity) (Real.rpow_pos_of_pos (ha i) _)
    refine ⟨b, hb, (min_le_left _ _).trans (by linarith), ?_⟩
    rw [ENNReal.ofReal_rpow_of_nonneg hb.le hq.le]
    apply ENNReal.ofReal_le_ofReal
    calc
      b ^ q ≤ ((a i) ^ q⁻¹) ^ q :=
        Real.rpow_le_rpow hb.le (min_le_right _ _) hq.le
      _ = a i := Real.rpow_inv_rpow (ha i).le hq.ne'
  choose b hb using hsmall
  have hball : ∀ (x : YEuclid n) (d : ℝ), 0 < d →
      Metric.ediam (Metric.ball x (d / 2)) = ENNReal.ofReal d := by
    intro x d hd
    letI : NeZero n := ⟨by omega⟩
    have hfin : Metric.ediam (Metric.ball x (d / 2)) ≠ ⊤ :=
      Metric.isBounded_ball.ediam_ne_top
    calc
      Metric.ediam (Metric.ball x (d / 2)) =
          ENNReal.ofReal (Metric.diam (Metric.ball x (d / 2))) :=
        (ENNReal.ofReal_toReal hfin).symm
      _ = ENNReal.ofReal d := by
        rw [Metric.diam_ball_eq x (by positivity)]
        congr 1
        ring
  let U : ℕ → Set (YEuclid n) := fun i =>
    if h : (W i).Nonempty ∧ Metric.ediam (W i) = 0 then
      Metric.ball h.1.choose (b i / 2)
    else W i
  have hU : ∀ i, W i ⊆ U i ∧
      Metric.ediam (U i) ≤ ENNReal.ofReal r ∧
      ((U i).Nonempty → 0 < Metric.ediam (U i)) ∧
      (Metric.ediam (U i)) ^ q ≤
        (Metric.ediam (W i)) ^ q + ENNReal.ofReal (a i) := by
    intro i
    dsimp only [U]
    split_ifs with hi
    · have hd := hball hi.1.choose (b i) (hb i).1
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro x hx
        have heq : x = hi.1.choose :=
          (Metric.ediam_eq_zero_iff.mp hi.2) hx hi.1.choose_spec
        rw [heq]
        exact Metric.mem_ball_self (half_pos (hb i).1)
      · rw [hd]
        exact ENNReal.ofReal_le_ofReal (hb i).2.1
      · intro _
        rw [hd]
        exact ENNReal.ofReal_pos.mpr (hb i).1
      · rw [hd]
        exact (hb i).2.2.trans (le_add_left le_rfl)
    · refine ⟨Subset.rfl, hW.2 i, ?_, le_add_right le_rfl⟩
      intro hne
      exact pos_iff_ne_zero.mpr (fun heq => hi ⟨hne, heq⟩)
  have hsum : (∑' i : ℕ, ENNReal.ofReal (a i)) = ENNReal.ofReal (ε / 4) := by
    have hs : Summable (fun i : ℕ => ε / 8 * (1 / 2 : ℝ) ^ i) :=
      summable_geometric_two.mul_left (ε / 8)
    dsimp only [a]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) hs,
      tsum_mul_left, tsum_geometric_two]
    congr 1
    ring
  refine ⟨U, ⟨?_, fun i => (hU i).2.1⟩, fun i => (hU i).2.2.1, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hW.1 hx)
    exact Set.mem_iUnion.mpr ⟨i, (hU i).1 hi⟩
  · calc
      yCost q U ≤ ∑' i, ((Metric.ediam (W i)) ^ q + ENNReal.ofReal (a i)) :=
        ENNReal.tsum_le_tsum fun i => (hU i).2.2.2
      _ = yCost q W + ENNReal.ofReal (ε / 4) := by
        rw [ENNReal.tsum_add, hsum]
        rfl
      _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 4) :=
        add_le_add_right hcost.le _
      _ = ENNReal.ofReal (ε / 2 + ε / 4) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
      _ < ENNReal.ofReal ε := (ENNReal.ofReal_lt_ofReal_iff hε).mpr (by linarith)

#check @T007
#print axioms T007

end Translation
