import Mathlib

open scoped ENNReal NNReal BigOperators

abbrev YuiEucl (n : ℕ) := EuclideanSpace ℝ (Fin n)
def YuiI : Set ℝ := Set.Icc 0 1
def YuiSnoc {n : ℕ} (x : YuiEucl n) (t : ℝ) : YuiEucl (n + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x i) t)
def YuiHead {n : ℕ} (z : YuiEucl (n + 1)) : YuiEucl n :=
  WithLp.toLp 2 (fun i : Fin n => z i.castSucc)
def YuiLast {n : ℕ} (z : YuiEucl (n + 1)) : ℝ := z (Fin.last n)
def YuiCylinder {n : ℕ} (E : Set (YuiEucl n)) : Set (YuiEucl (n + 1)) :=
  {z | YuiHead z ∈ E ∧ YuiLast z ∈ YuiI}
noncomputable def YuiCost {X : Type*} [PseudoEMetricSpace X] {ι : Type*}
    (s : ℝ) (U : ι → Set X) : ℝ≥0∞ :=
  ∑' i, ⨆ (_ : (U i).Nonempty), (Metric.ediam (U i)) ^ s
def YuiCover {X : Type*} [PseudoEMetricSpace X] (δ : ℝ) (A : Set X)
    (U : ℕ → Set X) : Prop :=
  A ⊆ ⋃ i, U i ∧ ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ
noncomputable def YuiContent {X : Type*} [PseudoEMetricSpace X]
    (s δ : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : YuiCover δ A U), YuiCost s U
noncomputable def YuiMeasure {X : Type*} [PseudoEMetricSpace X]
    (s : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨆ (δ : ℝ) (_ : 0 < δ), YuiContent s δ A

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace Translation
set_option autoImplicit false

namespace Local_T004
theorem yui_aux_0001 (n : ℕ) (E : Set (YuiEucl n)) (h_H001 : 0 ≤ n) (h_H002 : E.Nonempty) (h_H003 : IsCompact E) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) : yui_aux_type% "∃ L : ℝ, 0 < L ∧ ∀ x ∈ E, ∀ i : Fin n, -(L) < x i ∧ x i < L" := by
  obtain ⟨L, hL, hE⟩ := h_H003.isBounded.subset_ball_lt 0 (0 : YuiEucl n)
  refine ⟨L, hL, ?_⟩
  intro x hx i
  have hxL : ‖x‖ < L := by simpa using hE hx
  have hi : |x i| < L := lt_of_le_of_lt (by simpa using PiLp.norm_apply_le x i) hxL
  exact abs_lt.mp hi

theorem yui_aux_0002 (n : ℕ) (E : Set (YuiEucl n)) (h_H001 : 0 ≤ n) (h_H002 : E.Nonempty) (h_H003 : IsCompact E) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) : yui_aux_type% "∃ A : ℕ, 0 < A ∧ ∀ x ∈ E, ∀ i : Fin n, -(A : ℝ) < x i ∧ x i < A" := by
  obtain ⟨L, hL, hEL⟩ := @yui_aux_0001 n E h_H001 h_H002 h_H003 h_T002
  obtain ⟨A, hA⟩ := exists_nat_gt L
  refine ⟨A, Nat.cast_pos.mp (hL.trans hA), ?_⟩
  intro x hx i
  exact ⟨lt_trans (neg_lt_neg hA) (hEL x hx i).1, (hEL x hx i).2.trans hA⟩

theorem yui_aux_0003 (n : ℕ) (E : Set (YuiEucl n)) (h_H001 : 0 ≤ n) (h_H002 : E.Nonempty) (h_H003 : IsCompact E) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) : yui_aux_type% "(∀ (r : ℝ) (m : ℕ), 0 ≤ r → r < (m : ℝ) → ⌊r⌋₊ < m) ∧ (∀ x : YuiEucl n, WithLp.toLp 2 (WithLp.ofLp x) = x)" := by
  constructor
  · intro r m hr hm
    exact (Nat.floor_lt hr).mpr hm
  · intro x
    exact WithLp.toLp_ofLp 2 x

theorem yui_aux_0004 (n : ℕ) (E : Set (YuiEucl n)) (h_H001 : 0 ≤ n) (h_H002 : E.Nonempty) (h_H003 : IsCompact E) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) : yui_aux_type% "∀ (A k : ℕ), 0 < k →\n (∀ x ∈ E, ∀ i : Fin n, -(A : ℝ) < x i ∧ x i < A) →\n let U : (Fin n → Fin (2 * A * k)) → Set (YuiEucl n) := fun f =>\n   WithLp.toLp 2 '' (Set.pi Set.univ fun i : Fin n =>\n     Set.Icc (-(A : ℝ) + (f i : ℝ) / k)\n       (-(A : ℝ) + ((f i : ℝ) + 1) / k))\n E ⊆ ⋃ f, U f ∧\n ∀ f, Metric.ediam (U f) ≤\n   (((n : ℝ≥0) ^ (1 / (2 : ℝ≥0∞)).toReal : ℝ≥0) : ℝ≥0∞) * (1 / (k : ℝ≥0∞))" := by
  classical
  intro A k hk hE
  dsimp only
  constructor
  · intro x hx
    have kpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
    let f : Fin n → Fin (2 * A * k) := fun i =>
      ⟨⌊(x i + (A : ℝ)) * k⌋₊, by
        apply (@yui_aux_0003 n E h_H001 h_H002 h_H003 h_T002).1 _ _
          (mul_nonneg (by linarith [(hE x hx i).1]) kpos.le)
        have hi := (hE x hx i).2
        have hlt : (x i + (A : ℝ)) * k < (2 * A : ℝ) * k :=
          mul_lt_mul_of_pos_right (by linarith) kpos
        exact_mod_cast hlt⟩
    refine Set.mem_iUnion.mpr ⟨f, ?_⟩
    refine ⟨WithLp.ofLp x, ?_, (@yui_aux_0003 n E h_H001 h_H002 h_H003 h_T002).2 x⟩
    simp only [Set.mem_univ_pi, Set.mem_Icc]
    intro i
    have hnonneg : 0 ≤ (x i + (A : ℝ)) * k :=
      mul_nonneg (by linarith [(hE x hx i).1]) kpos.le
    change -(A : ℝ) + (⌊(x i + (A : ℝ)) * k⌋₊ : ℝ) / k ≤ x i ∧
      x i ≤ -(A : ℝ) + ((⌊(x i + (A : ℝ)) * k⌋₊ : ℝ) + 1) / k
    constructor
    · have hfloor := Nat.floor_le hnonneg
      have hd := (div_le_iff₀ kpos).mpr hfloor
      nlinarith
    · have hfloor := (Nat.lt_floor_add_one ((x i + (A : ℝ)) * k)).le
      have hd := (le_div_iff₀ kpos).mpr hfloor
      nlinarith
  · intro f
    have hLip := PiLp.lipschitzWith_toLp (p := (2 : ℝ≥0∞)) (β := fun _ : Fin n => ℝ)
    have hdiam := hLip.ediam_image_le
      (Set.pi Set.univ fun i : Fin n =>
        Set.Icc (-(A : ℝ) + (f i : ℝ) / k)
          (-(A : ℝ) + ((f i : ℝ) + 1) / k))
    simp only [Fintype.card_fin] at hdiam
    refine hdiam.trans (mul_le_mul_left' ?_ _)
    apply Metric.ediam_pi_le_of_le
    intro i
    rw [Real.ediam_Icc]
    have heq : -(A : ℝ) + ((f i : ℝ) + 1) / k -
        (-(A : ℝ) + (f i : ℝ) / k) = 1 / k := by ring
    rw [heq, ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr hk)]
    simp

theorem yui_aux_0005 (n : ℕ) (E : Set (YuiEucl n)) (h_H001 : 0 ≤ n) (h_H002 : E.Nonempty) (h_H003 : IsCompact E) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) : yui_aux_type% "∀ (A k : ℕ) (K : ℝ≥0∞) (s : ℝ), 0 < k → 0 ≤ s →\n (((2 * A * k : ℕ) : ℝ≥0∞) ^ n) * (K * (1 / (k : ℝ≥0∞))) ^ s =\n ((2 * A : ℕ) : ℝ≥0∞) ^ n * K ^ s * (1 / (k : ℝ≥0∞)) ^ (s - n)" := by
  intro A k K s hk hs
  have hk0 : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast hk.ne'
  have hki0 : (k : ℝ≥0∞)⁻¹ ≠ 0 := by simp
  have hkit : (k : ℝ≥0∞)⁻¹ ≠ ⊤ := by simp [hk0]
  have hp : (k : ℝ≥0∞) ^ n = ((k : ℝ≥0∞)⁻¹) ^ (-(n : ℝ)) := by
    rw [ENNReal.rpow_neg, ENNReal.inv_rpow, ENNReal.rpow_natCast, inv_inv]
  rw [Nat.cast_mul, mul_pow, ENNReal.mul_rpow_of_nonneg _ _ hs, one_div, hp]
  rw [sub_eq_add_neg, ENNReal.rpow_add _ _ hki0 hkit]
  simp only [mul_comm, mul_left_comm, mul_assoc]

theorem yui_aux_0006 (n : ℕ) (E : Set (YuiEucl n)) (h_H001 : 0 ≤ n) (h_H002 : E.Nonempty) (h_H003 : IsCompact E) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) : yui_aux_type% "Filter.Tendsto (fun k : ℕ => 1 / ((k + 1 : ℕ) : ℝ≥0∞)) Filter.atTop (nhds 0) ∧\n ∀ (u v : ℕ → ℝ≥0∞), (∀ᶠ k in Filter.atTop, u k ≤ v k) →\n   Filter.liminf u Filter.atTop ≤ Filter.liminf v Filter.atTop" := by
  constructor
  · simpa only [one_div, Function.comp_def] using
      ENNReal.tendsto_inv_nat_nhds_zero.comp (Filter.tendsto_add_atTop_nat 1)
  · intro u v huv
    exact Filter.liminf_le_liminf huv (by isBoundedDefault) (by isBoundedDefault)

theorem yui_aux_0007 (n : ℕ) (E : Set (YuiEucl n)) (h_H001 : 0 ≤ n) (h_H002 : E.Nonempty) (h_H003 : IsCompact E) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) : yui_aux_type% "∀ s : ℝ, (n : ℝ) < s →\n  MeasureTheory.Measure.hausdorffMeasure s E = 0" := by
  classical
  intro s hs
  have hs0 : 0 < s := lt_of_le_of_lt (Nat.cast_nonneg n) hs
  obtain ⟨A, hA, hE⟩ := @yui_aux_0002 n E h_H001 h_H002 h_H003 h_T002
  let K : ℝ≥0 := (n : ℝ≥0) ^ (1 / (2 : ℝ≥0∞)).toReal
  let G : ℕ → Type := fun k => Fin n → Fin (2 * A * (k + 1))
  let U : ∀ k : ℕ, G k → Set (YuiEucl n) := fun k f =>
    WithLp.toLp 2 '' (Set.pi Set.univ fun i : Fin n =>
      Set.Icc (-(A : ℝ) + (f i : ℝ) / (k + 1 : ℕ))
        (-(A : ℝ) + ((f i : ℝ) + 1) / (k + 1 : ℕ)))
  have hgrid (k : ℕ) : E ⊆ ⋃ f, U k f ∧
      ∀ f, Metric.ediam (U k f) ≤ (K : ℝ≥0∞) * (1 / (k + 1 : ℕ)) :=
    @yui_aux_0004 n E h_H001 h_H002 h_H003 h_T002 A (k + 1) (Nat.succ_pos k) hE
  have hinv : Filter.Tendsto (fun k : ℕ => (1 / ((k + 1 : ℕ) : ℝ≥0∞)))
      Filter.atTop (nhds 0) :=
    (@yui_aux_0006 n E h_H001 h_H002 h_H003 h_T002).1
  have hr : Filter.Tendsto (fun k : ℕ => (K : ℝ≥0∞) * (1 / ((k + 1 : ℕ) : ℝ≥0∞)))
      Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hinv (a := (K : ℝ≥0∞))
      (Or.inr ENNReal.coe_ne_top)
  let c : ℝ≥0∞ := ((2 * A : ℕ) : ℝ≥0∞) ^ n * (K : ℝ≥0∞) ^ s
  have hc : c ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by finiteness)
      (ENNReal.rpow_ne_top_of_nonneg hs0.le ENNReal.coe_ne_top)
  have hcost : Filter.Tendsto
      (fun k : ℕ => c * (1 / ((k + 1 : ℕ) : ℝ≥0∞)) ^ (s - n))
      Filter.atTop (nhds 0) :=
    (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hc (sub_pos.mpr hs)).comp hinv
  apply le_antisymm _ zero_le
  calc
    MeasureTheory.Measure.hausdorffMeasure s E ≤
        Filter.liminf (fun k => ∑ f : G k, Metric.ediam (U k f) ^ s) Filter.atTop :=
      MeasureTheory.Measure.hausdorffMeasure_le_liminf_sum s E _ hr U
        (Filter.Eventually.of_forall fun k => (hgrid k).2)
        (Filter.Eventually.of_forall fun k => (hgrid k).1)
    _ ≤ Filter.liminf
        (fun k : ℕ => c * (1 / ((k + 1 : ℕ) : ℝ≥0∞)) ^ (s - n)) Filter.atTop := by
      apply (@yui_aux_0006 n E h_H001 h_H002 h_H003 h_T002).2
      apply Filter.Eventually.of_forall
      intro k
      calc
        (∑ f : G k, Metric.ediam (U k f) ^ s) ≤
            ∑ f : G k, ((K : ℝ≥0∞) * (1 / ((k + 1 : ℕ) : ℝ≥0∞))) ^ s := by
          apply Finset.sum_le_sum
          intro f hf
          exact ENNReal.monotone_rpow_of_nonneg hs0.le ((hgrid k).2 f)
        _ = (((2 * A * (k + 1) : ℕ) : ℝ≥0∞) ^ n) *
            ((K : ℝ≥0∞) * (1 / ((k + 1 : ℕ) : ℝ≥0∞))) ^ s := by
          simp [G, Fintype.card_fun, nsmul_eq_mul]
        _ = c * (1 / ((k + 1 : ℕ) : ℝ≥0∞)) ^ (s - n) :=
          @yui_aux_0005 n E h_H001 h_H002 h_H003 h_T002 A (k + 1)
            (K : ℝ≥0∞) s (Nat.succ_pos k) hs0.le
    _ = 0 := hcost.liminf_eq

theorem yui_aux_0008 (n : ℕ) (E : Set (YuiEucl n)) (h_H001 : 0 ≤ n) (h_H002 : E.Nonempty) (h_H003 : IsCompact E) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) : yui_aux_type% "n = 0 → ∀ s : ℝ, 0 < s → YuiMeasure s E = 0" := by
  intro hn s hs
  subst n
  obtain ⟨x, hx⟩ := h_H002
  have hsing : E = {x} := by
    ext y
    constructor
    · intro hy
      exact Set.mem_singleton_iff.mpr (Subsingleton.elim y x)
    · intro hy
      exact (Set.mem_singleton_iff.mp hy) ▸ hx
  rw [hsing]
  unfold YuiMeasure
  apply le_antisymm _ zero_le
  refine iSup_le fun δ => iSup_le fun hδ => ?_
  unfold YuiContent
  refine iInf_le_of_le (fun _ : ℕ => ({x} : Set (YuiEucl 0))) (iInf_le_of_le ?_ ?_)
  · constructor
    · exact Set.subset_iUnion (fun _ : ℕ => ({x} : Set (YuiEucl 0))) 0
    · intro i
      simp [Metric.ediam_singleton]
  · simp [YuiCost, ENNReal.zero_rpow_of_pos hs]

theorem yui_aux_0009 (n : ℕ) (E : Set (YuiEucl n)) (h_H001 : 0 ≤ n) (h_H002 : E.Nonempty) (h_H003 : IsCompact E) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) : yui_aux_type% "∀ s : ℝ, (n : ℝ≥0∞) < ENNReal.ofReal s → (n : ℝ) < s ∧ 0 < s" := by
  intro s hs
  have h : ENNReal.ofReal (n : ℝ) < ENNReal.ofReal s := by simpa only [ENNReal.ofReal_natCast] using hs
  exact ENNReal.ofReal_lt_ofReal_iff'.mp h

end Local_T004
open Local_T004 in
theorem T004 (n : ℕ) (E : Set (YuiEucl n)) (h_H001 : 0 ≤ n) (h_H002 : E.Nonempty) (h_H003 : IsCompact E) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) :
    0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ := by
  have hupper : dimH E ≤ (n : ℝ≥0∞) := by
    by_contra! h
    obtain ⟨s, hsnonneg, hns, hsD⟩ :=
      ENNReal.lt_iff_exists_real_btwn.mp h
    obtain ⟨hnsReal, hspos⟩ :=
      @yui_aux_0009 n E h_H001 h_H002 h_H003 h_T002 s hns
    have hzero : YuiMeasure s E = 0 := by
      by_cases hn : n = 0
      · exact @yui_aux_0008 n E h_H001 h_H002 h_H003 h_T002 hn s hspos
      · have hnpos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
        rw [(h_T002.1 n E s hspos).1]
        exact @yui_aux_0007 n E h_H001 h_H002 h_H003 h_T002 s hnsReal
    have hDs : dimH E ≤ ENNReal.ofReal s :=
      (h_T002.1 n E s hspos).2.2.2.1 hzero
    exact (not_lt_of_ge hDs) hsD
  exact ⟨h_T002.2.1 n E, hupper, lt_of_le_of_lt hupper (by simp)⟩

#check @T004
#print axioms T004

end Translation
