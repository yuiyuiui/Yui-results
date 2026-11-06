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

namespace YuiAuxiliary
set_option autoImplicit false
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

theorem checked (n : ℕ) (E : Set (YuiEucl n)) (h_H001 : 0 ≤ n) (h_H002 : E.Nonempty) (h_H003 : IsCompact E) (h_T002 : (∀ (k : ℕ) (A : Set (YuiEucl k)) (a : ℝ), 0 < a → YuiMeasure a A = MeasureTheory.Measure.hausdorffMeasure a A ∧ (dimH A < ENNReal.ofReal a → YuiMeasure a A = 0) ∧ (ENNReal.ofReal a < dimH A → YuiMeasure a A = ⊤) ∧ (YuiMeasure a A = 0 → dimH A ≤ ENNReal.ofReal a) ∧ (YuiMeasure a A = ⊤ → ENNReal.ofReal a ≤ dimH A)) ∧ (∀ (k : ℕ) (A : Set (YuiEucl k)), 0 ≤ dimH A) ∧ (∀ (k : ℕ) (A B : Set (YuiEucl k)), A ⊆ B → dimH A ≤ dimH B) ∧ (∀ (k l : ℕ) (A : Set (YuiEucl k)) (g : A → YuiEucl l), Isometry g → dimH (Set.range g) = dimH A)) : yui_aux_type% "∀ (A k : ℕ) (K : ℝ≥0∞) (s : ℝ), 0 < k → 0 ≤ s →\n (((2 * A * k : ℕ) : ℝ≥0∞) ^ n) * (K * (1 / (k : ℝ≥0∞))) ^ s =\n ((2 * A : ℕ) : ℝ≥0∞) ^ n * K ^ s * (1 / (k : ℝ≥0∞)) ^ (s - n)" := by
  intro A k K s hk hs
  have hk0 : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast hk.ne'
  have hki0 : (k : ℝ≥0∞)⁻¹ ≠ 0 := by simp
  have hkit : (k : ℝ≥0∞)⁻¹ ≠ ⊤ := by simp [hk0]
  have hp : (k : ℝ≥0∞) ^ n = ((k : ℝ≥0∞)⁻¹) ^ (-(n : ℝ)) := by
    rw [ENNReal.rpow_neg, ENNReal.inv_rpow, ENNReal.rpow_natCast, inv_inv]
  rw [Nat.cast_mul, mul_pow, ENNReal.mul_rpow_of_nonneg _ _ hs, one_div, hp]
  rw [sub_eq_add_neg, ENNReal.rpow_add _ _ hki0 hkit]
  ac_rfl
#check @checked
#print axioms checked
end YuiAuxiliary
