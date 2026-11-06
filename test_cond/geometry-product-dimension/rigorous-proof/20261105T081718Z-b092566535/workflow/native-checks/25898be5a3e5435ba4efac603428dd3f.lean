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

namespace Local_T008
theorem yui_aux_0001 (n : ℕ) (E : Set (YuiEucl n)) (h_T003 : ∀ k : ℕ, (∀ (x : YuiEucl k) (t : ℝ), YuiHead (YuiSnoc x t) = x ∧ YuiLast (YuiSnoc x t) = t) ∧ (∀ z : YuiEucl (k + 1), YuiSnoc (YuiHead z) (YuiLast z) = z) ∧ (∀ (x y : YuiEucl k) (t u : ℝ), dist (YuiSnoc x t) (YuiSnoc y u) = Real.sqrt ((dist x y) ^ 2 + |t-u| ^ 2)) ∧ LipschitzWith 1 (YuiHead (n := k)) ∧ LipschitzWith 1 (YuiLast (n := k))) (h_T007 : 1 ≤ n → ∀ q : ℝ, dimH E < ENNReal.ofReal q → ∀ r ε : ℝ, 0 < r → r ≤ 1 → 0 < ε → ∃ (T : Set ℕ) (U : T → Set (YuiEucl n)), E ⊆ ⋃ i, U i ∧ (∀ i, (U i).Nonempty ∧ 0 < Metric.ediam (U i) ∧ Metric.ediam (U i) ≤ ENNReal.ofReal r) ∧ YuiCost q U < ENNReal.ofReal ε) : yui_aux_type% "∀ (N : ℕ) (t : ℝ), 0 < N → 0 ≤ t → t < 1 → ∃ j : Fin N, t ∈ Set.Icc ((j : ℝ) / N) (((j : ℝ) + 1) / N)" := by
  intro N t hN ht ht1
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hnon : 0 ≤ t * (N : ℝ) := mul_nonneg ht hNr.le
  have hprod : t * (N : ℝ) < N := by nlinarith
  have hj : ⌊t * (N : ℝ)⌋₊ < N := (Nat.floor_lt hnon).mpr hprod
  refine ⟨⟨⌊t * (N : ℝ)⌋₊, hj⟩, ?_, ?_⟩
  · exact (div_le_iff₀ hNr).mpr (Nat.floor_le hnon)
  · exact (le_div_iff₀ hNr).mpr (Nat.lt_floor_add_one (t * N)).le

theorem yui_aux_0002 (n : ℕ) (E : Set (YuiEucl n)) (h_T003 : ∀ k : ℕ, (∀ (x : YuiEucl k) (t : ℝ), YuiHead (YuiSnoc x t) = x ∧ YuiLast (YuiSnoc x t) = t) ∧ (∀ z : YuiEucl (k + 1), YuiSnoc (YuiHead z) (YuiLast z) = z) ∧ (∀ (x y : YuiEucl k) (t u : ℝ), dist (YuiSnoc x t) (YuiSnoc y u) = Real.sqrt ((dist x y) ^ 2 + |t-u| ^ 2)) ∧ LipschitzWith 1 (YuiHead (n := k)) ∧ LipschitzWith 1 (YuiLast (n := k))) (h_T007 : 1 ≤ n → ∀ q : ℝ, dimH E < ENNReal.ofReal q → ∀ r ε : ℝ, 0 < r → r ≤ 1 → 0 < ε → ∃ (T : Set ℕ) (U : T → Set (YuiEucl n)), E ⊆ ⋃ i, U i ∧ (∀ i, (U i).Nonempty ∧ 0 < Metric.ediam (U i) ∧ Metric.ediam (U i) ≤ ENNReal.ofReal r) ∧ YuiCost q U < ENNReal.ofReal ε) : yui_aux_type% "∀ d : ℝ, 0 < d → d ≤ 1 → ∃ N : ℕ, 0 < N ∧ 1 / (N : ℝ) ≤ d ∧ (N : ℝ) * d ≤ 2 ∧ (∀ t ∈ YuiI, ∃ j : Fin N, t ∈ Set.Icc ((j : ℝ) / N) (((j : ℝ) + 1) / N))" := by
  intro d hd hd1
  refine ⟨⌈1 / d⌉₊, Nat.ceil_pos.mpr (by positivity), ?_, ?_, ?_⟩
  · have h := Nat.le_ceil (1 / d)
    have hN : (0 : ℝ) < (⌈1 / d⌉₊ : ℝ) := by exact_mod_cast Nat.ceil_pos.mpr (by positivity : 0 < 1 / d)
    apply (div_le_iff₀ hN).mpr
    have := (div_le_iff₀ hd).mp h
    nlinarith
  · have h := (Nat.ceil_lt_add_one (by positivity : 0 ≤ 1 / d)).le
    have hmul := mul_le_mul_of_nonneg_right h hd.le
    rw [add_mul, div_mul_cancel₀ _ hd.ne'] at hmul
    nlinarith
  · intro t ht
    change 0 ≤ t ∧ t ≤ 1 at ht
    let N := ⌈1 / d⌉₊
    change ∃ j : Fin N, t ∈ Set.Icc ((j : ℝ) / N) (((j : ℝ) + 1) / N)
    have hN : 0 < N := Nat.ceil_pos.mpr (by positivity)
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    by_cases ht1 : t = 1
    · refine ⟨⟨N - 1, by omega⟩, ?_⟩
      change ((N - 1 : ℕ) : ℝ) / N ≤ t ∧ t ≤ (((N - 1 : ℕ) : ℝ) + 1) / N
      have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
      rw [hcast, ht1]
      constructor
      · apply (div_le_iff₀ hNr).mpr; nlinarith
      · apply (le_div_iff₀ hNr).mpr; nlinarith
    · exact yui_aux_0001 n E h_T003 h_T007 N t hN ht.1 (lt_of_le_of_ne ht.2 ht1)

theorem yui_aux_0003 (n : ℕ) (E : Set (YuiEucl n)) (h_T003 : ∀ k : ℕ, (∀ (x : YuiEucl k) (t : ℝ), YuiHead (YuiSnoc x t) = x ∧ YuiLast (YuiSnoc x t) = t) ∧ (∀ z : YuiEucl (k + 1), YuiSnoc (YuiHead z) (YuiLast z) = z) ∧ (∀ (x y : YuiEucl k) (t u : ℝ), dist (YuiSnoc x t) (YuiSnoc y u) = Real.sqrt ((dist x y) ^ 2 + |t-u| ^ 2)) ∧ LipschitzWith 1 (YuiHead (n := k)) ∧ LipschitzWith 1 (YuiLast (n := k))) (h_T007 : 1 ≤ n → ∀ q : ℝ, dimH E < ENNReal.ofReal q → ∀ r ε : ℝ, 0 < r → r ≤ 1 → 0 < ε → ∃ (T : Set ℕ) (U : T → Set (YuiEucl n)), E ⊆ ⋃ i, U i ∧ (∀ i, (U i).Nonempty ∧ 0 < Metric.ediam (U i) ∧ Metric.ediam (U i) ≤ ENNReal.ofReal r) ∧ YuiCost q U < ENNReal.ofReal ε) : yui_aux_type% "∀ (a b d : ℝ), 0 ≤ a → 0 ≤ b → 0 ≤ d → a ≤ d → b ≤ d → Real.sqrt (a^2+b^2) ≤ Real.sqrt 2*d" := by
  intro a b d ha hb hd had hbd
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hsq1 : a^2 ≤ d^2 := by nlinarith
  have hsq2 : b^2 ≤ d^2 := by nlinarith
  nlinarith

theorem yui_aux_0004 (n : ℕ) (E : Set (YuiEucl n)) (h_T003 : ∀ k : ℕ, (∀ (x : YuiEucl k) (t : ℝ), YuiHead (YuiSnoc x t) = x ∧ YuiLast (YuiSnoc x t) = t) ∧ (∀ z : YuiEucl (k + 1), YuiSnoc (YuiHead z) (YuiLast z) = z) ∧ (∀ (x y : YuiEucl k) (t u : ℝ), dist (YuiSnoc x t) (YuiSnoc y u) = Real.sqrt ((dist x y) ^ 2 + |t-u| ^ 2)) ∧ LipschitzWith 1 (YuiHead (n := k)) ∧ LipschitzWith 1 (YuiLast (n := k))) (h_T007 : 1 ≤ n → ∀ q : ℝ, dimH E < ENNReal.ofReal q → ∀ r ε : ℝ, 0 < r → r ≤ 1 → 0 < ε → ∃ (T : Set ℕ) (U : T → Set (YuiEucl n)), E ⊆ ⋃ i, U i ∧ (∀ i, (U i).Nonempty ∧ 0 < Metric.ediam (U i) ∧ Metric.ediam (U i) ≤ ENNReal.ofReal r) ∧ YuiCost q U < ENNReal.ofReal ε) : yui_aux_type% "∀ (U : Set (YuiEucl n)) (d a b : ℝ), 0 ≤ d → Metric.ediam U ≤ ENNReal.ofReal d → b - a ≤ d → Metric.ediam {z : YuiEucl (n+1) | YuiHead z ∈ U ∧ YuiLast z ∈ Set.Icc a b} ≤ ENNReal.ofReal (Real.sqrt 2 * d)" := by
  intro U d a b hd hU hab
  apply Metric.ediam_le_of_forall_dist_le
  intro z hz w hw
  have hdist : dist (YuiHead z) (YuiHead w) ≤ d := by
    have h := Metric.edist_le_ediam_of_mem hz.1 hw.1
    rw [edist_dist] at h
    exact (ENNReal.ofReal_le_ofReal_iff hd).mp (h.trans hU)
  have hlast : |YuiLast z - YuiLast w| ≤ d := by
    apply abs_le.mpr
    constructor <;> linarith [hz.2.1, hz.2.2, hw.2.1, hw.2.2]
  have hformula : dist z w = Real.sqrt ((dist (YuiHead z) (YuiHead w))^2 + |YuiLast z - YuiLast w|^2) := by
    conv_lhs => rw [← (h_T003 n).2.1 z, ← (h_T003 n).2.1 w]
    exact (h_T003 n).2.2.1 _ _ _ _
  rw [hformula]
  exact yui_aux_0003 n E h_T003 h_T007 _ _ _ dist_nonneg (abs_nonneg _) hd hdist hlast

theorem yui_aux_0005 (n : ℕ) (E : Set (YuiEucl n)) (h_T003 : ∀ k : ℕ, (∀ (x : YuiEucl k) (t : ℝ), YuiHead (YuiSnoc x t) = x ∧ YuiLast (YuiSnoc x t) = t) ∧ (∀ z : YuiEucl (k + 1), YuiSnoc (YuiHead z) (YuiLast z) = z) ∧ (∀ (x y : YuiEucl k) (t u : ℝ), dist (YuiSnoc x t) (YuiSnoc y u) = Real.sqrt ((dist x y) ^ 2 + |t-u| ^ 2)) ∧ LipschitzWith 1 (YuiHead (n := k)) ∧ LipschitzWith 1 (YuiLast (n := k))) (h_T007 : 1 ≤ n → ∀ q : ℝ, dimH E < ENNReal.ofReal q → ∀ r ε : ℝ, 0 < r → r ≤ 1 → 0 < ε → ∃ (T : Set ℕ) (U : T → Set (YuiEucl n)), E ⊆ ⋃ i, U i ∧ (∀ i, (U i).Nonempty ∧ 0 < Metric.ediam (U i) ∧ Metric.ediam (U i) ≤ ENNReal.ofReal r) ∧ YuiCost q U < ENNReal.ofReal ε) : yui_aux_type% "∀ (U : Set (YuiEucl n)) (r : ℝ), 0 < Metric.ediam U → Metric.ediam U ≤ ENNReal.ofReal r → 0 < Metric.diam U ∧ Metric.diam U ≤ r ∧ ENNReal.ofReal (Metric.diam U) = Metric.ediam U" := by
  intro U r hpos hle
  have hfin : Metric.ediam U ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  have hr : 0 ≤ r := le_of_lt (ENNReal.ofReal_pos.mp (lt_of_lt_of_le hpos hle))
  refine ⟨?_, ENNReal.toReal_le_of_le_ofReal hr hle, ?_⟩
  · exact ENNReal.toReal_pos hpos.ne' hfin
  · exact ENNReal.ofReal_toReal hfin

theorem yui_aux_0006 (n : ℕ) (E : Set (YuiEucl n)) (h_T003 : ∀ k : ℕ, (∀ (x : YuiEucl k) (t : ℝ), YuiHead (YuiSnoc x t) = x ∧ YuiLast (YuiSnoc x t) = t) ∧ (∀ z : YuiEucl (k + 1), YuiSnoc (YuiHead z) (YuiLast z) = z) ∧ (∀ (x y : YuiEucl k) (t u : ℝ), dist (YuiSnoc x t) (YuiSnoc y u) = Real.sqrt ((dist x y) ^ 2 + |t-u| ^ 2)) ∧ LipschitzWith 1 (YuiHead (n := k)) ∧ LipschitzWith 1 (YuiLast (n := k))) (h_T007 : 1 ≤ n → ∀ q : ℝ, dimH E < ENNReal.ofReal q → ∀ r ε : ℝ, 0 < r → r ≤ 1 → 0 < ε → ∃ (T : Set ℕ) (U : T → Set (YuiEucl n)), E ⊆ ⋃ i, U i ∧ (∀ i, (U i).Nonempty ∧ 0 < Metric.ediam (U i) ∧ Metric.ediam (U i) ≤ ENNReal.ofReal r) ∧ YuiCost q U < ENNReal.ofReal ε) : yui_aux_type% "∀ (d c q : ℝ) (N : ℕ), 0 < d → 0 < c → (N : ℝ) * d ≤ 2 → (N : ℝ≥0∞) * (ENNReal.ofReal (c*d)) ^ (q+1) ≤ ENNReal.ofReal (2*c^(q+1)) * (ENNReal.ofReal d)^q" := by
  intro d c q N hd hc hN
  rw [ENNReal.ofReal_rpow_of_pos (mul_pos hc hd), ENNReal.ofReal_rpow_of_pos hd]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg N),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * c^(q+1))]
  apply ENNReal.ofReal_le_ofReal
  rw [Real.mul_rpow hc.le hd.le, Real.rpow_add hd, Real.rpow_one]
  calc
    (N : ℝ) * (c ^ (q+1) * (d^q*d)) = ((N : ℝ)*d) * (c^(q+1)*d^q) := by ring
    _ ≤ 2 * (c^(q+1)*d^q) := mul_le_mul_of_nonneg_right hN (by positivity)
    _ = _ := by ring

theorem yui_aux_0007 (n : ℕ) (E : Set (YuiEucl n)) (h_T003 : ∀ k : ℕ, (∀ (x : YuiEucl k) (t : ℝ), YuiHead (YuiSnoc x t) = x ∧ YuiLast (YuiSnoc x t) = t) ∧ (∀ z : YuiEucl (k + 1), YuiSnoc (YuiHead z) (YuiLast z) = z) ∧ (∀ (x y : YuiEucl k) (t u : ℝ), dist (YuiSnoc x t) (YuiSnoc y u) = Real.sqrt ((dist x y) ^ 2 + |t-u| ^ 2)) ∧ LipschitzWith 1 (YuiHead (n := k)) ∧ LipschitzWith 1 (YuiLast (n := k))) (h_T007 : 1 ≤ n → ∀ q : ℝ, dimH E < ENNReal.ofReal q → ∀ r ε : ℝ, 0 < r → r ≤ 1 → 0 < ε → ∃ (T : Set ℕ) (U : T → Set (YuiEucl n)), E ⊆ ⋃ i, U i ∧ (∀ i, (U i).Nonempty ∧ 0 < Metric.ediam (U i) ∧ Metric.ediam (U i) ≤ ENNReal.ofReal r) ∧ YuiCost q U < ENNReal.ofReal ε) : yui_aux_type% "∀ (q : ℝ) (U : Set (YuiEucl n)) (d : ℝ), 0 < q → 0 < d → d ≤ 1 → ENNReal.ofReal d = Metric.ediam U → ∃ (N : ℕ) (V : Fin N → Set (YuiEucl (n+1))), {z : YuiEucl (n+1) | YuiHead z ∈ U ∧ YuiLast z ∈ YuiI} ⊆ ⋃ j, V j ∧ (∀ j, Metric.ediam (V j) ≤ ENNReal.ofReal (Real.sqrt 2*d)) ∧ YuiCost (q+1) V ≤ ENNReal.ofReal (2*(Real.sqrt 2)^(q+1)) * (Metric.ediam U)^q" := by
  intro q U d hq hd hd1 heq
  obtain ⟨N, hN, hlen, hmult, hcover⟩ := yui_aux_0002 n E h_T003 h_T007 d hd hd1
  let V : Fin N → Set (YuiEucl (n+1)) := fun j => {z | YuiHead z ∈ U ∧ YuiLast z ∈ Set.Icc ((j : ℝ)/N) (((j : ℝ)+1)/N)}
  have hdiam : ∀ j, Metric.ediam (V j) ≤ ENNReal.ofReal (Real.sqrt 2*d) := by
    intro j
    apply yui_aux_0004 n E h_T003 h_T007 U d _ _ hd.le heq.ge
    calc
      ((j : ℝ)+1)/N - (j : ℝ)/N = 1/(N : ℝ) := by ring
      _ ≤ d := hlen
  refine ⟨N, V, ?_, hdiam, ?_⟩
  · intro z hz
    obtain ⟨j, hj⟩ := hcover (YuiLast z) hz.2
    exact Set.mem_iUnion.mpr ⟨j, hz.1, hj⟩
  · calc
      YuiCost (q+1) V ≤ ∑' j : Fin N, (ENNReal.ofReal (Real.sqrt 2*d))^(q+1) := by
        apply ENNReal.tsum_le_tsum
        intro j
        apply iSup_le
        intro _
        exact ENNReal.rpow_le_rpow (hdiam j) (by linarith)
      _ = (N : ℝ≥0∞) * (ENNReal.ofReal (Real.sqrt 2*d))^(q+1) := by
        simp [tsum_fintype]
      _ ≤ ENNReal.ofReal (2*(Real.sqrt 2)^(q+1)) * (ENNReal.ofReal d)^q :=
        yui_aux_0006 n E h_T003 h_T007 d (Real.sqrt 2) q N hd (by positivity) hmult
      _ = _ := by rw [heq]

end Local_T008
open Local_T008 in
theorem T008 (n : ℕ) (E : Set (YuiEucl n)) (h_T003 : ∀ k : ℕ, (∀ (x : YuiEucl k) (t : ℝ), YuiHead (YuiSnoc x t) = x ∧ YuiLast (YuiSnoc x t) = t) ∧ (∀ z : YuiEucl (k + 1), YuiSnoc (YuiHead z) (YuiLast z) = z) ∧ (∀ (x y : YuiEucl k) (t u : ℝ), dist (YuiSnoc x t) (YuiSnoc y u) = Real.sqrt ((dist x y) ^ 2 + |t-u| ^ 2)) ∧ LipschitzWith 1 (YuiHead (n := k)) ∧ LipschitzWith 1 (YuiLast (n := k))) (h_T007 : 1 ≤ n → ∀ q : ℝ, dimH E < ENNReal.ofReal q → ∀ r ε : ℝ, 0 < r → r ≤ 1 → 0 < ε → ∃ (T : Set ℕ) (U : T → Set (YuiEucl n)), E ⊆ ⋃ i, U i ∧ (∀ i, (U i).Nonempty ∧ 0 < Metric.ediam (U i) ∧ Metric.ediam (U i) ≤ ENNReal.ofReal r) ∧ YuiCost q U < ENNReal.ofReal ε) :
    1 ≤ n → ∀ q : ℝ, dimH E < ENNReal.ofReal q → ∀ r ε : ℝ, 0 < r → r ≤ 1 → 0 < ε → ∃ W : ℕ → Set (YuiEucl (n + 1)), YuiCover (Real.sqrt 2 * r) (YuiCylinder E) W ∧ YuiCost (q + 1) W < ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q + 1) * ε) := by
  classical
  intro hn q hq r ε hr hr1 hε
  have hqpos : 0 < q := ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hq)
  obtain ⟨T, U, hcover, hU, hcost⟩ := h_T007 hn q hq r ε hr hr1 hε
  have hd : ∀ i : T, 0 < Metric.diam (U i) ∧ Metric.diam (U i) ≤ r ∧
      ENNReal.ofReal (Metric.diam (U i)) = Metric.ediam (U i) := by
    intro i
    exact yui_aux_0005 n E h_T003 h_T007 (U i) r (hU i).2.1 (hU i).2.2
  have hi := fun i : T => yui_aux_0007 n E h_T003 h_T007 q (U i) (Metric.diam (U i))
    hqpos (hd i).1 ((hd i).2.1.trans hr1) (hd i).2.2
  choose N V hVcover hVdiam hVcost using hi
  let K := Σ i : T, Fin (N i)
  let F : K → Set (YuiEucl (n+1)) := fun p => V p.1 p.2
  let W : ℕ → Set (YuiEucl (n+1)) := fun j => ⋃ p ∈ Encodable.decode₂ K j, F p
  have hFcover : YuiCylinder E ⊆ ⋃ p : K, F p := by
    intro z hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hz.1)
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hVcover i ⟨hi, hz.2⟩)
    exact Set.mem_iUnion.mpr ⟨⟨i,j⟩, hj⟩
  have hFdiam : ∀ p : K, Metric.ediam (F p) ≤ ENNReal.ofReal (Real.sqrt 2*r) := by
    intro p
    exact (hVdiam p.1 p.2).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (hd p.1).2.1 (Real.sqrt_nonneg 2)))
  have hWcost : YuiCost (q+1) W = YuiCost (q+1) F := by
    exact tsum_iUnion_decode₂
      (fun A : Set (YuiEucl (n+1)) => ⨆ _ : A.Nonempty, (Metric.ediam A)^(q+1))
      (by simp) F
  have hbase : (∑' i : T, (Metric.ediam (U i))^q) = YuiCost q U := by
    unfold YuiCost
    apply tsum_congr
    intro i
    simp [(hU i).1]
  have hFcost : YuiCost (q+1) F ≤ ENNReal.ofReal (2*(Real.sqrt 2)^(q+1)) * YuiCost q U := by
    calc
      YuiCost (q+1) F = ∑' i : T, YuiCost (q+1) (V i) := by
        unfold YuiCost
        exact ENNReal.tsum_sigma' _
      _ ≤ ∑' i : T, ENNReal.ofReal (2*(Real.sqrt 2)^(q+1)) * (Metric.ediam (U i))^q :=
        ENNReal.tsum_le_tsum hVcost
      _ = _ := by rw [ENNReal.tsum_mul_left, hbase]
  refine ⟨W, ⟨?_, ?_⟩, ?_⟩
  · change YuiCylinder E ⊆ ⋃ (j : ℕ) (p ∈ Encodable.decode₂ K j), F p
    rw [Encodable.iUnion_decode₂]
    exact hFcover
  · intro j
    change Metric.ediam (⋃ p ∈ Encodable.decode₂ K j, F p) ≤ _
    rw [Metric.ediam_iUnion_mem_option]
    exact iSup₂_le fun p _ => hFdiam p
  · rw [hWcost]
    have hcpos : 0 < 2*(Real.sqrt 2)^(q+1) := by positivity
    calc
      YuiCost (q+1) F ≤ ENNReal.ofReal (2*(Real.sqrt 2)^(q+1)) * YuiCost q U := hFcost
      _ < ENNReal.ofReal (2*(Real.sqrt 2)^(q+1)) * ENNReal.ofReal ε :=
        ENNReal.mul_lt_mul_right (ne_of_gt (ENNReal.ofReal_pos.mpr hcpos)) ENNReal.ofReal_ne_top hcost
      _ = _ := (ENNReal.ofReal_mul hcpos.le).symm

#check @T008
#print axioms T008

end Translation
