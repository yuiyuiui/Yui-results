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

theorem T008 (n : ℕ) (E : Set (YEuclid n)) (h_T001 : (∀ m : ℕ, yCritical (YEuclid m)) ∧ yCritical ℝ) (h_T002 : dimH E < ⊤ ∧ 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ (n = 0 → E = Set.univ ∧ (∃ x : YEuclid n, E = {x}) ∧ dimH E = 0) ∧ (∀ (s δ : ℝ), 0 < s → 0 < δ → yContent s δ E < ⊤)) (h_T007 : 1 ≤ n → ∀ (q r ε : ℝ), 0 < q → dimH E < ENNReal.ofReal q → 0 < r → r ≤ 1 → 0 < ε → ∃ U : ℕ → Set (YEuclid n), yCover r E U ∧ (∀ i, (U i).Nonempty → 0 < Metric.ediam (U i)) ∧ yCost q U < ENNReal.ofReal ε) :
    1 ≤ n → dimH (yProd E) ≤ dimH E + 1 := by
  classical
  have hinterval : ∀ a : ℝ, 0 < a → a ≤ 1 → ∃ (N : ℕ) (J : Fin N → Set ℝ), 0 < N ∧ (N : ℝ) ≤ 2 / a ∧ (∀ t ∈ yI, ∃ j, t ∈ J j) ∧ ∀ j s, s ∈ J j → ∀ t, t ∈ J j → dist s t ≤ a := by
    intro a ha ha1
    let N : ℕ := ⌈1 / a⌉₊
    have hN : 0 < N := Nat.ceil_pos.mpr (by positivity)
    have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    have hNa : (N : ℝ) ≤ 2 / a := by
      have hc : (N : ℝ) < 1 / a + 1 := Nat.ceil_lt_add_one (by positivity)
      have h1 : (1 : ℝ) ≤ 1 / a := (le_div_iff₀ ha).mpr (by simpa using ha1)
      rw [show 2 / a = 1 / a + 1 / a by ring]
      linarith
    have hlen : 1 / (N : ℝ) ≤ a := by
      have hc : 1 / a ≤ (N : ℝ) := Nat.le_ceil _
      apply (div_le_iff₀ hNr).mpr
      have := (div_le_iff₀ ha).mp hc
      nlinarith
    let J : Fin N → Set ℝ := fun j => Set.Icc ((j : ℝ) / N) (((j : ℝ) + 1) / N)
    refine ⟨N, J, hN, hNa, ?_, ?_⟩
    · intro t ht
      have ht0 : 0 ≤ t := ht.1
      have ht1 : t ≤ 1 := ht.2
      by_cases ht : t = 1
      · let j : Fin N := ⟨N-1, by omega⟩
        refine ⟨j, ?_⟩
        change (j : ℝ) / N ≤ t ∧ t ≤ ((j : ℝ) + 1) / N
        have hj : (j : ℝ) + 1 = (N : ℝ) := by
          dsimp [j]
          norm_cast
          omega
        rw [ht]
        constructor
        · apply (div_le_iff₀ hNr).mpr
          linarith
        · rw [hj, div_self (ne_of_gt hNr)]
      · have htlt : t < 1 := lt_of_le_of_ne ht1 ht
        let j : Fin N := ⟨⌊t * N⌋₊, (Nat.floor_lt (mul_nonneg ht0 hNr.le)).mpr (by nlinarith)⟩
        refine ⟨j, ?_⟩
        change (j : ℝ) / N ≤ t ∧ t ≤ ((j : ℝ) + 1) / N
        constructor
        · apply (div_le_iff₀ hNr).mpr
          exact Nat.floor_le (mul_nonneg ht0 hNr.le)
        · apply (le_div_iff₀ hNr).mpr
          exact (Nat.lt_floor_add_one (t * N)).le
    · intro j s hs t ht
      have hst : |s-t| ≤ 1 / (N : ℝ) := by
        change _ ≤ s ∧ s ≤ _ at hs
        change _ ≤ t ∧ t ≤ _ at ht
        simp only [add_div] at hs ht
        rw [abs_le]
        constructor <;> linarith
      exact (by simpa [Real.dist_eq] using hst : dist s t ≤ 1 / (N : ℝ)).trans hlen
  have hcountable : ∀ (ι : Type) [Countable ι] (s δ : ℝ) (A : Set (YEuclid (n+1))) (V : ι → Set (YEuclid (n+1))), 0 < s → A ⊆ ⋃ i, V i → (∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ) → yContent s δ A ≤ ∑' i, Metric.ediam (V i) ^ s := by
    intro ι hι s δ A V hs hcov hdiam
    letI : Encodable ι := Encodable.ofCountable ι
    let U : ℕ → Set (YEuclid (n+1)) := fun k => ⋃ b ∈ Encodable.decode₂ ι k, V b
    have hUcov : A ⊆ ⋃ k, U k := by
      simpa only [U, Encodable.iUnion_decode₂] using hcov
    have hUdiam : ∀ k, Metric.ediam (U k) ≤ ENNReal.ofReal δ := by
      intro k
      change Metric.ediam (⋃ b ∈ Encodable.decode₂ ι k, V b) ≤ ENNReal.ofReal δ
      apply Encodable.iUnion_decode₂_cases (C := fun B => Metric.ediam B ≤ ENNReal.ofReal δ)
      · simp
      · exact hdiam
    have hle : yContent s δ A ≤ ∑' k, Metric.ediam (U k) ^ s := by
      unfold yContent
      exact iInf_le_of_le U (iInf_le_of_le hUcov (iInf_le_of_le hUdiam le_rfl))
    refine hle.trans_eq ?_
    exact tsum_iUnion_decode₂ (fun B : Set (YEuclid (n+1)) => Metric.ediam B ^ s) (by simp [ENNReal.zero_rpow_of_pos hs]) V
  have hcostlemma : ∀ (q a : ℝ) (N : ℕ), 0 < q → 0 < a → (N : ℝ) ≤ 2 / a → (N : ℝ≥0∞) * (ENNReal.ofReal (Real.sqrt 2 * a)) ^ (q+1) ≤ ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q+1)) * (ENNReal.ofReal a) ^ q := by
    intro q a N hq ha hN
    have hsq : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hreal : (N : ℝ) * (Real.sqrt 2 * a) ^ (q+1) ≤ (2 * (Real.sqrt 2) ^ (q+1)) * a ^ q := by
      rw [Real.mul_rpow hsq.le ha.le, Real.rpow_add ha, Real.rpow_one]
      have hNa : (N : ℝ) * a ≤ 2 := (le_div_iff₀ ha).mp hN
      calc
        (N : ℝ) * ((Real.sqrt 2) ^ (q+1) * (a ^ q * a)) =
            ((Real.sqrt 2) ^ (q+1) * a ^ q) * ((N : ℝ) * a) := by ring
        _ ≤ ((Real.sqrt 2) ^ (q+1) * a ^ q) * 2 := mul_le_mul_of_nonneg_left hNa (by positivity)
        _ = _ := by ring
    have hc : 0 ≤ 2 * (Real.sqrt 2) ^ (q+1) := by positivity
    rw [← ENNReal.ofReal_natCast, ENNReal.ofReal_rpow_of_pos (mul_pos hsq ha),
      ← ENNReal.ofReal_mul (Nat.cast_nonneg N), ENNReal.ofReal_rpow_of_pos ha,
      ← ENNReal.ofReal_mul hc]
    exact ENNReal.ofReal_le_ofReal hreal
  have hgeo : ∀ (U : Set (YEuclid n)) (J : Set ℝ) (a : ℝ), 0 ≤ a → Metric.ediam U ≤ ENNReal.ofReal a → (∀ s ∈ J, ∀ t ∈ J, dist s t ≤ a) → Metric.ediam {z : YEuclid (n+1) | yHoriz z ∈ U ∧ yVert z ∈ J} ≤ ENNReal.ofReal (Real.sqrt 2 * a) := by
    intro U J a ha hd hJ
    apply Metric.ediam_le_of_forall_dist_le
    intro z hz w hw
    have hh : dist (yHoriz z) (yHoriz w) ≤ a := by
      exact (edist_le_ofReal ha).mp ((Metric.edist_le_ediam_of_mem hz.1 hw.1).trans hd)
    have hv : dist (yVert z) (yVert w) ≤ a := hJ _ hz.2 _ hw.2
    have heq : dist z w ^ 2 = dist (yHoriz z) (yHoriz w) ^ 2 + dist (yVert z) (yVert w) ^ 2 := by
      rw [PiLp.dist_sq_eq_of_L2, Fin.sum_univ_castSucc, PiLp.dist_sq_eq_of_L2]
      rfl
    have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hsq0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    have hh0 : 0 ≤ dist (yHoriz z) (yHoriz w) := dist_nonneg
    have hv0 : 0 ≤ dist (yVert z) (yVert w) := dist_nonneg
    have hd0 : 0 ≤ dist z w := dist_nonneg
    apply (sq_le_sq₀ hd0 (mul_nonneg hsq0 ha)).mp
    rw [mul_pow, hsq, heq]
    nlinarith [mul_self_le_mul_self hh0 hh, mul_self_le_mul_self hv0 hv]
  have hjoin : (∀ (x : YEuclid n) (t : ℝ), yHoriz (yJoin x t) = x ∧ yVert (yJoin x t) = t) ∧ (∀ z : YEuclid (n+1), yJoin (yHoriz z) (yVert z) = z) := by
    constructor
    · intro x t
      constructor
      · ext i
        simp [yHoriz, yJoin]
      · simp [yVert, yJoin]
    · intro z
      ext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [yJoin, yVert]
      · simp [yJoin, yHoriz]
  have himage : ∀ (U : Set (YEuclid n)) (J : Set ℝ), Set.image2 (@yJoin n) U J = {z : YEuclid (n+1) | yHoriz z ∈ U ∧ yVert z ∈ J} := by
    intro U J
    ext z
    constructor
    · rintro ⟨x, hx, t, ht, rfl⟩
      exact ⟨by simpa only [(hjoin.1 x t).1] using hx, by simpa only [(hjoin.1 x t).2] using ht⟩
    · intro hz
      exact ⟨yHoriz z, hz.1, yVert z, hz.2, hjoin.2 z⟩
  have hzero : ∀ (X : ℝ≥0∞) (C : ℝ), 0 < C → (∀ ε : ℝ, 0 < ε → X ≤ ENNReal.ofReal C * ENNReal.ofReal ε) → X = 0 := by
    intro X C hC h
    apply le_antisymm _ bot_le
    apply ENNReal.le_of_forall_pos_le_add
    intro η hη _
    have hηr : (0 : ℝ) < η := hη
    have he : 0 < (η : ℝ) / C := div_pos hηr hC
    have hb := h ((η : ℝ) / C) he
    rw [← ENNReal.ofReal_mul hC.le, mul_div_cancel₀ _ hC.ne'] at hb
    simpa using hb
  have hlimit : ∀ (Y D : ℝ≥0∞), D ≠ ⊤ → (∀ q : ℝ, 0 < q → D < ENNReal.ofReal q → Y ≤ ENNReal.ofReal (q+1)) → Y ≤ D+1 := by
    intro Y D hD h
    have heq : ENNReal.ofReal D.toReal = D := ENNReal.ofReal_toReal hD
    apply ENNReal.le_of_forall_pos_le_add
    intro η hη _
    have hηr : (0 : ℝ) < η := hη
    have hq : 0 < D.toReal + (η : ℝ) := add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg hηr
    have hlt : D < ENNReal.ofReal (D.toReal + (η : ℝ)) := by
      nth_rw 1 [← heq]
      apply (ENNReal.ofReal_lt_ofReal_iff hq).mpr
      linarith
    have hb := h (D.toReal + (η : ℝ)) hq hlt
    rw [ENNReal.ofReal_add (add_nonneg ENNReal.toReal_nonneg η.coe_nonneg) (by norm_num),
      ENNReal.ofReal_add ENNReal.toReal_nonneg η.coe_nonneg, heq,
      ENNReal.ofReal_one, ENNReal.ofReal_coe_nnreal] at hb
    simpa only [add_assoc, add_comm, add_left_comm] using hb
  have hbound : 1 ≤ n → ∀ q δ ε : ℝ, 0 < q → dimH E < ENNReal.ofReal q → 0 < δ → 0 < ε → yContent (q+1) δ (yProd E) ≤ ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q+1)) * ENNReal.ofReal ε := by
    intro hn q δ ε hq hD hδ hε
    have hsq : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    let r : ℝ := min 1 (δ / Real.sqrt 2)
    have hr : 0 < r := lt_min (by norm_num) (div_pos hδ hsq)
    have hr1 : r ≤ 1 := min_le_left _ _
    have hrδ : Real.sqrt 2 * r ≤ δ := by
      have h := min_le_right (1 : ℝ) (δ / Real.sqrt 2)
      have hh := (le_div_iff₀ hsq).mp h
      simpa only [mul_comm] using hh
    obtain ⟨U, hU, hpos, hcost⟩ := h_T007 hn q r ε hq hD hr hr1 hε
    have hfin : ∀ i, Metric.ediam (U i) ≠ ⊤ := fun i =>
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hU.2 i)
    let K := {i : ℕ // (U i).Nonempty}
    let a : K → ℝ := fun i => (Metric.ediam (U i)).toReal
    have ha : ∀ i, 0 < a i := fun i => ENNReal.toReal_pos (ne_of_gt (hpos i i.property)) (hfin i)
    have har : ∀ i, a i ≤ r := fun i => ENNReal.toReal_le_of_le_ofReal hr.le (hU.2 i)
    have ha1 : ∀ i, a i ≤ 1 := fun i => (har i).trans hr1
    have heq : ∀ i : K, ENNReal.ofReal (a i) = Metric.ediam (U i) := fun i =>
      ENNReal.ofReal_toReal (hfin i)
    choose N J hN hNa hJcov hJdiam using fun i : K => hinterval (a i) (ha i) (ha1 i)
    let V : (Σ i : K, Fin (N i)) → Set (YEuclid (n+1)) :=
      fun p => Set.image2 yJoin (U p.1) (J p.1 p.2)
    have hV : ∀ p, Metric.ediam (V p) ≤ ENNReal.ofReal (Real.sqrt 2 * a p.1) := by
      intro p
      simpa only [V, himage] using hgeo (U p.1) (J p.1 p.2) (a p.1) (ha p.1).le (heq p.1).ge (hJdiam p.1 p.2)
    have hVδ : ∀ p, Metric.ediam (V p) ≤ ENNReal.ofReal δ := by
      intro p
      exact (hV p).trans (ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_left (har p.1) hsq.le).trans hrδ))
    have hcov : yProd E ⊆ ⋃ p, V p := by
      intro z hz
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hU.1 hz.1)
      let k : K := ⟨i, ⟨yHoriz z, hi⟩⟩
      obtain ⟨j, hj⟩ := hJcov k (yVert z) hz.2
      apply Set.mem_iUnion.mpr
      refine ⟨⟨k,j⟩, ?_⟩
      change z ∈ Set.image2 yJoin (U k) (J k j)
      rw [himage]
      exact ⟨hi, hj⟩
    have hs : 0 < q+1 := by linarith
    calc
      yContent (q+1) δ (yProd E) ≤ ∑' p, Metric.ediam (V p) ^ (q+1) :=
        hcountable _ _ _ _ V hs hcov hVδ
      _ ≤ ∑' p : (Σ i : K, Fin (N i)), (ENNReal.ofReal (Real.sqrt 2 * a p.1)) ^ (q+1) :=
        ENNReal.tsum_le_tsum fun p => ENNReal.rpow_le_rpow (hV p) hs.le
      _ = ∑' i : K, (N i : ℝ≥0∞) * (ENNReal.ofReal (Real.sqrt 2 * a i)) ^ (q+1) := by
        rw [ENNReal.tsum_sigma' (fun p : (Σ i : K, Fin (N i)) => (ENNReal.ofReal (Real.sqrt 2 * a p.1)) ^ (q+1))]
        simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ ∑' i : K, ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q+1)) * (Metric.ediam (U i)) ^ q := by
        apply ENNReal.tsum_le_tsum
        intro i
        simpa only [heq i] using hcostlemma q (a i) (N i) hq (ha i) (hNa i)
      _ = ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q+1)) * ∑' i : K, (Metric.ediam (U i)) ^ q :=
        ENNReal.tsum_mul_left
      _ ≤ ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q+1)) * yCost q U := by
        apply mul_le_mul_left'
        exact ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective (fun i => Metric.ediam (U i) ^ q)
      _ ≤ ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q+1)) * ENNReal.ofReal ε :=
        mul_le_mul_left' hcost.le _
  intro hn
  apply hlimit (dimH (yProd E)) (dimH E) h_T002.1.ne
  intro q hq hD
  have hs : 0 < q+1 := by linarith
  have hhaus : yHaus (q+1) (yProd E) = 0 := by
    apply le_antisymm _ bot_le
    unfold yHaus
    apply iSup_le
    intro δ
    apply iSup_le
    intro hδ
    have hC : 0 < 2 * (Real.sqrt 2) ^ (q+1) := by
      apply mul_pos (by norm_num)
      exact Real.rpow_pos_of_pos (Real.sqrt_pos.mpr (by norm_num)) _
    have hz : yContent (q+1) δ (yProd E) = 0 :=
      hzero _ _ hC (fun ε hε => hbound hn q δ ε hq hD hδ hε)
    exact hz.le
  exact ((h_T001.1 (n+1)).2 (yProd E) (q+1) hs).2.2.2.1 hhaus

#check @T008
#print axioms T008

end Translation
