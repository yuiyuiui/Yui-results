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

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem checked (n : ℕ) (E : Set (GP.Space n)) (h_T001 : (∀ (m : ℕ) (A : Set (GP.Space m)), 0 ≤ dimH A ∧
  ∀ (s : ℝ), 0 < s →
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (dimH A < ENNReal.ofReal s → GP.hausdorff s A = 0) ∧
    (ENNReal.ofReal s < dimH A → GP.hausdorff s A = ⊤) ∧
    (GP.hausdorff s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GP.hausdorff s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) ∧ (∀ (A : Set ℝ) (s : ℝ), 0 < s →
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A)) (h_T002 : dimH E < ⊤ ∧ 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧
  (n = 0 → E = Set.univ ∧ (∃ x : GP.Space n, E = {x}) ∧ dimH E = 0) ∧
  ∀ (s δ : ℝ), 0 < s → 0 < δ → GP.content s δ E < ⊤) : yui_aux_type% "∀ {ι : Type} [Encodable ι] (q δ ε r : ℝ)\n    (U : ι → Set (GP.Space n)) (d : ι → ℝ),\n    0 < q → r ≤ 1 → Real.sqrt 2 * r ≤ δ →\n    E ⊆ ⋃ i, U i →\n    (∀ i, 0 < d i ∧ d i ≤ r ∧ Metric.ediam (U i) = ENNReal.ofReal (d i)) →\n    (∑' i, ENNReal.ofReal ((d i)^q)) ≤ ENNReal.ofReal ε →\n    GP.content (q+1) δ (GP.cylinder E) ≤\n      ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q+1) * ε)" := by
  classical
  have mesh : ∀ (r : ℝ), 0 < r → r ≤ 1 →
    ∃ (N : ℕ) (J : Fin N → Set ℝ), 0 < N ∧
      (↑N : ℝ) ≤ 2 / r ∧
      GP.unitInterval ⊆ ⋃ j, J j ∧
      (∀ j, Metric.ediam (J j) ≤ ENNReal.ofReal r) := by
    intro r hr hr1
    let N : ℕ := ⌈1 / r⌉₊
    have hN : 0 < N := Nat.ceil_pos.mpr (one_div_pos.mpr hr)
    have hNr : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
    have hceil : 1 / r ≤ (N : ℝ) := Nat.le_ceil _
    have hsize : (N : ℝ) ≤ 2 / r := by
      have h := (Nat.ceil_lt_add_one (le_of_lt (one_div_pos.mpr hr))).le
      have h1 : 1 ≤ 1 / r := (le_div_iff₀ hr).mpr (by simpa using hr1)
      dsimp [N]
      calc _ ≤ 1 / r + 1 := h
           _ ≤ 1 / r + 1 / r := add_le_add_right h1 _
           _ = 2 / r := by ring
    have hinv : 1 / (N : ℝ) ≤ r := by
      apply (div_le_iff₀ hNr).mpr
      have h := (div_le_iff₀ hr).mp hceil
      nlinarith
    let J : Fin N → Set ℝ := fun j => Set.Icc ((j : ℝ) / N) (((j : ℝ) + 1) / N)
    refine ⟨N, J, hN, hsize, ?_, ?_⟩
    · have cov : ∀ k : ℕ, k ≤ N → ∀ t : ℝ, 0 ≤ t → t ≤ (k : ℝ) / N →
          ∃ j : Fin N, t ∈ J j := by
        intro k
        induction k with
        | zero =>
          intro _ t ht ht'
          have ht0 : t ≤ 0 := by simpa using ht'
          have ht0 : t = 0 := le_antisymm ht0 ht
          subst t
          refine ⟨⟨0, hN⟩, ?_⟩
          simp [J, le_of_lt (one_div_pos.mpr hNr)]
        | succ k ih =>
          intro hk t ht ht'
          by_cases htk : t ≤ (k : ℝ) / N
          · exact ih (by omega) t ht htk
          · refine ⟨⟨k, by omega⟩, ?_, ?_⟩
            · exact (lt_of_not_ge htk).le
            · simpa [Nat.cast_add, Nat.cast_one] using ht'
      intro t ht
      obtain ⟨j, hj⟩ := cov N le_rfl t ht.1 (by simpa [ne_of_gt hNr] using ht.2)
      exact Set.mem_iUnion.mpr ⟨j, hj⟩
    · intro j
      dsimp [J]
      rw [Real.ediam_Icc]
      apply ENNReal.ofReal_le_ofReal
      calc ((j : ℝ) + 1) / N - (j : ℝ) / N = 1 / N := by ring
           _ ≤ r := hinv
  have productDiam : ∀ (U : Set (GP.Space n)) (J : Set ℝ) (r : ℝ), 0 ≤ r →
    Metric.ediam U ≤ ENNReal.ofReal r → Metric.ediam J ≤ ENNReal.ofReal r →
    Metric.ediam {z : GP.Space (n+1) | GP.horizontal z ∈ U ∧ GP.vertical z ∈ J}
      ≤ ENNReal.ofReal (Real.sqrt 2 * r) := by
    intro U J r hr hU hJ
    apply Metric.ediam_le
    intro z hz w hw
    rw [edist_dist]
    apply ENNReal.ofReal_le_ofReal
    have hdU : dist (GP.horizontal z) (GP.horizontal w) ≤ r := by
      have h := Metric.edist_le_of_ediam_le hz.1 hw.1 hU
      rwa [edist_dist, ENNReal.ofReal_le_ofReal_iff hr] at h
    have hdJ : dist (GP.vertical z) (GP.vertical w) ≤ r := by
      have h := Metric.edist_le_of_ediam_le hz.2 hw.2 hJ
      rwa [edist_dist, ENNReal.ofReal_le_ofReal_iff hr] at h
    have hsq : dist z w ^ 2 =
        dist (GP.horizontal z) (GP.horizontal w) ^ 2 +
          dist (GP.vertical z) (GP.vertical w) ^ 2 := by
      simp only [EuclideanSpace.dist_sq_eq, Fin.sum_univ_castSucc,
        GP.horizontal, GP.vertical, PiLp.toLp_apply]
    have hsqrt : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hnon : 0 ≤ Real.sqrt 2 * r := mul_nonneg (Real.sqrt_nonneg _) hr
    have hU2 : dist (GP.horizontal z) (GP.horizontal w) ^ 2 ≤ r ^ 2 := by
      nlinarith [dist_nonneg (x := GP.horizontal z) (y := GP.horizontal w)]
    have hJ2 : dist (GP.vertical z) (GP.vertical w) ^ 2 ≤ r ^ 2 := by
      nlinarith [dist_nonneg (x := GP.vertical z) (y := GP.vertical w)]
    have h2 : dist z w ^ 2 ≤ (Real.sqrt 2 * r) ^ 2 := by
      rw [mul_pow, hsqrt]
      linarith
    nlinarith [dist_nonneg (x := z) (y := w)]
  have compress : ∀ {X : Type} [MetricSpace X] {ι : Type} [Encodable ι]
      (s δ : ℝ) (A : Set X) (V : ι → Set X),
      A ⊆ ⋃ i, V i → (∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ) →
      GP.content s δ A ≤ ∑' i, (Metric.ediam (V i)) ^ s := by
    intro X _ ι _ s δ A V hcov hdiam
    classical
    let U : ℕ → Set X := fun j => ⋃ b ∈ Encodable.decode₂ ι j, V b
    have hU : GP.Cover A δ U := by
      constructor
      · simpa only [U, Encodable.iUnion_decode₂] using hcov
      · intro j
        dsimp [U]
        rw [Metric.ediam_iUnion_mem_option]
        exact iSup_le fun b => iSup_le fun _ => hdiam b
    calc
      GP.content s δ A ≤ GP.cost s U := iInf_le_of_le U (iInf_le _ hU)
      _ = ∑' i, ⨆ (_ : (V i).Nonempty), Metric.ediam (V i) ^ s := by
        exact tsum_iUnion_decode₂ (fun t : Set X => ⨆ (_ : t.Nonempty), Metric.ediam t ^ s)
          (by simp) V
      _ ≤ ∑' i, Metric.ediam (V i) ^ s := ENNReal.tsum_le_tsum (fun i => iSup_le fun _ => le_rfl)
  have numerical : ∀ (q r : ℝ) (N : ℕ), 0 < r → (N : ℝ) ≤ 2 / r →
    (N : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt 2 * r) ^ (q+1) ≤
      ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q+1)) * ENNReal.ofReal (r^q) := by
    intro q r N hr hN
    have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hNr : (N : ℝ) * r ≤ 2 := (le_div_iff₀ hr).mp hN
    have heq : (Real.sqrt 2 * r) ^ (q+1) = (Real.sqrt 2) ^ (q+1) * r^q * r := by
      rw [Real.mul_rpow hs.le hr.le, Real.rpow_add hr, Real.rpow_one]
      ring
    have hreal : (N : ℝ) * (Real.sqrt 2 * r) ^ (q+1) ≤
        (2 * (Real.sqrt 2) ^ (q+1)) * r^q := by
      rw [heq]
      calc (N : ℝ) * ((Real.sqrt 2)^(q+1) * r^q * r) =
          ((N : ℝ)*r) * ((Real.sqrt 2)^(q+1) * r^q) := by ring
           _ ≤ 2 * ((Real.sqrt 2)^(q+1) * r^q) :=
             mul_le_mul_of_nonneg_right hNr (by positivity)
           _ = _ := by ring
    have hcast : (N : ℝ≥0∞) = ENNReal.ofReal (N : ℝ) := by simp
    rw [hcast, ENNReal.ofReal_rpow_of_pos (mul_pos hs hr),
      ← ENNReal.ofReal_mul (Nat.cast_nonneg N),
      ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hreal
  intro ι _ q δ ε r U d hq hr1 hrδ hcov hd hsum
  choose N J hN hsize hJcov hJdiam using
    fun i => mesh (d i) (hd i).1 ((hd i).2.1.trans hr1)
  let V : (Σ i, Fin (N i)) → Set (GP.Space (n+1)) := fun p =>
    {z | GP.horizontal z ∈ U p.1 ∧ GP.vertical z ∈ J p.1 p.2}
  have hVdiam : ∀ p, Metric.ediam (V p) ≤ ENNReal.ofReal (Real.sqrt 2 * d p.1) := by
    intro p
    exact productDiam (U p.1) (J p.1 p.2) (d p.1) (hd p.1).1.le
      (hd p.1).2.2.le (hJdiam p.1 p.2)
  have hVcov : GP.cylinder E ⊆ ⋃ p, V p := by
    intro z hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hz.1)
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hJcov i hz.2)
    exact Set.mem_iUnion.mpr ⟨⟨i,j⟩, hi, hj⟩
  calc
    GP.content (q+1) δ (GP.cylinder E) ≤
        ∑' p, Metric.ediam (V p) ^ (q+1) :=
      compress (q+1) δ (GP.cylinder E) V hVcov (fun p =>
        (hVdiam p).trans (ENNReal.ofReal_le_ofReal
          ((mul_le_mul_of_nonneg_left (hd p.1).2.1 (Real.sqrt_nonneg _)).trans hrδ)))
    _ ≤ ∑' p : Σ i, Fin (N i), ENNReal.ofReal (Real.sqrt 2 * d p.1) ^ (q+1) :=
      ENNReal.tsum_le_tsum (fun p => ENNReal.rpow_le_rpow (hVdiam p) (by linarith))
    _ = ∑' i, (N i : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt 2 * d i) ^ (q+1) := by
      rw [ENNReal.tsum_sigma' (fun p : Σ i, Fin (N i) =>
        ENNReal.ofReal (Real.sqrt 2 * d p.1) ^ (q+1))]
      simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ ∑' i, ENNReal.ofReal (2 * (Real.sqrt 2)^(q+1)) * ENNReal.ofReal ((d i)^q) :=
      ENNReal.tsum_le_tsum (fun i => numerical q (d i) (N i) (hd i).1 (hsize i))
    _ = ENNReal.ofReal (2 * (Real.sqrt 2)^(q+1)) * ∑' i, ENNReal.ofReal ((d i)^q) :=
      ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (2 * (Real.sqrt 2)^(q+1)) * ENNReal.ofReal ε :=
      mul_le_mul_left' hsum _
    _ = ENNReal.ofReal (2 * (Real.sqrt 2)^(q+1) * ε) :=
      (ENNReal.ofReal_mul (by positivity)).symm
#check @checked
#print axioms checked
end YuiAuxiliary
