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

theorem T005 (n : ℕ) (E : Set (GP.Space n)) (h_T001 : (∀ (m : ℕ) (A : Set (GP.Space m)), 0 ≤ dimH A ∧
  ∀ (s : ℝ), 0 < s →
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (dimH A < ENNReal.ofReal s → GP.hausdorff s A = 0) ∧
    (ENNReal.ofReal s < dimH A → GP.hausdorff s A = ⊤) ∧
    (GP.hausdorff s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GP.hausdorff s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) ∧ (∀ (A : Set ℝ) (s : ℝ), 0 < s →
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A)) (h_T002 : dimH E < ⊤ ∧ 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧
  (n = 0 → E = Set.univ ∧ (∃ x : GP.Space n, E = {x}) ∧ dimH E = 0) ∧
  ∀ (s δ : ℝ), 0 < s → 0 < δ → GP.content s δ E < ⊤) :
    1 ≤ n → ∀ (q : ℝ), dimH E < ENNReal.ofReal q →
  ∀ (δ ε : ℝ), 0 < δ → 0 < ε →
    GP.content (q + 1) δ (GP.cylinder E) ≤
      ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q + 1) * ε) := by
  classical
  have initial : ∀ (q δ ε : ℝ), dimH E < ENNReal.ofReal q → 0 < δ → 0 < ε →
    ∃ (r : ℝ) (W : ℕ → Set (GP.Space n)),
      0 < q ∧ 0 < r ∧ r ≤ 1 ∧ Real.sqrt 2 * r ≤ δ ∧
        GP.Cover E r W ∧ GP.cost q W < ENNReal.ofReal (ε/2) := by
    intro q δ ε hdim hδ hε
    have hq : 0 < q := ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hdim)
    have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    let r : ℝ := min 1 (δ / Real.sqrt 2)
    have hr : 0 < r := lt_min zero_lt_one (div_pos hδ hs)
    have hr1 : r ≤ 1 := min_le_left _ _
    have hrδ : Real.sqrt 2 * r ≤ δ := by
      have h := (le_div_iff₀ hs).mp (min_le_right 1 (δ / Real.sqrt 2))
      simpa only [mul_comm] using h
    have hH : GP.hausdorff q E = 0 := (h_T001.1 n E).2 q hq |>.2.1 hdim
    have hzero : GP.content q r E = 0 := by
      apply le_antisymm _ bot_le
      calc GP.content q r E ≤ GP.hausdorff q E :=
             le_iSup_of_le r (le_iSup_of_le hr le_rfl)
           _ = 0 := hH
    have hex : GP.content q r E < ENNReal.ofReal (ε/2) := by
      rw [hzero]
      exact ENNReal.ofReal_pos.mpr (half_pos hε)
    simp only [GP.content, iInf_lt_iff, exists_prop] at hex
    obtain ⟨W, hW, hc⟩ := hex
    exact ⟨r, W, hq, hr, hr1, hrδ, hW, hc⟩
  have regular : 1 ≤ n → ∀ (q r ε : ℝ) (W : ℕ → Set (GP.Space n)),
    0 < q → 0 < r → 0 < ε → GP.Cover E r W →
    GP.cost q W < ENNReal.ofReal (ε/2) →
    ∃ (U : {i : ℕ // (W i).Nonempty} → Set (GP.Space n))
      (d : {i : ℕ // (W i).Nonempty} → ℝ),
      (E ⊆ ⋃ i, U i) ∧
      (∀ i, 0 < d i ∧ d i ≤ r ∧ Metric.ediam (U i) = ENNReal.ofReal (d i)) ∧
      (∑' i, ENNReal.ofReal ((d i)^q)) < ENNReal.ofReal ε := by
    classical
    have betas : ∀ (q r ε : ℝ), 0 < q → 0 < r → 0 < ε →
      ∃ b : ℕ → ℝ, (∀ i, 0 < b i ∧ b i ≤ r ∧ (b i) ^ q ≤ ε / 8 * ((1:ℝ)/2)^i) ∧
        (∑' i, ENNReal.ofReal (ε / 8 * ((1:ℝ)/2)^i)) = ENNReal.ofReal (ε / 4) := by
      intro q r ε hq hr hε
      let a : ℕ → ℝ := fun i => ε / 8 * ((1:ℝ)/2)^i
      let b : ℕ → ℝ := fun i => min (r/2) ((a i) ^ q⁻¹)
      have ha : ∀ i, 0 < a i := fun i => by dsimp [a]; positivity
      refine ⟨b, ?_, ?_⟩
      · intro i
        have hb : 0 < b i := lt_min (half_pos hr) (Real.rpow_pos_of_pos (ha i) _)
        refine ⟨hb, (min_le_left _ _).trans (by linarith), ?_⟩
        calc (b i) ^ q ≤ ((a i) ^ q⁻¹) ^ q :=
              Real.rpow_le_rpow hb.le (min_le_right _ _) hq.le
             _ = a i := Real.rpow_inv_rpow (ha i).le hq.ne'
      · rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => (ha i).le)
          (summable_geometric_two.mul_left (ε/8)), tsum_mul_left, tsum_geometric_two]
        congr 1
        ring
    intro hn q r ε W hq hr hε hW hcost
    letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    haveI : Nontrivial (GP.Space n) := inferInstance
    obtain ⟨b, hb, hsum⟩ := betas q r ε hq hr hε
    let K := {i : ℕ // (W i).Nonempty}
    let x : K → GP.Space n := fun i => i.property.choose
    let U : K → Set (GP.Space n) := fun i =>
      if Metric.ediam (W i) = 0 then Metric.ball (x i) (b i / 2) else W i
    let d : K → ℝ := fun i =>
      if Metric.ediam (W i) = 0 then b i else Metric.diam (W i)
    have hd : ∀ i, 0 < d i ∧ d i ≤ r ∧ Metric.ediam (U i) = ENNReal.ofReal (d i) := by
      intro i
      have ht : Metric.ediam (W i) ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hW.2 i)
      dsimp [U, d]
      split_ifs with hi
      · refine ⟨(hb i).1, (hb i).2.1, ?_⟩
        have heq : Metric.diam (Metric.ball (x i) (b i / 2)) = b i := by
          rw [Metric.diam_ball_eq _ (by linarith [(hb i).1])]
          ring
        exact (ENNReal.ofReal_toReal (Metric.isBounded_ball (x := x i) (r := b i / 2)).ediam_ne_top).symm.trans
          (congrArg ENNReal.ofReal heq)
      · exact ⟨ENNReal.toReal_pos hi ht,
          ENNReal.toReal_le_of_le_ofReal hr.le (hW.2 i), (ENNReal.ofReal_toReal ht).symm⟩
    have hsub : ∀ i : K, W i ⊆ U i := by
      intro i y hy
      dsimp [U]
      split_ifs with hi
      · have hxy : y = x i := (Metric.ediam_eq_zero_iff.mp hi) hy i.property.choose_spec
        rw [hxy]
        exact Metric.mem_ball_self (half_pos (hb i).1)
      · exact hy
    refine ⟨U, d, ?_, hd, ?_⟩
    · intro y hy
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hW.1 hy)
      exact Set.mem_iUnion.mpr ⟨⟨i, y, hi⟩, hsub ⟨i, y, hi⟩ hi⟩
    · have hpoint : ∀ i : K, ENNReal.ofReal ((d i)^q) ≤
          (⨆ (_ : (W i).Nonempty), Metric.ediam (W i)^q) +
            ENNReal.ofReal (ε/8 * ((1:ℝ)/2)^(i:ℕ)) := by
        intro i
        dsimp [d]
        split_ifs with hi
        · exact (ENNReal.ofReal_le_ofReal (hb i).2.2).trans (le_add_left le_rfl)
        · have heq : ENNReal.ofReal (Metric.diam (W i)^q) = Metric.ediam (W i)^q := by
            rw [← ENNReal.ofReal_rpow_of_nonneg Metric.diam_nonneg hq.le]
            congr 1
            exact ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hW.2 i))
          rw [heq]
          exact le_add_of_le_left (le_iSup_of_le i.property le_rfl)
      calc
        (∑' i, ENNReal.ofReal ((d i)^q)) ≤
            ∑' i : K, ((⨆ (_ : (W i).Nonempty), Metric.ediam (W i)^q) +
              ENNReal.ofReal (ε/8 * ((1:ℝ)/2)^(i:ℕ))) := ENNReal.tsum_le_tsum hpoint
        _ ≤ GP.cost q W + ENNReal.ofReal (ε/4) := by
          rw [ENNReal.tsum_add]
          exact add_le_add
            (ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
              (fun i => ⨆ (_ : (W i).Nonempty), Metric.ediam (W i)^q))
            ((ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
              (fun i => ENNReal.ofReal (ε/8 * ((1:ℝ)/2)^i))).trans_eq hsum)
        _ ≤ ENNReal.ofReal (ε/2) + ENNReal.ofReal (ε/4) := add_le_add hcost.le le_rfl
        _ = ENNReal.ofReal (ε/2+ε/4) := (ENNReal.ofReal_add (by positivity) (by positivity)).symm
        _ < ENNReal.ofReal ε := (ENNReal.ofReal_lt_ofReal_iff hε).mpr (by linarith)
  have productCover : ∀ {ι : Type} [Encodable ι] (q δ ε r : ℝ)
      (U : ι → Set (GP.Space n)) (d : ι → ℝ),
      0 < q → r ≤ 1 → Real.sqrt 2 * r ≤ δ →
      E ⊆ ⋃ i, U i →
      (∀ i, 0 < d i ∧ d i ≤ r ∧ Metric.ediam (U i) = ENNReal.ofReal (d i)) →
      (∑' i, ENNReal.ofReal ((d i)^q)) ≤ ENNReal.ofReal ε →
      GP.content (q+1) δ (GP.cylinder E) ≤
        ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q+1) * ε) := by
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
  intro hn q hdim δ ε hδ hε
  obtain ⟨r, W, hq, hr, hr1, hrδ, hW, hc⟩ := initial q δ ε hdim hδ hε
  obtain ⟨U, d, hcov, hd, hsum⟩ := regular hn q r ε W hq hr hε hW hc
  exact productCover q δ ε r U d hq hr1 hrδ hcov hd hsum.le

#check @T005
#print axioms T005

end Translation
