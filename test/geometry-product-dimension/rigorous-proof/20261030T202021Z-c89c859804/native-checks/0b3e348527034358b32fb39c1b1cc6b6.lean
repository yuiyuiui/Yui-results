import Mathlib
abbrev GPEucl (k : ℕ) := EuclideanSpace ℝ (Fin k)
def GPI : Set ℝ := Set.Icc 0 1
def GPappend {k : ℕ} (x : GPEucl k) (t : ℝ) : GPEucl (k + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x i) t)
def GPhead {k : ℕ} (z : GPEucl (k + 1)) : GPEucl k :=
  WithLp.toLp 2 (fun i : Fin k => z i.castSucc)
def GPproduct {k : ℕ} (A : Set (GPEucl k)) : Set (GPEucl (k + 1)) :=
  {z | GPhead z ∈ A ∧ z (Fin.last k) ∈ GPI}
def GPcover {X : Type*} [PseudoEMetricSpace X]
    (A : Set X) (δ : ℝ) (U : ℕ → Set X) : Prop :=
  A ⊆ ⋃ i, U i ∧ ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ
noncomputable def GPcost {X : Type*} [PseudoEMetricSpace X]
    (s : ℝ) (U : ℕ → Set X) : ENNReal :=
  ∑' i, (Metric.ediam (U i)) ^ s
noncomputable def GPcontent {X : Type*} [PseudoEMetricSpace X]
    (s δ : ℝ) (A : Set X) : ENNReal :=
  ⨅ (U : ℕ → Set X) (_ : GPcover A δ U), GPcost s U
noncomputable def GPmass {X : Type*} [PseudoEMetricSpace X]
    (s : ℝ) (A : Set X) : ENNReal :=
  ⨆ (δ : ℝ) (_ : 0 < δ), GPcontent s δ A

namespace Translation
set_option autoImplicit false

theorem T007 (n : ℕ) (E : Set (GPEucl n)) (h_T001 : (∀ (k : ℕ) (x : GPEucl k) (t : ℝ),
    GPhead (GPappend x t) = x ∧ (GPappend x t) (Fin.last k) = t) ∧
  (∀ (k : ℕ) (z : GPEucl (k + 1)), GPappend (GPhead z) (z (Fin.last k)) = z) ∧
  (∀ (k : ℕ) (x y : GPEucl k) (t u : ℝ),
    dist (GPappend x t) (GPappend y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ (k : ℕ) (z w : GPEucl (k + 1)),
    dist (GPhead z) (GPhead w) ≤ dist z w ∧
    |z (Fin.last k) - w (Fin.last k)| ≤ dist z w)) (h_T003 : ∀ (k : ℕ) (A : Set (GPEucl k)) (s : ℝ), 0 < s →
  GPmass s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
  0 ≤ dimH A ∧
  (dimH A < ENNReal.ofReal s → GPmass s A = 0) ∧
  (ENNReal.ofReal s < dimH A → GPmass s A = ⊤) ∧
  (GPmass s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
  (GPmass s A = ⊤ → ENNReal.ofReal s ≤ dimH A) ∧
  (∀ (δ₁ δ₂ : ℝ), 0 < δ₁ → 0 < δ₂ → δ₁ ≤ δ₂ →
    GPcontent s δ₂ A ≤ GPcontent s δ₁ A) ∧
  (GPmass s A = 0 → ∀ (δ ε : ℝ), 0 < δ → 0 < ε →
    ∃ U : ℕ → Set (GPEucl k), GPcover A δ U ∧ GPcost s U < ENNReal.ofReal ε) ∧
  (GPmass s A = ⊤ → ∀ (L δ₀ : ℝ), 0 < L → 0 < δ₀ →
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ₀ ∧ ENNReal.ofReal L < GPcontent s δ A)) (h_T005 : Bornology.IsBounded E ∧
  (∃ R : ℝ, 0 < R ∧ ∀ x ∈ E, ∀ j : Fin n, -R ≤ x j ∧ x j ≤ R) ∧
  (∀ (s δ : ℝ), 0 < s → 0 < δ →
  ∃ T : Finset (GPEucl n),
    (E ⊆ ⋃ x ∈ T, Metric.ball x (δ / 2)) ∧
    (∀ x ∈ T, Metric.ediam (Metric.ball x (δ / 2)) ≤ ENNReal.ofReal δ) ∧
    (∑ x ∈ T, (Metric.ediam (Metric.ball x (δ / 2))) ^ s) < (⊤ : ENNReal)) ∧
  (∀ (s δ : ℝ), 0 < s → 0 < δ → GPcontent s δ E < ⊤) ∧
  (0 ≤ dimH E ∧ dimH E ≤ (n : ENNReal) ∧ dimH E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ E.Subsingleton ∧ dimH E = 0)) :
    n = 0 →
  dimH (GPproduct E) ≤ dimH E + 1 ∧
  ∀ (q δ : ℝ), dimH E < ENNReal.ofReal q → 0 < δ →
    GPcontent (q + 1) δ (GPproduct E) = 0 ∧ GPmass (q + 1) (GPproduct E) = 0 := by
  classical
  have hcover : n = 0 → ∀ (N : ℕ) (a : ℝ), 0 < N → 0 < a →
      ∃ U : ℕ → Set (GPEucl (n + 1)),
        GPcover (GPproduct E) (1 / (N : ℝ)) U ∧
        GPcost a U ≤ ENNReal.ofReal ((N : ℝ) ^ (1 - a)) := by
    classical
    intro hn
    subst n
    have hpart : ∀ (N : ℕ), 0 < N → ∀ t ∈ GPI,
        ∃ i : ℕ, i < N ∧ t ∈ Set.Icc ((i : ℝ) / N) (((i : ℝ) + 1) / N) := by
      intro N hN t ht
      have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
      rcases ht with ⟨ht0, ht1⟩
      by_cases he : t = 1
      · subst t
        refine ⟨N - 1, by omega, ?_, ?_⟩
        · apply (div_le_iff₀ hNr).2
          have : ((N - 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.sub_le N 1
          simpa using this
        · apply (le_div_iff₀ hNr).2
          have : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by
            norm_cast
            omega
          linarith
      · have htlt : t < 1 := lt_of_le_of_ne ht1 he
        refine ⟨⌊t * N⌋₊, (Nat.floor_lt (mul_nonneg ht0 hNr.le)).2 ?_, ?_, ?_⟩
        · nlinarith
        · exact (div_le_iff₀ hNr).2 (Nat.floor_le (mul_nonneg ht0 hNr.le))
        · exact (le_div_iff₀ hNr).2 (Nat.lt_floor_add_one (t * N)).le
    have hcost : ∀ (N : ℕ) (a : ℝ), 0 < N → 0 < a →
        (N : ENNReal) * (ENNReal.ofReal (1 / (N : ℝ))) ^ a =
          ENNReal.ofReal ((N : ℝ) ^ (1 - a)) := by
      intro N a hN ha
      have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
      rw [ENNReal.ofReal_rpow_of_pos (one_div_pos.mpr hNr)]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hNr.le]
      congr 1
      rw [sub_eq_add_neg, Real.rpow_add hNr, Real.rpow_one,
        Real.rpow_neg_eq_inv_rpow, one_div]
    intro N a hN ha
    have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    let f : ℝ → GPEucl 1 := fun t => GPappend (0 : GPEucl 0) t
    have hf : ∀ t u : ℝ, dist (f t) (f u) = |t - u| := by
      intro t u
      dsimp [f]
      rw [h_T001.2.2.1, dist_self, zero_pow (by decide : 2 ≠ 0), zero_add,
        Real.sqrt_sq (abs_nonneg _)]
    let U : ℕ → Set (GPEucl 1) := fun i =>
      if i < N then f '' Set.Icc ((i : ℝ) / N) (((i : ℝ) + 1) / N) else ∅
    have hd : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal (1 / (N : ℝ)) := by
      intro i
      by_cases hi : i < N
      · dsimp [U]
        rw [if_pos hi]
        apply Metric.ediam_image_le_iff.mpr
        intro t ht u hu
        rw [edist_dist, hf]
        apply ENNReal.ofReal_le_ofReal
        apply abs_le.mpr
        simp only [Set.mem_Icc, add_div] at ht hu
        constructor
        · linarith [ht.1, hu.2]
        · linarith [hu.1, ht.2]
      · simp [U, hi]
    refine ⟨U, ⟨?_, hd⟩, ?_⟩
    · intro z hz
      obtain ⟨i, hi, hit⟩ := hpart N hN (z (Fin.last 0)) hz.2
      apply Set.mem_iUnion.mpr
      refine ⟨i, ?_⟩
      dsimp [U]
      rw [if_pos hi]
      refine ⟨z (Fin.last 0), hit, ?_⟩
      have hhead : GPhead z = (0 : GPEucl 0) := Subsingleton.elim _ _
      simpa only [f, ← hhead] using h_T001.2.1 0 z
    · calc
        GPcost a U = ∑ i ∈ Finset.range N, (Metric.ediam (U i)) ^ a := by
          apply tsum_eq_sum
          intro i hi
          have : ¬ i < N := by simpa using hi
          simp [U, this, ENNReal.zero_rpow_of_pos ha]
        _ ≤ ∑ i ∈ Finset.range N, (ENNReal.ofReal (1 / (N : ℝ))) ^ a := by
          exact Finset.sum_le_sum fun i _ => ENNReal.rpow_le_rpow (hd i) ha.le
        _ = (N : ENNReal) * (ENNReal.ofReal (1 / (N : ℝ))) ^ a := by simp
        _ = ENNReal.ofReal ((N : ℝ) ^ (1 - a)) := hcost N a hN ha
  have hlimit : ∀ a : ℝ, 1 < a → ∀ δ ε : ℝ, 0 < δ → 0 < ε →
      ∃ N : ℕ, 0 < N ∧ 1 / (N : ℝ) ≤ δ ∧ (N : ℝ) ^ (1 - a) < ε := by
    intro a ha δ ε hδ hε
    have ht : Filter.Tendsto (fun x : ℝ => x ^ (1 - a)) Filter.atTop (nhds 0) := by
      have h := tendsto_rpow_neg_atTop (show 0 < a - 1 by linarith)
      simpa only [neg_sub] using h
    obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp ((tendsto_order.mp ht).2 ε hε)
    obtain ⟨N, hN⟩ := exists_nat_gt (max T (max 0 (1 / δ)))
    have hNT : T ≤ (N : ℝ) := (le_max_left _ _).trans hN.le
    have hNpos : (0 : ℝ) < N := (le_trans (le_max_left _ _) (le_max_right _ _)).trans_lt hN
    have hNδ : 1 / δ < (N : ℝ) :=
      (le_trans (le_max_right _ _) (le_max_right _ _)).trans_lt hN
    refine ⟨N, Nat.cast_pos.mp hNpos, ?_, hT N hNT⟩
    apply (div_le_iff₀ hNpos).2
    have := (div_lt_iff₀ hδ).mp hNδ
    nlinarith
  intro hn
  obtain ⟨hE, hEss, hD⟩ := h_T005.2.2.2.2.2 hn
  have hcontent : ∀ a : ℝ, 1 < a → ∀ δ : ℝ, 0 < δ →
      GPcontent a δ (GPproduct E) = 0 := by
    intro a ha δ hδ
    apply le_antisymm _ zero_le
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    simp only [zero_add]
    have hεr : (0 : ℝ) < ε := by exact_mod_cast hε
    obtain ⟨N, hN, hNδ, hNa⟩ := hlimit a ha δ (ε : ℝ) hδ hεr
    obtain ⟨U, hU, hc⟩ := hcover hn N a hN (by linarith)
    have hUδ : GPcover (GPproduct E) δ U :=
      ⟨hU.1, fun i => (hU.2 i).trans (ENNReal.ofReal_le_ofReal hNδ)⟩
    have hi : GPcontent a δ (GPproduct E) ≤ GPcost a U :=
      iInf_le_of_le U (iInf_le_of_le hUδ le_rfl)
    apply (hi.trans hc).trans
    simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hNa.le
  have hmass : ∀ a : ℝ, 1 < a → GPmass a (GPproduct E) = 0 := by
    intro a ha
    apply le_antisymm _ zero_le
    change (⨆ (δ : ℝ) (_ : 0 < δ), GPcontent a δ (GPproduct E)) ≤ 0
    exact iSup_le fun δ => iSup_le fun hδ => (hcontent a ha δ hδ).le
  constructor
  · rw [hD, zero_add]
    by_contra hnot
    have hlt : (1 : ENNReal) < dimH (GPproduct E) := lt_of_not_ge hnot
    obtain ⟨a, ha0, h1a, haD⟩ := ENNReal.lt_iff_exists_real_btwn.mp hlt
    have ha : 1 < a := by
      have : ENNReal.ofReal (1 : ℝ) < ENNReal.ofReal a := by simpa using h1a
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num)).mp this
    have hb : dimH (GPproduct E) ≤ ENNReal.ofReal a :=
      (h_T003 (n + 1) (GPproduct E) a (by linarith)).2.2.2.2.1 (hmass a ha)
    exact (not_lt_of_ge hb) haD
  · intro q δ hq hδ
    have hqpos : 0 < q := by
      apply ENNReal.ofReal_pos.mp
      simpa only [hD] using hq
    exact ⟨hcontent (q + 1) (by linarith) δ hδ, hmass (q + 1) (by linarith)⟩

#check @T007
#print axioms T007

end Translation
