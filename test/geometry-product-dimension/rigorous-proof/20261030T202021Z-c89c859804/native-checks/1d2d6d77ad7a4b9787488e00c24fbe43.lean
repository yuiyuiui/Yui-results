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

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem checked (n : ℕ) (E : Set (GPEucl n)) (h_H001 : E.Nonempty) (h_T003 : ∀ (k : ℕ) (A : Set (GPEucl k)) (s : ℝ), 0 < s →
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
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ₀ ∧ ENNReal.ofReal L < GPcontent s δ A)) (h_T004 : Bornology.IsBounded E ∧
  (∃ R : ℝ, 0 < R ∧ ∀ x ∈ E, ∀ j : Fin n, -R ≤ x j ∧ x j ≤ R) ∧
  (∀ (s δ : ℝ), 0 < s → 0 < δ →
  ∃ T : Finset (GPEucl n),
    (E ⊆ ⋃ x ∈ T, Metric.ball x (δ / 2)) ∧
    (∀ x ∈ T, Metric.ediam (Metric.ball x (δ / 2)) ≤ ENNReal.ofReal δ) ∧
    (∑ x ∈ T, (Metric.ediam (Metric.ball x (δ / 2))) ^ s) < (⊤ : ENNReal)) ∧
  (∀ (s δ : ℝ), 0 < s → 0 < δ → GPcontent s δ E < ⊤)) : yui_aux_type% "∀ s : ℝ, (n : ℝ) < s → GPmass s E = 0" := by
  classical
  intro s hs
  have hspos : 0 < s := lt_of_le_of_lt (Nat.cast_nonneg n) hs
  have grid : ∀ (R m : ℝ), 0 < R → 1 ≤ m →
  let K := ⌈2 * R * m⌉₊
  let t : (Fin n → Fin K) → Set (GPEucl n) := fun f => {x | ∀ j, -R + (f j : ℝ) / m ≤ x j ∧ x j ≤ -R + ((f j : ℝ) + 1) / m}
  ((∀ x ∈ E, ∀ j, -R < x j ∧ x j < R) → E ⊆ ⋃ f, t f) ∧
  (∀ f, Metric.ediam (t f) ≤ ENNReal.ofReal (Real.sqrt (n : ℝ) / m)) ∧
  ((Fintype.card (Fin n → Fin K) : ℝ) ≤ (2 * R + 1)^n * m^n) := by
    classical
    intro R m hR hm
    dsimp only
    let K := ⌈2 * R * m⌉₊
    let t : (Fin n → Fin K) → Set (GPEucl n) := fun f => {x | ∀ j, -R + (f j : ℝ) / m ≤ x j ∧ x j ≤ -R + ((f j : ℝ) + 1) / m}
    change ((∀ x ∈ E, ∀ j, -R < x j ∧ x j < R) → E ⊆ ⋃ f, t f) ∧ _ ∧ _
    have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
    have hdiam : ∀ (h : ℝ), 0 ≤ h → ∀ (x y : GPEucl n), (∀ j, |x j - y j| ≤ h) → dist x y ≤ Real.sqrt (n : ℝ) * h := by
      intro h hh x y hxy
      rw [EuclideanSpace.dist_eq]
      calc
        Real.sqrt (∑ j : Fin n, dist (x j) (y j) ^ 2) ≤
            Real.sqrt (∑ j : Fin n, h ^ 2) := by
          apply Real.sqrt_le_sqrt
          exact Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (dist_nonneg) (by simpa [Real.dist_eq] using hxy j) 2
        _ = Real.sqrt (n : ℝ) * h := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq hh]
    refine ⟨?_, ?_, ?_⟩
    · intro hbox x hx
      let f : Fin n → Fin K := fun j => ⟨⌊(x j + R) * m⌋₊, by
        apply Nat.floor_lt_ceil_of_lt_of_pos
        · nlinarith [(hbox x hx j).2]
        · positivity⟩
      refine Set.mem_iUnion.mpr ⟨f, ?_⟩
      intro j
      have hfloor := Nat.floor_le (show 0 ≤ (x j + R) * m by nlinarith [(hbox x hx j).1])
      have hnext := (Nat.lt_floor_add_one ((x j + R) * m)).le
      constructor
      · change -R + (⌊(x j + R) * m⌋₊ : ℝ) / m ≤ x j
        have hd := (div_le_iff₀ hm0).mpr hfloor
        have heq : ((x j + R) * m) / m = x j + R := by field_simp
        linarith
      · change x j ≤ -R + ((⌊(x j + R) * m⌋₊ : ℝ) + 1) / m
        have hd := (le_div_iff₀ hm0).mpr hnext
        linarith
    · intro f
      apply Metric.ediam_le_of_forall_dist_le
      intro x hx y hy
      rw [div_eq_mul_inv]
      apply hdiam m⁻¹ (inv_nonneg.mpr hm0.le) x y
      intro j
      apply abs_le.mpr
      have hxj := hx j
      have hyj := hy j
      have heq : (-R + ((f j : ℝ) + 1) / m) - (-R + (f j : ℝ) / m) = m⁻¹ := by field_simp; ring
      constructor <;> linarith
    · have hk : (K : ℝ) ≤ (2 * R + 1) * m := by
        have hc := (Nat.ceil_lt_add_one (show 0 ≤ 2 * R * m by positivity)).le
        dsimp [K]
        nlinarith
      simpa [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, mul_pow] using
        (pow_le_pow_left₀ (Nat.cast_nonneg K) hk n)
  have sum_bound : ∀ (α : Type) [Fintype α] (U : α → Set (GPEucl n)) (d s : ℝ), 0 ≤ d → 0 ≤ s →
  (∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal d) →
  (∑ i, Metric.ediam (U i)^s) ≤ ENNReal.ofReal ((Fintype.card α : ℝ) * d^s) := by
    intro α _ U d s hd hs hU
    calc
      (∑ i, Metric.ediam (U i)^s) ≤ ∑ _ : α, (ENNReal.ofReal d)^s :=
        Finset.sum_le_sum fun i _ => ENNReal.rpow_le_rpow (hU i) hs
      _ = ENNReal.ofReal ((Fintype.card α : ℝ) * d^s) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rw [ENNReal.ofReal_rpow_of_nonneg hd hs, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  have algebra : ∀ (R m s : ℝ), 0 < m →
  (2 * R + 1)^n * m^n * (Real.sqrt (n : ℝ) / m)^s =
  ((2 * R + 1)^n * (Real.sqrt (n : ℝ))^s) * m^(-(s-(n : ℝ))) := by
    intro R m s hm
    rw [Real.div_rpow (Real.sqrt_nonneg _) hm.le, ← Real.rpow_natCast m n,
      show -(s - (n : ℝ)) = (n : ℝ) - s by ring, Real.rpow_sub hm]
    ring
  have limits : ∀ R s : ℝ, (n : ℝ) < s →
  Filter.Tendsto (fun m : ℝ => ENNReal.ofReal (((2*R+1)^n * (Real.sqrt (n : ℝ))^s) * m^(-(s-(n : ℝ))))) Filter.atTop (nhds 0) ∧
  Filter.Tendsto (fun m : ℝ => ENNReal.ofReal (Real.sqrt (n : ℝ) / m)) Filter.atTop (nhds 0) := by
    intro R s hs
    constructor
    · have hr : Filter.Tendsto (fun m : ℝ => ((2*R+1)^n * (Real.sqrt (n : ℝ))^s) * m^(-(s-(n : ℝ)))) Filter.atTop (nhds 0) := by
        simpa only [mul_zero] using (tendsto_rpow_neg_atTop (sub_pos.mpr hs)).const_mul ((2*R+1)^n * (Real.sqrt (n : ℝ))^s)
      simpa only [ENNReal.ofReal_zero, Function.comp_def] using (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hr
    · have hr : Filter.Tendsto (fun m : ℝ => Real.sqrt (n : ℝ) / m) Filter.atTop (nhds 0) :=
        Filter.Tendsto.div_atTop tendsto_const_nhds Filter.tendsto_id
      simpa only [ENNReal.ofReal_zero, Function.comp_def] using (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hr
  rcases h_T004.2.1 with ⟨R₀, hR₀, hbox₀⟩
  let R : ℝ := R₀ + 1
  have hR : 0 < R := by dsimp [R]; linarith
  have hbox : ∀ x ∈ E, ∀ j : Fin n, -R < x j ∧ x j < R := by
    intro x hx j
    rcases hbox₀ x hx j with ⟨ha, hb⟩
    dsimp [R]
    constructor <;> linarith
  let K : ℝ → ℕ := fun m => ⌈2 * R * m⌉₊
  let t : ∀ m : ℝ, (Fin n → Fin (K m)) → Set (GPEucl n) := fun m f =>
    {x | ∀ j, -R + (f j : ℝ) / m ≤ x j ∧ x j ≤ -R + ((f j : ℝ) + 1) / m}
  let B : ℝ → ENNReal := fun m =>
    ENNReal.ofReal (((2*R+1)^n * (Real.sqrt (n : ℝ))^s) * m^(-(s-(n : ℝ))))
  have hlim : Filter.Tendsto B Filter.atTop (nhds 0) := (limits R s hs).1
  have hr : Filter.Tendsto (fun m : ℝ => ENNReal.ofReal (Real.sqrt (n : ℝ) / m)) Filter.atTop (nhds 0) := (limits R s hs).2
  have hd : ∀ᶠ m : ℝ in Filter.atTop, ∀ f, Metric.ediam (t m f) ≤ ENNReal.ofReal (Real.sqrt (n : ℝ) / m) := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with m hm
    exact (grid R m hR hm).2.1
  have hc : ∀ᶠ m : ℝ in Filter.atTop, E ⊆ ⋃ f, t m f := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with m hm
    exact (grid R m hR hm).1 hbox
  have hcost : ∀ᶠ m : ℝ in Filter.atTop, (∑ f, Metric.ediam (t m f)^s) ≤ B m := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with m hm
    have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
    have hd0 : 0 ≤ Real.sqrt (n : ℝ) / m := div_nonneg (Real.sqrt_nonneg _) hm0.le
    calc
      (∑ f, Metric.ediam (t m f)^s) ≤
          ENNReal.ofReal ((Fintype.card (Fin n → Fin (K m)) : ℝ) * (Real.sqrt (n : ℝ) / m)^s) :=
        sum_bound _ (t m) _ _ hd0 hspos.le (grid R m hR hm).2.1
      _ ≤ ENNReal.ofReal ((2*R+1)^n * m^n * (Real.sqrt (n : ℝ) / m)^s) := by
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_right (grid R m hR hm).2.2 (Real.rpow_nonneg hd0 s)
      _ = B m := by rw [algebra R m s hm0]
  have hnative : MeasureTheory.Measure.hausdorffMeasure s E ≤
      Filter.liminf (fun m : ℝ => ∑ f, Metric.ediam (t m f)^s) Filter.atTop :=
    MeasureTheory.Measure.hausdorffMeasure_le_liminf_sum s E _ hr t hd hc
  have hlimle : Filter.liminf (fun m : ℝ => ∑ f, Metric.ediam (t m f)^s) Filter.atTop ≤
      Filter.liminf B Filter.atTop := Filter.liminf_le_liminf hcost
  have hzero : MeasureTheory.Measure.hausdorffMeasure s E = 0 :=
    le_antisymm (hnative.trans (hlimle.trans_eq hlim.liminf_eq)) bot_le
  exact (h_T003 n E s hspos).1.trans hzero
#check @checked
#print axioms checked
end YuiAuxiliary
