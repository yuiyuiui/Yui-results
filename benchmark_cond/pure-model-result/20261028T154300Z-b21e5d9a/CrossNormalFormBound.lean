import ResidualIdentity
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

theorem inclusionMap_val (s r : ℝ) (h : s ≤ r) (f : Sobolev r) :
    (inclusionMap s r h f).val = f.val := rfl

theorem frozenZ_regular {a b : ℝ} (f : Sobolev 2) (hfm : MeanZero f.val) :
    RegularFourierPath a b (fun t => frozenZ a t f.val) (fun t => (1 / 2 : ℂ) • B t f.val f.val) := by
  have hdC : Continuous (fun t : ℝ => (1 / 2 : ℂ) • BTwoBundled t f f) :=
    (continuous_const (y := (1 / 2 : ℂ))).smul
      (continuous_BTwoBundled continuous_id continuous_const continuous_const)
  apply regularFourierPath_of_bundled (continuous_frozenZBundled a f) hdC
  intro t _ k
  have h := (hasDerivAt_const t (f.val k)).add (stage_hasDerivAt
    (f.property.of_le (by norm_num)) (f.property.of_le (by norm_num)) hfm hfm a t k)
  simpa only [zero_add] using! h

/-- Internal cross normal-form bound. The trilinear term is explicit; its
bound is supplied separately by the cited dynamic theorem with proved paths. -/
theorem integral_B_cross_bound {a b A Ad M E : ℝ} (hab : a ≤ b)
    (hA : 0 ≤ A) (hAd : 0 ≤ Ad) (_hM : 0 ≤ M)
    (f : Sobolev 2) (hfm : MeanZero f.val)
    (Y dY : ℝ → Sobolev 1) (hYC : Continuous Y) (hdYC : Continuous dY)
    (hd : ∀ t ∈ Set.Ioo a b, ∀ k : ℤ,
      HasDerivAt (fun r : ℝ => (Y r).val k) ((dY t).val k) t)
    (hm : ∀ t ∈ Set.Icc a b, MeanZero (Y t).val) (hleft : (Y a).val = 0)
    (hZ : ∀ t ∈ Set.Icc a b, hNorm 0 (frozenZ a t f.val) ≤ M)
    (hIb : hNorm 0 (inverseDerivative (Y b).val) ≤ A)
    (hId : ∀ t ∈ Set.Icc a b, hNorm 0 (inverseDerivative (dY t).val) ≤ Ad)
    (hCI : InSobolev 0 (CIntegral a b (fun _ => f.val) (fun _ => f.val) (fun t => (Y t).val)))
    (hCIn : hNorm 0 (CIntegral a b (fun _ => f.val) (fun _ => f.val) (fun t => (Y t).val)) ≤ E) :
    InSobolev 0 (fun k => ∫ t : ℝ in a..b, B t (Y t).val (frozenZ a t f.val) k) ∧
    hNorm 0 (fun k => ∫ t : ℝ in a..b, B t (Y t).val (frozenZ a t f.val) k) ≤
      (Real.sqrt 2 * h1EmbeddingConstant) * A * M / 3 +
        (Real.sqrt 2 * h1EmbeddingConstant) * Ad * M * (b - a) / 3 + E / 6 := by
  let K : ℝ := Real.sqrt 2 * h1EmbeddingConstant
  have hK : 0 ≤ K := mul_nonneg (Real.sqrt_nonneg _) (le_trans zero_le_one h1EmbeddingConstant_ge_one)
  let g : ℝ → Sobolev 0 := fun t => inclusionMap 0 1 (by norm_num)
    (JZeroBundled t (inclusionMap 0 1 (by norm_num) (dY t))
      (inclusionMap 0 1 (by norm_num) (frozenZBundled a t f)))
  have hg : Continuous g := (inclusionMap 0 1 (by norm_num)).continuous.comp
    (continuous_JZeroBundled continuous_id ((inclusionMap 0 1 (by norm_num)).continuous.comp hdYC)
      ((inclusionMap 0 1 (by norm_num)).continuous.comp (continuous_frozenZBundled a f)))
  have hgb : ∀ t ∈ Set.Icc a b, ‖g t‖ ≤ K * Ad * M := by
    intro t ht
    rw [sobolev_norm]
    change hNorm 0 (J t (dY t).val (frozenZ a t f.val)) ≤ _
    calc
      _ ≤ K * hNorm 0 (inverseDerivative (dY t).val) * hNorm 0 (frozenZ a t f.val) :=
        J_inverse_bound ((dY t).property.of_le (by norm_num))
          ((frozenZBundled a t f).property.of_le (by norm_num)) t
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left (hId t ht) hK) (hZ t ht)
        (hNorm_nonneg _ _) (mul_nonneg hK hAd)
  obtain ⟨hI, hIn⟩ := coefficient_integral_bound hg hab hgb
  have hJ : InSobolev 0 (J b (Y b).val (frozenZ a b f.val)) :=
    (J_h1_bound ((Y b).property.of_le (by norm_num))
      ((frozenZBundled a b f).property.of_le (by norm_num)) b).1.of_le (by norm_num)
  have hJn : hNorm 0 (J b (Y b).val (frozenZ a b f.val)) ≤ K * A * M := by
    calc
      _ ≤ K * hNorm 0 (inverseDerivative (Y b).val) * hNorm 0 (frozenZ a b f.val) :=
        J_inverse_bound ((Y b).property.of_le (by norm_num))
          ((frozenZBundled a b f).property.of_le (by norm_num)) b
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hIb hK) (hZ b ⟨hab, le_rfl⟩)
        (hNorm_nonneg _ _) (mul_nonneg hK hA)
  have hregY := regularFourierPath_of_bundled hYC hdYC hd
  have hregZ := frozenZ_regular (a := a) (b := b) f hfm
  have hCIcont := continuous_JZeroBundled continuous_id
    ((inclusionMap 0 1 (by norm_num)).continuous.comp
      (continuous_BTwoBundled continuous_id (continuous_const (y := f)) (continuous_const (y := f))))
    ((inclusionMap 0 1 (by norm_num)).continuous.comp hYC)
  have heq : (fun k => ∫ t : ℝ in a..b, B t (Y t).val (frozenZ a t f.val) k) =
      (1 / 3 : ℂ) • J b (Y b).val (frozenZ a b f.val) -
        (1 / 3 : ℂ) • (fun k => ∫ t : ℝ in a..b, (g t).val k) -
        (1 / 6 : ℂ) • CIntegral a b (fun _ => f.val) (fun _ => f.val) (fun t => (Y t).val) := by
    funext k
    have hn := variable_normal_form hab hregY hregZ hm (fun t _ => hfm.add (stage_meanZero a t f.val f.val)) k
    have hfun : (fun t : ℝ => J t (dY t).val (frozenZ a t f.val) k +
        J t (Y t).val ((1 / 2 : ℂ) • B t f.val f.val) k) =
        (fun t : ℝ => (g t).val k + (1 / 2 : ℂ) * J t (B t f.val f.val) (Y t).val k) := by
      funext t
      rw [J_smul_right, J_comm t (Y t).val (B t f.val f.val)]
      rfl
    have hi1 : IntervalIntegrable (fun t : ℝ => (g t).val k) volume a b :=
      ((coefficientMap 0 k).continuous.comp hg).intervalIntegrable a b
    have hi2 : IntervalIntegrable (fun t : ℝ => J t (B t f.val f.val) (Y t).val k) volume a b := by
      have hc : Continuous (fun t : ℝ => J t (B t f.val f.val) (Y t).val k) := by
        simpa only [Function.comp_def, coefficientMap_apply, JZeroBundled_val,
          inclusionMap_val, BTwoBundled_val, id_eq] using
          (coefficientMap 1 k).continuous.comp hCIcont
      exact hc.intervalIntegrable a b
    rw [hfun, intervalIntegral.integral_add hi1 (hi2.const_mul _),
      intervalIntegral.integral_const_mul, J_B_integral, hleft, J_zero_left] at hn
    simp only [Pi.zero_apply, sub_zero] at hn
    change (∫ t : ℝ in a..b, B t (Y t).val (frozenZ a t f.val) k) =
      (1 / 3 : ℂ) * J b (Y b).val (frozenZ a b f.val) k -
        (1 / 3 : ℂ) * (∫ t : ℝ in a..b, (g t).val k) -
        (1 / 6 : ℂ) * CIntegral a b (fun _ => f.val) (fun _ => f.val) (fun t => (Y t).val) k
    linear_combination hn
  rw [heq]
  refine ⟨((hJ.smul _).sub (hI.smul _)).sub (hCI.smul _), ?_⟩
  have hs := hNorm_sub_le ((hJ.smul (1 / 3 : ℂ)).sub (hI.smul (1 / 3 : ℂ))) (hCI.smul (1 / 6 : ℂ))
  have hs' := hNorm_sub_le (hJ.smul (1 / 3 : ℂ)) (hI.smul (1 / 3 : ℂ))
  rw [hNorm_smul hCI] at hs
  rw [hNorm_smul hJ, hNorm_smul hI] at hs'
  have hn3 : ‖(1 / 3 : ℂ)‖ = (1 / 3 : ℝ) := by norm_num
  have hn6 : ‖(1 / 6 : ℂ)‖ = (1 / 6 : ℝ) := by norm_num
  rw [hn6] at hs
  rw [hn3] at hs'
  change hNorm 0 _ ≤ K * A * M / 3 + K * Ad * M * (b - a) / 3 + E / 6
  linarith

end KdV
