import Proof
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

theorem airyMap_norm (s t : ℝ) (f : Sobolev s) : ‖airyMap s t f‖ = ‖f‖ := by
  rw [sobolev_norm, sobolev_norm]
  exact airy_hNorm s t f.val

set_option maxHeartbeats 800000 in
/-- Joint continuity of the unitary group action. -/
theorem continuous_airy_action (s : ℝ) :
    Continuous (fun p : ℝ × Sobolev s => airyMap s p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  rintro ⟨t₀, f₀⟩
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h₁ : Filter.Tendsto (fun p : ℝ × Sobolev s => ‖p.2 - f₀‖)
      (nhds (t₀, f₀)) (nhds 0) := by
    simpa using ((continuous_snd.sub (continuous_const (y := f₀))).norm.continuousAt
      (x := (t₀, f₀))).tendsto
  have h₂ : Filter.Tendsto (fun p : ℝ × Sobolev s => ‖airyMap s p.1 f₀ - airyMap s t₀ f₀‖)
      (nhds (t₀, f₀)) (nhds 0) := by
    simpa using (((continuous_airy_fixed s f₀).comp continuous_fst).sub
      (continuous_const (y := airyMap s t₀ f₀))).norm.continuousAt (x := (t₀, f₀)) |>.tendsto
  have hb (p : ℝ × Sobolev s) : ‖airyMap s p.1 p.2 - airyMap s t₀ f₀‖ ≤
      ‖p.2 - f₀‖ + ‖airyMap s p.1 f₀ - airyMap s t₀ f₀‖ := by
    calc
      _ ≤ ‖airyMap s p.1 p.2 - airyMap s p.1 f₀‖ + ‖airyMap s p.1 f₀ - airyMap s t₀ f₀‖ :=
        norm_sub_le_norm_sub_add_norm_sub (airyMap s p.1 p.2)
          (airyMap s p.1 f₀) (airyMap s t₀ f₀)
      _ = _ := by rw [← map_sub, airyMap_norm]
  exact squeeze_zero (fun p : ℝ × Sobolev s =>
    norm_nonneg (airyMap s p.1 p.2 - airyMap s t₀ f₀)) hb (by simpa using h₁.add h₂)

theorem weight_add (s r : ℝ) (k : ℤ) : weight (s + r) k = weight s k * weight r k := by
  unfold weight
  rw [add_div, Real.rpow_add (by positivity : 0 < 1 + (k : ℝ) ^ 2)]

theorem weight_one_ge_abs (k : ℤ) : |(k : ℝ)| ≤ weight 1 k := by
  have h := weight_sq 1 k
  rw [Real.rpow_one] at h
  nlinarith [weight_pos 1 k, sq_abs (k : ℝ), abs_nonneg (k : ℝ)]

/-- The distributional spatial derivative on Fourier coefficients. -/
def derivative (f : Fourier) : Fourier := fun k => Complex.I * (k : ℂ) * f k

theorem derivative_weighted_bound (s : ℝ) (f : Fourier) (k : ℤ) :
    ‖weighted s (derivative f) k‖ ≤ ‖weighted (s + 1) f k‖ := by
  rw [norm_weighted, norm_weighted, weight_add]
  simp only [derivative, norm_mul, Complex.norm_I, Complex.norm_intCast, one_mul]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (weight_one_ge_abs k) (weight_pos s k).le) (norm_nonneg (f k))

theorem derivative_inSobolev {s : ℝ} {f : Fourier} (hf : InSobolev (s + 1) f) :
    InSobolev s (derivative f) := by
  apply Memℓp.mono' hf
  exact derivative_weighted_bound s f

theorem derivative_hNorm {s : ℝ} {f : Fourier} (hf : InSobolev (s + 1) f) :
    hNorm s (derivative f) ≤ hNorm (s + 1) f := by
  simpa using hNorm_le_of_weighted_bound hf (by norm_num : (0 : ℝ) ≤ 1)
    (fun k => by simpa using derivative_weighted_bound s f k)

/-- Every inverse Sobolev weight of order strictly larger than one half is in ℓ². -/
theorem negative_weight_square_summable {q : ℝ} (hq : 1 / 2 < q) :
    Summable (fun k : ℤ => weight (-q) k ^ 2) := by
  have htail := Real.summable_abs_int_rpow (b := 2 * q) (by linarith)
  have hdelta : Summable (fun k : ℤ => if k = 0 then (1 : ℝ) else 0) := (hasSum_ite_eq 0 1).summable
  apply (htail.add hdelta).of_nonneg_of_le (fun _ => sq_nonneg _)
  intro k
  rw [weight_sq]
  by_cases hk : k = 0
  · subst k
    norm_num
    positivity
  · simp only [if_neg hk, add_zero]
    have ha : 0 < |(k : ℝ)| := abs_pos.mpr (intCast_ne_zero hk)
    calc
      _ ≤ (|(k : ℝ)| ^ 2) ^ (-q) :=
        Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos ha) (by rw [sq_abs]; linarith) (by linarith)
      _ = |(k : ℝ)| ^ (-(2 * q)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
        congr 1
        ring

def negativeWeightLp (q : ℝ) (hq : 1 / 2 < q) : lp (fun _ : ℤ => ℂ) 2 :=
  ⟨fun k => (weight (-q) k : ℂ), memℓp_gen (by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (weight_pos (-q) _),
      ENNReal.toReal_ofNat, Real.rpow_two]
      using negative_weight_square_summable hq)⟩

def negativeProductConstant (q : ℝ) (hq : 1 / 2 < q) : ℝ := ‖negativeWeightLp q hq‖

theorem negative_product_bound {q : ℝ} (hq : 1 / 2 < q) {f g : Fourier}
    (hf : InSobolev 0 f) (hg : InSobolev 0 g) :
    InSobolev (-q) (product f g) ∧
      hNorm (-q) (product f g) ≤ negativeProductConstant q hq * hNorm 0 f * hNorm 0 g := by
  have hb (k : ℤ) : ‖weighted (-q) (product f g) k‖ ≤
      (hNorm 0 f * hNorm 0 g) * ‖negativeWeightLp q hq k‖ := by
    rw [norm_weighted]
    have hp := product_coeff_bound hf hg k
    change weight (-q) k * ‖product f g k‖ ≤
      (hNorm 0 f * hNorm 0 g) * ‖(weight (-q) k : ℂ)‖
    rw [Complex.norm_real, Real.norm_of_nonneg (weight_pos (-q) k).le]
    nlinarith [weight_pos (-q) k]
  have hh : Memℓp (weighted (-q) (product f g)) 2 := by
    apply Memℓp.mono' ((negativeWeightLp q hq).property.const_smul
      ((hNorm 0 f * hNorm 0 g : ℝ) : ℂ))
    intro k
    simpa only [Pi.smul_apply, norm_smul, Complex.norm_real,
      Real.norm_of_nonneg (mul_nonneg (hNorm_nonneg 0 f) (hNorm_nonneg 0 g))] using hb k
  refine ⟨hh, ?_⟩
  rw [hNorm_eq_lpNorm hh]
  calc
    _ ≤ ‖((hNorm 0 f * hNorm 0 g : ℝ) : ℂ) • negativeWeightLp q hq‖ := by
      apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro k
      simpa only [lp.coeFn_smul, Pi.smul_apply, norm_smul, Complex.norm_real,
        Real.norm_of_nonneg (mul_nonneg (hNorm_nonneg 0 f) (hNorm_nonneg 0 g))] using hb k
    _ = _ := by
      simp only [norm_smul, Complex.norm_real,
        Real.norm_of_nonneg (mul_nonneg (hNorm_nonneg 0 f) (hNorm_nonneg 0 g)), negativeProductConstant]
      ring

end KdV
