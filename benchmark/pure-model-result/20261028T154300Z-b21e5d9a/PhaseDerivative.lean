import Proof
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

def bilinearPhase (k a : ℤ) : ℝ := 3 * (k : ℝ) * (a : ℝ) * ((k - a : ℤ) : ℝ)

theorem airy_convolution_phase (t : ℝ) (k a : ℤ) (x y : ℂ) :
    Complex.exp (Complex.I * ((-t : ℝ) : ℂ) * (k : ℂ) ^ 3) *
      ((Complex.exp (Complex.I * (t : ℂ) * (a : ℂ) ^ 3) * x) *
        (Complex.exp (Complex.I * (t : ℂ) * ((k - a : ℤ) : ℂ) ^ 3) * y)) =
      oscillation (bilinearPhase k a) t * x * y := by
  have hp : -Complex.I * (t : ℂ) * (bilinearPhase k a : ℂ) =
      Complex.I * ((-t : ℝ) : ℂ) * (k : ℂ) ^ 3 +
        (Complex.I * (t : ℂ) * (a : ℂ) ^ 3 +
          Complex.I * (t : ℂ) * ((k - a : ℤ) : ℂ) ^ 3) := by
    unfold bilinearPhase
    push_cast
    ring
  rw [oscillation, hp, Complex.exp_add, Complex.exp_add]
  ring

def JMode (k a : ℤ) (f g : Fourier) (t : ℝ) : ℂ :=
  oscillation (bilinearPhase k a) t *
    (inverseDerivative f a * inverseDerivative g (k - a))

def BMode (k a : ℤ) (f g : Fourier) (t : ℝ) : ℂ :=
  (Complex.I * (k : ℂ)) * (oscillation (bilinearPhase k a) t * f a * g (k - a))

theorem J_coefficient_series {k : ℤ} (hk : k ≠ 0) (f g : Fourier) (t : ℝ) :
    J t f g k = ∑' a : ℤ, JMode k a f g t := by
  simp only [J, airy, removeMean, if_neg hk, product]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro a
  exact (airy_convolution_phase t k a (inverseDerivative f a) (inverseDerivative g (k - a))).trans
    (by unfold JMode; ring)

theorem B_coefficient_series (k : ℤ) (f g : Fourier) (t : ℝ) :
    B t f g k = ∑' a : ℤ, BMode k a f g t := by
  simp only [B, airy, derivative, product]
  rw [← mul_assoc, mul_comm (Complex.exp _) (Complex.I * (k : ℂ)), mul_assoc,
    ← tsum_mul_left, ← tsum_mul_left]
  apply tsum_congr
  intro a
  unfold BMode
  rw [airy_convolution_phase]

theorem JMode_derivative_factor {f g : Fourier} (hfm : MeanZero f) (hgm : MeanZero g)
    (k a : ℤ) (t : ℝ) :
    ((-Complex.I * (bilinearPhase k a : ℂ)) * oscillation (bilinearPhase k a) t) *
      (inverseDerivative f a * inverseDerivative g (k - a)) = 3 * BMode k a f g t := by
  change f 0 = 0 at hfm
  change g 0 = 0 at hgm
  by_cases ha : a = 0
  · subst a
    simp [inverseDerivative, BMode, hfm]
  · by_cases hb : k - a = 0
    · simp [inverseDerivative, hb, BMode, hgm]
    · have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha
      have hbC : ((k - a : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hb
      have hbD : (k : ℂ) - (a : ℂ) ≠ 0 := by exact_mod_cast hb
      simp only [inverseDerivative, if_neg ha, if_neg hb]
      have hc : (-Complex.I * (bilinearPhase k a : ℂ)) *
          ((Complex.I * (a : ℂ))⁻¹ * (Complex.I * ((k - a : ℤ) : ℂ))⁻¹) =
          3 * (Complex.I * (k : ℂ)) := by
        unfold bilinearPhase
        push_cast
        field_simp [haC, hbD]
        simp [Complex.I_sq]
      calc
        _ = ((-Complex.I * (bilinearPhase k a : ℂ)) *
            ((Complex.I * (a : ℂ))⁻¹ * (Complex.I * ((k - a : ℤ) : ℂ))⁻¹)) *
              (oscillation (bilinearPhase k a) t * f a * g (k - a)) := by ring
        _ = _ := by rw [hc]; unfold BMode; ring

theorem JMode_hasDerivAt {f g : Fourier} (hfm : MeanZero f) (hgm : MeanZero g)
    (k a : ℤ) (t : ℝ) : HasDerivAt (JMode k a f g) (3 * BMode k a f g t) t := by
  have h := (oscillation_derivative (bilinearPhase k a) t).mul_const
    (inverseDerivative f a * inverseDerivative g (k - a))
  rw [JMode_derivative_factor hfm hgm k a t] at h
  exact h


theorem BMode_norm (k a : ℤ) (f g : Fourier) (t : ℝ) :
    ‖BMode k a f g t‖ = |(k : ℝ)| * (‖f a‖ * ‖g (k - a)‖) := by
  simp [BMode, oscillation_norm, Complex.norm_intCast, mul_assoc]

theorem BMode_continuous (k a : ℤ) (f g : Fourier) : Continuous (BMode k a f g) := by
  unfold BMode
  exact continuous_const.mul (((oscillation_continuous _).mul continuous_const).mul continuous_const)

theorem absolute_convolution_summable {f g : Fourier} (hf : InSobolev 0 f)
    (hg : InSobolev 0 g) (k : ℤ) : Summable (fun a : ℤ => ‖f a‖ * ‖g (k - a)‖) := by
  simpa only [norm_mul] using (product_summable hf hg k).norm

theorem continuous_B_coefficient {f g : Fourier} (hf : InSobolev 0 f)
    (hg : InSobolev 0 g) (k : ℤ) : Continuous (fun t : ℝ => B t f g k) := by
  have heq : (fun t : ℝ => B t f g k) = (fun t : ℝ => ∑' a : ℤ, BMode k a f g t) :=
    funext (B_coefficient_series k f g)
  rw [heq]
  exact continuous_tsum (fun a => BMode_continuous k a f g)
    ((absolute_convolution_summable hf hg k).mul_left |(k : ℝ)|)
    (fun a t => (BMode_norm k a f g t).le)

/-- The normal-form phase derivative is proved on the full `L²` space,
with no Fourier truncation and no smoothness assumption. -/
theorem J_fixed_hasDerivAt {f g : Fourier} (hf : InSobolev 0 f) (hg : InSobolev 0 g)
    (hfm : MeanZero f) (hgm : MeanZero g) (k : ℤ) (t : ℝ) :
    HasDerivAt (fun r : ℝ => J r f g k) (3 * B t f g k) t := by
  by_cases hk : k = 0
  · subst k
    have hz : (fun r : ℝ => J r f g 0) = (fun _ : ℝ => (0 : ℂ)) :=
      funext (fun r => J_meanZero r f g)
    rw [hz, show B t f g 0 = 0 from B_meanZero t f g, mul_zero]
    exact hasDerivAt_const t (0 : ℂ)
  · have hfi := (inverseDerivative_inSobolev_one hf).of_le (by norm_num : (0 : ℝ) ≤ 1)
    have hgi := (inverseDerivative_inSobolev_one hg).of_le (by norm_num : (0 : ℝ) ≤ 1)
    have hj0 : Summable (fun a : ℤ => JMode k a f g 0) := by
      simpa only [JMode, oscillation_zero, one_mul] using product_summable hfi hgi k
    have hu := (absolute_convolution_summable hf hg k).mul_left (3 * |(k : ℝ)|)
    have hb (a : ℤ) (r : ℝ) : ‖(3 : ℂ) * BMode k a f g r‖ ≤
        (3 * |(k : ℝ)|) * (‖f a‖ * ‖g (k - a)‖) := by
      rw [norm_mul, BMode_norm]
      have hthree : ‖(3 : ℂ)‖ = (3 : ℝ) := by norm_num
      rw [hthree]
      exact le_of_eq (by ring)
    have h := hasDerivAt_tsum hu
      (fun a r => JMode_hasDerivAt hfm hgm k a r) hb hj0 t
    have hj : (fun r : ℝ => ∑' a : ℤ, JMode k a f g r) = (fun r : ℝ => J r f g k) :=
      funext (fun r => (J_coefficient_series hk f g r).symm)
    rw [hj] at h
    have heq : (∑' a : ℤ, (3 : ℂ) * BMode k a f g t) = 3 * B t f g k := by
      rw [tsum_mul_left, ← B_coefficient_series]
    rw [heq] at h
    exact h

/-- The constant-input normal form, with both endpoints retained. -/
theorem fixed_normal_form {f g : Fourier} (hf : InSobolev 0 f) (hg : InSobolev 0 g)
    (hfm : MeanZero f) (hgm : MeanZero g) (a b : ℝ) (k : ℤ) :
    (∫ t : ℝ in a..b, B t f g k) = (1 / 3 : ℂ) * (J b f g k - J a f g k) := by
  have hi : IntervalIntegrable (fun t : ℝ => (3 : ℂ) * B t f g k) volume a b :=
    (continuous_const.mul (continuous_B_coefficient hf hg k)).intervalIntegrable a b
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => J_fixed_hasDerivAt hf hg hfm hgm k t) hi
  rw [intervalIntegral.integral_const_mul] at h
  calc
    _ = (1 / 3 : ℂ) * (3 * ∫ t : ℝ in a..b, B t f g k) := by ring
    _ = _ := by rw [h]

end KdV
