import PhaseDerivative
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

theorem inverseDerivative_coeff_norm_le (f : Fourier) (k : ℤ) :
    ‖inverseDerivative f k‖ ≤ ‖f k‖ := by
  by_cases hk : k = 0
  · simp [inverseDerivative, hk]
  · have hkone : 1 ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk
    simp only [inverseDerivative, if_neg hk, norm_mul, norm_inv, Complex.norm_I,
      Complex.norm_intCast, one_mul]
    have hi : |(k : ℝ)|⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hkone
    nlinarith [norm_nonneg (f k)]

theorem JMode_norm_le (k a : ℤ) (f g : Fourier) (t : ℝ) :
    ‖JMode k a f g t‖ ≤ ‖f a‖ * ‖g (k - a)‖ := by
  simp only [JMode, norm_mul, oscillation_norm, one_mul]
  exact mul_le_mul (inverseDerivative_coeff_norm_le f a) (inverseDerivative_coeff_norm_le g (k - a))
    (norm_nonneg _) (norm_nonneg _)

theorem inverseDerivative_coeff_hasDerivAt {f df : ℝ → Fourier} {t : ℝ}
    (hf : ∀ k : ℤ, HasDerivAt (fun r : ℝ => f r k) (df t k) t) (k : ℤ) :
    HasDerivAt (fun r : ℝ => inverseDerivative (f r) k) (inverseDerivative (df t) k) t := by
  by_cases hk : k = 0
  · simpa only [inverseDerivative, if_pos hk] using hasDerivAt_const t (0 : ℂ)
  · simpa only [inverseDerivative, if_neg hk] using (hf k).const_mul (Complex.I * (k : ℂ))⁻¹

def variableJMode (k a : ℤ) (f g : ℝ → Fourier) (t : ℝ) : ℂ := JMode k a (f t) (g t) t

theorem variableJMode_hasDerivAt {f df g dg : ℝ → Fourier} {t : ℝ}
    (hf : ∀ k : ℤ, HasDerivAt (fun r : ℝ => f r k) (df t k) t)
    (hg : ∀ k : ℤ, HasDerivAt (fun r : ℝ => g r k) (dg t k) t)
    (hfm : MeanZero (f t)) (hgm : MeanZero (g t)) (k a : ℤ) :
    HasDerivAt (variableJMode k a f g)
      (3 * BMode k a (f t) (g t) t + JMode k a (df t) (g t) t + JMode k a (f t) (dg t) t) t := by
  have h := (oscillation_derivative (bilinearPhase k a) t).mul
    ((inverseDerivative_coeff_hasDerivAt hf a).mul (inverseDerivative_coeff_hasDerivAt hg (k - a)))
  apply h.congr_deriv
  have he := JMode_derivative_factor hfm hgm k a t
  dsimp [JMode] at *
  linear_combination he

/-- A common square-summable envelope supplies the analytic justification for
termwise differentiation. This is an internal regularity condition; deriving it
for the smooth trajectories used in the proof remains a separate obligation. -/
structure RegularFourierPath (a b : ℝ) (f df : ℝ → Fourier) : Prop where
  continuous : ∀ k, ContinuousOn (fun t : ℝ => f t k) (Set.Icc a b)
  derivative_continuous : ∀ k, ContinuousOn (fun t : ℝ => df t k) (Set.Icc a b)
  hasDerivAt : ∀ t ∈ Set.Ioo a b, ∀ k, HasDerivAt (fun r : ℝ => f r k) (df t k) t
  envelope : ∃ F Fd : Fourier, InSobolev 0 F ∧ InSobolev 0 Fd ∧
    ∀ t ∈ Set.Icc a b, ∀ k, ‖f t k‖ ≤ ‖F k‖ ∧ ‖df t k‖ ≤ ‖Fd k‖

theorem inSobolev_zero_of_coeff_bound {f F : Fourier} (hF : InSobolev 0 F)
    (hb : ∀ k, ‖f k‖ ≤ ‖F k‖) : InSobolev 0 f := by
  rw [inSobolev_zero_iff] at hF ⊢
  exact Memℓp.mono' hF hb

theorem inverseDerivative_coeff_continuousOn {f : ℝ → Fourier} {S : Set ℝ}
    (hf : ∀ k, ContinuousOn (fun t : ℝ => f t k) S) (k : ℤ) :
    ContinuousOn (fun t : ℝ => inverseDerivative (f t) k) S := by
  by_cases hk : k = 0
  · simpa only [inverseDerivative, if_pos hk] using continuousOn_const (c := (0 : ℂ))
  · simpa only [inverseDerivative, if_neg hk] using (hf k).const_mul (Complex.I * (k : ℂ))⁻¹

theorem variableJMode_continuousOn {f g : ℝ → Fourier} {S : Set ℝ}
    (hf : ∀ k, ContinuousOn (fun t : ℝ => f t k) S)
    (hg : ∀ k, ContinuousOn (fun t : ℝ => g t k) S) (k a : ℤ) :
    ContinuousOn (variableJMode k a f g) S := by
  exact (oscillation_continuous _).continuousOn.mul
    ((inverseDerivative_coeff_continuousOn hf a).mul (inverseDerivative_coeff_continuousOn hg (k - a)))

theorem variableBMode_continuousOn {f g : ℝ → Fourier} {S : Set ℝ}
    (hf : ∀ k, ContinuousOn (fun t : ℝ => f t k) S)
    (hg : ∀ k, ContinuousOn (fun t : ℝ => g t k) S) (k a : ℤ) :
    ContinuousOn (fun t : ℝ => BMode k a (f t) (g t) t) S := by
  exact continuousOn_const.mul (((oscillation_continuous _).continuousOn.mul (hf a)).mul (hg (k - a)))

end KdV
