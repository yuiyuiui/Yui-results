import VariableNormal
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

theorem JMode_envelope {f g F G : Fourier} (hf : ∀ k, ‖f k‖ ≤ ‖F k‖)
    (hg : ∀ k, ‖g k‖ ≤ ‖G k‖) (k a : ℤ) (t : ℝ) :
    ‖JMode k a f g t‖ ≤ ‖F a‖ * ‖G (k - a)‖ :=
  (JMode_norm_le k a f g t).trans (mul_le_mul (hf a) (hg (k - a)) (norm_nonneg _) (norm_nonneg _))

theorem three_BMode_envelope {f g F G : Fourier} (hf : ∀ k, ‖f k‖ ≤ ‖F k‖)
    (hg : ∀ k, ‖g k‖ ≤ ‖G k‖) (k a : ℤ) (t : ℝ) :
    ‖(3 : ℂ) * BMode k a f g t‖ ≤ (3 * |(k : ℝ)|) * (‖F a‖ * ‖G (k - a)‖) := by
  rw [norm_mul, BMode_norm]
  have hthree : ‖(3 : ℂ)‖ = (3 : ℝ) := by norm_num
  rw [hthree, ← mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul (hf a) (hg (k - a)) (norm_nonneg _) (norm_nonneg _))
    (by positivity)

theorem variable_J_continuousOn {a b : ℝ} {f g : ℝ → Fourier} {F G : Fourier}
    (hF : InSobolev 0 F) (hG : InSobolev 0 G)
    (hf : ∀ k, ContinuousOn (fun t : ℝ => f t k) (Set.Icc a b))
    (hg : ∀ k, ContinuousOn (fun t : ℝ => g t k) (Set.Icc a b))
    (hfb : ∀ t ∈ Set.Icc a b, ∀ k, ‖f t k‖ ≤ ‖F k‖)
    (hgb : ∀ t ∈ Set.Icc a b, ∀ k, ‖g t k‖ ≤ ‖G k‖) (k : ℤ) :
    ContinuousOn (fun t : ℝ => J t (f t) (g t) k) (Set.Icc a b) := by
  by_cases hk : k = 0
  · subst k
    have heq : (fun t : ℝ => J t (f t) (g t) 0) = (fun _ : ℝ => (0 : ℂ)) :=
      funext (fun t => J_meanZero t (f t) (g t))
    rw [heq]
    exact continuousOn_const
  · have heq : (fun t : ℝ => J t (f t) (g t) k) =
        (fun t : ℝ => ∑' j : ℤ, variableJMode k j f g t) :=
      funext (fun t => J_coefficient_series hk (f t) (g t) t)
    rw [heq]
    exact continuousOn_tsum (fun j => variableJMode_continuousOn hf hg k j)
      (absolute_convolution_summable hF hG k)
      (fun j t ht => JMode_envelope (hfb t ht) (hgb t ht) k j t)

theorem variable_B_continuousOn {a b : ℝ} {f g : ℝ → Fourier} {F G : Fourier}
    (hF : InSobolev 0 F) (hG : InSobolev 0 G)
    (hf : ∀ k, ContinuousOn (fun t : ℝ => f t k) (Set.Icc a b))
    (hg : ∀ k, ContinuousOn (fun t : ℝ => g t k) (Set.Icc a b))
    (hfb : ∀ t ∈ Set.Icc a b, ∀ k, ‖f t k‖ ≤ ‖F k‖)
    (hgb : ∀ t ∈ Set.Icc a b, ∀ k, ‖g t k‖ ≤ ‖G k‖) (k : ℤ) :
    ContinuousOn (fun t : ℝ => B t (f t) (g t) k) (Set.Icc a b) := by
  have heq : (fun t : ℝ => B t (f t) (g t) k) =
      (fun t : ℝ => ∑' j : ℤ, BMode k j (f t) (g t) t) :=
    funext (fun t => B_coefficient_series k (f t) (g t) t)
  rw [heq]
  apply continuousOn_tsum (fun j => variableBMode_continuousOn hf hg k j)
    ((absolute_convolution_summable hF hG k).mul_left |(k : ℝ)|)
  intro j t ht
  rw [BMode_norm]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul (hfb t ht j) (hgb t ht (k - j)) (norm_nonneg _) (norm_nonneg _)) (abs_nonneg _)

/-- Full time-dependent normal-form differentiation under explicit internal
regularity hypotheses. It is not imported as an external theorem. -/
theorem variable_J_hasDerivAt {a b : ℝ} {f df g dg : ℝ → Fourier}
    (hf : RegularFourierPath a b f df) (hg : RegularFourierPath a b g dg)
    (hfm : ∀ t ∈ Set.Icc a b, MeanZero (f t)) (hgm : ∀ t ∈ Set.Icc a b, MeanZero (g t))
    {t : ℝ} (ht : t ∈ Set.Ioo a b) (k : ℤ) :
    HasDerivAt (fun r : ℝ => J r (f r) (g r) k)
      (3 * B t (f t) (g t) k + J t (df t) (g t) k + J t (f t) (dg t) k) t := by
  by_cases hk : k = 0
  · subst k
    have heq : (fun r : ℝ => J r (f r) (g r) 0) = (fun _ : ℝ => (0 : ℂ)) :=
      funext (fun r => J_meanZero r (f r) (g r))
    rw [heq, show B t (f t) (g t) 0 = 0 from B_meanZero _ _ _,
      show J t (df t) (g t) 0 = 0 from J_meanZero _ _ _,
      show J t (f t) (dg t) 0 = 0 from J_meanZero _ _ _]
    simpa using hasDerivAt_const t (0 : ℂ)
  · obtain ⟨F, Fd, hF, hFd, hfb⟩ := hf.envelope
    obtain ⟨G, Gd, hG, hGd, hgb⟩ := hg.envelope
    have hFt r hr k := (hfb r hr k).1
    have hFdt r hr k := (hfb r hr k).2
    have hGt r hr k := (hgb r hr k).1
    have hGdt r hr k := (hgb r hr k).2
    have htc : t ∈ Set.Icc a b := ⟨ht.1.le, ht.2.le⟩
    have huB := (absolute_convolution_summable hF hG k).mul_left (3 * |(k : ℝ)|)
    have huD := absolute_convolution_summable hFd hG k
    have huE := absolute_convolution_summable hF hGd k
    have hu := (huB.add huD).add huE
    have hb (j : ℤ) (r : ℝ) (hr : r ∈ Set.Ioo a b) :
        ‖3 * BMode k j (f r) (g r) r + JMode k j (df r) (g r) r + JMode k j (f r) (dg r) r‖ ≤
          ((3 * |(k : ℝ)|) * (‖F j‖ * ‖G (k - j)‖) + ‖Fd j‖ * ‖G (k - j)‖) +
            ‖F j‖ * ‖Gd (k - j)‖ := by
      have hrc : r ∈ Set.Icc a b := ⟨hr.1.le, hr.2.le⟩
      calc
        _ ≤ (‖(3 : ℂ) * BMode k j (f r) (g r) r‖ + ‖JMode k j (df r) (g r) r‖) +
            ‖JMode k j (f r) (dg r) r‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
        _ ≤ _ := add_le_add
          (add_le_add (three_BMode_envelope (hFt r hrc) (hGt r hrc) k j r)
            (JMode_envelope (hFdt r hrc) (hGt r hrc) k j r))
          (JMode_envelope (hFt r hrc) (hGdt r hrc) k j r)
    have hj0 : Summable (fun j : ℤ => variableJMode k j f g t) :=
      Summable.of_norm_bounded (absolute_convolution_summable hF hG k)
        (fun j => JMode_envelope (hFt t htc) (hGt t htc) k j t)
    have h := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo isPreconnected_Ioo
      (fun j r hr => variableJMode_hasDerivAt (hf.hasDerivAt r hr) (hg.hasDerivAt r hr)
        (hfm r ⟨hr.1.le, hr.2.le⟩) (hgm r ⟨hr.1.le, hr.2.le⟩) k j)
      hb ht hj0 ht
    have heq : (fun r : ℝ => ∑' j : ℤ, variableJMode k j f g r) =
        (fun r : ℝ => J r (f r) (g r) k) :=
      funext (fun r => (J_coefficient_series hk (f r) (g r) r).symm)
    rw [heq] at h
    have hsB : Summable (fun j : ℤ => (3 : ℂ) * BMode k j (f t) (g t) t) :=
      Summable.of_norm_bounded huB (fun j => three_BMode_envelope (hFt t htc) (hGt t htc) k j t)
    have hsD : Summable (fun j : ℤ => JMode k j (df t) (g t) t) :=
      Summable.of_norm_bounded huD (fun j => JMode_envelope (hFdt t htc) (hGt t htc) k j t)
    have hsE : Summable (fun j : ℤ => JMode k j (f t) (dg t) t) :=
      Summable.of_norm_bounded huE (fun j => JMode_envelope (hFt t htc) (hGdt t htc) k j t)
    rw [(hsB.add hsD).tsum_add hsE, hsB.tsum_add hsD, tsum_mul_left,
      ← B_coefficient_series, ← J_coefficient_series hk, ← J_coefficient_series hk] at h
    exact h


/-- Equation (13), including the initial boundary value, proved by termwise
Fourier differentiation and the fundamental theorem of calculus. -/
theorem variable_normal_form {a b : ℝ} (hab : a ≤ b) {f df g dg : ℝ → Fourier}
    (hf : RegularFourierPath a b f df) (hg : RegularFourierPath a b g dg)
    (hfm : ∀ t ∈ Set.Icc a b, MeanZero (f t)) (hgm : ∀ t ∈ Set.Icc a b, MeanZero (g t))
    (k : ℤ) :
    (∫ t : ℝ in a..b, B t (f t) (g t) k) =
      (1 / 3 : ℂ) * (J b (f b) (g b) k - J a (f a) (g a) k) -
      (1 / 3 : ℂ) * ∫ t : ℝ in a..b, (J t (df t) (g t) k + J t (f t) (dg t) k) := by
  obtain ⟨F, Fd, hF, hFd, hfb⟩ := hf.envelope
  obtain ⟨G, Gd, hG, hGd, hgb⟩ := hg.envelope
  have hFt r hr k := (hfb r hr k).1
  have hFdt r hr k := (hfb r hr k).2
  have hGt r hr k := (hgb r hr k).1
  have hGdt r hr k := (hgb r hr k).2
  have hcJ := variable_J_continuousOn hF hG hf.continuous hg.continuous hFt hGt k
  have hcB := variable_B_continuousOn hF hG hf.continuous hg.continuous hFt hGt k
  have hcD := variable_J_continuousOn hFd hG hf.derivative_continuous hg.continuous hFdt hGt k
  have hcE := variable_J_continuousOn hF hGd hf.continuous hg.derivative_continuous hFt hGdt k
  have hiB := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hab hcB
  have hiD := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hab hcD
  have hiE := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hab hcE
  have hi3B := hiB.const_mul (3 : ℂ)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcJ
    (fun t ht => variable_J_hasDerivAt hf hg hfm hgm ht k) ((hi3B.add hiD).add hiE)
  rw [intervalIntegral.integral_add (hi3B.add hiD) hiE,
    intervalIntegral.integral_add hi3B hiD, intervalIntegral.integral_const_mul] at hFTC
  rw [intervalIntegral.integral_add hiD hiE]
  linear_combination (1 / 3 : ℂ) * hFTC

end KdV
