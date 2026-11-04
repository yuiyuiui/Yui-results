import HomogeneousContinuity
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

/-- The source's coefficient equation is stated only on nonzero modes. -/
def SourceNonzeroEquation (T : ℝ) (f : Fourier) (v : ℝ → Fourier) : Prop :=
  v 0 = f ∧ ∀ t ∈ Set.Icc 0 T, ∀ k : ℤ, k ≠ 0 →
    v t k = f k + (1 / 2 : ℂ) * ∫ s : ℝ in (0 : ℝ)..t, B (-s) (v s) (v s) k

theorem SourceNonzeroEquation.all_modes {T : ℝ} {f : Fourier} {v : ℝ → Fourier}
    (hv : SourceNonzeroEquation T f v) (hfm : MeanZero f)
    (hvm : ∀ t ∈ Set.Icc 0 T, MeanZero (v t)) : SourceTwistedEquation T f v := by
  refine ⟨hv.1, ?_⟩
  intro t ht k
  by_cases hk : k = 0
  · subst k
    rw [hvm t ht, hfm]
    simp [B, airy, derivative]
  · exact hv.2 t ht k hk

theorem source_phase_formula (s : ℝ) (k : ℤ) (f g : Fourier) :
    B (-s) f g k = (Complex.I * (k : ℂ)) *
      ∑' a : ℤ, Complex.exp (Complex.I * (s : ℂ) *
        (3 * (k : ℂ) * (a : ℂ) * ((k - a : ℤ) : ℂ))) * f a * g (k - a) := by
  rw [B_coefficient_series, ← tsum_mul_left]
  apply tsum_congr
  intro a
  unfold BMode oscillation bilinearPhase
  congr 3
  push_cast
  ring_nf

theorem reflectSign_B_reverse (t : ℝ) (f g : Fourier) :
    reflectSign (B t f g) = B (-t) (reflectSign f) (reflectSign g) := by
  simpa only [neg_neg] using reflectSign_B (-t) f g

theorem targetTwisted_to_source {T : ℝ} {f : Fourier} {v : ℝ → Fourier}
    (hv : TwistedEquation T f v) :
    SourceTwistedEquation T (reflectSign f) (fun t => reflectSign (v t)) := by
  refine ⟨congrArg reflectSign hv.1, ?_⟩
  intro t ht k
  have hs := hv.2 t ht (-k)
  have hi : (∫ s : ℝ in (0 : ℝ)..t, -B s (v s) (v s) (-k)) =
      ∫ s : ℝ in (0 : ℝ)..t, B (-s) (reflectSign (v s)) (reflectSign (v s)) k := by
    apply intervalIntegral.integral_congr
    intro s _
    exact congrFun (reflectSign_B_reverse s (v s) (v s)) k
  change -v t (-k) = -f (-k) + (1 / 2 : ℂ) * _
  rw [← hi, intervalIntegral.integral_neg]
  linear_combination -hs

theorem airy_kernel_mul (t s : ℝ) (k : ℤ) :
    Complex.exp (Complex.I * (t : ℂ) * (k : ℂ) ^ 3) *
      Complex.exp (Complex.I * ((-s : ℝ) : ℂ) * (k : ℂ) ^ 3) =
      Complex.exp (Complex.I * ((t : ℂ) - (s : ℂ)) * (k : ℂ) ^ 3) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring_nf

theorem untwist_Duhamel {T : ℝ} {f : Fourier} {v : ℝ → Fourier}
    (hv : TwistedEquation T f v) : Duhamel T f (fun t => airy t (v t)) := by
  refine ⟨?_, ?_⟩
  · simpa only [airy_zero] using hv.1
  · intro t ht k
    let E : ℂ := Complex.exp (Complex.I * (t : ℂ) * (k : ℂ) ^ 3)
    have hi : E * (∫ s : ℝ in (0 : ℝ)..t, B s (v s) (v s) k) =
        ∫ s : ℝ in (0 : ℝ)..t,
          Complex.exp (Complex.I * ((t : ℂ) - (s : ℂ)) * (k : ℂ) ^ 3) *
            (Complex.I * (k : ℂ)) * product (airy s (v s)) (airy s (v s)) k := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro s _
      change E * (Complex.exp (Complex.I * ((-s : ℝ) : ℂ) * (k : ℂ) ^ 3) *
        ((Complex.I * (k : ℂ)) * product (airy s (v s)) (airy s (v s)) k)) = _
      rw [← mul_assoc E, airy_kernel_mul]
      ring_nf
    change E * v t k = E * f k + (1 / 2 : ℂ) * _
    rw [hv.2 t ht k]
    calc
      _ = E * f k + (1 / 2 : ℂ) * (E * ∫ s : ℝ in (0 : ℝ)..t, B s (v s) (v s) k) := by ring
      _ = _ := by rw [hi]

/-- Conjugating the paper's Duhamel equation recovers the exact twisted
coefficient equation, without an extra solution premise. -/
theorem twist_Duhamel {T : ℝ} {f : Fourier} {u : ℝ → Fourier}
    (hu : Duhamel T f u) : TwistedEquation T f (fun t => airy (-t) (u t)) := by
  refine ⟨?_, ?_⟩
  · simpa only [neg_zero, airy_zero] using hu.1
  · intro t ht k
    let E : ℂ := Complex.exp (Complex.I * ((-t : ℝ) : ℂ) * (k : ℂ) ^ 3)
    have hi : E * (∫ s : ℝ in (0 : ℝ)..t,
          Complex.exp (Complex.I * ((t : ℂ) - (s : ℂ)) * (k : ℂ) ^ 3) *
            (Complex.I * (k : ℂ)) * product (u s) (u s) k) =
        ∫ s : ℝ in (0 : ℝ)..t,
          B s (airy (-s) (u s)) (airy (-s) (u s)) k := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro s _
      dsimp only [B]
      rw [airy_inverse_neg]
      change E * (Complex.exp (Complex.I * ((t : ℂ) - (s : ℂ)) * (k : ℂ) ^ 3) *
          (Complex.I * (k : ℂ)) * product (u s) (u s) k) =
        Complex.exp (Complex.I * ((-s : ℝ) : ℂ) * (k : ℂ) ^ 3) *
          ((Complex.I * (k : ℂ)) * product (u s) (u s) k)
      have he : E * Complex.exp (Complex.I * ((t : ℂ) - (s : ℂ)) * (k : ℂ) ^ 3) =
          Complex.exp (Complex.I * ((-s : ℝ) : ℂ) * (k : ℂ) ^ 3) := by
        dsimp [E]
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring_nf
      rw [mul_assoc (Complex.exp _) (Complex.I * (k : ℂ)) (product (u s) (u s) k), ← mul_assoc E, he]
    change E * u t k = f k + (1 / 2 : ℂ) * _
    rw [hu.2 t ht k]
    have he : E * airy t f k = f k := by
      change airy (-t) (airy t f) k = f k
      rw [airy_neg_inverse]
    calc
      _ = E * airy t f k + (1 / 2 : ℂ) * (E * ∫ s : ℝ in (0 : ℝ)..t,
          Complex.exp (Complex.I * ((t : ℂ) - (s : ℂ)) * (k : ℂ) ^ 3) *
            (Complex.I * (k : ℂ)) * product (u s) (u s) k) := by ring
      _ = _ := by rw [he, hi]

end KdV
