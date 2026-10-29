import Proof
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

/-- The reflection and sign change taking the cited source's equation
`U_t = U U_x + U_xxx` to the paper's equation. -/
def reflectSign (f : Fourier) : Fourier := fun k => -f (-k)

@[simp] theorem reflectSign_involutive (f : Fourier) : reflectSign (reflectSign f) = f := by
  funext k
  simp [reflectSign]

@[simp] theorem weight_even (s : ℝ) (k : ℤ) : weight s (-k) = weight s k := by
  simp [weight]

theorem reflectSign_inSobolev {s : ℝ} {f : Fourier} (hf : InSobolev s f) :
    InSobolev s (reflectSign f) := by
  have hs := hf.summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  apply memℓp_gen
  have hr := (Equiv.neg ℤ).summable_iff.mpr hs
  simpa only [Function.comp_def, Equiv.neg_apply, norm_weighted, reflectSign, norm_neg, weight_even] using hr

theorem reflectSign_hNorm (s : ℝ) (f : Fourier) : hNorm s (reflectSign f) = hNorm s f := by
  unfold hNorm
  congr 1
  calc
    _ = ∑' k : ℤ, ‖weighted s f (-k)‖ ^ 2 := by
      apply tsum_congr
      intro k
      simp [norm_weighted, reflectSign]
    _ = _ := (Equiv.neg ℤ).tsum_eq (fun k : ℤ => ‖weighted s f k‖ ^ 2)

theorem reflectSign_meanZero {f : Fourier} (hf : MeanZero f) : MeanZero (reflectSign f) := by
  simpa [MeanZero, reflectSign] using hf

theorem reflectSign_real {f : Fourier} (hf : RealValued f) : RealValued (reflectSign f) := by
  intro k
  simp only [reflectSign, neg_neg, map_neg]
  rw [hf k, starRingEnd_self_apply]

theorem reflectSign_airy (t : ℝ) (f : Fourier) :
    reflectSign (airy t f) = airy (-t) (reflectSign f) := by
  funext k
  simp only [reflectSign, airy, Int.cast_neg, Complex.ofReal_neg]
  rw [show Complex.I * (t : ℂ) * (-(k : ℂ)) ^ 3 = Complex.I * (-(t : ℂ)) * (k : ℂ) ^ 3 by ring]
  ring

theorem reflectSign_derivative (f : Fourier) : reflectSign (derivative f) = -derivative (reflectSign f) := by
  funext k
  simp only [reflectSign, derivative, Int.cast_neg, Pi.neg_apply]
  ring

theorem reflectSign_product (f g : Fourier) :
    reflectSign (product f g) = -product (reflectSign f) (reflectSign g) := by
  funext k
  change -(∑' a : ℤ, f a * g (-k - a)) = -(∑' a : ℤ, (-f (-a)) * (-g (-(k - a))))
  congr 1
  calc
    _ = ∑' a : ℤ, f (-a) * g (-k - -a) :=
      ((Equiv.neg ℤ).tsum_eq (fun a : ℤ => f a * g (-k - a))).symm
    _ = _ := by
      apply tsum_congr
      intro a
      rw [show -k - -a = -(k - a) by ring]
      ring

@[simp] theorem derivative_neg (f : Fourier) : derivative (-f) = -derivative f := by
  funext k
  simp [derivative]

/-- The full twisted vector field has the source sign after reflection. -/
theorem reflectSign_B (t : ℝ) (f g : Fourier) :
    reflectSign (B (-t) f g) = B t (reflectSign f) (reflectSign g) := by
  unfold B
  rw [reflectSign_airy, reflectSign_derivative, reflectSign_product, derivative_neg,
    neg_neg, reflectSign_airy, reflectSign_airy]
  simp only [neg_neg]

end KdV
