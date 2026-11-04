import NormalOps
noncomputable section
open scoped ComplexConjugate ENNReal
namespace KdV

theorem product_airy_zero (t : ℝ) (f g : Fourier) :
    product (airy t f) (airy t g) 0 = product f g 0 := by
  unfold product
  apply tsum_congr
  intro a
  simp only [airy, zero_sub, Int.cast_neg]
  calc
    _ = (Complex.exp (Complex.I * (t : ℂ) * (a : ℂ) ^ 3) *
        Complex.exp (Complex.I * (t : ℂ) * (-(a : ℂ)) ^ 3)) * (f a * g (-a)) := by ring
    _ = _ := by
      rw [← Complex.exp_add,
        show Complex.I * (t : ℂ) * (a : ℂ) ^ 3 +
          Complex.I * (t : ℂ) * (-(a : ℂ)) ^ 3 = 0 by ring]
      simp

/-- The stage written exactly as Li–Wu (7.3), before deleting the mean. -/
def sourceBilinearStage (a t : ℝ) (f g : Fourier) : Fourier :=
  (1 / 6 : ℂ) •
    (airy (-t) (product (airy t (inverseDerivative f)) (airy t (inverseDerivative g))) -
      airy (-a) (product (airy a (inverseDerivative f)) (airy a (inverseDerivative g))))

/-- Deleting the mean in each boundary value leaves its endpoint difference unchanged. -/
theorem bilinearStage_eq_source (a t : ℝ) (f g : Fourier) :
    bilinearStage a t f g = sourceBilinearStage a t f g := by
  unfold bilinearStage sourceBilinearStage
  congr 1
  funext k
  by_cases hk : k = 0
  · subst k
    simp only [Pi.sub_apply, J, airy_mean, removeMean_zero, sub_self, product_airy_zero]
  · simp [J, airy, removeMean, hk]

end KdV
