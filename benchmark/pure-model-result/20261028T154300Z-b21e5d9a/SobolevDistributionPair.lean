import ProductCoefficientMap
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

def sobolevWeightedZero (s : ℝ) : Sobolev s ≃ₗᵢ[ℂ] Sobolev 0 :=
  (sobolevIsometry s).trans (sobolevIsometry 0).symm

theorem sobolevWeightedZero_val (s : ℝ) (f : Sobolev s) :
    (sobolevWeightedZero s f).val = weighted s f.val := by
  funext k
  change (weight 0 k : ℂ)⁻¹ * weighted s f.val k = weighted s f.val k
  simp [weight]

theorem weight_neg_index (s : ℝ) (k : ℤ) : weight s (-k) = weight s k := by simp [weight]

/-- The bilinear distribution/test-function pairing, on H^-s × H^s.
 The missing conjugation is intentional: distributions act on test functions,
 rather than using the sesquilinear Hilbert inner product. -/
def distributionTest (s : ℝ) (φ : Sobolev s) : Sobolev (-s) →L[ℂ] ℂ :=
  ((productCoefficientMap 0).flip (sobolevWeightedZero s φ)).comp
    (sobolevWeightedZero (-s)).toContinuousLinearEquiv.toContinuousLinearMap

theorem distributionTest_apply (s : ℝ) (φ : Sobolev s) (f : Sobolev (-s)) :
    distributionTest s φ f = ∑' k : ℤ, f.val k * φ.val (-k) := by
  change product (sobolevWeightedZero (-s) f).val (sobolevWeightedZero s φ).val 0 = _
  rw [sobolevWeightedZero_val, sobolevWeightedZero_val]
  unfold product
  apply tsum_congr
  intro k
  simp only [zero_sub, weighted, weight_neg_index, weight_neg, Complex.ofReal_inv]
  calc
    _ = (((weight s k : ℂ)⁻¹) * (weight s k : ℂ)) * (f.val k * φ.val (-k)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (weight_pos s k).ne'), one_mul]

theorem distributionTest_bound (s : ℝ) (φ : Sobolev s) (f : Sobolev (-s)) :
    ‖distributionTest s φ f‖ ≤ ‖f‖ * ‖φ‖ := by
  have h := product_coeff_bound (sobolevWeightedZero (-s) f).property (sobolevWeightedZero s φ).property 0
  rw [← sobolev_norm, ← sobolev_norm, (sobolevWeightedZero (-s)).norm_map, (sobolevWeightedZero s).norm_map] at h
  exact h

/-- On functions this pairing is the same full convolution coefficient whose
 equality with normalized physical L² multiplication was proved earlier. -/
theorem distributionTest_function (s : ℝ) (hs : 0 ≤ s) (φ : Sobolev s) (f : Sobolev 0) :
    distributionTest s φ (inclusionMap (-s) 0 (by linarith) f) = product f.val φ.val 0 := by
  rw [distributionTest_apply]
  unfold product
  simp only [zero_sub, inclusionMap_val]

end KdV
