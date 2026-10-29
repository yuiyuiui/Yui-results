import IntegerProductMap
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

def physicalRHS (f : Fourier) : Fourier :=
  -derivative (derivative (derivative f)) + (1 / 2 : ℂ) • derivative (product f f)

theorem nat_order_succ (n : ℕ) : (((n + 1 : ℕ) : ℝ) + 1) = ((n + 2 : ℕ) : ℝ) := by push_cast; ring

def derivativeNatLinear (n : ℕ) : Sobolev ((n + 2 : ℕ) : ℝ) →ₗ[ℂ] Sobolev ((n + 1 : ℕ) : ℝ) where
  toFun f := ⟨derivative f.val, derivative_inSobolev (s := ((n + 1 : ℕ) : ℝ)) (by
    rw [nat_order_succ]
    exact f.property)⟩
  map_add' f g := by apply Sobolev.ext; exact derivative_add f.val g.val
  map_smul' z f := by apply Sobolev.ext; exact derivative_smul z f.val

def derivativeNatMap (n : ℕ) : Sobolev ((n + 2 : ℕ) : ℝ) →L[ℂ] Sobolev ((n + 1 : ℕ) : ℝ) :=
  (derivativeNatLinear n).mkContinuous 1 (fun f => by
    simp only [sobolev_norm, one_mul]
    have hf : InSobolev (((n + 1 : ℕ) : ℝ) + 1) f.val := by
      rw [nat_order_succ]
      exact f.property
    have hn := derivative_hNorm hf
    rw [nat_order_succ] at hn
    exact hn)

theorem derivativeNatMap_val (n : ℕ) (f : Sobolev ((n + 2 : ℕ) : ℝ)) :
    (derivativeNatMap n f).val = derivative f.val := rfl

def thirdDerivativeNatMap (n : ℕ) : Sobolev ((n + 4 : ℕ) : ℝ) →L[ℂ] Sobolev ((n + 1 : ℕ) : ℝ) :=
  (derivativeNatMap n).comp ((derivativeNatMap (n + 1)).comp (derivativeNatMap (n + 2)))

def physicalVectorField (n : ℕ) (f : Sobolev ((n + 4 : ℕ) : ℝ)) : Sobolev ((n + 1 : ℕ) : ℝ) :=
  -thirdDerivativeNatMap n f + (1 / 2 : ℂ) • derivativeNatMap n
    (productIntegerMap (n + 1)
      (inclusionMap ((n + 2 : ℕ) : ℝ) ((n + 4 : ℕ) : ℝ) (by push_cast; linarith) f)
      (inclusionMap ((n + 2 : ℕ) : ℝ) ((n + 4 : ℕ) : ℝ) (by push_cast; linarith) f))

theorem physicalVectorField_val (n : ℕ) (f : Sobolev ((n + 4 : ℕ) : ℝ)) :
    (physicalVectorField n f).val = physicalRHS f.val := rfl

theorem continuous_physicalVectorField (n : ℕ) : Continuous (physicalVectorField n) := by
  unfold physicalVectorField
  exact (thirdDerivativeNatMap n).continuous.neg.add
    ((continuous_const (y := (1 / 2 : ℂ))).smul ((derivativeNatMap n).continuous.comp
      (continuous_productIntegerMap (n + 1) (inclusionMap _ _ _).continuous (inclusionMap _ _ _).continuous)))

end KdV
