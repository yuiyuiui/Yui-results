import IntegerProductBound
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

def productIntegerBilinear (n : ℕ) : Sobolev ((n + 1 : ℕ) : ℝ) →ₗ[ℂ]
    Sobolev ((n + 1 : ℕ) : ℝ) →ₗ[ℂ] Sobolev ((n + 1 : ℕ) : ℝ) where
  toFun f := {
    toFun g := ⟨product f.val g.val, integer_product_inSobolev n f.property g.property⟩
    map_add' g h := by
      apply Sobolev.ext
      exact product_add_right (f.property.of_le (by positivity)) (g.property.of_le (by positivity)) (h.property.of_le (by positivity))
    map_smul' z g := by apply Sobolev.ext; exact product_smul_right z f.val g.val }
  map_add' f g := by
    apply LinearMap.ext
    intro h
    apply Sobolev.ext
    exact product_add_left (f.property.of_le (by positivity)) (g.property.of_le (by positivity)) (h.property.of_le (by positivity))
  map_smul' z f := by
    apply LinearMap.ext
    intro g
    apply Sobolev.ext
    exact product_smul_left z f.val g.val

def productIntegerMap (n : ℕ) : Sobolev ((n + 1 : ℕ) : ℝ) →L[ℂ]
    Sobolev ((n + 1 : ℕ) : ℝ) →L[ℂ] Sobolev ((n + 1 : ℕ) : ℝ) :=
  (productIntegerBilinear n).mkContinuous₂ ((3 : ℝ) ^ n * (2 * h1EmbeddingConstant))
    (fun f g => by simp only [sobolev_norm]; exact integer_product_bound n f.property g.property)

theorem productIntegerMap_val (n : ℕ) (f g : Sobolev ((n + 1 : ℕ) : ℝ)) :
    (productIntegerMap n f g).val = product f.val g.val := rfl

theorem continuous_productIntegerMap {X : Type*} [TopologicalSpace X] (n : ℕ)
    {f g : X → Sobolev ((n + 1 : ℕ) : ℝ)} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun t => productIntegerMap n (f t) (g t)) := by
  exact ((productIntegerMap n).continuous.comp hf).clm_apply hg

end KdV
