import Proof
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

def productCoefficientBilinear (k : ℤ) : Sobolev 0 →ₗ[ℂ] Sobolev 0 →ₗ[ℂ] ℂ where
  toFun f := {
    toFun g := product f.val g.val k
    map_add' g h := congrFun (product_add_right f.property g.property h.property) k
    map_smul' z g := congrFun (product_smul_right z f.val g.val) k }
  map_add' f g := by
    apply LinearMap.ext
    intro h
    exact congrFun (product_add_left f.property g.property h.property) k
  map_smul' z f := by
    apply LinearMap.ext
    intro g
    exact congrFun (product_smul_left z f.val g.val) k

def productCoefficientMap (k : ℤ) : Sobolev 0 →L[ℂ] Sobolev 0 →L[ℂ] ℂ :=
  (productCoefficientBilinear k).mkContinuous₂ 1 (fun f g => by
    simp only [sobolev_norm, one_mul]
    exact product_coeff_bound f.property g.property k)

theorem productCoefficientMap_apply (k : ℤ) (f g : Sobolev 0) :
    productCoefficientMap k f g = product f.val g.val k := rfl

theorem continuous_productCoefficientMap {X : Type*} [TopologicalSpace X] (k : ℤ)
    {f g : X → Sobolev 0} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => product (f x).val (g x).val k) :=
  ((productCoefficientMap k).continuous.comp hf).clm_apply hg

theorem continuous_BCoefficient {f g : ℝ → Sobolev 0} (hf : Continuous f) (hg : Continuous g) (k : ℤ) :
    Continuous (fun t : ℝ => B t (f t).val (g t).val k) := by
  have hp := continuous_productCoefficientMap k (continuous_airy_apply 0 continuous_id hf)
    (continuous_airy_apply 0 continuous_id hg)
  change Continuous (fun t : ℝ => Complex.exp (Complex.I * ((-t : ℝ) : ℂ) * (k : ℂ) ^ 3) *
    ((Complex.I * (k : ℂ)) * product (airy t (f t).val) (airy t (g t).val) k))
  have hE : Continuous (fun t : ℝ => Complex.exp (Complex.I * ((-t : ℝ) : ℂ) * (k : ℂ) ^ 3)) := by fun_prop
  exact hE.mul (continuous_const.mul hp)

end KdV
