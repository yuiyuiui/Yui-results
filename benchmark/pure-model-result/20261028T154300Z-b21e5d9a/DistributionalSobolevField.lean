import PhysicalVectorField
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

def negativeProductBilinear : Sobolev 0 →ₗ[ℂ] Sobolev 0 →ₗ[ℂ] Sobolev (-1) where
  toFun f := {
    toFun g := ⟨product f.val g.val, (negative_product_bound (q := 1) (by norm_num) f.property g.property).1⟩
    map_add' g h := by apply Sobolev.ext; exact product_add_right f.property g.property h.property
    map_smul' z g := by apply Sobolev.ext; exact product_smul_right z f.val g.val }
  map_add' f g := by
    apply LinearMap.ext
    intro h
    apply Sobolev.ext
    exact product_add_left f.property g.property h.property
  map_smul' z f := by
    apply LinearMap.ext
    intro g
    apply Sobolev.ext
    exact product_smul_left z f.val g.val

def negativeProductMap : Sobolev 0 →L[ℂ] Sobolev 0 →L[ℂ] Sobolev (-1) :=
  negativeProductBilinear.mkContinuous₂ (negativeProductConstant 1 (by norm_num))
    (fun f g => by simp only [sobolev_norm]; exact (negative_product_bound (q := 1) (by norm_num) f.property g.property).2)

def derivativeBetweenLinear (s r : ℝ) (h : r = s + 1) : Sobolev r →ₗ[ℂ] Sobolev s where
  toFun f := ⟨derivative f.val, derivative_inSobolev (s := s) (by rw [← h]; exact f.property)⟩
  map_add' f g := by apply Sobolev.ext; exact derivative_add f.val g.val
  map_smul' z f := by apply Sobolev.ext; exact derivative_smul z f.val

def derivativeBetweenMap (s r : ℝ) (h : r = s + 1) : Sobolev r →L[ℂ] Sobolev s :=
  (derivativeBetweenLinear s r h).mkContinuous 1 (fun f => by
    simp only [sobolev_norm, one_mul]
    have hf : InSobolev (s + 1) f.val := by rw [← h]; exact f.property
    have hn := derivative_hNorm hf
    rw [← h] at hn
    exact hn)

/-- Every term of the rough KdV equation lives in the actual complete H^-3
 space. This is a continuous polynomial map, with no additional regularity. -/
def physicalRoughField (f : Sobolev 0) : Sobolev (-3) :=
  -derivativeBetweenMap (-3) (-2) (by norm_num)
    (derivativeBetweenMap (-2) (-1) (by norm_num) (derivativeBetweenMap (-1) 0 (by norm_num) f)) +
    (1 / 2 : ℂ) • inclusionMap (-3) (-2) (by norm_num)
      (derivativeBetweenMap (-2) (-1) (by norm_num) (negativeProductMap f f))

theorem physicalRoughField_val (f : Sobolev 0) : (physicalRoughField f).val = physicalRHS f.val := rfl

theorem continuous_physicalRoughField : Continuous physicalRoughField := by
  unfold physicalRoughField
  have hp : Continuous (fun f : Sobolev 0 => negativeProductMap f f) :=
    (negativeProductMap.continuous.comp continuous_id).clm_apply continuous_id
  exact ((derivativeBetweenMap (-3) (-2) (by norm_num)).continuous.comp
    ((derivativeBetweenMap (-2) (-1) (by norm_num)).continuous.comp
      (derivativeBetweenMap (-1) 0 (by norm_num)).continuous)).neg.add
    ((continuous_const (y := (1 / 2 : ℂ))).smul ((inclusionMap (-3) (-2) (by norm_num)).continuous.comp
      ((derivativeBetweenMap (-2) (-1) (by norm_num)).continuous.comp hp)))

end KdV
