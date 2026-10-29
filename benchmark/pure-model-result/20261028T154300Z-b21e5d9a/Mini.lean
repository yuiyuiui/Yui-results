import Proof
noncomputable section
namespace KdV

def inclusionLinear (s r : ℝ) (hsr : s ≤ r) : Sobolev r →ₗ[ℂ] Sobolev s where
  toFun f := ⟨f.val, f.property.of_le hsr⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem inclusionLinear_val (s r : ℝ) (hsr : s ≤ r) (f : Sobolev r) :
    (inclusionLinear s r hsr f).val = f.val := by
  rfl

end KdV
