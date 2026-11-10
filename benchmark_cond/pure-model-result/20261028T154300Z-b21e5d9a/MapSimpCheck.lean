import Proof
noncomputable section
open KdV
example (f : ℝ → Sobolev 1) :
    (fun t : ℝ => (inclusionMap 0 1 (by norm_num) (f t)).val) = (fun t => (f t).val) := by
  simp only [inclusionMap_val]
example (f g : ℝ → Sobolev 1) (hf : Continuous f) (hg : Continuous g) (m : ℤ) :
    Continuous (fun t : ℝ => J t (f t).val (g t).val m) := by
  have h := (coefficientMap 1 m).continuous.comp (continuous_JZeroBundled continuous_id
        ((inclusionMap 0 1 (by norm_num)).continuous.comp hf)
        ((inclusionMap 0 1 (by norm_num)).continuous.comp hg))
  simp only [Function.comp_def, coefficientMap_apply, JZeroBundled_val, inclusionMap_val, id_eq] at h
  exact h
