import AlgebraOps
noncomputable section
open scoped ComplexConjugate ENNReal
namespace KdV

theorem inverseDerivative_sub (f g : Fourier) :
    inverseDerivative (f - g) = inverseDerivative f - inverseDerivative g := by
  funext k
  by_cases hk : k = 0 <;> simp [inverseDerivative, hk, mul_sub]

theorem removeMean_sub (f g : Fourier) : removeMean (f - g) = removeMean f - removeMean g := by
  funext k
  by_cases hk : k = 0 <;> simp [removeMean, hk]

theorem J_sub_left {f g h : Fourier} (hf : InSobolev 0 f) (hg : InSobolev 0 g)
    (hh : InSobolev 0 h) (t : ℝ) : J t (f - g) h = J t f h - J t g h := by
  have hfi := airy_inSobolev ((inverseDerivative_inSobolev_one hf).of_le (by norm_num : (0 : ℝ) ≤ 1)) t
  have hgi := airy_inSobolev ((inverseDerivative_inSobolev_one hg).of_le (by norm_num : (0 : ℝ) ≤ 1)) t
  have hhi := airy_inSobolev ((inverseDerivative_inSobolev_one hh).of_le (by norm_num : (0 : ℝ) ≤ 1)) t
  unfold J
  rw [inverseDerivative_sub, airy_sub]
  have hp : product (airy t (inverseDerivative f) - airy t (inverseDerivative g))
      (airy t (inverseDerivative h)) =
      product (airy t (inverseDerivative f)) (airy t (inverseDerivative h)) -
        product (airy t (inverseDerivative g)) (airy t (inverseDerivative h)) := by
    funext k
    unfold product
    simp only [Pi.sub_apply, sub_mul]
    exact (product_summable hfi hhi k).tsum_sub (product_summable hgi hhi k)
  rw [hp, removeMean_sub, airy_sub]

theorem J_sub_right {f g h : Fourier} (hf : InSobolev 0 f) (hg : InSobolev 0 g)
    (hh : InSobolev 0 h) (t : ℝ) : J t f (g - h) = J t f g - J t f h := by
  rw [J_comm t f (g - h), J_sub_left hg hh hf, J_comm t g f, J_comm t h f]

theorem bilinearStage_sub_left {f g h : Fourier} (hf : InSobolev 0 f) (hg : InSobolev 0 g)
    (hh : InSobolev 0 h) (a t : ℝ) :
    bilinearStage a t (f - g) h = bilinearStage a t f h - bilinearStage a t g h := by
  unfold bilinearStage
  rw [J_sub_left hf hg hh, J_sub_left hf hg hh]
  module

theorem bilinearStage_sub_right {f g h : Fourier} (hf : InSobolev 0 f) (hg : InSobolev 0 g)
    (hh : InSobolev 0 h) (a t : ℝ) :
    bilinearStage a t f (g - h) = bilinearStage a t f g - bilinearStage a t f h := by
  unfold bilinearStage
  rw [J_sub_right hf hg hh, J_sub_right hf hg hh]
  module

/-- Exact polarization of the stage; the numerical input needs only `L²`. -/
theorem bilinearStage_diagonal_sub {f w : Fourier} (hf : InSobolev 0 f) (hw : InSobolev 0 w)
    (a t : ℝ) : bilinearStage a t f f - bilinearStage a t w w =
      bilinearStage a t (f - w) f + bilinearStage a t w (f - w) := by
  rw [bilinearStage_sub_left hf hw hf, bilinearStage_sub_right hw hf hw]
  abel

theorem bilinearStage_diagonal_lipschitz {f w : Fourier} (hf : InSobolev 0 f) (hw : InSobolev 0 w)
    (a t : ℝ) :
    hNorm 1 (bilinearStage a t f f - bilinearStage a t w w) ≤
      ((4 / 3 : ℝ) * h1EmbeddingConstant) * (hNorm 0 f + hNorm 0 w) * hNorm 0 (f - w) := by
  rw [bilinearStage_diagonal_sub hf hw]
  obtain ⟨hm₁, hn₁⟩ := bilinearStage_h1_bound (hf.sub hw) hf a t
  obtain ⟨hm₂, hn₂⟩ := bilinearStage_h1_bound hw (hf.sub hw) a t
  calc
    _ ≤ hNorm 1 (bilinearStage a t (f - w) f) + hNorm 1 (bilinearStage a t w (f - w)) :=
      hNorm_add_le hm₁ hm₂
    _ ≤ _ := by nlinarith

end KdV
