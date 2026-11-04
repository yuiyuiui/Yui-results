import Proof
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

theorem fourierCoeff_conjugate (f : Torus → ℂ) (k : ℤ) :
    fourierCoeff (fun x => conj (f x)) k = conj (fourierCoeff f (-k)) := by
  rw [fourierCoeff, fourierCoeff, ← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  simp only [smul_eq_mul, map_mul, neg_neg, fourier_neg]

theorem fourierCoeff_star_lp (F : Lp ℂ 2 normalizedMeasure) (k : ℤ) :
    fourierCoeff (star F : Lp ℂ 2 normalizedMeasure) k = conj (fourierCoeff F (-k)) := by
  calc
    _ = fourierCoeff (fun x => conj (F x)) k :=
      congrFun (fourierCoeff_congr_ae (Lp.coeFn_star F)) k
    _ = _ := fourierCoeff_conjugate F k

theorem normalized_L2_fourier_ext {F G : Lp ℂ 2 normalizedMeasure}
    (h : ∀ k : ℤ, fourierCoeff F k = fourierCoeff G k) : F = G := by
  apply fourierBasis.repr.injective
  apply Subtype.ext
  funext k
  rw [fourierBasis_repr, fourierBasis_repr]
  exact h k

/-- Conjugate symmetry of coefficients is actual reality of the reconstructed
normalized torus `L²` element, not an unrelated predicate on sequences. -/
theorem reconstructL2_star (f : Sobolev 0) (hf : RealValued f.val) :
    star (reconstructL2 f) = reconstructL2 f := by
  apply normalized_L2_fourier_ext
  intro k
  rw [fourierCoeff_star_lp, reconstructL2_coeff, reconstructL2_coeff, hf k]
  simp

theorem reconstructL2_real_ae (f : Sobolev 0) (hf : RealValued f.val) :
    ∀ᵐ x ∂normalizedMeasure, (reconstructL2 f x).im = 0 := by
  have h := Lp.coeFn_star (reconstructL2 f)
  rw [reconstructL2_star f hf] at h
  filter_upwards [h] with x hx
  change reconstructL2 f x = conj (reconstructL2 f x) at hx
  have hi := congrArg Complex.im hx
  simp only [Complex.conj_im] at hi
  linarith

theorem reconstructL2_integrable (f : Sobolev 0) : Integrable (reconstructL2 f) normalizedMeasure := by
  exact (Lp.memLp (reconstructL2 f)).integrable (by norm_num)

theorem reconstructL2_mean (f : Sobolev 0) :
    (∫ x : Torus, reconstructL2 f x ∂normalizedMeasure) = f.val 0 := by
  have h := reconstructL2_coeff f 0
  simpa [fourierCoeff, normalizedMeasure] using h

theorem reconstructL2_meanZero (f : Sobolev 0) (hf : MeanZero f.val) :
    (∫ x : Torus, reconstructL2 f x ∂normalizedMeasure) = 0 := by
  rw [reconstructL2_mean]
  exact hf


theorem real_ae_fourier_symmetry (F : Lp ℂ 2 normalizedMeasure)
    (hf : ∀ᵐ x ∂normalizedMeasure, (F x).im = 0) : RealValued (fourierCoeff F) := by
  have hconj : (fun x => conj (F x)) =ᵐ[normalizedMeasure] F := by
    filter_upwards [hf] with x hx
    apply Complex.ext
    · simp
    · simp [hx]
  have hc := fourierCoeff_congr_ae hconj
  intro k
  calc
    _ = fourierCoeff (fun x => conj (F x)) (-k) := (congrFun hc (-k)).symm
    _ = conj (fourierCoeff F (-(-k))) := fourierCoeff_conjugate F (-k)
    _ = _ := by rw [neg_neg]

theorem reconstructL2_real_iff (f : Sobolev 0) :
    RealValued f.val ↔ ∀ᵐ x ∂normalizedMeasure, (reconstructL2 f x).im = 0 := by
  constructor
  · exact reconstructL2_real_ae f
  · intro h
    have hr := real_ae_fourier_symmetry (reconstructL2 f) h
    intro k
    simpa only [reconstructL2_coeff] using hr k

end KdV
