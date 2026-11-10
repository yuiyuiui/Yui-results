import RealReconstruction
noncomputable section
open scoped ComplexConjugate ENNReal ComplexInnerProductSpace
open MeasureTheory
namespace KdV

theorem fourier_character_memLp_top (n : ℤ) : MemLp (fourier n : Torus → ℂ) ∞ normalizedMeasure := by
  exact (memLp_congr_ae (coeFn_fourierLp ∞ n)).mp (Lp.memLp (fourierLp ∞ n))

theorem character_product_memLp (n : ℤ) (F : Lp ℂ 2 normalizedMeasure) :
    MemLp (fun x : Torus => fourier n x * F x) 2 normalizedMeasure :=
  (Lp.memLp F).mul' (fourier_character_memLp_top n)

def characterMultiplyLp (n : ℤ) (F : Lp ℂ 2 normalizedMeasure) : Lp ℂ 2 normalizedMeasure :=
  (character_product_memLp n F).toLp _

theorem characterMultiplyLp_ae (n : ℤ) (F : Lp ℂ 2 normalizedMeasure) :
    characterMultiplyLp n F =ᵐ[normalizedMeasure] (fun x : Torus => fourier n x * F x) :=
  MemLp.coeFn_toLp _

theorem fourierCoeff_character_mul (n a : ℤ) (f : Torus → ℂ) :
    fourierCoeff (fun x => fourier n x * f x) a = fourierCoeff f (a - n) := by
  unfold fourierCoeff
  apply integral_congr_ae
  filter_upwards with x
  simp only [smul_eq_mul]
  rw [← mul_assoc, ← fourier_add]
  rw [show -a + n = -(a - n) by omega]

theorem fourierCoeff_characterMultiplyLp (n a : ℤ) (F : Lp ℂ 2 normalizedMeasure) :
    fourierCoeff (characterMultiplyLp n F) a = fourierCoeff F (a - n) := by
  calc
    _ = fourierCoeff (fun x : Torus => fourier n x * F x) a :=
      congrFun (fourierCoeff_congr_ae (characterMultiplyLp_ae n F)) a
    _ = _ := fourierCoeff_character_mul n a F

/-- The actual pointwise product of two normalized torus `L²` functions is
integrable, including for rough data. -/
theorem normalized_L2_product_integrable (F G : Lp ℂ 2 normalizedMeasure) :
    Integrable (fun x : Torus => F x * G x) normalizedMeasure := by
  have h : MemLp (fun x : Torus => F x * G x) 1 normalizedMeasure := (Lp.memLp G).mul' (Lp.memLp F)
  exact memLp_one_iff_integrable.mp h

theorem productCoeff_eq_inner (F G : Lp ℂ 2 normalizedMeasure) (k : ℤ) :
    fourierCoeff (fun x : Torus => F x * G x) k =
      inner ℂ (star F : Lp ℂ 2 normalizedMeasure) (characterMultiplyLp (-k) G) := by
  rw [MeasureTheory.L2.inner_def]
  unfold fourierCoeff
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star F, characterMultiplyLp_ae (-k) G] with x hx hxG
  rw [hx, hxG]
  simp only [smul_eq_mul, RCLike.inner_apply']
  change fourier (-k) x * (F x * G x) = conj (conj (F x)) * (fourier (-k) x * G x)
  rw [starRingEnd_self_apply]
  ring

/-- Exact convolution formula for every pair of `L²` inputs. The proof is
Parseval's identity in the pinned Fourier Hilbert basis, not a formal interchange
of conditionally convergent Fourier series. -/
theorem normalized_L2_product_coeff (F G : Lp ℂ 2 normalizedMeasure) (k : ℤ) :
    fourierCoeff (fun x : Torus => F x * G x) k =
      ∑' a : ℤ, fourierCoeff F a * fourierCoeff G (k - a) := by
  rw [productCoeff_eq_inner]
  calc
    _ = inner ℂ (fourierBasis.repr (star F : Lp ℂ 2 normalizedMeasure))
        (fourierBasis.repr (characterMultiplyLp (-k) G)) :=
      (fourierBasis.repr.inner_map_map _ _).symm
    _ = ∑' a : ℤ, conj (fourierCoeff (star F : Lp ℂ 2 normalizedMeasure) a) *
        fourierCoeff (characterMultiplyLp (-k) G) a := by
      rw [lp.inner_eq_tsum]
      apply tsum_congr
      intro a
      simp only [RCLike.inner_apply', fourierBasis_repr]
      rfl
    _ = ∑' a : ℤ, fourierCoeff F (-a) * fourierCoeff G (a + k) := by
      apply tsum_congr
      intro a
      rw [fourierCoeff_star_lp, starRingEnd_self_apply, fourierCoeff_characterMultiplyLp, sub_neg_eq_add]
    _ = _ := by
      simpa only [Equiv.neg_apply, sub_neg_eq_add, add_comm] using
        (Equiv.neg ℤ).tsum_eq (fun a : ℤ => fourierCoeff F a * fourierCoeff G (k - a))

/-- The raw product used in the method and PDE is the Fourier sequence of
physical multiplication, with the prescribed normalized measure. -/
theorem reconstructL2_product_coeff (f g : Sobolev 0) (k : ℤ) :
    fourierCoeff (fun x : Torus => reconstructL2 f x * reconstructL2 g x) k = product f.val g.val k := by
  rw [normalized_L2_product_coeff]
  apply tsum_congr
  intro a
  rw [reconstructL2_coeff, reconstructL2_coeff]

end KdV
