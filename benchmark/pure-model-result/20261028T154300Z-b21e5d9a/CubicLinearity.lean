import CubicIdentities
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

theorem product_add_left_summable {f g h : Fourier}
    (hf : ∀ k, Summable (fun a : ℤ => f a * h (k - a)))
    (hg : ∀ k, Summable (fun a : ℤ => g a * h (k - a))) :
    product (f + g) h = product f h + product g h := by
  funext k
  simpa only [product, Pi.add_apply, add_mul] using (hf k).tsum_add (hg k)

theorem product_add_right_summable {f g h : Fourier}
    (hg : ∀ k, Summable (fun a : ℤ => f a * g (k - a)))
    (hh : ∀ k, Summable (fun a : ℤ => f a * h (k - a))) :
    product f (g + h) = product f g + product f h := by
  funext k
  simpa only [product, Pi.add_apply, mul_add] using (hg k).tsum_add (hh k)

theorem CIntegrand_add_left {f l g h : Fourier}
    (hf : InSobolev 0 f) (hl : InSobolev 0 l) (hg : InSobolev 0 g) (hh : InSobolev 0 h) (t : ℝ) :
    CIntegrand t (f + l) g h = CIntegrand t f g h + CIntegrand t l g h := by
  have hout := product_add_left_summable
    (fun k => (CIntegrand_summable_bound hf hg hh t k).1)
    (fun k => (CIntegrand_summable_bound hl hg hh t k).1)
  unfold CIntegrand
  rw [airy_add, product_add_left (airy_inSobolev hf t) (airy_inSobolev hl t) (airy_inSobolev hg t),
    removeMean_add, hout, removeMean_add, airy_add]

theorem CIntegrand_comm (t : ℝ) (f g h : Fourier) : CIntegrand t f g h = CIntegrand t g f h := by
  unfold CIntegrand
  rw [product_comm (airy t f) (airy t g)]

theorem CIntegrand_add_middle {f g l h : Fourier}
    (hf : InSobolev 0 f) (hg : InSobolev 0 g) (hl : InSobolev 0 l) (hh : InSobolev 0 h) (t : ℝ) :
    CIntegrand t f (g + l) h = CIntegrand t f g h + CIntegrand t f l h := by
  rw [CIntegrand_comm t f (g + l), CIntegrand_add_left hg hl hf hh,
    CIntegrand_comm t g f, CIntegrand_comm t l f]

theorem CIntegrand_add_right {f g h l : Fourier}
    (hf : InSobolev 0 f) (hg : InSobolev 0 g) (hh : InSobolev 0 h) (hl : InSobolev 0 l) (t : ℝ) :
    CIntegrand t f g (h + l) = CIntegrand t f g h + CIntegrand t f g l := by
  have hout := product_add_right_summable
    (fun k => (CIntegrand_summable_bound hf hg hh t k).1)
    (fun k => (CIntegrand_summable_bound hf hg hl t k).1)
  unfold CIntegrand
  rw [inverseDerivative_add, airy_add, hout, removeMean_add, airy_add]

theorem CIntegrand_smul_left (t : ℝ) (z : ℂ) (f g h : Fourier) :
    CIntegrand t (z • f) g h = z • CIntegrand t f g h := by
  unfold CIntegrand
  rw [airy_smul, product_smul_left, removeMean_smul, product_smul_left, removeMean_smul, airy_smul]

theorem CIntegrand_smul_middle (t : ℝ) (z : ℂ) (f g h : Fourier) :
    CIntegrand t f (z • g) h = z • CIntegrand t f g h := by
  rw [CIntegrand_comm t f (z • g), CIntegrand_smul_left, CIntegrand_comm t g f]

theorem CIntegrand_smul_right (t : ℝ) (z : ℂ) (f g h : Fourier) :
    CIntegrand t f g (z • h) = z • CIntegrand t f g h := by
  unfold CIntegrand
  rw [inverseDerivative_smul, airy_smul, product_smul_right, removeMean_smul, airy_smul]

theorem CIntegral_static_add_left {f l g h : Fourier}
    (hf : InSobolev 0 f) (hl : InSobolev 0 l) (hg : InSobolev 0 g) (hh : InSobolev 0 h) (a b : ℝ) :
    CIntegral a b (fun _ => f + l) (fun _ => g) (fun _ => h) =
      CIntegral a b (fun _ => f) (fun _ => g) (fun _ => h) +
        CIntegral a b (fun _ => l) (fun _ => g) (fun _ => h) := by
  funext k
  simp_rw [CIntegral_eq_integrand, CIntegrand_add_left hf hl hg hh]
  exact intervalIntegral.integral_add
    ((continuous_CIntegrand_fixed hf hg hh k).intervalIntegrable a b)
    ((continuous_CIntegrand_fixed hl hg hh k).intervalIntegrable a b)

theorem CIntegral_static_comm (a b : ℝ) (f g h : Fourier) :
    CIntegral a b (fun _ => f) (fun _ => g) (fun _ => h) =
      CIntegral a b (fun _ => g) (fun _ => f) (fun _ => h) := by
  funext k
  simp_rw [CIntegral_eq_integrand, CIntegrand_comm _ f g h]

theorem CIntegral_static_add_middle {f g l h : Fourier}
    (hf : InSobolev 0 f) (hg : InSobolev 0 g) (hl : InSobolev 0 l) (hh : InSobolev 0 h) (a b : ℝ) :
    CIntegral a b (fun _ => f) (fun _ => g + l) (fun _ => h) =
      CIntegral a b (fun _ => f) (fun _ => g) (fun _ => h) +
        CIntegral a b (fun _ => f) (fun _ => l) (fun _ => h) := by
  rw [CIntegral_static_comm a b f (g + l), CIntegral_static_add_left hg hl hf hh,
    CIntegral_static_comm a b g f, CIntegral_static_comm a b l f]

theorem CIntegral_static_add_right {f g h l : Fourier}
    (hf : InSobolev 0 f) (hg : InSobolev 0 g) (hh : InSobolev 0 h) (hl : InSobolev 0 l) (a b : ℝ) :
    CIntegral a b (fun _ => f) (fun _ => g) (fun _ => h + l) =
      CIntegral a b (fun _ => f) (fun _ => g) (fun _ => h) +
        CIntegral a b (fun _ => f) (fun _ => g) (fun _ => l) := by
  funext k
  simp_rw [CIntegral_eq_integrand, CIntegrand_add_right hf hg hh hl]
  exact intervalIntegral.integral_add
    ((continuous_CIntegrand_fixed hf hg hh k).intervalIntegrable a b)
    ((continuous_CIntegrand_fixed hf hg hl k).intervalIntegrable a b)

end KdV
