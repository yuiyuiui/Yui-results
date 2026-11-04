import Proof
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

theorem derivative_add (f g : Fourier) : derivative (f + g) = derivative f + derivative g := by
  funext k
  simp [derivative, mul_add]

theorem derivative_smul (z : ℂ) (f : Fourier) : derivative (z • f) = z • derivative f := by
  funext k
  simp [derivative, mul_left_comm]

theorem derivative_sub (f g : Fourier) : derivative (f - g) = derivative f - derivative g := by
  funext k
  simp [derivative, mul_sub]

def derivativeLinear (s : ℝ) : Sobolev (s + 1) →ₗ[ℂ] Sobolev s where
  toFun f := ⟨derivative f.val, derivative_inSobolev f.property⟩
  map_add' f g := by apply Sobolev.ext; exact derivative_add f.val g.val
  map_smul' z f := by apply Sobolev.ext; exact derivative_smul z f.val

def derivativeMap (s : ℝ) : Sobolev (s + 1) →L[ℂ] Sobolev s :=
  (derivativeLinear s).mkContinuous 1 (fun f => by
    simp only [sobolev_norm, one_mul]
    change hNorm s (derivative f.val) ≤ hNorm (s + 1) f.val
    exact derivative_hNorm f.property)

def inverseDerivativeSameLinear (s : ℝ) : Sobolev s →ₗ[ℂ] Sobolev s where
  toFun f := ⟨inverseDerivative f.val, inverseDerivative_inSobolev_same f.property⟩
  map_add' f g := by apply Sobolev.ext; exact inverseDerivative_add f.val g.val
  map_smul' z f := by apply Sobolev.ext; exact inverseDerivative_smul z f.val

def inverseDerivativeSameMap (s : ℝ) : Sobolev s →L[ℂ] Sobolev s :=
  (inverseDerivativeSameLinear s).mkContinuous 1 (fun f => by
    simp only [sobolev_norm, one_mul]
    change hNorm s (inverseDerivative f.val) ≤ hNorm s f.val
    exact inverseDerivative_hNorm_same f.property)

def coefficientLinear (s : ℝ) (k : ℤ) : Sobolev s →ₗ[ℂ] ℂ where
  toFun f := f.val k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def coefficientMap (s : ℝ) (k : ℤ) : Sobolev s →L[ℂ] ℂ :=
  (coefficientLinear s k).mkContinuous (weight s k)⁻¹ (fun f => by
    have h := weighted_coeff_bound f.property k
    rw [norm_weighted] at h
    simp only [sobolev_norm]
    change ‖f.val k‖ ≤ (weight s k)⁻¹ * hNorm s f.val
    calc
      _ = (weight s k)⁻¹ * (weight s k * ‖f.val k‖) := by
        rw [← mul_assoc, inv_mul_cancel₀ (weight_pos s k).ne', one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (weight_pos s k).le))

def productTwoBilinear : Sobolev 2 →ₗ[ℂ] Sobolev 2 →ₗ[ℂ] Sobolev 2 where
  toFun f := {
    toFun g := ⟨product f.val g.val, (h2_product_bound f.property g.property).1⟩
    map_add' g h := by
      apply Sobolev.ext
      exact product_add_right (f.property.of_le (by norm_num))
        (g.property.of_le (by norm_num)) (h.property.of_le (by norm_num))
    map_smul' z g := by apply Sobolev.ext; exact product_smul_right z f.val g.val }
  map_add' f g := by
    apply LinearMap.ext
    intro h
    apply Sobolev.ext
    exact product_add_left (f.property.of_le (by norm_num))
      (g.property.of_le (by norm_num)) (h.property.of_le (by norm_num))
  map_smul' z f := by
    apply LinearMap.ext
    intro g
    apply Sobolev.ext
    exact product_smul_left z f.val g.val

def productTwoMap : Sobolev 2 →L[ℂ] Sobolev 2 →L[ℂ] Sobolev 2 :=
  productTwoBilinear.mkContinuous₂ (6 * h1EmbeddingConstant) (fun f g => by
    simp only [sobolev_norm]
    exact (h2_product_bound f.property g.property).2)

set_option maxHeartbeats 800000 in
theorem continuous_airy_apply {X : Type*} [TopologicalSpace X]
    (s : ℝ) {a : X → ℝ} {f : X → Sobolev s} (ha : Continuous a) (hf : Continuous f) :
    Continuous (fun x => airyMap s (a x) (f x)) :=
  (continuous_airy_action s).comp (ha.prodMk hf)

def JTwoBundled (t : ℝ) (f g : Sobolev 2) : Sobolev 2 :=
  airyMap 2 (-t) (removeMeanMap 2 (productTwoMap
    (airyMap 2 t (inverseDerivativeSameMap 2 f))
    (airyMap 2 t (inverseDerivativeSameMap 2 g))))

theorem JTwoBundled_val (t : ℝ) (f g : Sobolev 2) :
    (JTwoBundled t f g).val = J t f.val g.val := rfl

@[fun_prop] theorem continuous_JTwoBundled (f g : Sobolev 2) :
    Continuous (fun t : ℝ => JTwoBundled t f g) := by
  unfold JTwoBundled
  have hf' := continuous_airy_fixed 2 (inverseDerivativeSameMap 2 f)
  have hg' := continuous_airy_fixed 2 (inverseDerivativeSameMap 2 g)
  apply continuous_airy_apply 2 continuous_neg
  fun_prop

def stageTwoBundled (a t : ℝ) (f g : Sobolev 2) : Sobolev 2 :=
  (1 / 6 : ℂ) • (JTwoBundled t f g - JTwoBundled a f g)

theorem stageTwoBundled_val (a t : ℝ) (f g : Sobolev 2) :
    (stageTwoBundled a t f g).val = bilinearStage a t f.val g.val := rfl

@[fun_prop] theorem continuous_stageTwoBundled (a : ℝ) (f g : Sobolev 2) :
    Continuous (fun t : ℝ => stageTwoBundled a t f g) := by
  unfold stageTwoBundled
  fun_prop

def derivativeTwoLinear : Sobolev 2 →ₗ[ℂ] Sobolev 1 where
  toFun f := ⟨derivative f.val, derivative_inSobolev (s := 1) (by norm_num; exact f.property)⟩
  map_add' f g := by apply Sobolev.ext; exact derivative_add f.val g.val
  map_smul' z f := by apply Sobolev.ext; exact derivative_smul z f.val

def derivativeTwoMap : Sobolev 2 →L[ℂ] Sobolev 1 :=
  derivativeTwoLinear.mkContinuous 1 (fun f => by
    simp only [sobolev_norm, one_mul]
    change hNorm 1 (derivative f.val) ≤ hNorm 2 f.val
    have h := derivative_hNorm (s := 1) (by norm_num; exact f.property)
    norm_num at h
    exact h)

def BTwoBundled (t : ℝ) (f g : Sobolev 2) : Sobolev 1 :=
  airyMap 1 (-t) (derivativeTwoMap (productTwoMap (airyMap 2 t f) (airyMap 2 t g)))

theorem BTwoBundled_val (t : ℝ) (f g : Sobolev 2) :
    (BTwoBundled t f g).val = B t f.val g.val := rfl

theorem continuous_BTwoBundled {X : Type*} [TopologicalSpace X]
    {t : X → ℝ} {f g : X → Sobolev 2} (ht : Continuous t)
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => BTwoBundled (t x) (f x) (g x)) := by
  unfold BTwoBundled
  have hf' := continuous_airy_apply 2 ht hf
  have hg' := continuous_airy_apply 2 ht hg
  apply continuous_airy_apply 1 ht.neg
  fun_prop

theorem B_sub_left {f g h : Fourier} (hf : InSobolev 0 f) (hg : InSobolev 0 g)
    (hh : InSobolev 0 h) (t : ℝ) : B t (f - g) h = B t f h - B t g h := by
  unfold B
  rw [airy_sub, product_sub_left (airy_inSobolev hf t) (airy_inSobolev hg t)
    (airy_inSobolev hh t), derivative_sub, airy_sub]

theorem B_sub_right {f g h : Fourier} (hf : InSobolev 0 f) (hg : InSobolev 0 g)
    (hh : InSobolev 0 h) (t : ℝ) : B t f (g - h) = B t f g - B t f h := by
  rw [B_comm t f (g - h), B_sub_left hg hh hf, B_comm t g f, B_comm t h f]

theorem B_diagonal_sub {f g : Fourier} (hf : InSobolev 0 f) (hg : InSobolev 0 g)
    (t : ℝ) : B t f f - B t g g = B t (f - g) f + B t g (f - g) := by
  rw [B_sub_left hf hg hf, B_sub_right hg hf hg]
  abel

end KdV
