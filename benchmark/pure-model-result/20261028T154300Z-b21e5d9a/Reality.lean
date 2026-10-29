import Proof
noncomputable section
open scoped ComplexConjugate
namespace KdV

theorem RealValued.add {f g : Fourier} (hf : RealValued f) (hg : RealValued g) :
    RealValued (f + g) := by
  intro k
  simp only [Pi.add_apply, hf k, hg k, map_add]

theorem RealValued.sub {f g : Fourier} (hf : RealValued f) (hg : RealValued g) :
    RealValued (f - g) := by
  intro k
  simp only [Pi.sub_apply, hf k, hg k, map_sub]

theorem RealValued.real_smul {f : Fourier} (hf : RealValued f) (r : ℝ) :
    RealValued ((r : ℂ) • f) := by
  intro k
  simp [Pi.smul_apply, hf k]

theorem RealValued.smul {f : Fourier} (hf : RealValued f) {z : ℂ} (hz : conj z = z) :
    RealValued (z • f) := by
  intro k
  simp [Pi.smul_apply, hf k, hz]

theorem RealValued.product {f g : Fourier} (hf : RealValued f) (hg : RealValued g) :
    RealValued (KdV.product f g) := by
  intro k
  change (∑' a : ℤ, f a * g (-k - a)) = conj (∑' a : ℤ, f a * g (k - a))
  rw [RCLike.conj_tsum]
  calc
    (∑' a : ℤ, f a * g (-k - a)) = ∑' a : ℤ, f (-a) * g (-k - -a) :=
      (Equiv.neg ℤ).tsum_eq (fun a : ℤ => f a * g (-k - a)) |>.symm
    _ = ∑' a : ℤ, conj (f a * g (k - a)) := by
      apply tsum_congr
      intro a
      rw [show -k - -a = -(k - a) by ring, hf a, hg (k - a), map_mul]

theorem RealValued.airy {f : Fourier} (hf : RealValued f) (t : ℝ) :
    RealValued (KdV.airy t f) := by
  intro k
  simp only [KdV.airy, hf k, map_mul, ← Complex.exp_conj, map_pow, map_intCast,
    Complex.conj_I, Complex.conj_ofReal, Int.cast_neg]
  congr 2
  ring

theorem RealValued.inverseDerivative {f : Fourier} (hf : RealValued f) :
    RealValued (KdV.inverseDerivative f) := by
  intro k
  by_cases hk : k = 0
  · simp [hk, KdV.inverseDerivative]
  · simp [KdV.inverseDerivative, hk, hf k, map_mul, map_inv₀]

theorem RealValued.removeMean {f : Fourier} (hf : RealValued f) :
    RealValued (KdV.removeMean f) := by
  intro k
  by_cases hk : k = 0 <;> simp [KdV.removeMean, hk, hf k]

theorem RealValued.mean {f : Fourier} (hf : RealValued f) : conj (KdV.mean f) = KdV.mean f := by
  exact (hf 0).symm

theorem RealValued.quadratic {f : Fourier} (hf : RealValued f) (τ : ℝ) :
    RealValued (KdV.quadratic τ f) := by
  unfold KdV.quadratic
  exact ((hf.inverseDerivative.airy τ).product (hf.inverseDerivative.airy τ)).removeMean.smul
    (by simp [map_ofNat]) |>.sub ((hf.inverseDerivative.product hf.inverseDerivative).removeMean.airy τ |>.smul
      (by simp [map_ofNat]))

theorem RealValued.cubicBoundary {f : Fourier} (hf : RealValued f) (τ s : ℝ) :
    RealValued (KdV.cubicBoundary τ s f) := by
  exact (((hf.inverseDerivative.airy s).product (hf.inverseDerivative.airy s)).product
    (hf.inverseDerivative.airy s)).inverseDerivative.airy (τ - s)

theorem RealValued.lastBoundary {f : Fourier} (hf : RealValued f) (τ s : ℝ) :
    RealValued (KdV.lastBoundary τ s f) := by
  exact (((hf.quadratic τ).inverseDerivative.inverseDerivative.airy (s - τ)).product
    (hf.inverseDerivative.airy s)).inverseDerivative.inverseDerivative.airy (τ - s)

theorem RealValued.cubicCorrection {f : Fourier} (hf : RealValued f) (τ : ℝ) :
    RealValued (KdV.cubicCorrection τ f) := by
  unfold KdV.cubicCorrection
  apply RealValued.sub
  · apply RealValued.sub
    · apply RealValued.add
      · exact ((hf.inverseDerivative.airy τ).product (hf.quadratic τ).inverseDerivative).removeMean.smul
          (by simp [map_ofNat])
      · exact (hf.inverseDerivative.airy τ).smul (by simp [map_ofNat, hf.product hf |>.mean])
    · exact ((hf.cubicBoundary τ τ).sub (hf.cubicBoundary τ 0)).smul (by simp [map_ofNat])
  · exact ((hf.lastBoundary τ τ).sub (hf.lastBoundary τ 0)).smul (by simp [map_ofNat])

theorem RealValued.step {f : Fourier} (hf : RealValued f) (τ : ℝ) : RealValued (KdV.step τ f) :=
  ((hf.airy τ).add (hf.quadratic τ)).add (hf.cubicCorrection τ)

theorem RealValued.numerical {f : Fourier} (hf : RealValued f) (τ : ℝ) (n : ℕ) :
    RealValued (KdV.numerical τ f n) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact ih.step τ

end KdV
