import Proof
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

/-- A proof-only Fourier support condition. It does not occur in the method. -/
def SupportedIn (m : ℕ) (f : Fourier) : Prop :=
  ∀ k : ℤ, k ∉ Finset.Icc (-(m : ℤ)) (m : ℤ) → f k = 0

theorem supportedIn_cutoff (m : ℕ) (f : Fourier) : SupportedIn m (cutoff m f) := by
  intro k hk
  exact if_neg hk

theorem SupportedIn.airy {m : ℕ} {f : Fourier} (hf : SupportedIn m f) (t : ℝ) :
    SupportedIn m (airy t f) := by
  intro k hk
  simp only [KdV.airy, hf k hk, mul_zero]

theorem SupportedIn.removeMean {m : ℕ} {f : Fourier} (hf : SupportedIn m f) :
    SupportedIn m (removeMean f) := by
  intro k hk
  by_cases hk0 : k = 0
  · simp [KdV.removeMean, hk0]
  · simp only [KdV.removeMean, if_neg hk0, hf k hk]

theorem SupportedIn.inverseDerivative {m : ℕ} {f : Fourier} (hf : SupportedIn m f) :
    SupportedIn m (inverseDerivative f) := by
  intro k hk
  by_cases hk0 : k = 0
  · simp [KdV.inverseDerivative, hk0]
  · simp only [KdV.inverseDerivative, if_neg hk0, hf k hk, mul_zero]

theorem SupportedIn.product {m n : ℕ} {f g : Fourier}
    (hf : SupportedIn m f) (hg : SupportedIn n g) : SupportedIn (m + n) (product f g) := by
  intro k hk
  have heq (a : ℤ) : f a * g (k - a) = 0 := by
    by_cases ha : a ∈ Finset.Icc (-(m : ℤ)) (m : ℤ)
    · have hga : k - a ∉ Finset.Icc (-(n : ℤ)) (n : ℤ) := by
        intro hga
        apply hk
        simp only [Finset.mem_Icc, Nat.cast_add] at ha hga ⊢
        constructor <;> omega
      rw [hg (k - a) hga, mul_zero]
    · rw [hf a ha, zero_mul]
  simp only [KdV.product, heq, tsum_zero]

theorem SupportedIn.CIntegrand {m n l : ℕ} {f g h : Fourier}
    (hf : SupportedIn m f) (hg : SupportedIn n g) (hh : SupportedIn l h) (t : ℝ) :
    SupportedIn (m + n + l) (CIntegrand t f g h) := by
  have hinner := ((hf.airy t).product (hg.airy t)).removeMean
  have houter := hinner.product (hh.inverseDerivative.airy t)
  exact houter.removeMean.airy (-t)

theorem CIntegral_cutoff_supported (m : ℕ) (a b : ℝ) (f g h : ℝ → Fourier) :
    SupportedIn (3 * m) (CIntegral a b (fun t => cutoff m (f t))
      (fun t => cutoff m (g t)) (fun t => cutoff m (h t))) := by
  intro k hk
  have hm : m + m + m = 3 * m := by omega
  change (∫ t : ℝ in a..b, CIntegrand t (cutoff m (f t)) (cutoff m (g t)) (cutoff m (h t)) k) = 0
  have heq : (fun t : ℝ => CIntegrand t (cutoff m (f t)) (cutoff m (g t)) (cutoff m (h t)) k) =
      (fun _ : ℝ => (0 : ℂ)) := by
    funext t
    exact (SupportedIn.CIntegrand (supportedIn_cutoff m (f t)) (supportedIn_cutoff m (g t))
      (supportedIn_cutoff m (h t)) t) k (by simpa only [hm] using hk)
  rw [heq, intervalIntegral.integral_zero]

theorem SupportedIn.highCutoff_eq_zero {m : ℕ} {f : Fourier} (hf : SupportedIn m f) :
    highCutoff m f = 0 := by
  funext k
  by_cases hk : k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ)
  · simp [highCutoff, cutoff, hk]
  · simp [highCutoff, cutoff, hk, hf k hk]

theorem high_output_all_low_zero (m : ℕ) (a b : ℝ) (f g h : ℝ → Fourier) :
    highCutoff (3 * m) (CIntegral a b (fun t => cutoff m (f t))
      (fun t => cutoff m (g t)) (fun t => cutoff m (h t))) = 0 :=
  (CIntegral_cutoff_supported m a b f g h).highCutoff_eq_zero

theorem cutoff_smul (m : ℕ) (z : ℂ) (f : Fourier) : cutoff m (z • f) = z • cutoff m f := by
  funext k
  by_cases hk : k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ) <;> simp [cutoff, hk]

def cutoffLinear (s : ℝ) (m : ℕ) : Sobolev s →ₗ[ℂ] Sobolev s where
  toFun f := ⟨cutoff m f.val, cutoff_inSobolev f.property m⟩
  map_add' f g := by apply Sobolev.ext; exact cutoff_add m f.val g.val
  map_smul' z f := by apply Sobolev.ext; exact cutoff_smul m z f.val

def cutoffMap (s : ℝ) (m : ℕ) : Sobolev s →L[ℂ] Sobolev s :=
  (cutoffLinear s m).mkContinuous 1 (fun f => by
    simp only [sobolev_norm, one_mul]
    change hNorm s (cutoff m f.val) ≤ hNorm s f.val
    exact cutoff_hNorm_le f.property m)

def highCutoffMap (s : ℝ) (m : ℕ) : Sobolev s →L[ℂ] Sobolev s :=
  ContinuousLinearMap.id ℂ (Sobolev s) - cutoffMap s m

theorem cutoffMap_val (s : ℝ) (m : ℕ) (f : Sobolev s) : (cutoffMap s m f).val = cutoff m f.val := rfl

theorem highCutoffMap_val (s : ℝ) (m : ℕ) (f : Sobolev s) :
    (highCutoffMap s m f).val = highCutoff m f.val := rfl

theorem highCutoff_hNorm_le {s : ℝ} {f : Fourier} (hf : InSobolev s f) (m : ℕ) :
    hNorm s (highCutoff m f) ≤ hNorm s f := by
  simpa only [sub_self, weight, zero_div, Real.rpow_zero, one_mul] using high_cutoff_bound (s := s) le_rfl hf m |>.2

theorem cutoffMap_norm_le (s : ℝ) (m : ℕ) (f : Sobolev s) : ‖cutoffMap s m f‖ ≤ ‖f‖ := by
  rw [sobolev_norm, sobolev_norm, cutoffMap_val]
  exact cutoff_hNorm_le f.property m

theorem highCutoffMap_norm_le (s : ℝ) (m : ℕ) (f : Sobolev s) : ‖highCutoffMap s m f‖ ≤ ‖f‖ := by
  rw [sobolev_norm, sobolev_norm, highCutoffMap_val]
  exact highCutoff_hNorm_le f.property m

theorem WeakTimeDerivative.cutoff {a b : ℝ} {f df : ℝ → Fourier}
    (hf : WeakTimeDerivative a b f df) (m : ℕ) :
    WeakTimeDerivative a b (fun t => cutoff m (f t)) (fun t => cutoff m (df t)) := by
  intro k φ hφ hsupp hs
  by_cases hk : k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ)
  · simpa only [KdV.cutoff, if_pos hk] using hf k φ hφ hsupp hs
  · simp only [KdV.cutoff, if_neg hk, mul_zero, intervalIntegral.integral_zero, neg_zero]

theorem WeakTimeDerivative.highCutoff {a b : ℝ} {f df : ℝ → Fourier}
    (hf : WeakTimeDerivative a b f df) (m : ℕ) :
    WeakTimeDerivative a b (fun t => highCutoff m (f t)) (fun t => highCutoff m (df t)) := by
  intro k φ hφ hsupp hs
  by_cases hk : k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ)
  · simp only [KdV.highCutoff, Pi.sub_apply, KdV.cutoff, if_pos hk, sub_self, mul_zero,
      intervalIntegral.integral_zero, neg_zero]
  · simpa only [KdV.highCutoff, Pi.sub_apply, KdV.cutoff, if_neg hk, sub_zero] using hf k φ hφ hsupp hs

end KdV
