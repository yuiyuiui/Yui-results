import CrossNormalFormBound
import SelfNormalFormBound
import CubicDefectEstimate
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

/-- The two integrated bilinear terms of the actual residual are small.
Their estimates follow from the proved normal forms and the moving-defect
trilinear bound, with no numerical higher norm in the constants. -/
theorem numerical_residual_bilinear_bounds (externalStep : LiWuStepIdentity)
    (externalStage : LiWuStageEstimate) (externalProduct : LiWuProductEstimate)
    (externalTrilinear : LiWuTrilinearEstimate)
    {T γ M : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ n : ℕ,
      0 < τ → τ ≤ 1 → ((n + 1 : ℕ) : ℝ) * τ ≤ T →
      ∀ f : Sobolev 2, RealValued f.val → MeanZero f.val →
      ∀ w : Fourier, InSobolev γ w → MeanZero w → hNorm γ w ≤ M → hNorm 0 (f.val - w) ≤ 1 →
        ∀ t ∈ Set.Icc ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ),
          let IC := fun k => ∫ s : ℝ in (n : ℝ) * τ..t,
            B s (interpolationRemainder τ ((n : ℝ) * τ) s f.val) (frozenZ ((n : ℝ) * τ) s f.val) k
          let IQ := fun k => ∫ s : ℝ in (n : ℝ) * τ..t,
            B s (interpolationRemainder τ ((n : ℝ) * τ) s f.val)
              (interpolationRemainder τ ((n : ℝ) * τ) s f.val) k
          InSobolev 0 IC ∧ hNorm 0 IC ≤ C * τ * (τ ^ γ + hNorm 0 (f.val - w)) ∧
          InSobolev 0 IQ ∧ hNorm 0 IQ ≤ C * τ * (τ ^ γ + hNorm 0 (f.val - w)) := by
  obtain ⟨Cn, hCn, hstage⟩ := numerical_stage_bounds externalStage hT hγ hγ1 hM
  obtain ⟨Cy, hCy, hL2⟩ := numerical_defect_l2_bound externalStage externalProduct externalTrilinear hT hγ hγ1 hM
  obtain ⟨Ci, hCi, hInv⟩ := numerical_defect_negative_bound externalStage externalProduct hT hγ hγ1 hM
  obtain ⟨Cd, hCd, hDeriv⟩ := numerical_defect_derivative_bound externalStage externalProduct hT hγ hγ1 hM
  obtain ⟨Ct, hCt, hCubic⟩ := numerical_cubic_defect_bound externalStep externalStage externalProduct
    externalTrilinear hT hγ hγ1 hM
  let K : ℝ := Real.sqrt 2 * h1EmbeddingConstant
  have hK : 0 ≤ K := mul_nonneg (Real.sqrt_nonneg _) (le_trans zero_le_one h1EmbeddingConstant_ge_one)
  let Mz : ℝ := M + 1 + 2 * Cn
  let My : ℝ := 2 * Cy
  have hMz : 0 ≤ Mz := by dsimp [Mz]; positivity
  have hMy : 0 ≤ My := by dsimp [My]; positivity
  let Cc : ℝ := K * Ci * Mz / 3 + K * Cd * Mz / 3 + Ct / 6
  let Cq : ℝ := K * Ci * My / 3 + (2 / 3 : ℝ) * K * Cd * My
  have hCc : 0 ≤ Cc := by dsimp [Cc]; positivity
  have hCq : 0 ≤ Cq := by dsimp [Cq]; positivity
  refine ⟨1 + Cc + Cq, by positivity, ?_⟩
  intro τ n hτ hτ1 hnT f hfr hfm w hw hwm hwM hδ t ht
  dsimp only
  let a : ℝ := (n : ℝ) * τ
  let Y := fun s => defectBundled externalStep τ hτ n s f hfr hfm
  let dY := fun s => defectDerivativeBundled externalStep τ hτ n s f hfr hfm
  let q : ℝ := τ ^ γ + hNorm 0 (f.val - w)
  have hq0 : 0 ≤ q := add_nonneg (Real.rpow_nonneg hτ.le γ) (hNorm_nonneg _ _)
  have hq2 : q ≤ 2 := by dsimp [q]; linarith [Real.rpow_le_one hτ.le hτ1 hγ.le]
  have hval (s : ℝ) : (Y s).val = interpolationRemainder τ a s f.val :=
    defectBundled_val externalStep τ hτ n s f hfr hfm
  have hdval (s : ℝ) : (dY s).val = interpolationRemainderDerivative τ a s f.val := rfl
  have hYC := continuous_defectBundled externalStep τ hτ n f hfr hfm
  have hdYC := continuous_defectDerivativeBundled externalStep τ hτ n f hfr hfm
  have hSub (s : ℝ) (hs : s ∈ Set.Icc a t) :
      s ∈ Set.Icc ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ) := ⟨hs.1, hs.2.trans ht.2⟩
  have hd : ∀ s ∈ Set.Ioo a t, ∀ k : ℤ,
      HasDerivAt (fun r : ℝ => (Y r).val k) ((dY s).val k) s := by
    intro s _ k
    simp_rw [hval, hdval]
    exact interpolationRemainder_hasDerivAt f hfm k
  have hm : ∀ s ∈ Set.Icc a t, MeanZero (Y s).val := by
    intro s _
    rw [hval]
    exact interpolationRemainder_meanZero τ a s hfm
  have hleft : (Y a).val = 0 := by
    rw [hval]
    unfold interpolationRemainder
    rw [localInterpolation_left, bilinearStage_self, add_zero, sub_self]
  have hY : ∀ s ∈ Set.Icc a t, hNorm 0 (Y s).val ≤ My := by
    intro s hs
    rw [hval]
    exact ((hL2 τ n hτ hτ1 hnT f hfm w hw hwm hwM hδ s (hSub s hs)).2).trans
      (by simpa only [My, mul_comm] using mul_le_mul_of_nonneg_left hq2 hCy.le)
  have hIb : hNorm 0 (inverseDerivative (Y t).val) ≤ Ci * τ * q := by
    rw [hval]
    exact (hInv τ n hτ hτ1 hnT f hfm w hw hwm hwM hδ t ht).2.1
  have hId : ∀ s ∈ Set.Icc a t, hNorm 0 (inverseDerivative (dY s).val) ≤ Cd * q := by
    intro s hs
    rw [hdval]
    exact (hDeriv τ n hτ hτ1 hnT f hfm w hw hwm hwM hδ s (hSub s hs)).2.1
  have hf0 := f.property.of_le (by norm_num : (0 : ℝ) ≤ 2)
  have hfM : hNorm 0 f.val ≤ M + 1 := by
    have hw0 := hw.of_le hγ.le
    have hh := hNorm_add_le (hf0.sub hw0) hw0
    rw [sub_add_cancel] at hh
    have hwM0 := (hNorm_mono hw hγ.le).trans hwM
    linarith
  have hZ : ∀ s ∈ Set.Icc a t, hNorm 0 (frozenZ a s f.val) ≤ Mz := by
    intro s hs
    have hF0 := (bilinearStage_h1_bound hf0 hf0 a s).1.of_le (by norm_num : (0 : ℝ) ≤ 1)
    have hFb := (hstage τ n s hτ hτ1 hnT (hSub s hs) f.val w hf0 hw hwm hwM hδ).2.2.2
    have hFb' : hNorm 0 (bilinearStage a s f.val f.val) ≤ 2 * Cn :=
      hFb.trans (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hq2 hCn.le)
    have hh := hNorm_add_le hf0 hF0
    change hNorm 0 (frozenZ a s f.val) ≤ _ at hh
    dsimp [Mz]
    linarith only [hh, hfM, hFb']
  obtain ⟨hCI, hCIn⟩ := hCubic τ n hτ hτ1 hnT f hfr hfm w hw hwm hwM hδ t ht
  have hCI' : InSobolev 0 (CIntegral a t (fun _ => f.val) (fun _ => f.val) (fun s => (Y s).val)) := by
    simpa only [hval] using hCI
  have hCIn' : hNorm 0 (CIntegral a t (fun _ => f.val) (fun _ => f.val) (fun s => (Y s).val)) ≤ Ct * τ * q := by
    simpa only [hval] using hCIn
  obtain ⟨hCross, hCrossN⟩ := integral_B_cross_bound ht.1
    (mul_nonneg (mul_nonneg hCi.le hτ.le) hq0) (mul_nonneg hCd.le hq0) hMz
    f hfm Y dY hYC hdYC hd hm hleft hZ hIb hId hCI' hCIn'
  obtain ⟨hSelf, hSelfN⟩ := integral_B_self_bound ht.1
    (mul_nonneg (mul_nonneg hCi.le hτ.le) hq0) (mul_nonneg hCd.le hq0) hMy
    Y dY hYC hdYC hd hm hleft hY hIb hId
  have hCrossN' : hNorm 0 (fun k => ∫ s : ℝ in a..t, B s (Y s).val (frozenZ a s f.val) k) ≤
      Cc * τ * q := by
    calc
      _ ≤ K * (Ci * τ * q) * Mz / 3 + K * (Cd * q) * Mz * (t - a) / 3 + (Ct * τ * q) / 6 := hCrossN
      _ ≤ K * (Ci * τ * q) * Mz / 3 + K * (Cd * q) * Mz * τ / 3 + (Ct * τ * q) / 6 := by
        gcongr
        exact grid_interval_length n ht
      _ = _ := by dsimp [Cc]; ring
  have hSelfN' : hNorm 0 (fun k => ∫ s : ℝ in a..t, B s (Y s).val (Y s).val k) ≤ Cq * τ * q := by
    calc
      _ ≤ K * (Ci * τ * q) * My / 3 + (2 / 3 : ℝ) * K * (Cd * q) * My * (t - a) := hSelfN
      _ ≤ K * (Ci * τ * q) * My / 3 + (2 / 3 : ℝ) * K * (Cd * q) * My * τ := by
        gcongr
        exact grid_interval_length n ht
      _ = _ := by dsimp [Cq]; ring
  have hCC : Cc ≤ 1 + Cc + Cq := by linarith
  have hCQ : Cq ≤ 1 + Cc + Cq := by linarith
  have hc := hCrossN'.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC hτ.le) hq0)
  have hs := hSelfN'.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCQ hτ.le) hq0)
  simpa only [hval, a, q] using And.intro hCross (And.intro hc (And.intro hSelf hs))

end KdV
