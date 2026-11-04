import ExternalBridges
noncomputable section
open KdV
namespace BareModelCompletion

theorem J_shift (a r : ℝ) (f g : Fourier) :
    airy (-a) (J r (airy a f) (airy a g)) = J (a + r) f g := by
  simp only [J, inverseDerivative_airy, ← airy_add_time]
  rw [show -a + -r = -(a + r) by ring, show r + a = a + r by ring]

theorem source_stage_shift (a t : ℝ) (f g : Fourier) :
    sourceBilinearStage a t f g =
      airy (-a) (sourceBilinearStage 0 (t - a) (airy a f) (airy a g)) := by
  simp only [← bilinearStage_eq_source, bilinearStage, airy_smul, airy_sub, J_shift]
  rw [show a + (t - a) = t by ring, add_zero]

theorem source_stage_power_nonneg {γ ε β : ℝ} (hγ : 0 < γ) (_hγ1 : γ ≤ 1)
    (hε : 0 < ε) (hβ : β ≤ 1 + γ) : 0 ≤ sourceStagePower γ ε β := by
  have hd : 0 < 1 + γ - sourceStageLower γ ε := by
    unfold sourceStageLower
    split_ifs <;> linarith
  exact div_nonneg (by linarith) hd.le

/-- Preserve the source's complete-grid quantification. An arbitrary shorter
step is embedded in a grid with the *same* T; its grid step is between tau and
2*tau. Airy conjugation moves its start to grid point zero. -/
theorem stage_grid_to_historical (h : LiWuLemma72Grid) : LiWuStageEstimate := by
  intro T hT γ hγ hγ1 ε hε β hb hb1
  obtain ⟨C, hC, hbound⟩ := h T hT γ hγ hγ1 ε hε β hb hb1
  let q := sourceStagePower γ ε β
  have hq : 0 ≤ q := source_stage_power_nonneg hγ hγ1 hε hb1
  refine ⟨C * (2 : ℝ) ^ q, mul_pos hC (Real.rpow_pos_of_pos (by norm_num) _), ?_⟩
  intro τ n t hτ hn ht f g hf hg hfm hgm
  have hτT : τ ≤ T := by
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    push_cast at hn
    nlinarith
  have hx : 1 ≤ T / τ := (le_div_iff₀ hτ).mpr (by simpa using hτT)
  let L := ⌊T / τ⌋₊
  have hL : 0 < L := Nat.floor_pos.mpr hx
  have hLr : 0 < (L : ℝ) := by exact_mod_cast hL
  have hL1 : 1 ≤ (L : ℝ) := by exact_mod_cast hL
  have hfloor : (L : ℝ) ≤ T / τ := Nat.floor_le (by positivity)
  have hfloor2 : T / τ < (L : ℝ) + 1 := Nat.lt_floor_add_one _
  let θ := T / (L : ℝ)
  have hθ : 0 < θ := div_pos hT hLr
  have hτθ : τ ≤ θ := by
    apply (le_div_iff₀ hLr).mpr
    have hh := (le_div_iff₀ hτ).mp hfloor
    nlinarith
  have hθτ : θ ≤ 2 * τ := by
    apply (div_le_iff₀ hLr).mpr
    have hh : T / τ ≤ 2 * (L : ℝ) := by linarith
    have hh' := (div_le_iff₀ hτ).mp hh
    nlinarith
  let a := (n : ℝ) * τ
  have ht0 : t - a ∈ Set.Icc (0 : ℝ) θ := by
    have h1 := ht.1
    have h2 := ht.2
    push_cast at h2
    constructor <;> dsimp [a] <;> linarith
  have hfm' : MeanZero (airy a f) := by simpa only [MeanZero, airy_mean] using hfm
  have hgm' : MeanZero (airy a g) := by simpa only [MeanZero, airy_mean] using hgm
  have hz := hbound L hL 0 hL (t - a)
  simp only [Nat.cast_zero, zero_mul, Nat.zero_add, Nat.cast_one, one_mul] at hz
  obtain ⟨hm, hbnd⟩ := hz ht0 (airy a f) (airy a g) (airy_inSobolev hf a) (airy_inSobolev hg a) hfm' hgm'
  have hmember := airy_inSobolev hm (-a)
  rw [← source_stage_shift] at hmember
  refine ⟨hmember, ?_⟩
  have hnrm : sourceNorm β (sourceBilinearStage a t f g) =
      sourceNorm β (sourceBilinearStage 0 (t - a) (airy a f) (airy a g)) := by
    rw [source_stage_shift]
    simp only [sourceNorm, airy_hNorm]
  change sourceNorm β (sourceBilinearStage a t f g) ≤ _
  rw [hnrm]
  simp only [sourceNorm, airy_hNorm] at hbnd
  change sourceNorm β (sourceBilinearStage 0 (t - a) (airy a f) (airy a g)) ≤
    C * θ ^ q * sourceNorm γ f * sourceNorm γ g at hbnd
  have hpow : θ ^ q ≤ (2 : ℝ) ^ q * τ ^ q := by
    calc
      _ ≤ (2 * τ) ^ q := Real.rpow_le_rpow hθ.le hθτ hq
      _ = _ := Real.mul_rpow (by norm_num) hτ.le
  have hnf : 0 ≤ sourceNorm γ f := mul_nonneg sourceNormalization_pos.le (hNorm_nonneg _ _)
  have hng : 0 ≤ sourceNorm γ g := mul_nonneg sourceNormalization_pos.le (hNorm_nonneg _ _)
  calc
    _ ≤ C * θ ^ q * sourceNorm γ f * sourceNorm γ g := hbnd
    _ ≤ C * ((2 : ℝ) ^ q * τ ^ q) * sourceNorm γ f * sourceNorm γ g :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC.le) hnf) hng
    _ = _ := by ring

end BareModelCompletion
