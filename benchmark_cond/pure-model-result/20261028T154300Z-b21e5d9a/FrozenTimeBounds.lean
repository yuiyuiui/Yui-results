import RestartedAllTimeBounds
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

def frozenL2Path (a : ℝ) (f : Sobolev 2) (t : ℝ) : Sobolev 0 :=
  inclusionMap 0 1 (by norm_num) (frozenZBundled a t f)

def frozenNegativeDerivative (f : Sobolev 2) (t : ℝ) : Sobolev (-pStar) :=
  inclusionMap (-pStar) 1 (by norm_num [pStar]) ((1 / 2 : ℂ) • BTwoBundled t f f)

theorem numerical_frozen_time_bounds (externalStage : LiWuStageEstimate)
    {T γ M : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ n : ℕ,
      0 < τ → τ ≤ 1 → ((n + 1 : ℕ) : ℝ) * τ ≤ T →
      ∀ f : Sobolev 2, MeanZero f.val → ∀ w : Fourier, InSobolev γ w → MeanZero w →
        hNorm γ w ≤ M → hNorm 0 (f.val - w) ≤ 1 →
        ∀ t ∈ Set.Icc ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ),
          let a := (n : ℝ) * τ
          MemLp (frozenL2Path a f) ∞ (volume.restrict (Set.Icc a t)) ∧
          MemLp (frozenNegativeDerivative f) ∞ (volume.restrict (Set.Icc a t)) ∧
          WeakTimeDerivative a t (fun s => (frozenL2Path a f s).val) (fun s => (frozenNegativeDerivative f s).val) ∧
          timeXNorm a t (frozenL2Path a f) (frozenNegativeDerivative f) ≤ C := by
  obtain ⟨Cn, hCn, hstage⟩ := numerical_stage_bounds externalStage hT hγ hγ1 hM
  let K := negativeProductConstant (9 / 14) (by norm_num)
  have hK : 0 ≤ K := norm_nonneg _
  let Z := M + 1 + 2 * Cn
  let D := (1 / 2 : ℝ) * K * (M + 1) ^ 2
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨1 + Z + D, by positivity, ?_⟩
  intro τ n hτ hτ1 hnT f hfm w hw hwm hwM hδ t ht
  dsimp only
  let a : ℝ := (n : ℝ) * τ
  have hf0 := f.property.of_le (by norm_num : (0 : ℝ) ≤ 2)
  have hw0 := hw.of_le hγ.le
  have hfM : hNorm 0 f.val ≤ M + 1 := by
    have hh := hNorm_add_le (hf0.sub hw0) hw0
    rw [sub_add_cancel] at hh
    have hwM0 := (hNorm_mono hw hγ.le).trans hwM
    linarith
  have hfc : Continuous (frozenL2Path a f) := (inclusionMap 0 1 (by norm_num)).continuous.comp
    (continuous_frozenZBundled a f)
  have hdc : Continuous (frozenNegativeDerivative f) := (inclusionMap (-pStar) 1 (by norm_num [pStar])).continuous.comp
    ((continuous_const (y := (1 / 2 : ℂ))).smul (continuous_BTwoBundled continuous_id (continuous_const (y := f)) (continuous_const (y := f))))
  refine ⟨continuousOn_memLp_top_Icc hfc.continuousOn, continuousOn_memLp_top_Icc hdc.continuousOn,
    (frozenZ_regular f hfm).weakTimeDerivative ht.1, ?_⟩
  have hfb : timeLInfinity a t (frozenL2Path a f) ≤ Z := by
    apply timeLInfinity_le_of_bound hZ
    intro s hs
    have hss : s ∈ Set.Icc ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ) := ⟨hs.1, hs.2.trans ht.2⟩
    have hFb := (hstage τ n s hτ hτ1 hnT hss f.val w hf0 hw hwm hwM hδ).2.2.2
    have hq2 : τ ^ γ + hNorm 0 (f.val - w) ≤ 2 := by linarith [Real.rpow_le_one hτ.le hτ1 hγ.le]
    have hF0 := (bilinearStage_h1_bound hf0 hf0 a s).1.of_le (by norm_num : (0 : ℝ) ≤ 1)
    have hF2 : hNorm 0 (bilinearStage a s f.val f.val) ≤ 2 * Cn :=
      hFb.trans (by nlinarith)
    rw [sobolev_norm]
    exact (hNorm_add_le hf0 hF0).trans (by change hNorm 0 f.val + hNorm 0 (bilinearStage a s f.val f.val) ≤ Z; dsimp [Z]; linarith)
  have hdb : timeLInfinity a t (frozenNegativeDerivative f) ≤ D := by
    apply timeLInfinity_le_of_bound hD
    intro s _
    obtain ⟨hB, hBn⟩ := B_negative_bound hf0 hf0 s
    have hfnonneg := hNorm_nonneg 0 f.val
    rw [sobolev_norm]
    change hNorm (-pStar) ((1 / 2 : ℂ) • B s f.val f.val) ≤ D
    rw [hNorm_smul hB, show ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) by norm_num]
    calc
      _ ≤ (1 / 2 : ℝ) * (K * hNorm 0 f.val * hNorm 0 f.val) := mul_le_mul_of_nonneg_left hBn (by norm_num)
      _ ≤ (1 / 2 : ℝ) * (K * (M + 1) * (M + 1)) := by gcongr
      _ = D := by dsimp [D]; ring
  exact (add_le_add hfb hdb).trans (by linarith)

end KdV
