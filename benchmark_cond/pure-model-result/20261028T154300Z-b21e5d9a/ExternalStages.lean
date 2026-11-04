import StageIdentity
noncomputable section
open scoped ComplexConjugate ENNReal
namespace KdV

/-- Li–Wu use unnormalized Lebesgue measure on the period-`2π` torus. -/
def sourceNormalization : ℝ := Real.sqrt (2 * Real.pi)

theorem sourceNormalization_pos : 0 < sourceNormalization := by
  unfold sourceNormalization
  positivity

def sourceNorm (s : ℝ) (f : Fourier) : ℝ := sourceNormalization * hNorm s f

/-- The `+` losses in Li–Wu (2.3) are represented by a fixed positive `ε`. -/
def sourceProductExponent (γ ε : ℝ) : ℝ :=
  if γ = 0 then 1 / 2 + ε else if γ < 1 / 2 then 1 / 2 - γ
  else if γ = 1 / 2 then ε else 0

/-- Explicit external premise: Li–Wu, author manuscript (2.2)–(2.3).
This imports only the spatial product theorem, with its two positive losses,
and with the source's unnormalized norms. It asserts no numerical estimate. -/
def LiWuProductEstimate : Prop :=
  ∀ γ : ℝ, 0 ≤ γ → γ ≤ 1 → ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∀ f g : Fourier,
      InSobolev γ f → InSobolev (sourceProductExponent γ ε) g →
        InSobolev 0 (product f g) ∧
        sourceNorm 0 (product f g) ≤ C * sourceNorm γ f * sourceNorm (sourceProductExponent γ ε) g

/-- The three lower endpoints in the full cited stage estimate. -/
def sourceStageLower (γ ε : ℝ) : ℝ :=
  if γ < 1 / 2 then 2 * γ - 3 / 2 else if γ = 1 / 2 then -1 / 2 - ε else γ - 1

def sourceStagePower (γ ε β : ℝ) : ℝ := (1 + γ - β) / (1 + γ - sourceStageLower γ ε)

/-- Explicit external premise: Li–Wu Lemma 7.2, with the stage represented by
its source endpoint formula (7.3). The bound is bilinear, over the whole source
regularity interval; constants precede the time step, starting time and inputs.
The source's standing zero-mode convention is included. -/
def LiWuStageEstimate : Prop :=
  ∀ T : ℝ, 0 < T → ∀ γ : ℝ, 0 < γ → γ ≤ 1 → ∀ ε : ℝ, 0 < ε →
    ∀ β : ℝ, sourceStageLower γ ε ≤ β → β ≤ 1 + γ →
      ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ n : ℕ, ∀ t : ℝ, 0 < τ → ((n + 1 : ℕ) : ℝ) * τ ≤ T →
        t ∈ Set.Icc ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ) → ∀ f g : Fourier,
          InSobolev γ f → InSobolev γ g → MeanZero f → MeanZero g →
            InSobolev β (sourceBilinearStage ((n : ℝ) * τ) t f g) ∧
            sourceNorm β (sourceBilinearStage ((n : ℝ) * τ) t f g) ≤
              C * τ ^ (sourceStagePower γ ε β) * sourceNorm γ f * sourceNorm γ g

/-- Normalization is derived, rather than silently built into the external premise. -/
theorem normalized_product_estimate (externalProduct : LiWuProductEstimate)
    {γ ε : ℝ} (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ f g : Fourier,
      InSobolev γ f → InSobolev (sourceProductExponent γ ε) g →
        InSobolev 0 (product f g) ∧
        hNorm 0 (product f g) ≤ C * hNorm γ f * hNorm (sourceProductExponent γ ε) g := by
  obtain ⟨C, hC, hb⟩ := externalProduct γ hγ hγ1 ε hε
  refine ⟨C * sourceNormalization, mul_pos hC sourceNormalization_pos, ?_⟩
  intro f g hf hg
  obtain ⟨hm, hn⟩ := hb f g hf hg
  refine ⟨hm, (mul_le_mul_iff_right₀ sourceNormalization_pos).mp ?_⟩
  unfold sourceNorm at hn
  nlinarith [hn]

theorem normalized_stage_estimate (externalStage : LiWuStageEstimate)
    {T γ ε β : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hε : 0 < ε)
    (hβ : sourceStageLower γ ε ≤ β) (hβ1 : β ≤ 1 + γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ n : ℕ, ∀ t : ℝ, 0 < τ → ((n + 1 : ℕ) : ℝ) * τ ≤ T →
      t ∈ Set.Icc ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ) → ∀ f g : Fourier,
        InSobolev γ f → InSobolev γ g → MeanZero f → MeanZero g →
          InSobolev β (bilinearStage ((n : ℝ) * τ) t f g) ∧
          hNorm β (bilinearStage ((n : ℝ) * τ) t f g) ≤
            C * τ ^ (sourceStagePower γ ε β) * hNorm γ f * hNorm γ g := by
  obtain ⟨C, hC, hb⟩ := externalStage T hT γ hγ hγ1 ε hε β hβ hβ1
  refine ⟨C * sourceNormalization, mul_pos hC sourceNormalization_pos, ?_⟩
  intro τ n t hτ hnT ht f g hf hg hfm hgm
  obtain ⟨hm, hn⟩ := hb τ n t hτ hnT ht f g hf hg hfm hgm
  rw [← bilinearStage_eq_source] at hm hn
  refine ⟨hm, (mul_le_mul_iff_right₀ sourceNormalization_pos).mp ?_⟩
  unfold sourceNorm at hn
  nlinarith [hn]

/-- The paper's fixed choice of the product exponent; its endpoint loss is `1/8`. -/
def aGamma (γ : ℝ) : ℝ := sourceProductExponent γ (1 / 8)

theorem aGamma_parameters {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    0 ≤ aGamma γ ∧ aGamma γ < 1 ∧
    sourceStageLower γ (1 / 8) ≤ aGamma γ ∧ aGamma γ ≤ 1 + γ ∧
    0 < 1 + γ - sourceStageLower γ (1 / 8) ∧
    γ ≤ sourceStagePower γ (1 / 8) (aGamma γ) := by
  by_cases hlow : γ < 1 / 2
  · simp only [aGamma, sourceProductExponent, ne_of_gt hγ, if_false, hlow, if_true,
      sourceStageLower, sourceStagePower]
    refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, ?_⟩
    apply (le_div_iff₀ (by linarith : 0 < 1 + γ - (2 * γ - 3 / 2))).mpr
    nlinarith [sq_nonneg γ]
  · by_cases hmid : γ = 1 / 2
    · subst γ
      norm_num [aGamma, sourceProductExponent, sourceStageLower, sourceStagePower]
    · have hhigh : 1 / 2 < γ := lt_of_le_of_ne (le_of_not_gt hlow) (Ne.symm hmid)
      simp only [aGamma, sourceProductExponent, ne_of_gt hγ, if_false, hlow, hmid,
        sourceStageLower, sourceStagePower]
      refine ⟨le_rfl, by norm_num, by linarith, by linarith, by linarith, ?_⟩
      apply (le_div_iff₀ (by linarith : 0 < 1 + γ - (γ - 1))).mpr
      nlinarith

/-- The two stage bounds (18) follow from the full cited estimate; no stage
bound specialized to the desired numerical trajectory is assumed. -/
theorem paper_stage_bounds (externalStage : LiWuStageEstimate)
    {T γ : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ n : ℕ, ∀ t : ℝ, 0 < τ → τ ≤ 1 → ((n + 1 : ℕ) : ℝ) * τ ≤ T →
      t ∈ Set.Icc ((n : ℝ) * τ) (((n + 1 : ℕ) : ℝ) * τ) → ∀ f g : Fourier,
        InSobolev γ f → InSobolev γ g → MeanZero f → MeanZero g →
          InSobolev (aGamma γ) (bilinearStage ((n : ℝ) * τ) t f g) ∧
          InSobolev (1 + γ) (bilinearStage ((n : ℝ) * τ) t f g) ∧
          hNorm (aGamma γ) (bilinearStage ((n : ℝ) * τ) t f g) ≤ C * τ ^ γ * hNorm γ f * hNorm γ g ∧
          hNorm (1 + γ) (bilinearStage ((n : ℝ) * τ) t f g) ≤ C * hNorm γ f * hNorm γ g := by
  obtain ⟨ha0, ha1, hba, hab, hd, hpower⟩ := aGamma_parameters hγ hγ1
  obtain ⟨C₁, hC₁, hb₁⟩ := normalized_stage_estimate externalStage hT hγ hγ1
    (by norm_num : (0 : ℝ) < 1 / 8) hba hab
  obtain ⟨C₂, hC₂, hb₂⟩ := normalized_stage_estimate externalStage hT hγ hγ1
    (by norm_num : (0 : ℝ) < 1 / 8) (β := 1 + γ) (by linarith) le_rfl
  refine ⟨max C₁ C₂, lt_of_lt_of_le hC₁ (le_max_left _ _), ?_⟩
  intro τ n t hτ hτ1 hnT ht f g hf hg hfm hgm
  obtain ⟨hm₁, hn₁⟩ := hb₁ τ n t hτ hnT ht f g hf hg hfm hgm
  obtain ⟨hm₂, hn₂⟩ := hb₂ τ n t hτ hnT ht f g hf hg hfm hgm
  refine ⟨hm₁, hm₂, hn₁.trans ?_, hn₂.trans ?_⟩
  · have hp := Real.rpow_le_rpow_of_exponent_ge hτ hτ1 hpower
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul (le_max_left C₁ C₂) hp (Real.rpow_nonneg hτ.le _) (by positivity))
        (hNorm_nonneg γ f)) (hNorm_nonneg γ g)
  · simp only [sourceStagePower, sub_self, zero_div, Real.rpow_zero, mul_one]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) (hNorm_nonneg γ f)) (hNorm_nonneg γ g)

end KdV
