import Proof
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

/-- Distributional time derivative on the open interval. In particular this
is stronger than merely prescribing an almost-everywhere classical derivative. -/
def WeakTimeDerivative (a b : ℝ) (f df : ℝ → Fourier) : Prop :=
  ∀ k : ℤ, ∀ φ : ℝ → ℝ, ContDiff ℝ (⊤ : WithTop ℕ∞) φ → HasCompactSupport φ →
    Function.support φ ⊆ Set.Ioo a b →
      (∫ t : ℝ in a..b, ((deriv φ t : ℝ) : ℂ) * f t k) =
        -(∫ t : ℝ in a..b, (φ t : ℂ) * df t k)

/-- The unnormalized spatial norm, with the essential supremum in time.
Finiteness is always supplied separately as `MemLp ... ∞`. -/
def sourceLInfinity {s : ℝ} (a b : ℝ) (f : ℝ → Sobolev s) : ℝ :=
  sourceNormalization * (eLpNorm f ∞ (volume.restrict (Set.Icc a b))).toReal

def sourceLInfinityZero {α : ℝ} (hα : 0 ≤ α) (a b : ℝ) (f : ℝ → Sobolev α) : ℝ :=
  sourceLInfinity a b (fun t => inclusionMap 0 α hα (f t))

def sourceLInfinityNegative {α : ℝ} (hα : 0 ≤ α) (a b : ℝ) (f : ℝ → Sobolev α) : ℝ :=
  sourceLInfinity a b (fun t => inclusionMap (-pStar) α (by dsimp [pStar]; linarith) (f t))

def sourceXNorm {α : ℝ} (hα : 0 ≤ α) (a b : ℝ)
    (f : ℝ → Sobolev α) (df : ℝ → Sobolev (-pStar)) : ℝ :=
  sourceLInfinityZero hα a b f + sourceLInfinity a b df

/-- Explicit external premise: both parts of Li–Wu Proposition 3.4.
The derivative is distributional, the input hypotheses are essential bounds
in the actual complete Sobolev spaces, and the operator is (3.13). The negative
norm may be placed on any specified input while leaving the operator's slots
fixed, exactly as the source's permutation sentence states. A fixed bound `H`
on the interval length makes the implicit bounded-length convention explicit. -/
structure LiWuTrilinearEstimate : Prop where
  dynamic : ∀ H : ℝ, 0 < H → ∀ α : ℝ, ∀ hα : 0 ≤ α, α ≤ 1 →
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℝ, 0 ≤ a → a ≤ b → b - a ≤ H →
      ∀ f : Fin 3 → ℝ → Sobolev α, ∀ df : Fin 3 → ℝ → Sobolev (-pStar),
        (∀ j, MemLp (f j) ∞ (volume.restrict (Set.Icc a b))) →
        (∀ j, MemLp (df j) ∞ (volume.restrict (Set.Icc a b))) →
        (∀ j, WeakTimeDerivative a b (fun t => (f j t).val) (fun t => (df j t).val)) →
          InSobolev 0 (CIntegral a b (fun t => (f 0 t).val)
            (fun t => (f 1 t).val) (fun t => (f 2 t).val)) ∧
          ∀ i : Fin 3,
            sourceNorm 0 (CIntegral a b (fun t => (f 0 t).val)
              (fun t => (f 1 t).val) (fun t => (f 2 t).val)) ≤
              C * (b - a) * (∏ j : Fin 3, sourceXNorm hα a b (f j) (df j)) +
              C * sourceLInfinityNegative hα a b (f i) *
                (∏ j : Fin 3, if j = i then 1 else sourceLInfinityZero hα a b (f j))
  timeIndependent : ∀ H : ℝ, 0 < H → ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℝ, 0 ≤ a → a ≤ b → b - a ≤ H →
      ∀ f g h : Fourier, InSobolev α f → InSobolev α g → InSobolev α h →
        InSobolev 0 (CIntegral a b (fun _ => f) (fun _ => g) (fun _ => h)) ∧
        sourceNorm 0 (CIntegral a b (fun _ => f) (fun _ => g) (fun _ => h)) ≤
          C * (b - a) ^ α * sourceNorm α f * sourceNorm α g * sourceNorm α h

theorem sourceLInfinity_nonneg {s : ℝ} (a b : ℝ) (f : ℝ → Sobolev s) :
    0 ≤ sourceLInfinity a b f :=
  mul_nonneg sourceNormalization_pos.le ENNReal.toReal_nonneg

theorem sourceXNorm_nonneg {α : ℝ} (hα : 0 ≤ α) (a b : ℝ)
    (f : ℝ → Sobolev α) (df : ℝ → Sobolev (-pStar)) : 0 ≤ sourceXNorm hα a b f df :=
  add_nonneg (sourceLInfinity_nonneg _ _ _) (sourceLInfinity_nonneg _ _ _)

/-- Normalizing a trilinear source estimate contributes two powers of the
fixed spatial measure factor. This does not import any residual estimate. -/
theorem normalized_static_trilinear (externalTrilinear : LiWuTrilinearEstimate)
    {H α : ℝ} (hH : 0 < H) (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℝ, 0 ≤ a → a ≤ b → b - a ≤ H →
      ∀ f g h : Fourier, InSobolev α f → InSobolev α g → InSobolev α h →
        InSobolev 0 (CIntegral a b (fun _ => f) (fun _ => g) (fun _ => h)) ∧
        hNorm 0 (CIntegral a b (fun _ => f) (fun _ => g) (fun _ => h)) ≤
          C * (b - a) ^ α * hNorm α f * hNorm α g * hNorm α h := by
  obtain ⟨C, hC, hb⟩ := externalTrilinear.timeIndependent H hH α hα hα1
  refine ⟨C * sourceNormalization ^ 2, mul_pos hC (sq_pos_of_pos sourceNormalization_pos), ?_⟩
  intro a b ha hab hHbound f g h hf hg hh
  obtain ⟨hm, hn⟩ := hb a b ha hab hHbound f g h hf hg hh
  refine ⟨hm, (mul_le_mul_iff_right₀ sourceNormalization_pos).mp ?_⟩
  unfold sourceNorm at hn
  nlinarith only [hn]

end KdV
