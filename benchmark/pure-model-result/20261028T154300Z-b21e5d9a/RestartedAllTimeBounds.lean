import Proof
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

def affineErrorPath (externalStep : LiWuStepIdentity) {T τ : ℝ} (hT : 0 ≤ T) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {u : ℝ → Fourier} (hu : KdVSolution 2 T f.val u) (k : ℕ) (z : ℂ) (t : ℝ) : Sobolev 1 :=
  exactTwistedOne hT hu t - z • errorPath externalStep hT hτ f hfr hfm hu k t

def affineErrorDerivativeFamily (externalStep : LiWuStepIdentity) {T τ : ℝ} (hT : 0 ≤ T) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {u : ℝ → Fourier} (hu : KdVSolution 2 T f.val u) (z : ℂ) (j : ℕ) (t : ℝ) : Sobolev 1 :=
  exactTwistedDerivative hT hu t - z • errorDerivativeFamily externalStep hT hτ f hfr hfm hu j t

theorem continuous_affineErrorPath (externalStep : LiWuStepIdentity) {T τ : ℝ} (hT : 0 ≤ T) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {u : ℝ → Fourier} (hu : KdVSolution 2 T f.val u) (k : ℕ) (z : ℂ) :
    Continuous (affineErrorPath externalStep hT hτ f hfr hfm hu k z) :=
  ((inclusionMap 1 2 (by norm_num)).continuous.comp (continuous_extendedTwistedPath hT hu)).sub
    ((continuous_const (y := z)).smul (continuous_errorPath externalStep hT hτ f hfr hfm hu k))

theorem continuous_affineErrorDerivativeFamily (externalStep : LiWuStepIdentity) {T τ : ℝ} (hT : 0 ≤ T) (hτ : 0 < τ)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {u : ℝ → Fourier} (hu : KdVSolution 2 T f.val u) (z : ℂ) (j : ℕ) :
    Continuous (affineErrorDerivativeFamily externalStep hT hτ f hfr hfm hu z j) :=
  (continuous_exactTwistedDerivative hT hu).sub
    ((continuous_const (y := z)).smul (continuous_errorDerivativeFamily externalStep hT hτ f hfr hfm hu j))

theorem affineErrorPath_hasDerivAt_on_step (externalStep : LiWuStepIdentity) {T τ : ℝ}
    (hT : 0 ≤ T) (hτ : 0 < τ) (k : ℕ) (hTotal : ((k + 1 : ℕ) : ℝ) * τ ≤ T)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {u : ℝ → Fourier} (hu : KdVSolution 2 T f.val u) (z : ℂ) {j : ℕ} (hjk : j ≤ k) {t : ℝ}
    (ht : t ∈ Set.Ioo ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ)) (m : ℤ) :
    HasDerivAt (fun r : ℝ => (affineErrorPath externalStep hT hτ f hfr hfm hu k z r).val m)
      ((affineErrorDerivativeFamily externalStep hT hτ f hfr hfm hu z j t).val m) t := by
  have ht0 : 0 < t := lt_of_le_of_lt (mul_nonneg (Nat.cast_nonneg j) hτ.le) ht.1
  have htT : t < T := lt_of_lt_of_le ht.2
    ((mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_succ hjk) hτ.le).trans hTotal)
  exact (extendedTwistedPath_hasDerivAt hT hu ⟨ht0, htT⟩ m).sub
    ((errorPath_hasDerivAt_on_step externalStep hT hτ k hTotal f hfr hfm hu hjk ht m).const_mul z)

/-- Every affine combination used in (28) has the actual piecewise weak
 derivative, not a formally assigned derivative. -/
theorem affine_error_time_membership (externalStep : LiWuStepIdentity) {T τ : ℝ}
    (hT : 0 ≤ T) (hτ : 0 < τ) (k : ℕ) (hTotal : ((k + 1 : ℕ) : ℝ) * τ ≤ T)
    (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {u : ℝ → Fourier} (hu : KdVSolution 2 T f.val u) (z : ℂ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ ((k + 1 : ℕ) : ℝ) * τ) :
    MemLp (fun t => exactL2Path hT hu t - z • errorL2Path externalStep hT hτ f hfr hfm hu k t)
      ∞ (volume.restrict (Set.Icc a b)) ∧
    MemLp (fun t => exactNegativeDerivative hT hu t - z • errorNegativeDerivative externalStep hT hτ f hfr hfm hu k t)
      ∞ (volume.restrict (Set.Icc a b)) ∧
    WeakTimeDerivative a b
      (fun t => (exactL2Path hT hu t - z • errorL2Path externalStep hT hτ f hfr hfm hu k t).val)
      (fun t => (exactNegativeDerivative hT hu t - z • errorNegativeDerivative externalStep hT hτ f hfr hfm hu k t).val) := by
  have he := error_time_membership externalStep hT hτ k hTotal f hfr hfm hu ha hab hb
  have hv : MemLp (exactL2Path hT hu) ∞ (volume.restrict (Set.Icc a b)) :=
    continuousOn_memLp_top_Icc (((inclusionMap 0 2 (by norm_num)).continuous.comp
      (continuous_extendedTwistedPath hT hu)).continuousOn)
  have hdv : MemLp (exactNegativeDerivative hT hu) ∞ (volume.restrict (Set.Icc a b)) :=
    continuousOn_memLp_top_Icc (((inclusionMap (-pStar) 1 (by norm_num [pStar])).continuous.comp
      (continuous_exactTwistedDerivative hT hu)).continuousOn)
  refine ⟨hv.sub (he.1.const_smul z), hdv.sub (he.2.1.const_smul z), ?_⟩
  have hw := grid_weakTimeDerivative τ hτ k
    (affineErrorPath externalStep hT hτ f hfr hfm hu k z)
    (affineErrorDerivativeFamily externalStep hT hτ f hfr hfm hu z)
    (continuous_affineErrorPath externalStep hT hτ f hfr hfm hu k z)
    (continuous_affineErrorDerivativeFamily externalStep hT hτ f hfr hfm hu z)
    (fun j hj t ht m => affineErrorPath_hasDerivAt_on_step externalStep hT hτ k hTotal f hfr hfm hu z hj ht m)
    ha hab hb
  have hd (t : ℝ) : concatenate τ (affineErrorDerivativeFamily externalStep hT hτ f hfr hfm hu z) k t =
      exactTwistedDerivative hT hu t - z • concatenate τ (errorDerivativeFamily externalStep hT hτ f hfr hfm hu) k t :=
    concatenate_map τ _ (fun r w => exactTwistedDerivative hT hu r - z • w) k t
  simpa only [affineErrorPath, hd, sobolev_val_sub, sobolev_val_smul, exactL2Path,
    exactNegativeDerivative, errorL2Path, errorNegativeDerivative, exactTwistedOne, inclusionMap_val] using hw

/-- The remaining uniform `X` bounds in (28). The coefficient `z=1` gives
 the numerical interpolation and `z=1/2` the midpoint in the error equation. -/
theorem restarted_affine_error_time_bounds (externalStep : LiWuStepIdentity)
    (externalStage : LiWuStageEstimate) (externalProduct : LiWuProductEstimate)
    (externalTrilinear : LiWuTrilinearEstimate)
    {T γ M : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ hτ : 0 < τ, τ ≤ 1 → ∀ k : ℕ,
      ((k + 1 : ℕ) : ℝ) * τ ≤ T →
      ∀ f : Sobolev 2, ∀ hfr : RealValued f.val, ∀ hfm : MeanZero f.val,
      ∀ u : ℝ → Fourier, ∀ hu : KdVSolution 2 T f.val u,
        (∀ t ∈ Set.Icc 0 T, hNorm γ (u t) ≤ M) →
        ∀ j0 : ℕ, j0 ≤ k → ∀ b E : ℝ, (j0 : ℝ) * τ ≤ b → b ≤ ((k + 1 : ℕ) : ℝ) * τ →
          0 ≤ E → E ≤ 1 →
          (∀ t ∈ Set.Icc ((j0 : ℝ) * τ) b,
            hNorm 0 (errorPath externalStep hT.le hτ f hfr hfm hu k t).val ≤ E) →
          ∀ z : ℂ, ‖z‖ ≤ 1 →
          timeXNorm ((j0 : ℝ) * τ) b
            (fun t => exactL2Path hT.le hu t - z • errorL2Path externalStep hT.le hτ f hfr hfm hu k t)
            (fun t => exactNegativeDerivative hT.le hu t - z • errorNegativeDerivative externalStep hT.le hτ f hfr hfm hu k t) ≤ C := by
  obtain ⟨Ce, hCe, he⟩ := restarted_error_time_bound externalStep externalStage externalProduct externalTrilinear hT hγ hγ1 hM
  let Cv := M + (1 / 2 : ℝ) * negativeProductConstant (9 / 14) (by norm_num) * M ^ 2
  have hK : 0 ≤ negativeProductConstant (9 / 14) (by norm_num) := norm_nonneg _
  have hCv : 0 ≤ Cv := by dsimp [Cv]; positivity
  refine ⟨1 + Cv + 2 * Ce, by positivity, ?_⟩
  intro τ hτ hτ1 k hTotal f hfr hfm u hu huM j0 hj0 b E hab hb hE hE1 hbound z hz
  have ha : 0 ≤ (j0 : ℝ) * τ := mul_nonneg (Nat.cast_nonneg _) hτ.le
  obtain ⟨hv, hdv, _, hxv⟩ := exact_time_bounds hT.le hγ.le (by linarith : γ ≤ 2) hM hu huM ha hab (hb.trans hTotal)
  obtain ⟨he0, hde, _⟩ := error_time_membership externalStep hT.le hτ k hTotal f hfr hfm hu ha hab hb
  have hxe := he τ hτ hτ1 k hTotal f hfr hfm u hu huM j0 hj0 b E hab hb hE hE1 hbound
  have hq2 : τ ^ γ + E ≤ 2 := by linarith [Real.rpow_le_one hτ.le hτ1 hγ.le]
  calc
    _ ≤ timeXNorm ((j0 : ℝ) * τ) b (exactL2Path hT.le hu) (exactNegativeDerivative hT.le hu) +
        ‖z‖ * timeXNorm ((j0 : ℝ) * τ) b (errorL2Path externalStep hT.le hτ f hfr hfm hu k)
          (errorNegativeDerivative externalStep hT.le hτ f hfr hfm hu k) := timeXNorm_affine_le hv he0 hdv hde z
    _ ≤ Cv + 2 * Ce := by
      have he2 : timeXNorm ((j0 : ℝ) * τ) b (errorL2Path externalStep hT.le hτ f hfr hfm hu k)
          (errorNegativeDerivative externalStep hT.le hτ f hfr hfm hu k) ≤ 2 * Ce := by nlinarith
      exact add_le_add hxv (calc
        _ ≤ 1 * (2 * Ce) := mul_le_mul hz he2 (timeXNorm_nonneg _ _ _ _) (by norm_num)
        _ = _ := one_mul _)
    _ ≤ _ := by linarith

theorem affineErrorPath_one (externalStep : LiWuStepIdentity) {T τ : ℝ}
    (hT : 0 ≤ T) (hτ : 0 < τ) (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {u : ℝ → Fourier} (hu : KdVSolution 2 T f.val u) (k : ℕ) (t : ℝ) :
    affineErrorPath externalStep hT hτ f hfr hfm hu k 1 t = globalInterpolation externalStep τ hτ f hfr hfm k t := by
  simp only [affineErrorPath, errorPath, one_smul, sub_sub_cancel]

theorem affineErrorPath_half (externalStep : LiWuStepIdentity) {T τ : ℝ}
    (hT : 0 ≤ T) (hτ : 0 < τ) (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {u : ℝ → Fourier} (hu : KdVSolution 2 T f.val u) (k : ℕ) (t : ℝ) :
    affineErrorPath externalStep hT hτ f hfr hfm hu k (1 / 2) t = errorMidpoint externalStep hT hτ f hfr hfm hu k t := rfl

end KdV
