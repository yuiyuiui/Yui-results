import GalerkinBridges
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory KdV
namespace BareModelCompletion

/-- Representation correspondence (7.2) = (7.3), proved using the unchanged
historical fixed-input normal form. This is valid for all real endpoints. -/
theorem liWuStage72_eq_endpoint {f g : Fourier}
    (hf : InSobolev 0 f) (hg : InSobolev 0 g)
    (hfm : MeanZero f) (hgm : MeanZero g) (a t : ℝ) :
    liWuStage72 a t f g = sourceBilinearStage a t f g := by
  rw [← bilinearStage_eq_source]
  funext k
  change (1 / 2 : ℂ) * (∫ r : ℝ in a..t, B r f g k) =
    (1 / 6 : ℂ) * (J t f g k - J a f g k)
  rw [fixed_normal_form hf hg hfm hgm]
  ring

/-- Original integral stage estimate implies the historical endpoint port. -/
theorem stage_to_historical (h : HistoricalIntegralStageEstimate) : LiWuStageEstimate := by
  intro T hT γ hγ hγ1 ε hε β hb hb1
  obtain ⟨C, hC, hc⟩ := h T hT γ hγ hγ1 ε hε β hb hb1
  refine ⟨C, hC, ?_⟩
  intro τ n t hτ hn ht f g hf hg hfm hgm
  have he := hc τ n t hτ hn ht f g hf hg hfm hgm
  rw [liWuStage72_eq_endpoint (hf.of_le hγ.le) (hg.of_le hγ.le) hfm hgm] at he
  exact he

/-- Reverse direction: this reformulation has lost no source-stage conclusion. -/
theorem historical_to_stage (h : LiWuStageEstimate) : HistoricalIntegralStageEstimate := by
  intro T hT γ hγ hγ1 ε hε β hb hb1
  obtain ⟨C, hC, hc⟩ := h T hT γ hγ hγ1 ε hε β hb hb1
  refine ⟨C, hC, ?_⟩
  intro τ n t hτ hn ht f g hf hg hfm hgm
  rw [liWuStage72_eq_endpoint (hf.of_le hγ.le) (hg.of_le hγ.le) hfm hgm]
  exact hc τ n t hτ hn ht f g hf hg hfm hgm

theorem stage_iff_historical : HistoricalIntegralStageEstimate ↔ LiWuStageEstimate :=
  ⟨stage_to_historical, historical_to_stage⟩

/-- Essential boundedness supplies the Bochner integrals in the weak derivative
identity. No continuity of the input trajectory is assumed. -/
theorem smul_interval_coefficient {s a b : ℝ} (hab : a ≤ b)
    {f : ℝ → Sobolev s} (hf : MemLp f ∞ (volume.restrict (Set.Icc a b)))
    {ψ : ℝ → ℂ} (hψ : Continuous ψ) (k : ℤ) :
    (∫ t : ℝ in a..b, ψ t • f t).val k = (∫ t : ℝ in a..b, ψ t * (f t).val k) := by
  have hψm := continuousOn_memLp_top_Icc (a := a) (b := b) hψ.continuousOn
  have hm : MemLp (fun t => ψ t • f t) ∞ (volume.restrict (Set.Icc a b)) := hf.smul hψm
  have hi : IntervalIntegrable (fun t => ψ t • f t) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr (hm.integrable (by simp))
  have hh := congrFun (sobolev_integral_val hi) k
  simpa only [sobolev_val_smul, Pi.smul_apply, smul_eq_mul] using hh

/-- Both directions of coefficientwise and complete-space distributional time
derivatives, under exactly the published essential-bound hypotheses. -/
theorem weakTimeDerivative_iff_bochner {α a b : ℝ} (hα : 0 ≤ α) (hab : a ≤ b)
    {f : ℝ → Sobolev α} {df : ℝ → Sobolev (-pStar)}
    (hf : MemLp f ∞ (volume.restrict (Set.Icc a b)))
    (hd : MemLp df ∞ (volume.restrict (Set.Icc a b))) :
    WeakTimeDerivative a b (fun t => (f t).val) (fun t => (df t).val) ↔
      BochnerWeakTimeDerivative hα a b f df := by
  let F : ℝ → Sobolev (-pStar) := fun t => inclusionMap (-pStar) α (by dsimp [pStar]; linarith) (f t)
  have hF : MemLp F ∞ (volume.restrict (Set.Icc a b)) :=
    (inclusionMap (-pStar) α (by dsimp [pStar]; linarith)).comp_memLp' hf
  constructor
  · intro h φ hφ hcomp hsupp
    have hD : Continuous (fun t : ℝ => ((deriv φ t : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (hφ.continuous_deriv (by simp))
    have hV : Continuous (fun t : ℝ => ((φ t : ℝ) : ℂ)) := Complex.continuous_ofReal.comp hφ.continuous
    apply Sobolev.ext
    funext k
    change (∫ t : ℝ in a..b, ((deriv φ t : ℝ) : ℂ) • F t).val k =
      -(∫ t : ℝ in a..b, ((φ t : ℝ) : ℂ) • df t).val k
    rw [smul_interval_coefficient hab hF hD k, smul_interval_coefficient hab hd hV k]
    change (∫ t : ℝ in a..b, ((deriv φ t : ℝ) : ℂ) * (f t).val k) =
      -(∫ t : ℝ in a..b, ((φ t : ℝ) : ℂ) * (df t).val k)
    exact h k φ hφ hcomp hsupp
  · intro h k φ hφ hcomp hsupp
    have hD : Continuous (fun t : ℝ => ((deriv φ t : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (hφ.continuous_deriv (by simp))
    have hV : Continuous (fun t : ℝ => ((φ t : ℝ) : ℂ)) := Complex.continuous_ofReal.comp hφ.continuous
    have hh := congrArg (fun z : Sobolev (-pStar) => z.val k) (h φ hφ hcomp hsupp)
    change (∫ t : ℝ in a..b, ((deriv φ t : ℝ) : ℂ) • F t).val k =
      -(∫ t : ℝ in a..b, ((φ t : ℝ) : ℂ) • df t).val k at hh
    rw [smul_interval_coefficient hab hF hD k, smul_interval_coefficient hab hd hV k] at hh
    exact hh

/-- Restrict only the original bounded-length parameter and prove the needed
weak-derivative representation conversion. -/
theorem trilinear_to_historical (h : LiWuProposition34) : LiWuTrilinearEstimate where
  dynamic := by
    intro H hH _ α hα hα1
    obtain ⟨C, hC, hb⟩ := h.dynamic H hH α hα hα1
    refine ⟨C, hC, ?_⟩
    intro a b ha hab hlen f df hf hd hweak
    exact hb a b ha hab hlen f df hf hd
      (fun j => (weakTimeDerivative_iff_bochner hα hab (hf j) (hd j)).mp (hweak j))
  timeIndependent := fun H hH _ => h.timeIndependent H hH

theorem galerkin_to_historical (h : BITTheorem42) : BITGalerkinEstimate := by
  intro s hs M hM T hT r hr
  obtain ⟨A, hA, hb⟩ := h s hs M hM T hT r hr
  refine ⟨A, hA, ?_⟩
  intro m hm f v hfr hf hfn hfM hc hreal hode
  exact (hb m hm f v hfr hf hfn hfM hc hreal hode).2


theorem bit42_from_joint (h : BITTheorems42And43) : BITTheorem42 := by
  intro s hs M hM T hT r hr
  obtain ⟨A, hA, hb, _⟩ := h s hs M hM T hT r hr
  exact ⟨A, hA, hb⟩

/-- Taking norms gives the exact weaker convergence port used historically. -/
theorem strongLp43_to_scalar {σ T : ℝ} {G : ℕ → ℝ → Fourier} {v : ℝ → Fourier}
    (hG : ∀ n, ∀ t ∈ Set.Icc 0 T, MeanZero (G n t))
    (hv : ∀ t ∈ Set.Icc 0 T, MeanZero (v t)) (h : BITStrongLp43 σ T G v) :
    ∀ p : ℝ, 1 < p → SourceLpConvergence σ T p G v := by
  obtain ⟨W, w, hW, hw, hp⟩ := h
  have he (n : ℕ) : (fun t => homogeneousNorm σ (G n t - v t)) =ᵐ[volume.restrict (Set.Icc 0 T)]
      (fun t => ‖W n t - w t‖) := by
    filter_upwards [hW n, hw, ae_restrict_mem measurableSet_Icc] with t hnt hvt ht
    have hz : MeanZero (G n t - v t) := by
      change G n t 0 - v t 0 = 0
      rw [hG n t ht, hv t ht, sub_self]
    have hd : (W n t - w t).val = homogeneousWeighted σ (G n t - v t) := by
      change (W n t).val - (w t).val = _
      rw [hnt, hvt, homogeneousWeighted_sub]
      rfl
    have hi : InHomSobolev σ (G n t - v t) := ⟨hz, by rw [← hd]; exact (W n t - w t).property⟩
    have hrep : homogeneousLp σ (G n t - v t) hi = W n t - w t := Subtype.ext hd.symm
    rw [← homogeneousLp_norm σ (G n t - v t) hi, hrep]
  intro p hpp
  obtain ⟨hWp, hwp, hlim⟩ := hp p hpp
  refine ⟨fun n => (memLp_congr_ae (he n)).mpr ((hWp n).sub hwp).norm, ?_⟩
  have hnorm (n : ℕ) : eLpNorm (fun t => homogeneousNorm σ (G n t - v t)) (ENNReal.ofReal p)
      (volume.restrict (Set.Icc 0 T)) = eLpNorm (fun t => W n t - w t) (ENNReal.ofReal p)
      (volume.restrict (Set.Icc 0 T)) := by
    rw [eLpNorm_congr_ae (he n), eLpNorm_norm]
  simpa only [hnorm] using hlim

theorem limit43For_to_certificate {A s T σ : ℝ} {f : Fourier}
    {G : ℕ → ℝ → Fourier} {v : ℝ → Fourier} (hA : 0 ≤ A)
    (hG : ∀ m, HomSobolevContinuousOn s T (G m) ∧
      (∀ t ∈ Set.Icc 0 T, RealValued (G m t)) ∧ SourceGalerkinODE (m + 1) T f (G m))
    (hGB : ∀ m, ∀ t ∈ Set.Icc 0 T, homogeneousNorm s (G m t) ≤ A)
    (hv : BITLimit43For A s T f σ G v) : SourceLimitCertificate s T f σ v := by
  obtain ⟨hw, he, hb, henergy, idx, hidx, hlp, hstar⟩ := hv
  have hscalar := strongLp43_to_scalar
    (fun n t ht => ((hG (idx n)).1.1 t ht).1) (fun t ht => (hw.2.1 t ht).2) hlp
  exact ⟨hw, he, A, hA, hb, henergy, G, idx, hidx,
    (fun m => ⟨(hG m).1, (hG m).2.1, (hG m).2.2, hGB m⟩), hscalar, hstar⟩

theorem limit_to_historical (h41 : BITProposition41) (h : BITTheorems42And43) : BITExistenceLimit := by
  intro T hT s hs f hfr hf σ hσ hσs
  obtain ⟨A, hA, hgal, hl⟩ := h s hs.le (homogeneousNorm 0 f)
    (homogeneousNorm_nonneg 0 f) T hT (homogeneousNorm s f) (homogeneousNorm_nonneg s f)
  obtain ⟨G, hGG⟩ := source_global_galerkin_family h41 hs.le f hfr hf
  have hG (m : ℕ) := (hGG m).1 T hT
  obtain ⟨v, hv⟩ := hl hs f hfr hf rfl le_rfl G hGG σ hσ hσs
  have hGB (m : ℕ) : ∀ t ∈ Set.Icc 0 T, homogeneousNorm s (G m t) ≤ A :=
    (hgal (m + 1) (by omega) f (G m) hfr hf rfl le_rfl
      (hG m).1 (hG m).2.1 (hG m).2.2).2
  exact ⟨v, limit43For_to_certificate hA hG hGB hv⟩

theorem original_limit_exists (h41 : BITProposition41) (h : BITTheorems42And43)
    {s T : ℝ} (hs : 0 < s) (hT : 0 < T) (f : Fourier)
    (hfr : RealValued f) (hf : InHomSobolev s f) :
    ∃ v : ℝ → Fourier, BITConstructedLimit43 s T f v := by
  obtain ⟨A, hA, hgal, hl⟩ := h s hs.le (homogeneousNorm 0 f)
    (homogeneousNorm_nonneg 0 f) T hT (homogeneousNorm s f) (homogeneousNorm_nonneg s f)
  obtain ⟨G, hGG⟩ := source_global_galerkin_family h41 hs.le f hfr hf
  have hG (m : ℕ) := (hGG m).1 T hT
  obtain ⟨v, hv⟩ := hl hs f hfr hf rfl le_rfl G hGG (s / 2) (by linarith) (by linarith)
  refine ⟨v, s / 2, by linarith, by linarith, A, hA, G, hGG, ?_, hv⟩
  intro m
  exact (hgal (m + 1) (by omega) f (G m) hfr hf rfl le_rfl
      (hG m).1 (hG m).2.1 (hG m).2.2).2

theorem original_constructed_weak {s T : ℝ} {f : Fourier} {v : ℝ → Fourier}
    (hv : BITConstructedLimit43 s T f v) : SourceWeakSolution T f v := by
  obtain ⟨σ, _, _, A, _, G, _, _, hv⟩ := hv
  exact hv.1

theorem liWuStage72_eq_bilinear {f g : Fourier}
    (hf : InSobolev 0 f) (hg : InSobolev 0 g) (hfm : MeanZero f) (hgm : MeanZero g) (a t : ℝ) :
    liWuStage72 a t f g = bilinearStage a t f g := by
  rw [liWuStage72_eq_endpoint hf hg hfm hgm, ← bilinearStage_eq_source]

theorem liWuCross410_eq_frozenCross {f : Fourier} (hf : InSobolev 0 f)
    (hfm : MeanZero f) (a t : ℝ) : liWuCross410 a t f = frozenCross a t f := by
  funext k
  unfold liWuCross410 frozenCross
  congr 1
  funext r
  rw [liWuStage72_eq_bilinear hf hf hfm hfm]

theorem liWuEta415_eq_covariance (τ α β : ℝ) : liWuEta415 τ α β = covariance τ α β := by
  unfold liWuEta415 covariance phaseAverage
  congr 2
  apply intervalIntegral.integral_congr
  intro r _
  dsimp only
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem liWuRemainder61_eq_remainder (τ t : ℝ) (f g h : Fourier) :
    liWuRemainder61 τ t f g h = remainder τ t f g h := by
  unfold liWuRemainder61 remainder
  simp_rw [liWuEta415_eq_covariance]

theorem step_to_historical (h : LiWuStep52) : LiWuStepIdentity := by
  intro τ hτ n f hf _ hfm
  have he := h 1 (by norm_num) le_rfl τ hτ n f hf hfm
  have hf0 := hf.of_le (by norm_num : (0 : ℝ) ≤ 1)
  rw [liWuStage72_eq_bilinear hf0 hf0 hfm hfm, liWuCross410_eq_frozenCross hf0 hfm, liWuRemainder61_eq_remainder] at he
  exact he

/-- The continuous-representative formulation is equivalent, with the same
neighborhood and constant, to the historical essential-time formulation. -/
theorem source_local_lipschitz_iff {s T : ℝ} (hT : 0 < T)
    {f : Fourier} {v : ℝ → Fourier} (hv : HomSobolevContinuousOn s T v) :
    SourceLocalLipschitzAllTimes s T f v ↔ SourceLocalLipschitz s T f v := by
  constructor
  · rintro ⟨r, hr, C, hC, hb⟩
    refine ⟨r, hr, C, hC, ?_⟩
    intro g hgr hg hgf w hw hwC
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hb g hgr hg hgf w hw hwC t ht
  · rintro ⟨r, hr, C, hC, hb⟩
    refine ⟨r, hr, C, hC, ?_⟩
    intro g hgr hg hgf w hw hwC
    exact homogeneous_bound_of_ae hT (hv.sub hwC) (hb g hgr hg hgf w hw hwC)


/-- Open and closed time intervals give exactly the same essential norms and
representative classes for Lebesgue time measure. -/
theorem source_time_measure_eq (a b : ℝ) :
    volume.restrict (Set.Ioo a b) = volume.restrict (Set.Icc a b) :=
  restrict_Ioo_eq_restrict_Icc

theorem CIntegral_congr_ae {a b : ℝ} (hab : a ≤ b)
    {f f' g g' h h' : ℝ → Fourier}
    (hf : f =ᵐ[volume.restrict (Set.Icc a b)] f')
    (hg : g =ᵐ[volume.restrict (Set.Icc a b)] g')
    (hh : h =ᵐ[volume.restrict (Set.Icc a b)] h') :
    CIntegral a b f g h = CIntegral a b f' g' h' := by
  funext k
  unfold CIntegral
  apply intervalIntegral.integral_congr_ae_restrict
  rw [Set.uIoc_of_le hab, restrict_Ioc_eq_restrict_Icc]
  filter_upwards [hf, hg, hh] with t ht ht' ht''
  rw [ht, ht', ht'']

theorem weakTimeDerivative_congr_ae {a b : ℝ} (hab : a ≤ b)
    {f g df dg : ℝ → Fourier}
    (hf : f =ᵐ[volume.restrict (Set.Icc a b)] g)
    (hd : df =ᵐ[volume.restrict (Set.Icc a b)] dg) :
    WeakTimeDerivative a b f df ↔ WeakTimeDerivative a b g dg := by
  have hint {F G : ℝ → Fourier} (he : F =ᵐ[volume.restrict (Set.Icc a b)] G)
      (ψ : ℝ → ℂ) (k : ℤ) :
      (∫ t : ℝ in a..b, ψ t * F t k) = (∫ t : ℝ in a..b, ψ t * G t k) := by
    apply intervalIntegral.integral_congr_ae_restrict
    rw [Set.uIoc_of_le hab, restrict_Ioc_eq_restrict_Icc]
    filter_upwards [he] with t ht
    rw [ht]
  constructor
  · intro h k φ hφ hcomp hsupp
    rw [← hint hf (fun t => ((deriv φ t : ℝ) : ℂ)) k,
      ← hint hd (fun t => ((φ t : ℝ) : ℂ)) k]
    exact h k φ hφ hcomp hsupp
  · intro h k φ hφ hcomp hsupp
    rw [hint hf (fun t => ((deriv φ t : ℝ) : ℂ)) k,
      hint hd (fun t => ((φ t : ℝ) : ℂ)) k]
    exact h k φ hφ hcomp hsupp


/-- The unnormalized source Hilbert norm is an actual rescaling of the complete
weighted coefficient space, not a change to the target norm. -/
theorem source_rescaled_norm {s : ℝ} (f : Sobolev s) :
    ‖(sourceNormalization : ℂ) • f‖ = sourceNorm s f.val := by
  rw [norm_smul, sobolev_norm]
  simp only [Complex.norm_real, Real.norm_of_nonneg sourceNormalization_pos.le, sourceNorm]

theorem source_rescaled_memLp_iff {s : ℝ} (a b : ℝ) (f : ℝ → Sobolev s) :
    MemLp ((sourceNormalization : ℂ) • f) ∞ (volume.restrict (Set.Icc a b)) ↔
      MemLp f ∞ (volume.restrict (Set.Icc a b)) := by
  have hκ : (sourceNormalization : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr sourceNormalization_pos.ne'
  constructor
  · intro h
    have hi := h.const_smul ((sourceNormalization : ℂ)⁻¹)
    simpa only [smul_smul, inv_mul_cancel₀ hκ, one_smul] using hi
  · intro h
    exact h.const_smul (sourceNormalization : ℂ)

theorem source_rescaled_time_norm {s : ℝ} (a b : ℝ) (f : ℝ → Sobolev s) :
    (eLpNorm ((sourceNormalization : ℂ) • f) ∞ (volume.restrict (Set.Icc a b))).toReal =
      sourceLInfinity a b f := by
  rw [eLpNorm_const_smul, ENNReal.toReal_mul]
  simp only [toReal_enorm, Complex.norm_real, Real.norm_of_nonneg sourceNormalization_pos.le, sourceLInfinity]


theorem step_grid_to_universal (h : LiWuStep52Grid) : LiWuStep52 := by
  intro γ hγ hγ1 τ hτ n f hf hfm
  let L := n + 1
  have hL : 0 < L := by dsimp [L]; omega
  have hLr : 0 < (L : ℝ) := by exact_mod_cast hL
  have hT : 0 < (L : ℝ) * τ := mul_pos hLr hτ
  have heq : ((L : ℝ) * τ) / (L : ℝ) = τ := by field_simp
  have hh := h γ hγ hγ1 ((L : ℝ) * τ) hT L hL n (by dsimp [L]; omega) f hf hfm
  simpa only [heq] using hh

theorem step_universal_to_grid (h : LiWuStep52) : LiWuStep52Grid := by
  intro γ hγ hγ1 T hT L hL
  dsimp only
  intro n _ f hf hfm
  exact h γ hγ hγ1 (T / (L : ℝ)) (div_pos hT (by exact_mod_cast hL)) n f hf hfm

theorem step_grid_iff_universal : LiWuStep52Grid ↔ LiWuStep52 :=
  ⟨step_grid_to_universal, step_universal_to_grid⟩

theorem step_grid_to_historical (h : LiWuStep52Grid) : LiWuStepIdentity :=
  step_to_historical (step_grid_to_universal h)


/-- Restricting an upper norm bound to nonnegative values loses no original
case: all data hypotheses in a negative-bound case are contradictory. -/
theorem bit42_43_all_bounds_iff : BITTheorems42And43AllBounds ↔ BITTheorems42And43 := by
  constructor
  · intro h s hs M _ T hT r _
    exact h s hs M T hT r
  · intro h s hs M T hT r
    by_cases hM : 0 ≤ M
    · by_cases hr : 0 ≤ r
      · exact h s hs M hM T hT r hr
      · have impossible (f : Fourier) (he : homogeneousNorm s f = r) : False := by
          have := homogeneousNorm_nonneg s f
          linarith
        refine ⟨0, le_rfl, ?_, ?_⟩
        · intro m hm f v hfr hf he
          exact False.elim (impossible f he)
        · intro hs' f hfr hf he
          exact False.elim (impossible f he)
    · have impossible (f : Fourier) (he : homogeneousNorm 0 f ≤ M) : False := by
        have := homogeneousNorm_nonneg 0 f
        linarith
      refine ⟨0, le_rfl, ?_, ?_⟩
      · intro m hm f v hfr hf he hfm
        exact False.elim (impossible f hfm)
      · intro hs' f hfr hf he hfm
        exact False.elim (impossible f hfm)

end BareModelCompletion
