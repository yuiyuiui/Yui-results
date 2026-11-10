import FlowBounds
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

theorem homogeneousNorm_sub_le {s : ℝ} {f g : Fourier}
    (hf : InHomSobolev s f) (hg : InHomSobolev s g) :
    homogeneousNorm s (f - g) ≤ homogeneousNorm s f + homogeneousNorm s g := by
  have heq : homogeneousLp s (f - g) (hf.sub hg) =
      homogeneousLp s f hf - homogeneousLp s g hg := by
    apply Subtype.ext
    exact homogeneousWeighted_sub s f g
  rw [← homogeneousLp_norm s (f - g) (hf.sub hg), heq,
    ← homogeneousLp_norm s f hf, ← homogeneousLp_norm s g hg]
  exact norm_sub_le _ _

theorem HomSobolevContinuousOn.sub {s T : ℝ} {v w : ℝ → Fourier}
    (hv : HomSobolevContinuousOn s T v) (hw : HomSobolevContinuousOn s T w) :
    HomSobolevContinuousOn s T (fun t => v t - w t) := by
  refine ⟨fun t ht => (hv.1 t ht).sub (hw.1 t ht), ?_⟩
  intro t ht ε hε
  obtain ⟨δv, hδv, hbv⟩ := hv.2 t ht (ε / 2) (by linarith)
  obtain ⟨δw, hδw, hbw⟩ := hw.2 t ht (ε / 2) (by linarith)
  refine ⟨min δv δw, lt_min hδv hδw, ?_⟩
  intro r hr hrt
  have heq : (v r - w r) - (v t - w t) = (v r - v t) - (w r - w t) := by
    abel
  rw [heq]
  exact (homogeneousNorm_sub_le ((hv.1 r hr).sub (hv.1 t ht))
    ((hw.1 r hr).sub (hw.1 t ht))).trans_lt
      (by have hvb := hbv r hr (lt_of_lt_of_le hrt (min_le_left _ _))
          have hwb := hbw r hr (lt_of_lt_of_le hrt (min_le_right _ _))
          linarith)

/-- The source essential-supremum dependence estimate holds at every time,
including zero and the terminal time, in its continuous solution class. -/
theorem source_flow_lipschitz (externalLipschitz : BITWeakerLipschitz)
    {M θ : ℝ} (hM : 0 ≤ M) (hθ : -1 < θ) (hθ0 : θ ≤ 0) :
    ∃ C' : ℝ, 0 < C' ∧ ∃ CM : ℝ, 0 < CM ∧ ∀ T : ℝ, 0 < T →
      ∀ f g : Fourier, RealValued f → RealValued g → InHomSobolev 0 f → InHomSobolev 0 g →
        homogeneousNorm 0 f + homogeneousNorm 0 g ≤ M →
        ∀ v w : ℝ → Fourier, SourceWeakSolution T f v → SourceWeakSolution T g w →
          HomSobolevContinuousOn 0 T v → HomSobolevContinuousOn 0 T w →
            ∀ t ∈ Set.Icc 0 T,
              homogeneousNorm θ (v t - w t) ≤ C' * CM ^ T * homogeneousNorm θ (f - g) := by
  obtain ⟨C', hC', CM, hCM, hb⟩ := externalLipschitz M hM θ hθ hθ0
  refine ⟨C', hC', CM, hCM, ?_⟩
  intro T hT f g hfr hgr hf hg hfg v w hv hw hvC hwC
  exact homogeneous_bound_of_ae hT ((hvC.sub hwC).of_le hθ0)
    (hb T hT f g hfr hgr hf hg hfg v w hv hw hvC hwC)

/-- Uniform physical `L²` solution dependence on each initial-data ball. Both
flows may have different positive Sobolev orders; their norms enter only through
the initial `L²` ball. -/
theorem kdv_flow_l2_lipschitz (externalLipschitz : BITWeakerLipschitz)
    {M T : ℝ} (hM : 0 ≤ M) (hT : 0 < T) :
    ∃ C : ℝ, 0 < C ∧ ∀ s r : ℝ, 0 ≤ s → 0 ≤ r → ∀ f g : Fourier,
      RealValued f → MeanZero f → InSobolev s f →
      RealValued g → MeanZero g → InSobolev r g → hNorm 0 f + hNorm 0 g ≤ M →
      ∀ u w : ℝ → Fourier, KdVSolution s T f u → KdVSolution r T g w →
        ∀ t ∈ Set.Icc 0 T, hNorm 0 (u t - w t) ≤ C * hNorm 0 (f - g) := by
  obtain ⟨C', hC', CM, hCM, hb⟩ := source_flow_lipschitz externalLipschitz hM
    (by norm_num : (-1 : ℝ) < 0) le_rfl
  refine ⟨C' * CM ^ T, mul_pos hC' (Real.rpow_pos_of_pos hCM _), ?_⟩
  intro s r hs hr f g hfr hfm hf hgr hgm hg hfg u w hu hw t ht
  have hf0 := hf.of_le hs
  have hg0 := hg.of_le hr
  have hfh := homogeneous_reflectSign (hf0.to_homogeneous le_rfl hfm)
  have hgh := homogeneous_reflectSign (hg0.to_homogeneous le_rfl hgm)
  have hfg' : homogeneousNorm 0 (reflectSign f) + homogeneousNorm 0 (reflectSign g) ≤ M := by
    simpa only [homogeneousNorm_reflectSign, homogeneousNorm_zero] using hfg
  have hb' := hb T hT (reflectSign f) (reflectSign g) (reflectSign_real hfr)
    (reflectSign_real hgr) hfh hgh hfg' (fun t => sourceFrame t (u t))
    (fun t => sourceFrame t (w t)) (kdv_solution_sourceWeak hs hu)
    (kdv_solution_sourceWeak hr hw) ((kdv_solution_to_source hs hu).2.1.of_le hs)
    ((kdv_solution_to_source hr hw).2.1.of_le hr) t ht
  rw [sourceFrame_difference_norm] at hb'
  simpa only [← reflectSign_sub, homogeneousNorm_reflectSign,
    homogeneousNorm_zero] using hb'

end KdV
