import FlowLimitHelpers
noncomputable section
open scoped ENNReal
open MeasureTheory KdV
namespace BareModelCompletion

 theorem source_exists_high (h41 : BITProposition41) (h43 : BITTheorems42And43) (h51 : BITTheorem51)
    {s T : ℝ} (hs : 1 / 2 < s) (hT : 0 < T) (f : Fourier)
    (hfr : RealValued f) (hf : InHomSobolev s f) :
    ∃ v : ℝ → Fourier, SourceWeakSolution T f v ∧ HomSobolevContinuousOn s T v := by
  obtain ⟨v, hv⟩ := original_limit_exists h41 h43 (by linarith : 0 < s) hT f hfr hf
  have hc := (h51.regularity s hs T hT f hfr hf v hv).1
  exact ⟨v, original_constructed_weak hv, hc⟩

 theorem source_exists_low (h41 : BITProposition41) (h43 : BITTheorems42And43) (h63 : BITTheorem63)
    {s T : ℝ} (hs : 0 < s) (hs1 : s ≤ 1 / 2) (hT : 0 < T) (f : Fourier)
    (hfr : RealValued f) (hf : InHomSobolev s f) :
    ∃ v : ℝ → Fourier, SourceWeakSolution T f v ∧ HomSobolevContinuousOn s T v := by
  obtain ⟨v, hv⟩ := original_limit_exists h41 h43 hs hT f hfr hf
  have hc := (h63.regularity s hs hs1 T hT f hfr hf v hv).1
  exact ⟨v, original_constructed_weak hv, hc⟩

theorem homogeneous_continuity_congr {s T : ℝ} {v w : ℝ → Fourier}
    (hc : HomSobolevContinuousOn s T w) (he : ∀ t ∈ Set.Icc 0 T, v t = w t) :
    HomSobolevContinuousOn s T v := by
  refine ⟨fun t ht => ?_, ?_⟩
  · rw [he t ht]
    exact hc.1 t ht
  · intro t ht ε hε
    obtain ⟨δ, hδ, hb⟩ := hc.2 t ht ε hε
    refine ⟨δ, hδ, ?_⟩
    intro r hr hrt
    rw [he r hr, he t ht]
    exact hb r hr hrt

 theorem high_to_historical (h41 : BITProposition41) (h43 : BITTheorems42And43) (h51 : BITTheorem51)
    (hL : BITTheorem65) : BITHigherRegularity := by
  intro s hs T hT f hfr hf v hv
  have hvweak : SourceWeakSolution T f v := by
    obtain ⟨σ, _, _, hcert⟩ := hv
    exact hcert.1
  obtain ⟨v0, hv0⟩ := original_limit_exists h41 h43 (by linarith : 0 < s) hT f hfr hf
  obtain ⟨hc0, hu0, he0⟩ := h51.regularity s hs T hT f hfr hf v0 hv0
  have heq := hu0 v hvweak
  have hc := homogeneous_continuity_congr hc0 heq
  have hu : BITUniqueWeak T f v := fun w hw t ht => (hu0 w hw t ht).trans (heq t ht).symm
  have he : ∀ t ∈ Set.Icc 0 T, homogeneousNorm 0 (v t) = homogeneousNorm 0 f := by
    intro t ht
    rw [heq t ht]
    exact he0 t ht
  have hsphere : ∀ S : ℝ, 0 < S → ∃ K : ℝ, 0 < K ∧
      ∀ f g : Fourier, RealValued f → RealValued g → InHomSobolev s f → InHomSobolev s g →
      homogeneousNorm s f = S → homogeneousNorm s g = S →
      ∀ v w : ℝ → Fourier, SourceWeakSolution T f v → SourceWeakSolution T g w →
      HomSobolevContinuousOn s T v → HomSobolevContinuousOn s T w →
      ∀ t ∈ Set.Icc 0 T, homogeneousNorm s (v t - w t) ≤ K * homogeneousNorm s (f - g) := by
    intro S hS
    obtain ⟨δ, hδ, C, hC, hb⟩ := h51.dependence s hs T hT
    have hCS : 0 < C (2 * S) := hC (2 * S) (by positivity)
    refine ⟨(C (2 * S) + 1) ^ (⌊T / δ (2 * S)⌋₊ + 1), by positivity, ?_⟩
    intro a b har hbr ha hb' haN hbN va vb hva hvb hvaC hvbC
    have hh := hb b a hbr har hb' ha vb va hvb hva hvbC hvaC
    simpa only [haN, hbN, show S + S = 2 * S by ring] using hh
  have hl := local_lipschitz_from_spheres hL (by linarith : 0 < s) hT
    (source_exists_high h41 h43 h51 hs hT) hsphere hfr hf hvweak hc
  exact ⟨hc, (fun w hw _ => hu w hw), hl, he⟩

theorem bitHomSup_le_of_ae {s T A : ℝ} (hA : 0 ≤ A) (v : ℝ → Fourier)
    (hb : ∀ᵐ t ∂volume.restrict (Set.Icc 0 T), homogeneousNorm s (v t) ≤ A) :
    bitHomSup s T v ≤ A := by
  have he : eLpNorm (fun t => homogeneousNorm s (v t)) ∞ (volume.restrict (Set.Icc 0 T)) ≤ ENNReal.ofReal A := by
    rw [eLpNorm_exponent_top]
    apply eLpNormEssSup_le_of_ae_bound
    filter_upwards [hb] with t ht
    simpa only [Real.norm_eq_abs, abs_of_nonneg (homogeneousNorm_nonneg _ _)] using ht
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top he
  simpa only [bitHomSup, ENNReal.toReal_ofReal hA] using ht

theorem homogeneous_essential_sub {s T : ℝ} {v w : ℝ → Fourier}
    (hv : HomogeneousEssentiallyBounded s T v) (hw : HomogeneousEssentiallyBounded s T w) :
    HomogeneousEssentiallyBounded s T (fun t => v t - w t) := by
  obtain ⟨V, hV, heV⟩ := hv
  obtain ⟨W, hW, heW⟩ := hw
  refine ⟨fun t => V t - W t, hV.sub hW, ?_⟩
  filter_upwards [heV, heW] with t ht ht'
  refine ⟨?_, ?_⟩
  · change v t 0 - w t 0 = 0
    rw [ht.1, ht'.1, sub_self]
  · change (V t).val - (W t).val = homogeneousWeighted s (v t - w t)
    rw [ht.2, ht'.2, homogeneousWeighted_sub]
    rfl

theorem homogeneous_essential_scalar_memLp {s T : ℝ} {v : ℝ → Fourier}
    (hv : HomogeneousEssentiallyBounded s T v) :
    MemLp (fun t => homogeneousNorm s (v t)) ∞ (volume.restrict (Set.Icc 0 T)) := by
  obtain ⟨V, hV, heV⟩ := hv
  have he : (fun t => ‖V t‖) =ᵐ[volume.restrict (Set.Icc 0 T)] (fun t => homogeneousNorm s (v t)) := by
    filter_upwards [heV] with t ht
    have hi : InHomSobolev s (v t) := ⟨ht.1, by rw [← ht.2]; exact (V t).property⟩
    have hh : homogeneousLp s (v t) hi = V t := Subtype.ext ht.2.symm
    rw [← hh, homogeneousLp_norm]
  exact (memLp_congr_ae he).mp hV.norm

/-- Both directions of the L-infinity norm/essential-bound correspondence.
Thus the a.e. formulation of the published (6.7) conclusion loses no content. -/
theorem bitHomSup_le_iff {s T B : ℝ} {v : ℝ → Fourier}
    (hv : HomogeneousEssentiallyBounded s T v) (hB : 0 ≤ B) :
    bitHomSup s T v ≤ B ↔
      ∀ᵐ t ∂volume.restrict (Set.Icc 0 T), homogeneousNorm s (v t) ≤ B := by
  constructor
  · intro hb
    have hm := homogeneous_essential_scalar_memLp hv
    have hfinite : eLpNormEssSup (fun t => homogeneousNorm s (v t))
        (volume.restrict (Set.Icc 0 T)) ≠ ∞ := by
      simpa only [eLpNorm_exponent_top] using hm.2.ne
    filter_upwards [ae_le_eLpNormEssSup (f := fun t => homogeneousNorm s (v t))
      (μ := volume.restrict (Set.Icc 0 T))] with t ht
    have hh := ENNReal.toReal_mono hfinite ht
    have hh' : homogeneousNorm s (v t) ≤ bitHomSup s T v := by
      simpa only [bitHomSup, eLpNorm_exponent_top, toReal_enorm, Real.norm_eq_abs,
        abs_of_nonneg (homogeneousNorm_nonneg _ _)] using hh
    exact hh'.trans hb
  · exact bitHomSup_le_of_ae hB v

theorem dependence67_norm_to_ae (h : BITDependence67Norm) : BITDependence67 := by
  intro s hs hs1 T hT M hM
  obtain ⟨τ, hτ, C, hC, C', hC', hb⟩ := h s hs hs1 T hT M hM
  refine ⟨τ, hτ, C, hC, C', hC', ?_⟩
  intro f g hfr hgr hf hg v w hv hw hvB hwB hbound
  have hK : 0 ≤ C' * (2 * C + 1) ^ (⌊T / τ⌋₊ + 1) := by positivity
  exact (bitHomSup_le_iff (homogeneous_essential_sub hvB hwB)
    (mul_nonneg hK (homogeneousNorm_nonneg _ _))).mp
    (hb f g hfr hgr hf hg v w hv hw hvB hwB hbound)

theorem dependence67_ae_to_norm (h : BITDependence67) : BITDependence67Norm := by
  intro s hs hs1 T hT M hM
  obtain ⟨τ, hτ, C, hC, C', hC', hb⟩ := h s hs hs1 T hT M hM
  refine ⟨τ, hτ, C, hC, C', hC', ?_⟩
  intro f g hfr hgr hf hg v w hv hw hvB hwB hbound
  have hK : 0 ≤ C' * (2 * C + 1) ^ (⌊T / τ⌋₊ + 1) := by positivity
  exact (bitHomSup_le_iff (homogeneous_essential_sub hvB hwB)
    (mul_nonneg hK (homogeneousNorm_nonneg _ _))).mpr
    (hb f g hfr hgr hf hg v w hv hw hvB hwB hbound)

theorem dependence67_iff : BITDependence67Norm ↔ BITDependence67 :=
  ⟨dependence67_norm_to_ae, dependence67_ae_to_norm⟩

/-- The common (4.13)/(4.20) bound transfers to every continuous weak flow by
original uniqueness. Its dependence remains fixed before the initial datum. -/
theorem low_fixed_sphere_bound (h41 : BITProposition41) (h43 : BITTheorems42And43) (h63 : BITTheorem63)
    {s T S : ℝ} (hs : 0 < s) (hs1 : s ≤ 1 / 2) (hT : 0 < T) (hS : 0 < S) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ f : Fourier, RealValued f → InHomSobolev s f →
      homogeneousNorm s f = S → ∀ v : ℝ → Fourier, SourceWeakSolution T f v →
      ∀ᵐ t ∂volume.restrict (Set.Icc 0 T), homogeneousNorm s (v t) ≤ A := by
  obtain ⟨A, hA, hgal, hl⟩ := h43 s hs.le S hS.le T hT S hS.le
  refine ⟨A, hA, ?_⟩
  intro f hfr hf hfN v hv
  have hf0 : homogeneousNorm 0 f ≤ S := (homogeneousNorm_mono hf hs.le).trans_eq hfN
  obtain ⟨G, hGG⟩ := source_global_galerkin_family h41 hs.le f hfr hf
  have hG (m : ℕ) := (hGG m).1 T hT
  obtain ⟨w, hw⟩ := hl hs f hfr hf hfN hf0 G hGG (s / 2) (by linarith) (by linarith)
  have hGB (m : ℕ) : ∀ t ∈ Set.Icc 0 T, homogeneousNorm s (G m t) ≤ A :=
    (hgal (m + 1) (by omega) f (G m) hfr hf hfN hf0
      (hG m).1 (hG m).2.1 (hG m).2.2).2
  have hconstructed : BITConstructedLimit43 s T f w :=
    ⟨s / 2, by linarith, by linarith, A, hA, G, hGG, hGB, hw⟩
  have hu := (h63.regularity s hs hs1 T hT f hfr hf w hconstructed).2
  filter_upwards [hw.2.2.1, ae_restrict_mem measurableSet_Icc] with t ht hti
  rw [hu v hv t hti]
  exact ht

 theorem low_to_historical (h41 : BITProposition41) (h43 : BITTheorems42And43) (h63 : BITTheorem63)
    (hL : BITTheorem65) : BITLowRegularity := by
  intro s hs hs1 T hT f hfr hf v hv
  have hvweak : SourceWeakSolution T f v := by
    obtain ⟨σ, _, _, hcert⟩ := hv
    exact hcert.1
  obtain ⟨v0, hv0⟩ := original_limit_exists h41 h43 hs hT f hfr hf
  obtain ⟨hc0, hu0⟩ := h63.regularity s hs hs1 T hT f hfr hf v0 hv0
  have heq := hu0 v hvweak
  have hc := homogeneous_continuity_congr hc0 heq
  have hu : BITUniqueWeak T f v := fun w hw t ht => (hu0 w hw t ht).trans (heq t ht).symm
  have hsphere : ∀ S : ℝ, 0 < S → ∃ K : ℝ, 0 < K ∧
      ∀ f g : Fourier, RealValued f → RealValued g → InHomSobolev s f → InHomSobolev s g →
      homogeneousNorm s f = S → homogeneousNorm s g = S →
      ∀ v w : ℝ → Fourier, SourceWeakSolution T f v → SourceWeakSolution T g w →
      HomSobolevContinuousOn s T v → HomSobolevContinuousOn s T w →
      ∀ t ∈ Set.Icc 0 T, homogeneousNorm s (v t - w t) ≤ K * homogeneousNorm s (f - g) := by
    intro S hS
    obtain ⟨A, hA, hbound⟩ := low_fixed_sphere_bound h41 h43 h63 hs hs1 hT hS
    obtain ⟨τ, hτ, C, hC, C', hC', hb⟩ := dependence67_norm_to_ae h63.dependence s hs hs1 T hT (2 * A) (by positivity)
    refine ⟨C' * (2 * C + 1) ^ (⌊T / τ⌋₊ + 1), by positivity, ?_⟩
    intro a b har hbr ha hb' haN hbN va vb hva hvb hvaC hvbC
    have hB : bitHomSup s T va + bitHomSup s T vb ≤ 2 * A := by
      have h1 := bitHomSup_le_of_ae hA va (hbound a har ha haN va hva)
      have h2 := bitHomSup_le_of_ae hA vb (hbound b hbr hb' hbN vb hvb)
      linarith
    have hh := hb a b har hbr ha hb' va vb hva hvb hvaC.essentiallyBounded hvbC.essentiallyBounded hB
    exact homogeneous_bound_of_ae hT (hvaC.sub hvbC) hh
  have hl := local_lipschitz_from_spheres hL hs hT
    (source_exists_low h41 h43 h63 hs hs1 hT) hsphere hfr hf hvweak hc
  exact ⟨hc, (fun w hw _ => hu w hw), hl⟩


theorem bit65_norm_to_historical (h : BITTheorem65Norm) : BITWeakerLipschitz := by
  intro M hM θ hθ hθ0
  obtain ⟨C, hC, A, hA, hb⟩ := h M hM θ hθ hθ0
  refine ⟨C, hC, A, hA, ?_⟩
  intro T hT f g hfr hgr hf hg hfg v w hv hw hvC hwC
  have he : HomogeneousEssentiallyBounded θ T (fun t => v t - w t) :=
    ((hvC.sub hwC).of_le hθ0).essentiallyBounded
  have hK : 0 ≤ C * A ^ T := by positivity
  exact (bitHomSup_le_iff he (mul_nonneg hK (homogeneousNorm_nonneg _ _))).mp
    (hb T hT f g hfr hgr hf hg hfg v w hv hw hvC hwC)

theorem bit65_historical_to_norm (h : BITWeakerLipschitz) : BITTheorem65Norm := by
  intro M hM θ hθ hθ0
  obtain ⟨C, hC, A, hA, hb⟩ := h M hM θ hθ hθ0
  refine ⟨C, hC, A, hA, ?_⟩
  intro T hT f g hfr hgr hf hg hfg v w hv hw hvC hwC
  have he : HomogeneousEssentiallyBounded θ T (fun t => v t - w t) :=
    ((hvC.sub hwC).of_le hθ0).essentiallyBounded
  have hK : 0 ≤ C * A ^ T := by positivity
  exact (bitHomSup_le_iff he (mul_nonneg hK (homogeneousNorm_nonneg _ _))).mpr
    (hb T hT f g hfr hgr hf hg hfg v w hv hw hvC hwC)

theorem bit65_iff_historical : BITTheorem65Norm ↔ BITWeakerLipschitz :=
  ⟨bit65_norm_to_historical, bit65_historical_to_norm⟩


/-- The all-time energy conclusion also follows for the low-regularity original
constructed flow once its published continuity conclusion is available. -/
theorem original_constructed_energy {s T : ℝ} (hs : 0 ≤ s) (hT : 0 < T)
    {f : Fourier} {v : ℝ → Fourier} (hv : BITConstructedLimit43 s T f v)
    (hc : HomSobolevContinuousOn s T v) :
    ∀ t ∈ Set.Icc 0 T, homogeneousNorm 0 (v t) = homogeneousNorm 0 f := by
  obtain ⟨σ, _, _, A, _, G, _, _, hv⟩ := hv
  exact Measure.eqOn_Icc_of_ae_eq volume (ne_of_lt hT) hv.2.2.2.1
    (hc.of_le hs).norm_continuousOn continuousOn_const


theorem bit65_all_bounds_iff : BITTheorem65AllBounds ↔ BITTheorem65Norm := by
  constructor
  · intro h M _ θ hθ hθ0
    exact h M θ hθ hθ0
  · intro h M θ hθ hθ0
    by_cases hM : 0 ≤ M
    · exact h M hM θ hθ hθ0
    · refine ⟨1, by norm_num, 1, by norm_num, ?_⟩
      intro T hT f g hfr hgr hf hg hfg
      have hf0 := homogeneousNorm_nonneg 0 f
      have hg0 := homogeneousNorm_nonneg 0 g
      have hfalse : False := by linarith
      exact False.elim hfalse

end BareModelCompletion
