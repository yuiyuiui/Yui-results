import RegularityBridges

noncomputable section
open scoped ENNReal
open MeasureTheory KdV
namespace BareModelCompletion

/-- Classical smooth solutions of (1), with the initial trace specified
separately. The PDE is differentiated in time; no Duhamel equation is a field. -/
structure PaperSmoothSolution (T : ℝ) (f : Fourier) (u : ℝ → Fourier) : Prop where
  initial : u 0 = f
  spatial : ∀ s : ℝ, SobolevContinuousOn s T u
  temporal : ∀ k : ℤ, ∀ m : ℕ, ContDiffOn ℝ m (fun t => u t k) (Set.Icc 0 T)
  equation : ∀ t ∈ Set.Ioo 0 T, ∀ k : ℤ,
    HasDerivAt (fun r => u r k) (physicalRHS (u t) k) t
  reality : ∀ t ∈ Set.Icc 0 T, RealValued (u t) ∧ MeanZero (u t)

/-- Variation of constants for the classical equation, on the entire closed
interval, including the independently supplied initial trace. -/
theorem classical_to_duhamel {T : ℝ} {f : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hc : SobolevContinuousOn 0 T u) (hi : u 0 = f)
    (hd : ∀ t ∈ Set.Ioo 0 T, ∀ k : ℤ,
      HasDerivAt (fun r => u r k) (physicalRHS (u t) k) t) : Duhamel T f u := by
  let v := fun t => airy (-t) (u t)
  have hvC : SobolevContinuousOn 0 T v := hc.airy_path (fun t : ℝ => -t) continuous_neg
  have hv0 : v 0 = f := by simp [v, hi]
  have hvE : TwistedEquation T f v := by
    refine ⟨hv0, ?_⟩
    intro t ht k
    have hcont : ContinuousOn (fun r => v r k) (Set.Icc 0 t) :=
      (hvC.coeff_continuousOn k).mono (Set.Icc_subset_Icc le_rfl ht.2)
    let U := sobolevExtension hT u hc
    have hUC : Continuous U := continuous_sobolevExtension hT _
    have hUv (r : ℝ) (hr : r ∈ Set.Icc 0 T) : (U r).val = u r :=
      sobolevExtension_val_on hT _ hr
    have hprod : ContinuousOn (fun r => product (u r) (u r) k) (Set.Icc 0 t) := by
      apply ((continuous_productCoefficientMap k hUC hUC).continuousOn).congr
      intro r hr
      change product (u r) (u r) k = product (U r).val (U r).val k
      rw [hUv r ⟨hr.1, hr.2.trans ht.2⟩]
    let E := fun r : ℝ => Complex.exp (Complex.I * ((-r : ℝ) : ℂ) * (k : ℂ) ^ 3)
    let D := fun r : ℝ => (1 / 2 : ℂ) * E r * (Complex.I * (k : ℂ)) * product (u r) (u r) k
    have hEC : Continuous E := by dsimp [E]; fun_prop
    have hDC : ContinuousOn D (Set.Icc 0 t) :=
      (((continuous_const.mul hEC).mul continuous_const).continuousOn).mul hprod
    have hder (r : ℝ) (hr : r ∈ Set.Ioo 0 t) : HasDerivAt (fun r => v r k) (D r) r := by
      have hE : HasDerivAt E (-(Complex.I * (k : ℂ) ^ 3) * E r) r := by
        have h := (((((hasDerivAt_id r).neg).ofReal_comp).const_mul Complex.I).mul_const ((k : ℂ) ^ 3)).cexp
        simpa only [E, Pi.neg_apply, id_eq, Complex.ofReal_neg, Complex.ofReal_one, mul_neg, mul_one, neg_mul,
          mul_comm] using h
      have h := hE.mul (hd r ⟨hr.1, hr.2.trans_le ht.2⟩ k)
      change HasDerivAt (fun r => E r * u r k) (D r) r
      apply h.congr_deriv
      rw [physicalRHS_coefficient]
      dsimp [D]
      ring
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 hcont hder
      (ContinuousOn.intervalIntegrable_of_Icc ht.1 hDC)
    have hD : (∫ r : ℝ in (0 : ℝ)..t, D r) = (1 / 2 : ℂ) * ∫ r : ℝ in (0 : ℝ)..t, B r (v r) (v r) k := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro r _
      dsimp [D, E, B, v, airy, derivative]
      rw [airy_inverse_neg]
      ring
    rw [hD, hv0] at hFTC
    linear_combination -hFTC
  have h := untwist_Duhamel hvE
  simpa only [v, airy_inverse_neg] using h

theorem paperSmooth_iff_historical {T : ℝ} (hT : 0 ≤ T) (f : Fourier) (u : ℝ → Fourier) :
    PaperSmoothSolution T f u ↔ SmoothSolution T f u := by
  constructor
  · intro h
    exact ⟨classical_to_duhamel hT (h.spatial 0) h.initial h.equation,
      h.spatial, h.temporal, h.reality⟩
  · intro h
    refine ⟨h.1.1, h.2.1, h.2.2.1, ?_, h.2.2.2⟩
    intro t ht k
    rw [physicalRHS_coefficient]
    exact rough_physical_coefficient_hasDerivAt hT (by norm_num : (0 : ℝ) ≤ 2)
      ⟨h.2.1 2, h.1, h.2.2.2⟩ ht k

/-- Smooth approximation in the paper's initial H^γ and uniform solution L²
topologies, using classical PDE solutions rather than integral equations. -/
def PaperSmoothApproximation (γ T : ℝ) (f : Fourier) (u : ℝ → Fourier) : Prop :=
  ∃ data : ℕ → Fourier, ∃ solutions : ℕ → ℝ → Fourier,
    (∀ m, PaperSmoothSolution T (data m) (solutions m)) ∧
    Filter.Tendsto (fun m => hNorm γ (data m - f)) Filter.atTop (nhds 0) ∧
    ∀ ε : ℝ, 0 < ε → ∃ m₀ : ℕ, ∀ m ≥ m₀,
      ∀ t ∈ Set.Icc 0 T, hNorm 0 (solutions m t - u t) < ε

theorem paperApproximation_iff_historical {γ T : ℝ} (hT : 0 ≤ T) (f : Fourier) (u : ℝ → Fourier) :
    PaperSmoothApproximation γ T f u ↔ ObtainedBySmoothApproximation γ T f u := by
  constructor <;> rintro ⟨data, solutions, hs, hd, hu⟩
  · exact ⟨data, solutions, fun m => (paperSmooth_iff_historical hT _ _).mp (hs m), hd, hu⟩
  · exact ⟨data, solutions, fun m => (paperSmooth_iff_historical hT _ _).mpr (hs m), hd, hu⟩


/-- The paper's spatial distribution pairing, with its normalized measure:
Fourier coefficients act bilinearly on the reflected test coefficients. -/
def paperPair (a ψ : Fourier) : ℂ := ∑' k : ℤ, a k * ψ (-k)

/-- Distributional equation (1), tested against every smooth spatial test and
every compactly supported smooth time test. All solutions are evaluated in
their continuous representatives by the surrounding solution definition. -/
def PaperDistributionalKdV (T : ℝ) (u : ℝ → Fourier) : Prop :=
  ∀ φ : ℝ → ℝ, ContDiff ℝ (⊤ : WithTop ℕ∞) φ → HasCompactSupport φ →
    Function.support φ ⊆ Set.Ioo 0 T →
    ∀ ψ : Fourier, (∀ s : ℝ, InSobolev s ψ) →
      (∫ t : ℝ in (0 : ℝ)..T, ((deriv φ t : ℝ) : ℂ) * paperPair (u t) ψ) =
        -(∫ t : ℝ in (0 : ℝ)..T, (φ t : ℂ) * paperPair (physicalRHS (u t)) ψ)

/-- The independent continuous distributional/initial-trace/approximation
convention in Section 2. Neither this definition nor its classical approximants
assume Duhamel, stability, or a convergence rate. -/
structure PaperSolution (γ T : ℝ) (f : Fourier) (u : ℝ → Fourier) : Prop where
  continuous : SobolevContinuousOn γ T u
  initial : u 0 = f
  reality : ∀ t ∈ Set.Icc 0 T, RealValued (u t) ∧ MeanZero (u t)
  equation : PaperDistributionalKdV T u
  approximation : PaperSmoothApproximation γ T f u

theorem kdv_to_paper_distribution {γ T : ℝ} {f : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hγ : 0 ≤ γ) (hu : KdVSolution γ T f u) : PaperDistributionalKdV T u := by
  obtain ⟨U, F, hUC, hFC, hval, hweak⟩ := kdv_solution_distributional_spatial_tests hT hγ hu
  intro φ hφ hsupp hsupport ψ hψ
  have hh := hweak φ hφ hsupp hsupport (⟨ψ, hψ 3⟩ : Sobolev 3)
  have he1 : (∫ t : ℝ in (0 : ℝ)..T, ((deriv φ t : ℝ) : ℂ) *
      distributionTest 3 ⟨ψ, hψ 3⟩ (inclusionMap (-3) 0 (by norm_num) (U t))) =
      ∫ t : ℝ in (0 : ℝ)..T, ((deriv φ t : ℝ) : ℂ) * paperPair (u t) ψ := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hT] at ht
    dsimp only
    rw [distributionTest_apply]
    change _ * (∑' k : ℤ, (U t).val k * ψ (-k)) = _
    rw [(hval t ht).1]
    rfl
  have he2 : (∫ t : ℝ in (0 : ℝ)..T, (φ t : ℂ) * distributionTest 3 ⟨ψ, hψ 3⟩ (F t)) =
      ∫ t : ℝ in (0 : ℝ)..T, (φ t : ℂ) * paperPair (physicalRHS (u t)) ψ := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hT] at ht
    dsimp only
    rw [distributionTest_apply, (hval t ht).2]
    rfl
  rwa [he1, he2] at hh

/-- Integral equations depend only on the closed-interval representative. -/
theorem duhamel_congr_on {T : ℝ} (hT : 0 ≤ T) {f : Fourier} {u v : ℝ → Fourier}
    (hd : Duhamel T f v) (heq : ∀ t ∈ Set.Icc 0 T, u t = v t) : Duhamel T f u := by
  refine ⟨(heq 0 ⟨le_rfl, hT⟩).trans hd.1, ?_⟩
  intro t ht k
  rw [heq t ht, hd.2 t ht k]
  congr 2
  apply intervalIntegral.integral_congr
  intro r hr
  rw [Set.uIcc_of_le ht.1] at hr
  dsimp only
  rw [heq r ⟨hr.1, hr.2.trans ht.2⟩]

/-- Smooth approximation determines the same continuous representative as the
exact flow. This comparison uses exact-flow theorems only, and assumes no PDE
or integral equation for the limit path. -/
theorem approximation_determines_flow
    (h41 : BITProposition41) (h43 : BITTheorems42And43)
    (h51 : BITTheorem51) (h63 : BITTheorem63) (h65 : BITTheorem65)
    {γ T : ℝ} (hγ : 0 < γ) (hT : 0 < T) {f : Fourier}
    (hf : InSobolev γ f) (hfr : RealValued f) (hfm : MeanZero f)
    {u : ℝ → Fourier} (hc : SobolevContinuousOn γ T u)
    (ha : ObtainedBySmoothApproximation γ T f u) : KdVSolution γ T f u := by
  obtain ⟨v, hv⟩ := positive_kdv_flow_exists
    (galerkin_to_historical (bit42_from_joint h43)) (limit_to_historical h41 h43)
    (high_to_historical h41 h43 h51 h65) (low_to_historical h41 h43 h63 h65)
    hγ hT hf hfr hfm
  obtain ⟨data, solutions, hsol, hdata, happ⟩ := ha
  have hzero : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT.le⟩
  have hdγ (m : ℕ) : InSobolev γ (data m) := by
    have hh := (hsol m).2.1 γ |>.1 0 hzero
    rwa [(hsol m).1.1] at hh
  have hd0 (m : ℕ) := (hdγ m).of_le hγ.le
  have hdr (m : ℕ) : RealValued (data m) ∧ MeanZero (data m) := by
    simpa only [(hsol m).1.1] using (hsol m).2.2.2 0 hzero
  have hdif (m : ℕ) := (hdγ m).sub hf
  have hdata0 : Filter.Tendsto (fun m => hNorm 0 (data m - f)) Filter.atTop (nhds 0) :=
    squeeze_zero (fun m => hNorm_nonneg _ _) (fun m => hNorm_mono (hdif m) hγ.le) hdata
  obtain ⟨C, hC, hdep⟩ := kdv_flow_l2_lipschitz h65
    (show 0 ≤ 2 * hNorm 0 f + 1 by linarith [hNorm_nonneg 0 f]) hT
  have hbound : ∀ᶠ m : ℕ in Filter.atTop, hNorm 0 (data m) + hNorm 0 f ≤ 2 * hNorm 0 f + 1 := by
    filter_upwards [hdata0.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with m hm
    have hh : hNorm 0 (data m) ≤ hNorm 0 (data m - f) + hNorm 0 f := by
      simpa only [sub_add_cancel] using hNorm_add_le ((hd0 m).sub (hf.of_le hγ.le)) (hf.of_le hγ.le)
    linarith
  have heq : ∀ t ∈ Set.Icc 0 T, u t = v t := by
    intro t ht
    have hun := (hc.1 t ht).of_le hγ.le
    have hvn := (hv.1.1 t ht).of_le hγ.le
    have hlim : Filter.Tendsto (fun m => C * hNorm 0 (data m - f)) Filter.atTop (nhds 0) := by
      simpa only [mul_zero] using (tendsto_const_nhds (x := C)).mul hdata0
    have hz : hNorm 0 (u t - v t) ≤ 0 := by
      apply le_of_forall_pos_le_add
      intro ε hε
      obtain ⟨m₀, hm₀⟩ := happ (ε / 2) (by positivity)
      have hevent := hlim.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by positivity))
      obtain ⟨m, hmB, hmE, hmm⟩ := (hbound.and (hevent.and (Filter.eventually_ge_atTop m₀))).exists
      have hsm : KdVSolution γ T (data m) (solutions m) :=
        ⟨(hsol m).2.1 γ, (hsol m).1, (hsol m).2.2.2⟩
      have hcomp := hdep γ γ hγ.le hγ.le (data m) f (hdr m).1 (hdr m).2 (hdγ m)
        hfr hfm hf hmB (solutions m) v hsm hv t ht
      have hsn := ((hsol m).2.1 0).1 t ht
      have hsplit : u t - v t = (u t - solutions m t) + (solutions m t - v t) := by abel
      have hh := hNorm_add_le (hun.sub hsn) (hsn.sub hvn)
      rw [← hsplit, hNorm_sub_symm 0 (u t) (solutions m t)] at hh
      have happm := hm₀ m hmm t ht
      linarith
    funext k
    have hk := weighted_coeff_bound (hun.sub hvn) k
    rw [weighted_zero] at hk
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (hk.trans hz) (norm_nonneg _)))
  exact ⟨hc, duhamel_congr_on hT.le hv.2.1 heq, fun t ht => heq t ht ▸ hv.2.2 t ht⟩

/-- Full two-way correspondence with the paper's independent distributional
PDE, initial trace and classical smooth approximation convention. -/
theorem paperSolution_iff_exactSolution
    (h41 : BITProposition41) (h43 : BITTheorems42And43)
    (h51 : BITTheorem51) (h63 : BITTheorem63) (h65 : BITTheorem65)
    {γ T : ℝ} (hγ : 0 < γ) (hT : 0 < T) {f : Fourier}
    (hf : InSobolev γ f) (hfr : RealValued f) (hfm : MeanZero f) (u : ℝ → Fourier) :
    PaperSolution γ T f u ↔ ExactSolution γ T f u := by
  constructor
  · intro h
    have ha := (paperApproximation_iff_historical hT.le f u).mp h.approximation
    exact ⟨approximation_determines_flow h41 h43 h51 h63 h65 hγ hT hf hfr hfm h.continuous ha, ha⟩
  · intro h
    exact ⟨h.1.1, h.1.2.1.1, h.1.2.2, kdv_to_paper_distribution hT.le hγ.le h.1,
      (paperApproximation_iff_historical hT.le f u).mpr h.2⟩


/-- Continuous representatives which agree almost everywhere agree at both
endpoints as well as in the interior. No extra trace convention is imposed. -/
theorem continuous_representatives_eq {γ T : ℝ} (hT : 0 < T)
    {u v : ℝ → Fourier} (hu : SobolevContinuousOn γ T u) (hv : SobolevContinuousOn γ T v)
    (he : u =ᵐ[volume.restrict (Set.Icc 0 T)] v) :
    ∀ t ∈ Set.Icc 0 T, u t = v t := by
  intro t ht
  funext k
  apply Measure.eqOn_Icc_of_ae_eq volume (ne_of_lt hT) ?_
    (hu.coeff_continuousOn k) (hv.coeff_continuousOn k) ht
  filter_upwards [he] with r hr
  exact congrFun hr k

/-- The target statement with the paper's independent solution convention.
Every other definition and quantifier is literally the historical target. -/
def PaperTheoremOne : Prop :=
  ∀ T : ℝ, 0 < T → ∀ γ : ℝ, 0 < γ → γ ≤ 1 → ∀ R : ℝ, 0 < R →
    ∃ C : ℝ, 0 < C ∧ ∃ τ₀ : ℝ, 0 < τ₀ ∧
      ∀ f : Fourier, InSobolev γ f → RealValued f → MeanZero f → hNorm γ f ≤ R →
        ∀ u : ℝ → Fourier, PaperSolution γ T f u →
          ∀ L : ℕ, 0 < L → T / (L : ℝ) ≤ τ₀ →
            maximumError T L f u ≤ C * (T / (L : ℝ)) ^ γ

/-- Substantive two-way target equivalence; it preserves C and τ₀ exactly,
the uniform data ball, the unfiltered step, and the complete time grid. -/
theorem theoremOne_iff_paper
    (h41 : BITProposition41) (h43 : BITTheorems42And43)
    (h51 : BITTheorem51) (h63 : BITTheorem63) (h65 : BITTheorem65) :
    TheoremOne ↔ PaperTheoremOne := by
  constructor <;> intro h T hT γ hγ hγ1 R hR
  · obtain ⟨C, hC, τ₀, hτ₀, hb⟩ := h T hT γ hγ hγ1 R hR
    refine ⟨C, hC, τ₀, hτ₀, ?_⟩
    intro f hf hfr hfm hfR u hu
    exact hb f hf hfr hfm hfR u
      ((paperSolution_iff_exactSolution h41 h43 h51 h63 h65 hγ hT hf hfr hfm u).mp hu)
  · obtain ⟨C, hC, τ₀, hτ₀, hb⟩ := h T hT γ hγ hγ1 R hR
    refine ⟨C, hC, τ₀, hτ₀, ?_⟩
    intro f hf hfr hfm hfR u hu
    exact hb f hf hfr hfm hfR u
      ((paperSolution_iff_exactSolution h41 h43 h51 h63 h65 hγ hT hf hfr hfm u).mpr hu)

end BareModelCompletion
