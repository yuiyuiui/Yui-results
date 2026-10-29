import HomogeneousContinuity
noncomputable section
open scoped ComplexConjugate ENNReal
namespace KdV

def sobolevRestriction (s T : ℝ) (u : ℝ → Fourier)
    (hu : ∀ t ∈ Set.Icc 0 T, InSobolev s (u t)) : Set.Icc (0 : ℝ) T → Sobolev s :=
  fun t => ⟨u t.val, hu t.val t.property⟩

theorem sobolevRestriction_norm_sub (s T : ℝ) (u : ℝ → Fourier)
    (hu : ∀ t ∈ Set.Icc 0 T, InSobolev s (u t)) (r t : Set.Icc (0 : ℝ) T) :
    ‖sobolevRestriction s T u hu r - sobolevRestriction s T u hu t‖ =
      hNorm s (u r.val - u t.val) := sobolev_norm _

theorem SobolevContinuousOn.continuous_restriction {s T : ℝ} {u : ℝ → Fourier}
    (hu : SobolevContinuousOn s T u) : Continuous (sobolevRestriction s T u hu.1) := by
  rw [Metric.continuous_iff]
  intro t ε hε
  obtain ⟨δ, hδ, hb⟩ := hu.2 t.val t.property ε hε
  refine ⟨δ, hδ, ?_⟩
  intro r hr
  rw [dist_eq_norm, sobolevRestriction_norm_sub]
  exact hb r.val r.property (by simpa only [Subtype.dist_eq, Real.dist_eq] using hr)

theorem sobolevContinuousOn_of_restriction {s T : ℝ} {u : ℝ → Fourier}
    (hu : ∀ t ∈ Set.Icc 0 T, InSobolev s (u t))
    (hc : Continuous (sobolevRestriction s T u hu)) : SobolevContinuousOn s T u := by
  refine ⟨hu, ?_⟩
  intro t ht ε hε
  obtain ⟨δ, hδ, hb⟩ := Metric.continuous_iff.mp hc ⟨t, ht⟩ ε hε
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrt
  have hd : dist (⟨r, hr⟩ : Set.Icc (0 : ℝ) T) ⟨t, ht⟩ < δ := by
    simpa only [Subtype.dist_eq, Real.dist_eq] using hrt
  have h := hb ⟨r, hr⟩ hd
  simpa only [dist_eq_norm, sobolevRestriction_norm_sub] using h

set_option maxHeartbeats 800000 in
theorem SobolevContinuousOn.airy_path {s T : ℝ} {u : ℝ → Fourier}
    (hu : SobolevContinuousOn s T u) (a : ℝ → ℝ) (ha : Continuous a) :
    SobolevContinuousOn s T (fun t => airy (a t) (u t)) := by
  have hm : ∀ t ∈ Set.Icc 0 T, InSobolev s (airy (a t) (u t)) :=
    fun t ht => airy_inSobolev (hu.1 t ht) (a t)
  apply sobolevContinuousOn_of_restriction hm
  have heq : sobolevRestriction s T (fun t => airy (a t) (u t)) hm =
      (fun t : Set.Icc (0 : ℝ) T => airyMap s (a t.val) (sobolevRestriction s T u hu.1 t)) := by
    funext t
    apply Sobolev.ext
    rfl
  rw [heq]
  have hcTime : Continuous (fun t : Set.Icc (0 : ℝ) T => a t.val) :=
    ha.comp continuous_subtype_val
  have hcData : Continuous (sobolevRestriction s T u hu.1) := hu.continuous_restriction
  have hcPair : Continuous (fun t : Set.Icc (0 : ℝ) T => (a t.val, sobolevRestriction s T u hu.1 t)) :=
    hcTime.prodMk hcData
  exact (continuous_airy_action s).comp hcPair

theorem SobolevContinuousOn.of_le {s r T : ℝ} (hsr : s ≤ r) {u : ℝ → Fourier}
    (hu : SobolevContinuousOn r T u) : SobolevContinuousOn s T u := by
  refine ⟨fun t ht => (hu.1 t ht).of_le hsr, ?_⟩
  intro t ht ε hε
  obtain ⟨δ, hδ, hb⟩ := hu.2 t ht ε hε
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrt
  exact (hNorm_mono ((hu.1 r hr).sub (hu.1 t ht)) hsr).trans_lt (hb r hr hrt)

theorem inhomogeneous_continuity_to_homogeneous {s T : ℝ} (hs : 0 ≤ s) {u : ℝ → Fourier}
    (hu : SobolevContinuousOn s T u) (hum : ∀ t ∈ Set.Icc 0 T, MeanZero (u t)) :
    HomSobolevContinuousOn s T u := by
  refine ⟨fun t ht => (hu.1 t ht).to_homogeneous hs (hum t ht), ?_⟩
  intro t ht ε hε
  obtain ⟨δ, hδ, hb⟩ := hu.2 t ht ε hε
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrt
  have hm : MeanZero (u r - u t) := by
    change u r 0 - u t 0 = 0
    rw [hum r hr, hum t ht, sub_self]
  exact (homogeneousNorm_le_hNorm hs ((hu.1 r hr).sub (hu.1 t ht)) hm).trans_lt (hb r hr hrt)

end KdV
