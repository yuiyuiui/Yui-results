import Proof
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

def HomogeneousEssentiallyBounded (s T : ℝ) (v : ℝ → Fourier) : Prop :=
  ∃ w : ℝ → L2Seq, MemLp w ∞ (volume.restrict (Set.Icc 0 T)) ∧
    ∀ᵐ t ∂volume.restrict (Set.Icc 0 T), MeanZero (v t) ∧ (w t).val = homogeneousWeighted s (v t)

theorem HomogeneousEssentiallyBounded.inHom_ae {s T : ℝ} {v : ℝ → Fourier}
    (hv : HomogeneousEssentiallyBounded s T v) :
    ∀ᵐ t ∂volume.restrict (Set.Icc 0 T), InHomSobolev s (v t) := by
  obtain ⟨w, hw, heq⟩ := hv
  filter_upwards [heq] with t ht
  refine ⟨ht.1, ?_⟩
  rw [← ht.2]
  exact (w t).property

def homogeneousTrajectory (s T : ℝ) (v : ℝ → Fourier)
    (hv : ∀ t ∈ Set.Icc 0 T, InHomSobolev s (v t)) (t : ℝ) : L2Seq :=
  if ht : t ∈ Set.Icc 0 T then homogeneousLp s (v t) (hv t ht) else 0

theorem homogeneousTrajectory_norm_sub (s T : ℝ) (v : ℝ → Fourier)
    (hv : ∀ t ∈ Set.Icc 0 T, InHomSobolev s (v t)) {r t : ℝ}
    (hr : r ∈ Set.Icc 0 T) (ht : t ∈ Set.Icc 0 T) :
    ‖homogeneousTrajectory s T v hv r - homogeneousTrajectory s T v hv t‖ = homogeneousNorm s (v r - v t) := by
  simp only [homogeneousTrajectory, dif_pos hr, dif_pos ht]
  have heq : homogeneousLp s (v r - v t) ((hv r hr).sub (hv t ht)) =
      homogeneousLp s (v r) (hv r hr) - homogeneousLp s (v t) (hv t ht) := by
    apply Subtype.ext
    exact homogeneousWeighted_sub s (v r) (v t)
  rw [← heq, homogeneousLp_norm]

theorem HomSobolevContinuousOn.continuous_homogeneousTrajectory {s T : ℝ} {v : ℝ → Fourier}
    (hv : HomSobolevContinuousOn s T v) :
    ContinuousOn (homogeneousTrajectory s T v hv.1) (Set.Icc 0 T) := by
  rw [Metric.continuousOn_iff]
  intro t ht ε hε
  obtain ⟨δ, hδ, hb⟩ := hv.2 t ht ε hε
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrt
  rw [dist_eq_norm, homogeneousTrajectory_norm_sub s T v hv.1 hr ht]
  exact hb r hr (by simpa only [Real.dist_eq] using hrt)

/-- Continuous homogeneous paths have actual `L∞` representatives in time;
this is proved rather than assumed when applying the cited weak-flow results. -/
theorem HomSobolevContinuousOn.essentiallyBounded {s T : ℝ} {v : ℝ → Fourier}
    (hv : HomSobolevContinuousOn s T v) : HomogeneousEssentiallyBounded s T v := by
  let w := homogeneousTrajectory s T v hv.1
  have hc : ContinuousOn w (Set.Icc 0 T) := hv.continuous_homogeneousTrajectory
  have hbd : BddAbove ((fun t : ℝ => ‖w t‖) '' Set.Icc 0 T) :=
    (isCompact_Icc.image_of_continuousOn hc.norm).bddAbove
  obtain ⟨B, hB⟩ := hbd
  have hw : MemLp w ∞ (volume.restrict (Set.Icc 0 T)) :=
    MemLp.of_bound (hc.aestronglyMeasurable measurableSet_Icc) B (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact hB ⟨t, ht, rfl⟩)
  refine ⟨w, hw, ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  refine ⟨(hv.1 t ht).1, ?_⟩
  simp only [w, homogeneousTrajectory, dif_pos ht, homogeneousLp]

theorem HomSobolevContinuousOn.of_le {s r T : ℝ} (hsr : s ≤ r) {v : ℝ → Fourier}
    (hv : HomSobolevContinuousOn r T v) : HomSobolevContinuousOn s T v := by
  refine ⟨fun t ht => (hv.1 t ht).of_le hsr, ?_⟩
  intro t ht ε hε
  obtain ⟨δ, hδ, hb⟩ := hv.2 t ht ε hε
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrt
  exact (homogeneousNorm_mono ((hv.1 r hr).sub (hv.1 t ht)) hsr).trans_lt (hb r hr hrt)

/-- The cited source's mean-zero real weak solution class, in the precise
integrated Fourier representation of Definition 3.1. Its time-space requirement
is actual essential boundedness in the complete weighted `ℓ²` space. -/
def SourceWeakSolution (T : ℝ) (f : Fourier) (v : ℝ → Fourier) : Prop :=
  SourceNonzeroEquation T f v ∧ (∀ t ∈ Set.Icc 0 T, RealValued (v t) ∧ MeanZero (v t)) ∧
    HomogeneousEssentiallyBounded 0 T v

/-- Every target Sobolev solution satisfies the full weak source hypotheses
under the proved change of equation. -/
theorem kdv_solution_sourceWeak {s T : ℝ} (hs : 0 ≤ s) {f : Fourier} {u : ℝ → Fourier}
    (hu : KdVSolution s T f u) :
    SourceWeakSolution T (reflectSign f) (fun t => sourceFrame t (u t)) := by
  obtain ⟨hEq, hc, hr⟩ := kdv_solution_to_source hs hu
  refine ⟨hEq, ?_, (hc.of_le hs).essentiallyBounded⟩
  intro t ht
  exact ⟨hr t ht, (hc.1 t ht).1⟩

end KdV
