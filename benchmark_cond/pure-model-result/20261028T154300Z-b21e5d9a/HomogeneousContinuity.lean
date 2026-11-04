import Homogeneous
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

@[simp] theorem homogeneousWeighted_sub (s : ℝ) (f g : Fourier) :
    homogeneousWeighted s (f - g) = homogeneousWeighted s f - homogeneousWeighted s g := by
  funext k
  simp [homogeneousWeighted, mul_sub]

theorem InHomSobolev.sub {s : ℝ} {f g : Fourier} (hf : InHomSobolev s f) (hg : InHomSobolev s g) :
    InHomSobolev s (f - g) := by
  refine ⟨?_, ?_⟩
  · change f 0 - g 0 = 0
    rw [hf.1, hg.1, sub_self]
  · rw [homogeneousWeighted_sub]
    exact hf.2.sub hg.2

/-- Norm continuity in the cited source's homogeneous Sobolev spaces. -/
def HomSobolevContinuousOn (s T : ℝ) (v : ℝ → Fourier) : Prop :=
  (∀ t ∈ Set.Icc 0 T, InHomSobolev s (v t)) ∧
    ∀ t ∈ Set.Icc 0 T, ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ r ∈ Set.Icc 0 T,
        |r - t| < δ → homogeneousNorm s (v r - v t) < ε

theorem homogeneous_continuity_to_inhomogeneous {s T : ℝ} (hs : 0 ≤ s) {v : ℝ → Fourier}
    (hv : HomSobolevContinuousOn s T v) : SobolevContinuousOn s T v := by
  refine ⟨fun t ht => (hv.1 t ht).to_inhomogeneous hs, ?_⟩
  intro t ht ε hε
  have hC : 0 < (2 : ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) s
  obtain ⟨δ, hδ, hb⟩ := hv.2 t ht (ε / (2 : ℝ) ^ s) (div_pos hε hC)
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrt
  calc
    _ ≤ (2 : ℝ) ^ s * homogeneousNorm s (v r - v t) :=
      hNorm_le_homogeneousNorm hs ((hv.1 r hr).sub (hv.1 t ht))
    _ < (2 : ℝ) ^ s * (ε / (2 : ℝ) ^ s) := mul_lt_mul_of_pos_left (hb r hr hrt) hC
    _ = ε := by field_simp [hC.ne']

theorem reflectSign_sub (f g : Fourier) : reflectSign (f - g) = reflectSign f - reflectSign g := by
  funext k
  simp only [reflectSign, Pi.sub_apply]
  ring

theorem HomSobolevContinuousOn.reflectSign {s T : ℝ} {v : ℝ → Fourier}
    (hv : HomSobolevContinuousOn s T v) :
    HomSobolevContinuousOn s T (fun t => KdV.reflectSign (v t)) := by
  refine ⟨fun t ht => homogeneous_reflectSign (hv.1 t ht), ?_⟩
  intro t ht ε hε
  obtain ⟨δ, hδ, hb⟩ := hv.2 t ht ε hε
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrt
  rw [← reflectSign_sub, homogeneousNorm_reflectSign]
  exact hb r hr hrt

/-- Definition 3.1 / equation (3.9) in Babin–Ilyin–Titi, retaining the source
phase sign. Membership and continuity hypotheses are stated separately. -/
def SourceTwistedEquation (T : ℝ) (f : Fourier) (v : ℝ → Fourier) : Prop :=
  v 0 = f ∧ ∀ t ∈ Set.Icc 0 T, ∀ k : ℤ,
    v t k = f k + (1 / 2 : ℂ) * ∫ s : ℝ in (0 : ℝ)..t, B (-s) (v s) (v s) k

/-- The target equation after conjugation by `S_{-t}`. -/
def TwistedEquation (T : ℝ) (f : Fourier) (v : ℝ → Fourier) : Prop :=
  v 0 = f ∧ ∀ t ∈ Set.Icc 0 T, ∀ k : ℤ,
    v t k = f k + (1 / 2 : ℂ) * ∫ s : ℝ in (0 : ℝ)..t, B s (v s) (v s) k

/-- The source-to-target transformation is proved, rather than being silently
incorporated into an external well-posedness assumption. -/
theorem sourceTwisted_to_target {T : ℝ} {f : Fourier} {v : ℝ → Fourier}
    (hv : SourceTwistedEquation T f v) :
    TwistedEquation T (reflectSign f) (fun t => reflectSign (v t)) := by
  refine ⟨congrArg reflectSign hv.1, ?_⟩
  intro t ht k
  have hs := hv.2 t ht (-k)
  have hi : (∫ s : ℝ in (0 : ℝ)..t, -B (-s) (v s) (v s) (-k)) =
      ∫ s : ℝ in (0 : ℝ)..t, B s (reflectSign (v s)) (reflectSign (v s)) k := by
    apply intervalIntegral.integral_congr
    intro s _
    exact congrFun (reflectSign_B s (v s) (v s)) k
  change -v t (-k) = -f (-k) + (1 / 2 : ℂ) * _
  rw [← hi, intervalIntegral.integral_neg]
  linear_combination -hs

end KdV
