import Proof
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

theorem RegularFourierPath.restrict {a b c d : ℝ} {f df : ℝ → Fourier}
    (hf : RegularFourierPath a b f df) (hac : a ≤ c) (hdb : d ≤ b) :
    RegularFourierPath c d f df where
  continuous k := (hf.continuous k).mono (fun _ ht => ⟨hac.trans ht.1, ht.2.trans hdb⟩)
  derivative_continuous k := (hf.derivative_continuous k).mono (fun _ ht => ⟨hac.trans ht.1, ht.2.trans hdb⟩)
  hasDerivAt t ht := hf.hasDerivAt t ⟨lt_of_le_of_lt hac ht.1, lt_of_lt_of_le ht.2 hdb⟩
  envelope := by
    obtain ⟨F, Fd, hF, hFd, hb⟩ := hf.envelope
    exact ⟨F, Fd, hF, hFd, fun t ht => hb t ⟨hac.trans ht.1, ht.2.trans hdb⟩⟩

theorem timeLInfinity_mono_interval {s a b c d : ℝ} {f : ℝ → Sobolev s}
    (hf : MemLp f ∞ (volume.restrict (Set.Icc a b))) (hsub : Set.Icc c d ⊆ Set.Icc a b) :
    timeLInfinity c d f ≤ timeLInfinity a b f := by
  exact ENNReal.toReal_mono hf.2.ne (eLpNorm_mono_measure f (Measure.restrict_mono hsub le_rfl))

theorem memLp_mono_interval {s a b c d : ℝ} {f : ℝ → Sobolev s}
    (hf : MemLp f ∞ (volume.restrict (Set.Icc a b))) (hsub : Set.Icc c d ⊆ Set.Icc a b) :
    MemLp f ∞ (volume.restrict (Set.Icc c d)) :=
  MemLp.mono_measure (Measure.restrict_mono hsub le_rfl) hf

theorem timeLInfinity_nonneg {s : ℝ} (a b : ℝ) (f : ℝ → Sobolev s) :
    0 ≤ timeLInfinity a b f := ENNReal.toReal_nonneg

theorem timeXNorm_nonneg (a b : ℝ) (f : ℝ → Sobolev 0) (df : ℝ → Sobolev (-pStar)) :
    0 ≤ timeXNorm a b f df := add_nonneg (timeLInfinity_nonneg _ _ _) (timeLInfinity_nonneg _ _ _)

def JZeroBundled (t : ℝ) (f g : Sobolev 0) : Sobolev 1 :=
  airyMap 1 (-t) (removeMeanMap 1 (productMap
    (airyMap 1 t (inverseDerivativeMap f)) (airyMap 1 t (inverseDerivativeMap g))))

theorem JZeroBundled_val (t : ℝ) (f g : Sobolev 0) : (JZeroBundled t f g).val = J t f.val g.val := rfl

theorem continuous_JZeroBundled {X : Type*} [TopologicalSpace X]
    {t : X → ℝ} {f g : X → Sobolev 0} (ht : Continuous t)
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => JZeroBundled (t x) (f x) (g x)) := by
  unfold JZeroBundled
  have hf' := continuous_airy_apply 1 ht ((inverseDerivativeMap).continuous.comp hf)
  have hg' := continuous_airy_apply 1 ht ((inverseDerivativeMap).continuous.comp hg)
  apply continuous_airy_apply 1 ht.neg
  fun_prop

theorem B_add_left {f g h : Fourier} (hf : InSobolev 0 f) (hg : InSobolev 0 g)
    (hh : InSobolev 0 h) (t : ℝ) : B t (f + g) h = B t f h + B t g h := by
  unfold B
  rw [airy_add, product_add_left (airy_inSobolev hf t) (airy_inSobolev hg t)
    (airy_inSobolev hh t), derivative_add, airy_add]

theorem B_add_right {f g h : Fourier} (hf : InSobolev 0 f) (hg : InSobolev 0 g)
    (hh : InSobolev 0 h) (t : ℝ) : B t f (g + h) = B t f g + B t f h := by
  rw [B_comm t f (g + h), B_add_left hg hh hf, B_comm t g f, B_comm t h f]

theorem B_smul_left (t : ℝ) (z : ℂ) (f g : Fourier) : B t (z • f) g = z • B t f g := by
  unfold B
  rw [airy_smul, product_smul_left, derivative_smul, airy_smul]

theorem B_smul_right (t : ℝ) (z : ℂ) (f g : Fourier) : B t f (z • g) = z • B t f g := by
  rw [B_comm t f (z • g), B_smul_left, B_comm t g f]

theorem B_diagonal_add {f g : Fourier} (hf : InSobolev 0 f) (hg : InSobolev 0 g) (t : ℝ) :
    B t (f + g) (f + g) = B t f f + (2 : ℂ) • B t f g + B t g g := by
  rw [B_add_left hf hg (hf.add hg), B_add_right hf hf hg, B_add_right hg hf hg, B_comm t g f]
  module

end KdV
