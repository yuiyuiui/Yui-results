import Mathlib
open MeasureTheory Set Filter
open scoped BigOperators ContDiff
noncomputable section
namespace WaveMap
abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)
def positive (n : ℕ) : Set (Space n × ℝ) := {p | 0 < p.2}
def box (n : ℕ) (R : ℝ) : Set (Space n) := {x | ∀ j, x j ∈ Icc (-R) R}
def openBox (n : ℕ) (R : ℝ) : Set (Space n) := {x | ∀ j, x j ∈ Ioo (-R) R}
def timeInterval (t : ℝ) : Set ℝ := Icc (t / 2) (3 * t / 2)
def timeInterior (t : ℝ) : Set ℝ := Ioo (t / 2) (3 * t / 2)
def spatial {n : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Space n → F) (j : Fin n) (x : Space n) : F :=
  fderiv ℝ f x (PiLp.single 2 j 1)
def ut {n m : ℕ} (u : Space n × ℝ → Space m) (x : Space n) (t : ℝ) : Space m :=
  deriv (fun r => u (x, r)) t
def utt {n m : ℕ} (u : Space n × ℝ → Space m) (x : Space n) (t : ℝ) : Space m :=
  deriv (ut u x) t
def ux {n m : ℕ} (u : Space n × ℝ → Space m) (j : Fin n) (x : Space n) (t : ℝ) : Space m :=
  spatial (fun y => u (y, t)) j x
def uxx {n m : ℕ} (u : Space n × ℝ → Space m) (j : Fin n) (x : Space n) (t : ℝ) : Space m :=
  spatial (fun y => ux u j y t) j x
def utx {n m : ℕ} (u : Space n × ℝ → Space m) (j : Fin n) (x : Space n) (t : ℝ) : Space m :=
  spatial (fun y => ut u y t) j x
def laplace {n m : ℕ} (u : Space n × ℝ → Space m) (x : Space n) (t : ℝ) : Space m :=
  ∑ j, uxx u j x t
def density {n m : ℕ} (u : Space n × ℝ → Space m) (x : Space n) (t : ℝ) : ℝ :=
  ‖ut u x t‖ ^ 2 + ∑ j, ‖ux u j x t‖ ^ 2
def densityTime {n m : ℕ} (u : Space n × ℝ → Space m) (x : Space n) (t : ℝ) : ℝ :=
  deriv (density u x) t
def energy {n m : ℕ} (u : Space n × ℝ → Space m) (t : ℝ) : ℝ :=
  ∫ x, density u x t
def kineticProduct {n m : ℕ} (u : Space n × ℝ → Space m) (t : ℝ) (x : Space n) : ℝ :=
  inner ℝ (ut u x t) (utt u x t)
def gradientProduct {n m : ℕ} (u : Space n × ℝ → Space m) (j : Fin n) (t : ℝ) (x : Space n) : ℝ :=
  inner ℝ (ux u j x t) (utx u j x t)
def laplaceProduct {n m : ℕ} (u : Space n × ℝ → Space m) (j : Fin n) (t : ℝ) (x : Space n) : ℝ :=
  inner ℝ (ut u x t) (uxx u j x t)
def flux {n m : ℕ} (u : Space n × ℝ → Space m) (j : Fin n) (t : ℝ) (x : Space n) : ℝ :=
  inner ℝ (ut u x t) (ux u j x t)
def terms {n m : ℕ} (u : Space n × ℝ → Space m) (t : ℝ) (j : Fin n) : List (Space n → ℝ) :=
  [fun x => density u x t, fun x => densityTime u x t, kineticProduct u t,
   gradientProduct u j t, laplaceProduct u j t, flux u j t, spatial (flux u j t) j]
def quotient {n m : ℕ} (u : Space n × ℝ → Space m) (t h : ℝ) (x : Space n) : ℝ :=
  (density u x (t + h) - density u x t) / h
def bound (n : ℕ) (R B : ℝ) : Space n → ℝ :=
  (box n R).indicator (fun _ => B)
end WaveMap

namespace Translation
set_option autoImplicit false

theorem T004 (n : ℕ) (m : ℕ) (u : WaveMap.Space n × ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H002 : ContDiffOn ℝ (∞ : ℕ∞ω) u (WaveMap.positive n)) :
    ∀ (x : WaveMap.Space n) (t : ℝ), 0 < t →
  HasDerivAt (WaveMap.density u x) (WaveMap.densityTime u x t) t ∧
  WaveMap.densityTime u x t = 2 * WaveMap.kineticProduct u t x +
    2 * ∑ j, WaveMap.gradientProduct u j t x := by
  have hderivs : ∀ (x : WaveMap.Space n) (t : ℝ), 0 < t →
      HasDerivAt (WaveMap.ut u x) (WaveMap.utt u x t) t ∧
        ∀ j : Fin n, HasDerivAt (fun r => WaveMap.ux u j x r) (WaveMap.utx u j x t) t := by
    have hopen : IsOpen (WaveMap.positive n) := isOpen_lt continuous_const continuous_snd
    have hsmooth (y : WaveMap.Space n) (s : ℝ) (hs : 0 < s) :
        ContDiffAt ℝ (∞ : ℕ∞ω) u (y, s) :=
      h_H002.contDiffAt (hopen.mem_nhds hs)
    have htime (y : WaveMap.Space n) (s : ℝ) (hs : 0 < s) :
        WaveMap.ut u y s = fderiv ℝ u (y, s) (0, 1) := by
      have hd := ((hsmooth y s hs).differentiableAt (by simp)).hasFDerivAt
      simpa [WaveMap.ut, Function.comp_def] using
        (hd.comp_hasDerivAt s ((hasDerivAt_const s y).prodMk (hasDerivAt_id s))).deriv
    have hspace (y : WaveMap.Space n) (s : ℝ) (hs : 0 < s) (j : Fin n) :
        WaveMap.ux u j y s =
          fderiv ℝ u (y, s) (PiLp.single 2 j 1, 0) := by
      have hd := ((hsmooth y s hs).differentiableAt (by simp)).hasFDerivAt
      have he := (hd.comp y (hasFDerivAt_prodMk_left (𝕜 := ℝ) y s)).fderiv
      simp only [Function.comp_def] at he
      simp only [WaveMap.ux, WaveMap.spatial, he, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.inl_apply]
    intro x t ht
    have h := hsmooth x t ht
    have hdf : DifferentiableAt ℝ (fderiv ℝ u) (x, t) :=
      (h.fderiv_right (m := 1) (by
        change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top)).differentiableAt one_ne_zero
    have hdir (v : WaveMap.Space n × ℝ) :
        HasFDerivAt (fun p => fderiv ℝ u p v)
          ((fderiv ℝ (fderiv ℝ u) (x, t)).flip v) (x, t) := by
      simpa using hdf.hasFDerivAt.clm_apply (hasFDerivAt_const v (x, t))
    have hT : HasFDerivAt (fun p : WaveMap.Space n × ℝ => WaveMap.ut u p.1 p.2)
        ((fderiv ℝ (fderiv ℝ u) (x, t)).flip (0, 1)) (x, t) := by
      apply (hdir (0, 1)).congr_of_eventuallyEq
      filter_upwards [hopen.mem_nhds ht] with p hp
      exact htime p.1 p.2 hp
    constructor
    · exact (hT.comp_hasDerivAt t
        ((hasDerivAt_const t x).prodMk (hasDerivAt_id t))).differentiableAt.hasDerivAt
    · intro j
      have hX : HasFDerivAt (fun p : WaveMap.Space n × ℝ => WaveMap.ux u j p.1 p.2)
          ((fderiv ℝ (fderiv ℝ u) (x, t)).flip (PiLp.single 2 j 1, 0)) (x, t) := by
        apply (hdir (PiLp.single 2 j 1, 0)).congr_of_eventuallyEq
        filter_upwards [hopen.mem_nhds ht] with p hp
        exact hspace p.1 p.2 hp j
      have htx : WaveMap.utx u j x t =
          fderiv ℝ (fderiv ℝ u) (x, t) (PiLp.single 2 j 1, 0) (0, 1) := by
        have he := (hT.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x t)).fderiv
        simp only [Function.comp_def] at he
        simp [WaveMap.utx, WaveMap.spatial, he]
      have hsym := h.isSymmSndFDerivAt (by
        simp only [minSmoothness_of_isRCLikeNormedField]
        change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top)
      have hd := hX.comp_hasDerivAt t
        ((hasDerivAt_const t x).prodMk (hasDerivAt_id t))
      simpa only [Function.comp_def, ContinuousLinearMap.flip_apply,
        htx, hsym.eq (0, 1) (PiLp.single 2 j 1, 0)] using hd
  intro x t ht
  obtain ⟨hT, hX⟩ := hderivs x t ht
  have hd : HasDerivAt (WaveMap.density u x)
      (2 * WaveMap.kineticProduct u t x +
        2 * ∑ j, WaveMap.gradientProduct u j t x) t := by
    change HasDerivAt (fun r => ‖WaveMap.ut u x r‖ ^ 2 +
      ∑ j : Fin n, ‖WaveMap.ux u j x r‖ ^ 2) _ t
    simpa [WaveMap.kineticProduct, WaveMap.gradientProduct,
      Finset.mul_sum] using
      hT.norm_sq.fun_add (HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => (hX j).norm_sq))
  exact ⟨by simpa only [WaveMap.densityTime, hd.deriv] using hd, hd.deriv⟩

#check @T004
#print axioms T004

end Translation
