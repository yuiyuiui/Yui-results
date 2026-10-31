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

theorem T001 (n : ℕ) (m : ℕ) (u : WaveMap.Space n × ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H002 : ContDiffOn ℝ (∞ : ℕ∞ω) u (WaveMap.positive n)) (h_H004 : ∀ (x : WaveMap.Space n) (t : ℝ), 0 < t → ‖u (x,t)‖ = 1) (h_H005 : ∀ (x : WaveMap.Space n) (t : ℝ), 0 < t → ∃ a : ℝ, WaveMap.utt u x t - WaveMap.laplace u x t = a • u (x,t)) :
    ∀ (x : WaveMap.Space n) (t : ℝ), 0 < t →
  inner ℝ (u (x,t)) (WaveMap.ut u x t) = 0 ∧
  inner ℝ (WaveMap.ut u x t) (WaveMap.utt u x t - WaveMap.laplace u x t) = 0 ∧
  inner ℝ (u (x,t)) (WaveMap.utt u x t) = -(‖WaveMap.ut u x t‖ ^ 2) ∧
  (∀ j : Fin n, inner ℝ (u (x,t)) (WaveMap.uxx u j x t) = -(‖WaveMap.ux u j x t‖ ^ 2)) ∧
  (∀ a : ℝ, WaveMap.utt u x t - WaveMap.laplace u x t = a • u (x,t) →
    a = (∑ j, ‖WaveMap.ux u j x t‖ ^ 2) - ‖WaveMap.ut u x t‖ ^ 2) ∧
  WaveMap.utt u x t - WaveMap.laplace u x t =
    ((∑ j, ‖WaveMap.ux u j x t‖ ^ 2) - ‖WaveMap.ut u x t‖ ^ 2) • u (x,t) := by
  have unit_derivatives : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
      (f : E → WaveMap.Space m) (s : Set E),
      IsOpen s → ContDiffOn ℝ (∞ : ℕ∞ω) f s →
      (∀ y ∈ s, ‖f y‖ = 1) →
      ∀ x ∈ s, ∀ v : E,
        inner ℝ (f x) (fderiv ℝ f x v) = 0 ∧
        inner ℝ (f x) (fderiv ℝ (fun y => fderiv ℝ f y v) x v) =
          -(‖fderiv ℝ f x v‖ ^ 2) := by
    intro E _ _ f s hs hf hn
    have hd : ∀ x ∈ s, DifferentiableAt ℝ f x := by
      intro x hx
      exact (hf.contDiffAt (hs.mem_nhds hx)).differentiableAt (by simp)
    have hfirst : ∀ x ∈ s, ∀ v : E, inner ℝ (f x) (fderiv ℝ f x v) = 0 := by
      intro x hx v
      have he : (fun y => inner ℝ (f y) (f y)) =ᶠ[nhds x] (fun _ => (1 : ℝ)) := by
        filter_upwards [hs.mem_nhds hx] with y hy
        simp [real_inner_self_eq_norm_sq, hn y hy]
      have hz : fderiv ℝ (fun y => inner ℝ (f y) (f y)) x v = 0 := by
        rw [he.fderiv_eq]
        simp
      rw [fderiv_inner_apply ℝ (hd x hx) (hd x hx), real_inner_comm (f x) (fderiv ℝ f x v)] at hz
      linarith
    intro x hx v
    refine ⟨hfirst x hx v, ?_⟩
    have hdf : ContDiffOn ℝ (1 : ℕ∞ω) (fun y => fderiv ℝ f y v) s :=
      (hf.fderiv_of_isOpen (m := 1) hs (by decide)).clm_apply contDiffOn_const
    have hdd : DifferentiableAt ℝ (fun y => fderiv ℝ f y v) x :=
      (hdf.contDiffAt (hs.mem_nhds hx)).differentiableAt (by simp)
    have he : (fun y => inner ℝ (f y) (fderiv ℝ f y v)) =ᶠ[nhds x] (fun _ => (0 : ℝ)) := by
      filter_upwards [hs.mem_nhds hx] with y hy
      exact hfirst y hy v
    have hz : fderiv ℝ (fun y => inner ℝ (f y) (fderiv ℝ f y v)) x v = 0 := by
      rw [he.fderiv_eq]
      simp
    rw [fderiv_inner_apply ℝ (hd x hx) hdd, real_inner_self_eq_norm_sq] at hz
    linarith
  intro x t ht
  have htimeSmooth : ContDiffOn ℝ (∞ : ℕ∞ω) (fun r : ℝ => u (x,r)) (Ioi (0 : ℝ)) :=
    h_H002.comp (contDiffOn_const.prodMk contDiffOn_id) (by intro r hr; exact hr)
  have hspaceSmooth : ContDiffOn ℝ (∞ : ℕ∞ω) (fun y : WaveMap.Space n => u (y,t)) univ :=
    h_H002.comp (contDiffOn_id.prodMk contDiffOn_const) (by intro y hy; exact ht)
  have htime := unit_derivatives ℝ (fun r => u (x,r)) (Ioi (0 : ℝ))
    isOpen_Ioi htimeSmooth (fun r hr => h_H004 x r hr) t ht 1
  change inner ℝ (u (x,t)) (WaveMap.ut u x t) = 0 ∧
    inner ℝ (u (x,t)) (WaveMap.utt u x t) = -(‖WaveMap.ut u x t‖ ^ 2) at htime
  have hspace : ∀ j : Fin n, inner ℝ (u (x,t)) (WaveMap.uxx u j x t) =
      -(‖WaveMap.ux u j x t‖ ^ 2) := by
    intro j
    exact (unit_derivatives (WaveMap.Space n) (fun y => u (y,t)) univ
      isOpen_univ hspaceSmooth (fun y _ => h_H004 y t ht) x (mem_univ x)
      (PiLp.single 2 j 1)).2
  obtain ⟨a, ha⟩ := h_H005 x t ht
  have hnormal : inner ℝ (WaveMap.ut u x t)
      (WaveMap.utt u x t - WaveMap.laplace u x t) = 0 := by
    rw [ha, inner_smul_right, real_inner_comm (u (x,t)) (WaveMap.ut u x t),
      htime.1, mul_zero]
  have hu : inner ℝ (u (x,t)) (u (x,t)) = 1 := by
    rw [real_inner_self_eq_norm_sq, h_H004 x t ht]
    norm_num
  have hcoefficient : ∀ a : ℝ, WaveMap.utt u x t - WaveMap.laplace u x t = a • u (x,t) →
      a = (∑ j, ‖WaveMap.ux u j x t‖ ^ 2) - ‖WaveMap.ut u x t‖ ^ 2 := by
    intro b hb
    have heq := congrArg (fun v : WaveMap.Space m => inner ℝ (u (x,t)) v) hb
    rw [inner_sub_right, inner_smul_right, hu, mul_one, htime.2] at heq
    simp only [WaveMap.laplace, inner_sum, hspace, Finset.sum_neg_distrib] at heq
    linarith
  refine ⟨htime.1, hnormal, htime.2, hspace, hcoefficient, ?_⟩
  rw [ha, hcoefficient a ha]

#check @T001
#print axioms T001

end Translation
