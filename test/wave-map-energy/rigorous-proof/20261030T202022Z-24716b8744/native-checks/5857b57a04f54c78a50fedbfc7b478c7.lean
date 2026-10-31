import Mathlib
open scoped ContDiff Topology BigOperators
open Set MeasureTheory
noncomputable section
namespace WaveMap
abbrev V (n : ℕ) := Fin n → ℝ
abbrev W (m : ℕ) := EuclideanSpace ℝ (Fin m)
def domain (n : ℕ) : Set (V n × ℝ) := {p | 0 < p.2}
def box (n : ℕ) (R : ℝ) : Set (V n) := Set.Icc (fun _ => -R) (fun _ => R)
def innerBox (n : ℕ) (R : ℝ) : Set (V n) := {x | ∀ j, -R < x j ∧ x j < R}
def ut {n m : ℕ} (u : V n × ℝ → W m) (x : V n) (t : ℝ) : W m :=
  deriv (fun s => u (x,s)) t
def utt {n m : ℕ} (u : V n × ℝ → W m) (x : V n) (t : ℝ) : W m :=
  deriv (fun s => ut u x s) t
def ux {n m : ℕ} (u : V n × ℝ → W m) (j : Fin n) (x : V n) (t : ℝ) : W m :=
  fderiv ℝ (fun y => u (y,t)) x (Pi.single j 1)
def uxx {n m : ℕ} (u : V n × ℝ → W m) (j : Fin n) (x : V n) (t : ℝ) : W m :=
  fderiv ℝ (fun y => ux u j y t) x (Pi.single j 1)
def uxt {n m : ℕ} (u : V n × ℝ → W m) (j : Fin n) (x : V n) (t : ℝ) : W m :=
  fderiv ℝ (fun y => ut u y t) x (Pi.single j 1)
def lap {n m : ℕ} (u : V n × ℝ → W m) (x : V n) (t : ℝ) : W m :=
  ∑ j, uxx u j x t
def e {n m : ℕ} (u : V n × ℝ → W m) (x : V n) (t : ℝ) : ℝ :=
  ‖ut u x t‖ ^ 2 + ∑ j, ‖ux u j x t‖ ^ 2
def et {n m : ℕ} (u : V n × ℝ → W m) (x : V n) (t : ℝ) : ℝ :=
  deriv (fun s => e u x s) t
def A {n m : ℕ} (u : V n × ℝ → W m) (x : V n) (t : ℝ) : ℝ :=
  inner ℝ (ut u x t) (utt u x t)
def B {n m : ℕ} (u : V n × ℝ → W m) (j : Fin n) (x : V n) (t : ℝ) : ℝ :=
  inner ℝ (ux u j x t) (uxt u j x t)
def T {n m : ℕ} (u : V n × ℝ → W m) (j : Fin n) (x : V n) (t : ℝ) : ℝ :=
  inner ℝ (ut u x t) (uxx u j x t)
def g {n m : ℕ} (u : V n × ℝ → W m) (j : Fin n) (x : V n) (t : ℝ) : ℝ :=
  inner ℝ (ut u x t) (ux u j x t)
def dg {n m : ℕ} (u : V n × ℝ → W m) (j : Fin n) (x : V n) (t : ℝ) : ℝ :=
  fderiv ℝ (fun y => g u j y t) x (Pi.single j 1)
def energy {n m : ℕ} (u : V n × ℝ → W m) (t : ℝ) : ℝ :=
  ∫ x, e u x t
def fields {n m : ℕ} (u : V n × ℝ → W m) : Set ((V n × ℝ) → ℝ) :=
  {f | f = (fun p => e u p.1 p.2) ∨ f = (fun p => et u p.1 p.2) ∨
    f = (fun p => A u p.1 p.2) ∨
    (∃ j, f = (fun p => B u j p.1 p.2)) ∨
    (∃ j, f = (fun p => T u j p.1 p.2)) ∨
    (∃ j, f = (fun p => g u j p.1 p.2)) ∨
    (∃ j, f = (fun p => dg u j p.1 p.2))}
end WaveMap
open WaveMap

namespace Translation
set_option autoImplicit false

theorem T001 (n : ℕ) (m : ℕ) (u : V n × ℝ → W m) (q : W m) (h_H002 : ContDiffOn ℝ ∞ u (domain n)) (h_H004 : ∀ x t, 0 < t → ‖u (x,t)‖ = 1) (h_H005 : ∀ x t, 0 < t → ∃ a : ℝ, utt u x t - lap u x t = a • u (x,t)) :
    ∀ x t, 0 < t →
inner ℝ (u (x,t)) (ut u x t) = 0 ∧
inner ℝ (ut u x t) (utt u x t - lap u x t) = 0 ∧
inner ℝ (u (x,t)) (utt u x t) = -(‖ut u x t‖^2) ∧
(∀ j : Fin n, inner ℝ (u (x,t)) (uxx u j x t) = -(‖ux u j x t‖^2)) ∧
(∀ a : ℝ, utt u x t - lap u x t = a • u (x,t) →
a = (∑ j, ‖ux u j x t‖^2) - ‖ut u x t‖^2) ∧
utt u x t - lap u x t = ((∑ j, ‖ux u j x t‖^2) - ‖ut u x t‖^2) • u (x,t) := by
  classical
  have geometry : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → W m) (s : Set E), IsOpen s →
    (∀ y ∈ s, ContDiffAt ℝ 2 f y) →
    (∀ y ∈ s, ‖f y‖ = 1) →
    ∀ z ∈ s, ∀ v : E,
      inner ℝ (f z) (fderiv ℝ f z v) = 0 ∧
      inner ℝ (f z) (fderiv ℝ (fun y => fderiv ℝ f y v) z v) =
        -(‖fderiv ℝ f z v‖ ^ 2) := by
    intro E _ _ f s hs hf hn
    have first : ∀ z ∈ s, ∀ v : E, inner ℝ (f z) (fderiv ℝ f z v) = 0 := by
      intro z hz v
      have heq : (fun y => inner ℝ (f y) (f y)) =ᶠ[𝓝 z] (fun _ => (1 : ℝ)) := by
        filter_upwards [hs.mem_nhds hz] with y hy
        rw [real_inner_self_eq_norm_sq, hn y hy]
        norm_num
      have hd := ((hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) z).congr_of_eventuallyEq heq).fderiv
      have he := congrArg (fun L : E →L[ℝ] ℝ => L v) hd
      rw [fderiv_inner_apply ℝ (hf z hz |>.differentiableAt (by norm_num))
        (hf z hz |>.differentiableAt (by norm_num)) v] at he
      simp only [ContinuousLinearMap.zero_apply] at he
      rw [real_inner_comm (f z) (fderiv ℝ f z v)] at he
      linarith
    intro z hz v
    refine ⟨first z hz v, ?_⟩
    have hdf : DifferentiableAt ℝ f z := (hf z hz).differentiableAt (by norm_num)
    have hcd : ContDiffAt ℝ 1 (fun y => fderiv ℝ f y v) z :=
      ((hf z hz).fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
    have heq : (fun y => inner ℝ (f y) (fderiv ℝ f y v)) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
      filter_upwards [hs.mem_nhds hz] with y hy
      exact first y hy v
    have hd := ((hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) z).congr_of_eventuallyEq heq).fderiv
    have he := congrArg (fun L : E →L[ℝ] ℝ => L v) hd
    rw [fderiv_inner_apply ℝ hdf hcd.differentiableAt_one v] at he
    simp only [ContinuousLinearMap.zero_apply, real_inner_self_eq_norm_sq] at he
    linarith
  have slices : ∀ x t, 0 < t →
    (∀ r ∈ Set.Ioi (0 : ℝ), ContDiffAt ℝ 2 (fun s => u (x,s)) r) ∧
    (∀ y : V n, ContDiffAt ℝ 2 (fun z => u (z,t)) y) := by
    have hopen : IsOpen (domain n) := isOpen_lt continuous_const continuous_snd
    have smooth : ∀ x t, 0 < t → ContDiffAt ℝ 2 u (x,t) := by
      intro x t ht
      exact (h_H002.contDiffAt (hopen.mem_nhds ht)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    intro x t ht
    constructor
    · intro r hr
      exact (smooth x r hr).comp r (contDiffAt_const.prodMk contDiffAt_id)
    · intro y
      exact (smooth y t ht).comp y (contDiffAt_id.prodMk contDiffAt_const)
  intro x t ht
  have htime := geometry ℝ (fun s => u (x,s)) (Set.Ioi 0) isOpen_Ioi
    (slices x t ht).1 (fun r hr => h_H004 x r hr) t ht 1
  have hfirst : inner ℝ (u (x,t)) (ut u x t) = 0 := htime.1
  have hsecond : inner ℝ (u (x,t)) (utt u x t) = -(‖ut u x t‖ ^ 2) := htime.2
  have hspace : ∀ j : Fin n, inner ℝ (u (x,t)) (uxx u j x t) = -(‖ux u j x t‖ ^ 2) := by
    intro j
    exact (geometry (V n) (fun y => u (y,t)) Set.univ isOpen_univ
      (fun y _ => (slices x t ht).2 y)
      (fun y _ => h_H004 y t ht) x (Set.mem_univ x) (Pi.single j 1)).2
  obtain ⟨a, ha⟩ := h_H005 x t ht
  have hnormal : inner ℝ (ut u x t) (utt u x t - lap u x t) = 0 := by
    rw [ha, real_inner_smul_right, real_inner_comm (u (x,t)) (ut u x t), hfirst, mul_zero]
  have hscalar : ∀ a : ℝ, utt u x t - lap u x t = a • u (x,t) →
      a = (∑ j, ‖ux u j x t‖ ^ 2) - ‖ut u x t‖ ^ 2 := by
    intro b hb
    have he := congrArg (fun w : W m => inner ℝ (u (x,t)) w) hb
    rw [inner_sub_right, hsecond, lap, inner_sum] at he
    simp_rw [hspace] at he
    rw [Finset.sum_neg_distrib, real_inner_smul_right, real_inner_self_eq_norm_sq,
      h_H004 x t ht] at he
    norm_num at he
    linarith
  refine ⟨hfirst, hnormal, hsecond, hspace, hscalar, ?_⟩
  rw [ha, hscalar a ha]

#check @T001
#print axioms T001

end Translation
