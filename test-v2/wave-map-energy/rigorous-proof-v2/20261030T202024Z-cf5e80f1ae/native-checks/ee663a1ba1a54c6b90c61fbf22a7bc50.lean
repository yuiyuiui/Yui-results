import Mathlib
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
namespace WaveEnergy
abbrev X (n : ℕ) := Fin n → ℝ
abbrev V (m : ℕ) := EuclideanSpace ℝ (Fin m)
def domain (n : ℕ) : Set (X n × ℝ) := {p | 0 < p.2}
noncomputable def mu (n : ℕ) : Measure (X n) := Measure.pi (fun _ : Fin n => (volume : Measure ℝ))
noncomputable def dt {n : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : X n × ℝ → F) (p : X n × ℝ) : F := deriv (fun r : ℝ => f (p.1, r)) p.2
noncomputable def dx {n : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : X n × ℝ → F) (j : Fin n) (p : X n × ℝ) : F :=
  fderiv ℝ (fun y : X n => f (y, p.2)) p.1 (Pi.single j 1)
noncomputable def lap {n m : ℕ} (u : X n × ℝ → V m) (p : X n × ℝ) : V m :=
  ∑ j : Fin n, dx (dx u j) j p
noncomputable def density {n m : ℕ} (u : X n × ℝ → V m) (p : X n × ℝ) : ℝ :=
  ‖dt u p‖ ^ 2 + ∑ j : Fin n, ‖dx u j p‖ ^ 2
noncomputable def energy {n m : ℕ} (u : X n × ℝ → V m) (t : ℝ) : ℝ :=
  ∫ x : X n, density u (x, t) ∂mu n
noncomputable def kinetic {n m : ℕ} (u : X n × ℝ → V m) (p : X n × ℝ) : ℝ :=
  inner ℝ (dt u p) (dt (dt u) p)
noncomputable def mixed {n m : ℕ} (u : X n × ℝ → V m) (j : Fin n) (p : X n × ℝ) : ℝ :=
  inner ℝ (dx u j p) (dx (dt u) j p)
noncomputable def lapTerm {n m : ℕ} (u : X n × ℝ → V m) (j : Fin n) (p : X n × ℝ) : ℝ :=
  inner ℝ (dt u p) (dx (dx u j) j p)
noncomputable def flux {n m : ℕ} (u : X n × ℝ → V m) (j : Fin n) (p : X n × ℝ) : ℝ :=
  inner ℝ (dt u p) (dx u j p)
def box {n : ℕ} (R : ℝ) : Set (X n) := {x | ∀ j, x j ∈ Icc (-R) R}
def scalarTerms {n m : ℕ} (u : X n × ℝ → V m) : Set (X n × ℝ → ℝ) :=
  {f | f = density u ∨ f = dt (density u) ∨ f = kinetic u ∨
    ∃ j : Fin n, f = mixed u j ∨ f = lapTerm u j ∨ f = flux u j ∨ f = dx (flux u j) j}
structure Window {n m : ℕ} (u : X n × ℝ → V m) (q : V m)
    (t0 : ℝ) (C : Set (X n)) (R : ℝ) : Prop where
  compact : IsCompact C
  radius_pos : 0 < R
  inside : ∀ x ∈ C, ∀ j : Fin n, x j ∈ Ioo (-R) R
  constant : ∀ x, x ∉ C → ∀ r ∈ Icc (t0 / 2) (3 * t0 / 2), u (x, r) = q
  box_volume : mu n (box R) = ENNReal.ofReal ((2 * R) ^ n)
  box_finite : mu n (box R) < ⊤
  derivatives_zero : ∀ k : ℕ, 0 < k → ∀ x, x ∉ C →
    ∀ r ∈ Ioo (t0 / 2) (3 * t0 / 2), iteratedFDeriv ℝ k u (x, r) = 0
  sections : ∀ f ∈ scalarTerms u, ∀ r ∈ Ioo (t0 / 2) (3 * t0 / 2),
    Continuous (fun x => f (x, r)) ∧ (∀ x, x ∉ C → f (x, r) = 0) ∧
    Integrable (fun x => f (x, r)) (mu n)
  uniform : ∀ f ∈ scalarTerms u, ∀ a b : ℝ,
    Icc a b ⊆ Ioo (t0 / 2) (3 * t0 / 2) →
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ box R, ∀ r ∈ Icc a b, |f (x, r)| ≤ B
abbrev Other (n : ℕ) (j : Fin n) := {i : Fin n // i ≠ j} → ℝ
noncomputable def otherMu {n : ℕ} (j : Fin n) : Measure (Other n j) :=
  Measure.pi (fun _ : {i : Fin n // i ≠ j} => (volume : Measure ℝ))
def otherBox {n : ℕ} (j : Fin n) (R : ℝ) : Set (Other n j) :=
  {y | ∀ i, y i ∈ Icc (-R) R}
def insert {n : ℕ} (j : Fin n) (p : Other n j × ℝ) : X n :=
  fun i => if h : i = j then p.2 else p.1 ⟨i,h⟩
end WaveEnergy
open WaveEnergy

namespace Translation
set_option autoImplicit false

theorem T001 (n : ℕ) (m : ℕ) (u : X n × ℝ → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ u (domain n)) (h_H004 : ∀ x : X n, ∀ t : ℝ, 0 < t → ‖u (x,t)‖ = 1) :
    ∀ x : X n, ∀ t : ℝ, 0 < t →
  inner ℝ (u (x,t)) (dt u (x,t)) = 0 ∧
  inner ℝ (u (x,t)) (dt (dt u) (x,t)) = -(‖dt u (x,t)‖ ^ 2) ∧
  (∀ j : Fin n, inner ℝ (u (x,t)) (dx (dx u j) j (x,t)) = -(‖dx u j (x,t)‖ ^ 2)) := by
  have unit_direction : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      (f : E → V m) (s : Set E), IsOpen s → ContDiffOn ℝ ∞ f s →
      (∀ z ∈ s, ‖f z‖ = 1) → ∀ z ∈ s, ∀ v : E,
      inner ℝ (f z) (fderiv ℝ f z v) = 0 ∧
      inner ℝ (f z) (fderiv ℝ (fun y => fderiv ℝ f y v) z v) =
        -(‖fderiv ℝ f z v‖ ^ 2) := by
    intro E _ _ f s hs hf hn
    have hd : ∀ z ∈ s, DifferentiableAt ℝ f z := fun z hz =>
      (hf.contDiffAt (hs.mem_nhds hz)).differentiableAt (by simp)
    have hfirst : ∀ z ∈ s, ∀ v : E, inner ℝ (f z) (fderiv ℝ f z v) = 0 := by
      intro z hz v
      have he : (fun y => inner ℝ (f y) (f y)) =ᶠ[nhds z] (fun _ => (1 : ℝ)) := by
        filter_upwards [hs.mem_nhds hz] with y hy
        rw [real_inner_self_eq_norm_sq, hn y hy]
        norm_num
      have he' : fderiv ℝ (fun y => inner ℝ (f y) (f y)) z v = 0 := by
        rw [he.fderiv_eq]
        simp
      rw [fderiv_inner_apply ℝ (hd z hz) (hd z hz), real_inner_comm (f z) (fderiv ℝ f z v)] at he'
      linarith
    intro z hz v
    refine ⟨hfirst z hz v, ?_⟩
    have hD : ContDiffOn ℝ 1 (fun y => fderiv ℝ f y v) s :=
      (hf.fderiv_of_isOpen hs (by
        change ((1 + 1 : ℕ∞) : WithTop ℕ∞) ≤ (⊤ : ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top)).clm_apply contDiffOn_const
    have hdD : DifferentiableAt ℝ (fun y => fderiv ℝ f y v) z :=
      (hD.contDiffAt (hs.mem_nhds hz)).differentiableAt one_ne_zero
    have he : (fun y => inner ℝ (f y) (fderiv ℝ f y v)) =ᶠ[nhds z] (fun _ => (0 : ℝ)) := by
      filter_upwards [hs.mem_nhds hz] with y hy
      exact hfirst y hy v
    have he' : fderiv ℝ (fun y => inner ℝ (f y) (fderiv ℝ f y v)) z v = 0 := by
      rw [he.fderiv_eq]
      simp
    rw [fderiv_inner_apply ℝ (hd z hz) hdD, real_inner_self_eq_norm_sq] at he'
    linarith
  intro x t ht
  have htime : ContDiffOn ℝ ∞ (fun r : ℝ => u (x, r)) (Ioi 0) :=
    h_H002.comp (contDiffOn_const.prodMk contDiffOn_id) (by
      intro r hr
      exact hr)
  have hspace : ContDiffOn ℝ ∞ (fun y : X n => u (y, t)) univ :=
    h_H002.comp (contDiffOn_id.prodMk contDiffOn_const) (by
      intro y hy
      exact ht)
  have hT := unit_direction (fun r : ℝ => u (x, r)) (Ioi 0) isOpen_Ioi
    htime (fun r hr => h_H004 x r hr) t ht 1
  refine ⟨?_, ?_, ?_⟩
  · simpa only [dt, fderiv_apply_one_eq_deriv] using hT.1
  · simpa only [dt, fderiv_apply_one_eq_deriv] using hT.2
  · intro j
    have hS := unit_direction (fun y : X n => u (y, t)) univ isOpen_univ
      hspace (fun y _ => h_H004 y t ht) x (mem_univ x) (Pi.single j 1)
    simpa only [dx] using hS.2

#check @T001
#print axioms T001

end Translation
