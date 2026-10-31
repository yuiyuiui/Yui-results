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

theorem T013 (n : ℕ) (m : ℕ) (u : X n × ℝ → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ u (domain n)) (h_T002 : ∀ x : X n, ∀ t : ℝ, 0 < t →
  inner ℝ (u (x,t)) (dt u (x,t)) = 0 ∧
  inner ℝ (u (x,t)) (dt (dt u) (x,t)) = -(‖dt u (x,t)‖ ^ 2) ∧
  (∀ j : Fin n, inner ℝ (u (x,t)) (dx (dx u j) j (x,t)) = -(‖dx u j (x,t)‖ ^ 2)) ∧
  inner ℝ (dt u (x,t)) (dt (dt u) (x,t) - lap u (x,t)) = 0 ∧
  dt (dt u) (x,t) - lap u (x,t) =
    ((∑ j : Fin n, ‖dx u j (x,t)‖ ^ 2) - ‖dt u (x,t)‖ ^ 2) • u (x,t) ∧
  (∀ a : ℝ, dt (dt u) (x,t) - lap u (x,t) = a • u (x,t) →
    a = (∑ j : Fin n, ‖dx u j (x,t)‖ ^ 2) - ‖dt u (x,t)‖ ^ 2)) (h_T004 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (X n), ∃ R : ℝ, Window u q t0 C R) ∧
  ContDiffOn ℝ ∞ (density u) (domain n) ∧
  ContDiffOn ℝ ∞ (dt (density u)) (domain n) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : X n => density u (x,t)) (mu n))) (h_T008 : ∀ t : ℝ, 0 < t →
  DifferentiableAt ℝ (energy u) t ∧
  deriv (energy u) t = (∫ x : X n, dt (density u) (x,t) ∂mu n) ∧
  deriv (energy u) t =
    2 * (∫ x : X n, kinetic u (x,t) ∂mu n) +
    2 * ∑ j : Fin n, (∫ x : X n, mixed u j (x,t) ∂mu n) ∧
  Integrable (fun x : X n => dt (density u) (x,t)) (mu n) ∧
  Integrable (fun x : X n => kinetic u (x,t)) (mu n) ∧
  (∀ j : Fin n, Integrable (fun x : X n => mixed u j (x,t)) (mu n)) ∧
  (∀ x : X n, dt (density u) (x,t) =
    2 * kinetic u (x,t) + 2 * ∑ j : Fin n, mixed u j (x,t))) (h_T012 : ∀ t : ℝ, 0 < t → ∀ j : Fin n,
  (∫ x : X n, mixed u j (x,t) ∂mu n) = -(∫ x : X n, lapTerm u j (x,t) ∂mu n) ∧
  Integrable (fun x : X n => mixed u j (x,t)) (mu n) ∧
  Integrable (fun x : X n => lapTerm u j (x,t)) (mu n)) :
    ∀ t : ℝ, 0 < t →
  Integrable (fun x : X n => density u (x,t)) (mu n) ∧
  DifferentiableAt ℝ (energy u) t ∧ deriv (energy u) t = 0 := by
  intro t ht
  have he := h_T008 t ht
  have hk : Integrable (fun x : X n => kinetic u (x,t)) (mu n) :=
    he.2.2.2.2.1
  have hl : ∀ j : Fin n, Integrable (fun x : X n => lapTerm u j (x,t)) (mu n) :=
    fun j => (h_T012 t ht j).2.2
  have hs : Integrable (fun x : X n => ∑ j : Fin n, lapTerm u j (x,t)) (mu n) :=
    integrable_finsetSum Finset.univ (fun j _ => hl j)
  have hlin :
      (∫ x : X n, (kinetic u (x,t) - ∑ j : Fin n, lapTerm u j (x,t)) ∂mu n) =
        (∫ x : X n, kinetic u (x,t) ∂mu n) -
          ∑ j : Fin n, (∫ x : X n, lapTerm u j (x,t) ∂mu n) := by
    rw [integral_sub hk hs, integral_finsetSum Finset.univ (fun j _ => hl j)]
  have hp : ∀ x : X n, kinetic u (x,t) - ∑ j : Fin n, lapTerm u j (x,t) = 0 := by
    intro x
    have hw := (h_T002 x t ht).2.2.2.1
    simpa only [kinetic, lapTerm, lap, inner_sub_right, inner_sum] using hw
  refine ⟨h_T004.2.2.2 t ht, he.1, ?_⟩
  calc
    deriv (energy u) t =
        2 * (∫ x : X n, kinetic u (x,t) ∂mu n) +
        2 * ∑ j : Fin n, (∫ x : X n, mixed u j (x,t) ∂mu n) := he.2.2.1
    _ = 2 * ((∫ x : X n, kinetic u (x,t) ∂mu n) -
          ∑ j : Fin n, (∫ x : X n, lapTerm u j (x,t) ∂mu n)) := by
      simp_rw [(h_T012 t ht _).1]
      rw [Finset.sum_neg_distrib]
      ring
    _ = 2 * (∫ x : X n, (kinetic u (x,t) - ∑ j : Fin n, lapTerm u j (x,t)) ∂mu n) := by
      rw [hlin]
    _ = 0 := by simp [hp]

#check @T013
#print axioms T013

end Translation
