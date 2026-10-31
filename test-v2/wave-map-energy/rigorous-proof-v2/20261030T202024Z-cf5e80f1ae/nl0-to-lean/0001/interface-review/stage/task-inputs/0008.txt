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

#check (∀ (n : ℕ) (m : ℕ) (u : X n × ℝ → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ u (domain n)) (h_H004 : ∀ x : X n, ∀ t : ℝ, 0 < t → ‖u (x,t)‖ = 1), ∀ x : X n, ∀ t : ℝ, 0 < t →
  inner ℝ (u (x,t)) (dt u (x,t)) = 0 ∧
  inner ℝ (u (x,t)) (dt (dt u) (x,t)) = -(‖dt u (x,t)‖ ^ 2) ∧
  (∀ j : Fin n, inner ℝ (u (x,t)) (dx (dx u j) j (x,t)) = -(‖dx u j (x,t)‖ ^ 2)))
#check (∀ (n : ℕ) (m : ℕ) (u : X n × ℝ → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ u (domain n)) (h_H004 : ∀ x : X n, ∀ t : ℝ, 0 < t → ‖u (x,t)‖ = 1) (h_H005 : ∀ x : X n, ∀ t : ℝ, 0 < t → ∃ a : ℝ, dt (dt u) (x,t) - lap u (x,t) = a • u (x,t)) (h_T001 : ∀ x : X n, ∀ t : ℝ, 0 < t →
  inner ℝ (u (x,t)) (dt u (x,t)) = 0 ∧
  inner ℝ (u (x,t)) (dt (dt u) (x,t)) = -(‖dt u (x,t)‖ ^ 2) ∧
  (∀ j : Fin n, inner ℝ (u (x,t)) (dx (dx u j) j (x,t)) = -(‖dx u j (x,t)‖ ^ 2))), ∀ x : X n, ∀ t : ℝ, 0 < t →
  inner ℝ (u (x,t)) (dt u (x,t)) = 0 ∧
  inner ℝ (u (x,t)) (dt (dt u) (x,t)) = -(‖dt u (x,t)‖ ^ 2) ∧
  (∀ j : Fin n, inner ℝ (u (x,t)) (dx (dx u j) j (x,t)) = -(‖dx u j (x,t)‖ ^ 2)) ∧
  inner ℝ (dt u (x,t)) (dt (dt u) (x,t) - lap u (x,t)) = 0 ∧
  dt (dt u) (x,t) - lap u (x,t) =
    ((∑ j : Fin n, ‖dx u j (x,t)‖ ^ 2) - ‖dt u (x,t)‖ ^ 2) • u (x,t) ∧
  (∀ a : ℝ, dt (dt u) (x,t) - lap u (x,t) = a • u (x,t) →
    a = (∑ j : Fin n, ‖dx u j (x,t)‖ ^ 2) - ‖dt u (x,t)‖ ^ 2))
#check (∀ (n : ℕ) (m : ℕ) (u : X n × ℝ → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H006 : ∀ s t : ℝ, 0 < s → s < t → ∃ C : Set (X n), IsCompact C ∧ ∀ x : X n, x ∉ C → ∀ r : ℝ, r ∈ Icc s t → u (x,r) = q), ∀ t0 : ℝ, 0 < t0 →
  ∃ C : Set (X n), ∃ R : ℝ, IsCompact C ∧ 0 < R ∧
    (∀ x ∈ C, ∀ j : Fin n, x j ∈ Ioo (-R) R) ∧
    (∀ x, x ∉ C → ∀ r ∈ Icc (t0/2) (3*t0/2), u (x,r) = q))
#check (∀ (n : ℕ) (m : ℕ) (u : X n × ℝ → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ u (domain n)) (h_H003 : ‖q‖ = 1) (h_H006 : ∀ s t : ℝ, 0 < s → s < t → ∃ C : Set (X n), IsCompact C ∧ ∀ x : X n, x ∉ C → ∀ r : ℝ, r ∈ Icc s t → u (x,r) = q) (h_T003 : ∀ t0 : ℝ, 0 < t0 →
  ∃ C : Set (X n), ∃ R : ℝ, IsCompact C ∧ 0 < R ∧
    (∀ x ∈ C, ∀ j : Fin n, x j ∈ Ioo (-R) R) ∧
    (∀ x, x ∉ C → ∀ r ∈ Icc (t0/2) (3*t0/2), u (x,r) = q)), (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (X n), ∃ R : ℝ, Window u q t0 C R) ∧
  ContDiffOn ℝ ∞ (density u) (domain n) ∧
  ContDiffOn ℝ ∞ (dt (density u)) (domain n) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : X n => density u (x,t)) (mu n)))
#check (∀ (n : ℕ) (m : ℕ) (u : X n × ℝ → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ u (domain n)) (h_T004 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (X n), ∃ R : ℝ, Window u q t0 C R) ∧
  ContDiffOn ℝ ∞ (density u) (domain n) ∧
  ContDiffOn ℝ ∞ (dt (density u)) (domain n) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : X n => density u (x,t)) (mu n))), ∀ x : X n, ∀ t : ℝ, 0 < t →
  HasDerivAt (fun r : ℝ => density u (x,r)) (dt (density u) (x,t)) t ∧
  dt (density u) (x,t) = 2 * kinetic u (x,t) + 2 * ∑ j : Fin n, mixed u j (x,t))
#check (∀ (n : ℕ) (m : ℕ) (u : X n × ℝ → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ u (domain n)) (h_T004 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (X n), ∃ R : ℝ, Window u q t0 C R) ∧
  ContDiffOn ℝ ∞ (density u) (domain n) ∧
  ContDiffOn ℝ ∞ (dt (density u)) (domain n) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : X n => density u (x,t)) (mu n))) (h_T005 : ∀ x : X n, ∀ t : ℝ, 0 < t →
  HasDerivAt (fun r : ℝ => density u (x,r)) (dt (density u) (x,t)) t ∧
  dt (density u) (x,t) = 2 * kinetic u (x,t) + 2 * ∑ j : Fin n, mixed u j (x,t)), ∀ t0 : ℝ, 0 < t0 → ∃ R B : ℝ, 0 < R ∧ 0 ≤ B ∧
  Integrable ((box R).indicator (fun _ : X n => B)) (mu n) ∧
  (∀ x ∈ box R, ∀ r ∈ Icc (t0-t0/4) (t0+t0/4), |dt (density u) (x,r)| ≤ B) ∧
  (∀ x : X n, ∀ h : ℝ, 0 < |h| → |h| < t0/4 →
    |(density u (x,t0+h) - density u (x,t0))/h| ≤
      (box R).indicator (fun _ : X n => B) x))
#check (∀ (n : ℕ) (m : ℕ) (u : X n × ℝ → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ u (domain n)) (h_T004 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (X n), ∃ R : ℝ, Window u q t0 C R) ∧
  ContDiffOn ℝ ∞ (density u) (domain n) ∧
  ContDiffOn ℝ ∞ (dt (density u)) (domain n) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : X n => density u (x,t)) (mu n))) (h_T005 : ∀ x : X n, ∀ t : ℝ, 0 < t →
  HasDerivAt (fun r : ℝ => density u (x,r)) (dt (density u) (x,t)) t ∧
  dt (density u) (x,t) = 2 * kinetic u (x,t) + 2 * ∑ j : Fin n, mixed u j (x,t)) (h_T006 : ∀ t0 : ℝ, 0 < t0 → ∃ R B : ℝ, 0 < R ∧ 0 ≤ B ∧
  Integrable ((box R).indicator (fun _ : X n => B)) (mu n) ∧
  (∀ x ∈ box R, ∀ r ∈ Icc (t0-t0/4) (t0+t0/4), |dt (density u) (x,r)| ≤ B) ∧
  (∀ x : X n, ∀ h : ℝ, 0 < |h| → |h| < t0/4 →
    |(density u (x,t0+h) - density u (x,t0))/h| ≤
      (box R).indicator (fun _ : X n => B) x)), ∀ t0 : ℝ, 0 < t0 → ∀ h : ℕ → ℝ,
  (∀ k : ℕ, 0 < |h k| ∧ |h k| < t0/4) →
  Tendsto h atTop (nhds 0) →
  Tendsto (fun k : ℕ => (energy u (t0+h k) - energy u t0)/h k) atTop
    (nhds (∫ x : X n, dt (density u) (x,t0) ∂mu n)))
#check (∀ (n : ℕ) (m : ℕ) (u : X n × ℝ → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ u (domain n)) (h_T004 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (X n), ∃ R : ℝ, Window u q t0 C R) ∧
  ContDiffOn ℝ ∞ (density u) (domain n) ∧
  ContDiffOn ℝ ∞ (dt (density u)) (domain n) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : X n => density u (x,t)) (mu n))) (h_T005 : ∀ x : X n, ∀ t : ℝ, 0 < t →
  HasDerivAt (fun r : ℝ => density u (x,r)) (dt (density u) (x,t)) t ∧
  dt (density u) (x,t) = 2 * kinetic u (x,t) + 2 * ∑ j : Fin n, mixed u j (x,t)) (h_T007 : ∀ t0 : ℝ, 0 < t0 → ∀ h : ℕ → ℝ,
  (∀ k : ℕ, 0 < |h k| ∧ |h k| < t0/4) →
  Tendsto h atTop (nhds 0) →
  Tendsto (fun k : ℕ => (energy u (t0+h k) - energy u t0)/h k) atTop
    (nhds (∫ x : X n, dt (density u) (x,t0) ∂mu n))), ∀ t : ℝ, 0 < t →
  DifferentiableAt ℝ (energy u) t ∧
  deriv (energy u) t = (∫ x : X n, dt (density u) (x,t) ∂mu n) ∧
  deriv (energy u) t =
    2 * (∫ x : X n, kinetic u (x,t) ∂mu n) +
    2 * ∑ j : Fin n, (∫ x : X n, mixed u j (x,t) ∂mu n) ∧
  Integrable (fun x : X n => dt (density u) (x,t)) (mu n) ∧
  Integrable (fun x : X n => kinetic u (x,t)) (mu n) ∧
  (∀ j : Fin n, Integrable (fun x : X n => mixed u j (x,t)) (mu n)) ∧
  (∀ x : X n, dt (density u) (x,t) =
    2 * kinetic u (x,t) + 2 * ∑ j : Fin n, mixed u j (x,t)))
#check (∀ (n : ℕ) (m : ℕ) (u : X n × ℝ → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ u (domain n)) (h_T004 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (X n), ∃ R : ℝ, Window u q t0 C R) ∧
  ContDiffOn ℝ ∞ (density u) (domain n) ∧
  ContDiffOn ℝ ∞ (dt (density u)) (domain n) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : X n => density u (x,t)) (mu n))), ∀ t0 : ℝ, 0 < t0 → ∀ j : Fin n,
  ContDiff ℝ ∞ (fun x : X n => flux u j (x,t0)) ∧
  (∀ x : X n, dx (flux u j) j (x,t0) =
    inner ℝ (dx (dt u) j (x,t0)) (dx u j (x,t0)) + lapTerm u j (x,t0)) ∧
  (∀ x : X n, HasDerivAt (fun z : ℝ => flux u j (Function.update x j z,t0))
    (dx (flux u j) j (x,t0)) (x j)) ∧
  (∀ C : Set (X n), ∀ R : ℝ, Window u q t0 C R →
    ∀ x : X n, x j = -R ∨ x j = R → flux u j (x,t0) = 0))
#check (∀ (n : ℕ) (m : ℕ) (u : X n × ℝ → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ u (domain n)) (h_T004 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (X n), ∃ R : ℝ, Window u q t0 C R) ∧
  ContDiffOn ℝ ∞ (density u) (domain n) ∧
  ContDiffOn ℝ ∞ (dt (density u)) (domain n) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : X n => density u (x,t)) (mu n))) (h_T009 : ∀ t0 : ℝ, 0 < t0 → ∀ j : Fin n,
  ContDiff ℝ ∞ (fun x : X n => flux u j (x,t0)) ∧
  (∀ x : X n, dx (flux u j) j (x,t0) =
    inner ℝ (dx (dt u) j (x,t0)) (dx u j (x,t0)) + lapTerm u j (x,t0)) ∧
  (∀ x : X n, HasDerivAt (fun z : ℝ => flux u j (Function.update x j z,t0))
    (dx (flux u j) j (x,t0)) (x j)) ∧
  (∀ C : Set (X n), ∀ R : ℝ, Window u q t0 C R →
    ∀ x : X n, x j = -R ∨ x j = R → flux u j (x,t0) = 0)), ∀ t0 : ℝ, 0 < t0 → ∀ j : Fin n,
  ∀ C : Set (X n), ∀ R : ℝ, Window u q t0 C R →
  ∀ x : X n, (∫ z in (-R)..R,
    dx (flux u j) j (Function.update x j z,t0)) = 0)
#check (∀ (n : ℕ) (m : ℕ) (u : X n × ℝ → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ u (domain n)) (h_T004 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (X n), ∃ R : ℝ, Window u q t0 C R) ∧
  ContDiffOn ℝ ∞ (density u) (domain n) ∧
  ContDiffOn ℝ ∞ (dt (density u)) (domain n) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : X n => density u (x,t)) (mu n))) (h_T009 : ∀ t0 : ℝ, 0 < t0 → ∀ j : Fin n,
  ContDiff ℝ ∞ (fun x : X n => flux u j (x,t0)) ∧
  (∀ x : X n, dx (flux u j) j (x,t0) =
    inner ℝ (dx (dt u) j (x,t0)) (dx u j (x,t0)) + lapTerm u j (x,t0)) ∧
  (∀ x : X n, HasDerivAt (fun z : ℝ => flux u j (Function.update x j z,t0))
    (dx (flux u j) j (x,t0)) (x j)) ∧
  (∀ C : Set (X n), ∀ R : ℝ, Window u q t0 C R →
    ∀ x : X n, x j = -R ∨ x j = R → flux u j (x,t0) = 0)) (h_T010 : ∀ t0 : ℝ, 0 < t0 → ∀ j : Fin n,
  ∀ C : Set (X n), ∀ R : ℝ, Window u q t0 C R →
  ∀ x : X n, (∫ z in (-R)..R,
    dx (flux u j) j (Function.update x j z,t0)) = 0), ∀ t0 : ℝ, 0 < t0 → ∀ j : Fin n,
  ∀ C : Set (X n), ∀ R : ℝ, Window u q t0 C R →
  MeasurePreserving (insert j)
    (((otherMu j).restrict (otherBox j R)).prod (volume.restrict (Icc (-R) R)))
    ((mu n).restrict (box R)) ∧
  (∫ x in box R, dx (flux u j) j (x,t0) ∂mu n) = 0)
#check (∀ (n : ℕ) (m : ℕ) (u : X n × ℝ → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ u (domain n)) (h_T004 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (X n), ∃ R : ℝ, Window u q t0 C R) ∧
  ContDiffOn ℝ ∞ (density u) (domain n) ∧
  ContDiffOn ℝ ∞ (dt (density u)) (domain n) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : X n => density u (x,t)) (mu n))) (h_T009 : ∀ t0 : ℝ, 0 < t0 → ∀ j : Fin n,
  ContDiff ℝ ∞ (fun x : X n => flux u j (x,t0)) ∧
  (∀ x : X n, dx (flux u j) j (x,t0) =
    inner ℝ (dx (dt u) j (x,t0)) (dx u j (x,t0)) + lapTerm u j (x,t0)) ∧
  (∀ x : X n, HasDerivAt (fun z : ℝ => flux u j (Function.update x j z,t0))
    (dx (flux u j) j (x,t0)) (x j)) ∧
  (∀ C : Set (X n), ∀ R : ℝ, Window u q t0 C R →
    ∀ x : X n, x j = -R ∨ x j = R → flux u j (x,t0) = 0)) (h_T011 : ∀ t0 : ℝ, 0 < t0 → ∀ j : Fin n,
  ∀ C : Set (X n), ∀ R : ℝ, Window u q t0 C R →
  MeasurePreserving (insert j)
    (((otherMu j).restrict (otherBox j R)).prod (volume.restrict (Icc (-R) R)))
    ((mu n).restrict (box R)) ∧
  (∫ x in box R, dx (flux u j) j (x,t0) ∂mu n) = 0), ∀ t : ℝ, 0 < t → ∀ j : Fin n,
  (∫ x : X n, mixed u j (x,t) ∂mu n) = -(∫ x : X n, lapTerm u j (x,t) ∂mu n) ∧
  Integrable (fun x : X n => mixed u j (x,t)) (mu n) ∧
  Integrable (fun x : X n => lapTerm u j (x,t)) (mu n))
#check (∀ (n : ℕ) (m : ℕ) (u : X n × ℝ → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ u (domain n)) (h_T002 : ∀ x : X n, ∀ t : ℝ, 0 < t →
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
  Integrable (fun x : X n => lapTerm u j (x,t)) (mu n)), ∀ t : ℝ, 0 < t →
  Integrable (fun x : X n => density u (x,t)) (mu n) ∧
  DifferentiableAt ℝ (energy u) t ∧ deriv (energy u) t = 0)
#check (∀ (n : ℕ) (m : ℕ) (u : X n × ℝ → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ u (domain n)) (h_T013 : ∀ t : ℝ, 0 < t →
  Integrable (fun x : X n => density u (x,t)) (mu n) ∧
  DifferentiableAt ℝ (energy u) t ∧ deriv (energy u) t = 0), (∀ t : ℝ, 0 < t →
  Integrable (fun x : X n => density u (x,t)) (mu n) ∧
  DifferentiableAt ℝ (energy u) t ∧ deriv (energy u) t = 0) ∧
  (∀ s : ℝ, 0 < s → ∀ t : ℝ, 0 < t → energy u s = energy u t))

end Translation
