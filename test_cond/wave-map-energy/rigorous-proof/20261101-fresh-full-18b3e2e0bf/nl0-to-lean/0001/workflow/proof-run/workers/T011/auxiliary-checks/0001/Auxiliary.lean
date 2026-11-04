import Mathlib

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace WaveMap

abbrev X (n : ℕ) := Fin n → ℝ
abbrev V (m : ℕ) := EuclideanSpace ℝ (Fin m)

def domain (n : ℕ) : Set (X n × ℝ) := {p | 0 < p.2}
def box (n : ℕ) (R : ℝ) : Set (X n) :=
  Set.pi Set.univ (fun _ => Set.Icc (-R) R)
def openBox (n : ℕ) (R : ℝ) : Set (X n) :=
  Set.pi Set.univ (fun _ => Set.Ioo (-R) R)
def slab (t : ℝ) : Set ℝ := Set.Icc (t / 2) (3 * t / 2)

noncomputable def dt {n m : ℕ} (u : X n × ℝ → V m) : X n × ℝ → V m :=
  fun p => deriv (fun r : ℝ => u (p.1, r)) p.2
noncomputable def dx {n m : ℕ} (u : X n × ℝ → V m) (j : Fin n) :
    X n × ℝ → V m :=
  fun p => fderiv ℝ (fun x : X n => u (x, p.2)) p.1 (Pi.single j 1)
noncomputable def lap {n m : ℕ} (u : X n × ℝ → V m) : X n × ℝ → V m :=
  fun p => ∑ j : Fin n, dx (dx u j) j p
noncomputable def density {n m : ℕ} (u : X n × ℝ → V m) :
    X n × ℝ → ℝ :=
  fun p => ‖dt u p‖ ^ 2 + ∑ j : Fin n, ‖dx u j p‖ ^ 2
noncomputable def densityT {n m : ℕ} (u : X n × ℝ → V m) :
    X n × ℝ → ℝ :=
  fun p => deriv (fun r : ℝ => density u (p.1, r)) p.2
noncomputable def energy {n m : ℕ} (u : X n × ℝ → V m) (t : ℝ) : ℝ :=
  ∫ x : X n, density u (x, t)
noncomputable def timeProduct {n m : ℕ} (u : X n × ℝ → V m) :
    X n × ℝ → ℝ :=
  fun p => inner ℝ (dt u p) (dt (dt u) p)
noncomputable def mixedProduct {n m : ℕ} (u : X n × ℝ → V m) (j : Fin n) :
    X n × ℝ → ℝ :=
  fun p => inner ℝ (dx u j p) (dx (dt u) j p)
noncomputable def lapProduct {n m : ℕ} (u : X n × ℝ → V m) (j : Fin n) :
    X n × ℝ → ℝ :=
  fun p => inner ℝ (dt u p) (dx (dx u j) j p)
noncomputable def flux {n m : ℕ} (u : X n × ℝ → V m) (j : Fin n) :
    X n × ℝ → ℝ :=
  fun p => inner ℝ (dt u p) (dx u j p)
noncomputable def fluxDx {n m : ℕ} (u : X n × ℝ → V m) (j : Fin n) :
    X n × ℝ → ℝ :=
  fun p => fderiv ℝ (fun x : X n => flux u j (x, p.2)) p.1 (Pi.single j 1)

def sectionGood {n : ℕ} (C : Set (X n)) (R : ℝ) (f : X n → ℝ) : Prop :=
  Continuous f ∧ (∀ x, x ∉ C → f x = 0) ∧
  (∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ box n R, |f x| ≤ B) ∧ Integrable f

def supportGeometry {n m : ℕ} (u : X n × ℝ → V m) (q : V m)
    (t : ℝ) (C : Set (X n)) (R : ℝ) : Prop :=
  IsCompact C ∧ 0 < R ∧ C ⊆ openBox n R ∧
  (∀ x, x ∉ C → ∀ r ∈ slab t, u (x, r) = q) ∧
  volume (box n R) = ENNReal.ofReal ((2 * R) ^ n) ∧
  volume (box n R) < ⊤ ∧
  (∀ k : ℕ, ∀ x, x ∉ C → ∀ r ∈ interior (slab t),
    iteratedFDeriv ℝ (k + 1) u (x, r) = 0)

def supportSections {n m : ℕ} (u : X n × ℝ → V m)
    (t : ℝ) (C : Set (X n)) (R : ℝ) : Prop :=
  ∀ r ∈ interior (slab t),
    sectionGood C R (fun x => density u (x, r)) ∧
    sectionGood C R (fun x => densityT u (x, r)) ∧
    sectionGood C R (fun x => timeProduct u (x, r)) ∧
    (∀ j : Fin n,
      sectionGood C R (fun x => mixedProduct u j (x, r)) ∧
      sectionGood C R (fun x => lapProduct u j (x, r)) ∧
      sectionGood C R (fun x => fluxDx u j (x, r)))

noncomputable def quotient {n m : ℕ} (u : X n × ℝ → V m)
    (t h : ℝ) (x : X n) : ℝ :=
  (density u (x, t + h) - density u (x, t)) / h

abbrev Other {n : ℕ} (j : Fin n) := {i : Fin n // i ≠ j}
def insertCoord {n : ℕ} (j : Fin n) (y : Other j → ℝ) (z : ℝ) : X n :=
  fun i => if h : i = j then z else y ⟨i, h⟩
def otherBox {n : ℕ} (j : Fin n) (R : ℝ) : Set (Other j → ℝ) :=
  Set.pi Set.univ (fun _ => Set.Icc (-R) R)

end WaveMap

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem checked (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_T002 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t →
  (inner ℝ (u (x, t)) (WaveMap.dt u (x, t)) = 0 ∧
   inner ℝ (WaveMap.dt u (x, t)) (WaveMap.dt (WaveMap.dt u) (x, t) - WaveMap.lap u (x, t)) = 0) ∧
  (∀ a : ℝ, WaveMap.dt (WaveMap.dt u) (x, t) - WaveMap.lap u (x, t) = a • u (x, t) →
    a = (∑ j : Fin n, ‖WaveMap.dx u j (x, t)‖ ^ 2) - ‖WaveMap.dt u (x, t)‖ ^ 2) ∧
  WaveMap.dt (WaveMap.dt u) (x, t) - WaveMap.lap u (x, t) =
    ((∑ j : Fin n, ‖WaveMap.dx u j (x, t)‖ ^ 2) - ‖WaveMap.dt u (x, t)‖ ^ 2) • u (x, t)) (h_T004 : (∀ t : ℝ, 0 < t → ∃ C : Set (WaveMap.X n), ∃ R : ℝ,
    WaveMap.supportGeometry u q t C R ∧ WaveMap.supportSections u t C R) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : WaveMap.X n => WaveMap.density u (x, t))) ∧
  ContinuousOn (WaveMap.density u) (WaveMap.domain n) ∧
  ContinuousOn (WaveMap.densityT u) (WaveMap.domain n)) (h_T007 : (∀ t : ℝ, 0 < t →
    HasDerivAt (WaveMap.energy u) (∫ x : WaveMap.X n, WaveMap.densityT u (x, t)) t ∧
    Integrable (fun x : WaveMap.X n => WaveMap.densityT u (x, t)) ∧
    Integrable (fun x : WaveMap.X n => WaveMap.timeProduct u (x, t)) ∧
    ∀ j : Fin n, Integrable (fun x : WaveMap.X n => WaveMap.mixedProduct u j (x, t))) ∧
  (∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t →
    WaveMap.densityT u (x, t) =
      2 * WaveMap.timeProduct u (x, t) + 2 * ∑ j : Fin n, WaveMap.mixedProduct u j (x, t))) (h_T010 : ∀ t : ℝ, 0 < t → ∀ j : Fin n,
  (∫ x : WaveMap.X n, WaveMap.mixedProduct u j (x, t)) =
    -(∫ x : WaveMap.X n, WaveMap.lapProduct u j (x, t)) ∧
  Integrable (fun x : WaveMap.X n => WaveMap.mixedProduct u j (x, t)) ∧
  Integrable (fun x : WaveMap.X n => WaveMap.lapProduct u j (x, t))) : yui_aux_type% "∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t → WaveMap.timeProduct u (x,t) - ∑ j : Fin n, WaveMap.lapProduct u j (x,t) = 0" := by
  intro x t ht
  have h := (h_T002 x t ht).1.2
  simpa only [WaveMap.timeProduct, WaveMap.lapProduct, WaveMap.lap, inner_sub_right, inner_sum] using h
#check @checked
#print axioms checked
end YuiAuxiliary
