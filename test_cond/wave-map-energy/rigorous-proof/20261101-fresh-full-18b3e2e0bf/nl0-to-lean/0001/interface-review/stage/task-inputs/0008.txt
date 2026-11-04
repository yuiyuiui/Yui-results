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

namespace Translation
set_option autoImplicit false

def __signature_T001 : Prop :=
  (∀ (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_H004 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t → ‖u (x, t)‖ = 1) (h_H005 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t → ∃ a : ℝ, WaveMap.dt (WaveMap.dt u) (x, t) - WaveMap.lap u (x, t) = a • u (x, t)), (∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t → inner ℝ (u (x, t)) (WaveMap.dt u (x, t)) = 0 ∧ inner ℝ (WaveMap.dt u (x, t)) (WaveMap.dt (WaveMap.dt u) (x, t) - WaveMap.lap u (x, t)) = 0))
def __signature_T002 : Prop :=
  (∀ (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_H004 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t → ‖u (x, t)‖ = 1) (h_H005 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t → ∃ a : ℝ, WaveMap.dt (WaveMap.dt u) (x, t) - WaveMap.lap u (x, t) = a • u (x, t)) (h_T001 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t → inner ℝ (u (x, t)) (WaveMap.dt u (x, t)) = 0 ∧ inner ℝ (WaveMap.dt u (x, t)) (WaveMap.dt (WaveMap.dt u) (x, t) - WaveMap.lap u (x, t)) = 0), (∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t →
  (inner ℝ (u (x, t)) (WaveMap.dt u (x, t)) = 0 ∧
   inner ℝ (WaveMap.dt u (x, t)) (WaveMap.dt (WaveMap.dt u) (x, t) - WaveMap.lap u (x, t)) = 0) ∧
  (∀ a : ℝ, WaveMap.dt (WaveMap.dt u) (x, t) - WaveMap.lap u (x, t) = a • u (x, t) →
    a = (∑ j : Fin n, ‖WaveMap.dx u j (x, t)‖ ^ 2) - ‖WaveMap.dt u (x, t)‖ ^ 2) ∧
  WaveMap.dt (WaveMap.dt u) (x, t) - WaveMap.lap u (x, t) =
    ((∑ j : Fin n, ‖WaveMap.dx u j (x, t)‖ ^ 2) - ‖WaveMap.dt u (x, t)‖ ^ 2) • u (x, t)))
def __signature_T003 : Prop :=
  (∀ (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_H006 : ∀ s t : ℝ, 0 < s → s < t → ∃ C : Set (WaveMap.X n), IsCompact C ∧ ∀ x : WaveMap.X n, x ∉ C → ∀ r ∈ Set.Icc s t, u (x, r) = q), (∀ t : ℝ, 0 < t → ∃ C : Set (WaveMap.X n), ∃ R : ℝ, WaveMap.supportGeometry u q t C R))
def __signature_T004 : Prop :=
  (∀ (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_T003 : ∀ t : ℝ, 0 < t → ∃ C : Set (WaveMap.X n), ∃ R : ℝ, WaveMap.supportGeometry u q t C R), ((∀ t : ℝ, 0 < t → ∃ C : Set (WaveMap.X n), ∃ R : ℝ,
    WaveMap.supportGeometry u q t C R ∧ WaveMap.supportSections u t C R) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : WaveMap.X n => WaveMap.density u (x, t))) ∧
  ContinuousOn (WaveMap.density u) (WaveMap.domain n) ∧
  ContinuousOn (WaveMap.densityT u) (WaveMap.domain n)))
def __signature_T005 : Prop :=
  (∀ (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)), (∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t →
  HasDerivAt (fun r : ℝ => WaveMap.density u (x, r)) (WaveMap.densityT u (x, t)) t ∧
  WaveMap.densityT u (x, t) =
    2 * WaveMap.timeProduct u (x, t) + 2 * ∑ j : Fin n, WaveMap.mixedProduct u j (x, t)))
def __signature_T006 : Prop :=
  (∀ (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_T004 : (∀ t : ℝ, 0 < t → ∃ C : Set (WaveMap.X n), ∃ R : ℝ,
    WaveMap.supportGeometry u q t C R ∧ WaveMap.supportSections u t C R) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : WaveMap.X n => WaveMap.density u (x, t))) ∧
  ContinuousOn (WaveMap.density u) (WaveMap.domain n) ∧
  ContinuousOn (WaveMap.densityT u) (WaveMap.domain n)) (h_T005 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t →
  HasDerivAt (fun r : ℝ => WaveMap.density u (x, r)) (WaveMap.densityT u (x, t)) t ∧
  WaveMap.densityT u (x, t) =
    2 * WaveMap.timeProduct u (x, t) + 2 * ∑ j : Fin n, WaveMap.mixedProduct u j (x, t)), (∀ t : ℝ, 0 < t → ∃ η B R : ℝ,
  0 < η ∧ 0 ≤ B ∧ 0 < R ∧ η < t ∧
  Integrable ((WaveMap.box n R).indicator (fun _ => B)) ∧
  ∀ h : ℝ, 0 < |h| → |h| < η → ∀ x : WaveMap.X n,
    |WaveMap.quotient u t h x| ≤ (WaveMap.box n R).indicator (fun _ => B) x))
def __signature_T007 : Prop :=
  (∀ (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_T004 : (∀ t : ℝ, 0 < t → ∃ C : Set (WaveMap.X n), ∃ R : ℝ,
    WaveMap.supportGeometry u q t C R ∧ WaveMap.supportSections u t C R) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : WaveMap.X n => WaveMap.density u (x, t))) ∧
  ContinuousOn (WaveMap.density u) (WaveMap.domain n) ∧
  ContinuousOn (WaveMap.densityT u) (WaveMap.domain n)) (h_T005 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t →
  HasDerivAt (fun r : ℝ => WaveMap.density u (x, r)) (WaveMap.densityT u (x, t)) t ∧
  WaveMap.densityT u (x, t) =
    2 * WaveMap.timeProduct u (x, t) + 2 * ∑ j : Fin n, WaveMap.mixedProduct u j (x, t)) (h_T006 : ∀ t : ℝ, 0 < t → ∃ η B R : ℝ,
  0 < η ∧ 0 ≤ B ∧ 0 < R ∧ η < t ∧
  Integrable ((WaveMap.box n R).indicator (fun _ => B)) ∧
  ∀ h : ℝ, 0 < |h| → |h| < η → ∀ x : WaveMap.X n,
    |WaveMap.quotient u t h x| ≤ (WaveMap.box n R).indicator (fun _ => B) x), ((∀ t : ℝ, 0 < t →
    HasDerivAt (WaveMap.energy u) (∫ x : WaveMap.X n, WaveMap.densityT u (x, t)) t ∧
    Integrable (fun x : WaveMap.X n => WaveMap.densityT u (x, t)) ∧
    Integrable (fun x : WaveMap.X n => WaveMap.timeProduct u (x, t)) ∧
    ∀ j : Fin n, Integrable (fun x : WaveMap.X n => WaveMap.mixedProduct u j (x, t))) ∧
  (∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t →
    WaveMap.densityT u (x, t) =
      2 * WaveMap.timeProduct u (x, t) + 2 * ∑ j : Fin n, WaveMap.mixedProduct u j (x, t))))
def __signature_T008 : Prop :=
  (∀ (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m), (∀ (j : Fin n) (R : ℝ), 0 < R → ∀ f : WaveMap.X n → ℝ,
  IntegrableOn f (WaveMap.box n R) →
  (∫ x in WaveMap.box n R, f x) =
    ∫ y in WaveMap.otherBox j R, ∫ z in Set.Icc (-R) R, f (WaveMap.insertCoord j y z)))
def __signature_T009 : Prop :=
  (∀ (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_T004 : (∀ t : ℝ, 0 < t → ∃ C : Set (WaveMap.X n), ∃ R : ℝ,
    WaveMap.supportGeometry u q t C R ∧ WaveMap.supportSections u t C R) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : WaveMap.X n => WaveMap.density u (x, t))) ∧
  ContinuousOn (WaveMap.density u) (WaveMap.domain n) ∧
  ContinuousOn (WaveMap.densityT u) (WaveMap.domain n)) (h_T008 : ∀ (j : Fin n) (R : ℝ), 0 < R → ∀ f : WaveMap.X n → ℝ,
  IntegrableOn f (WaveMap.box n R) →
  (∫ x in WaveMap.box n R, f x) =
    ∫ y in WaveMap.otherBox j R, ∫ z in Set.Icc (-R) R, f (WaveMap.insertCoord j y z)), (∀ t : ℝ, 0 < t → ∀ j : Fin n,
  (∀ x : WaveMap.X n, WaveMap.fluxDx u j (x, t) =
    WaveMap.mixedProduct u j (x, t) + WaveMap.lapProduct u j (x, t)) ∧
  Integrable (fun x : WaveMap.X n => WaveMap.fluxDx u j (x, t)) ∧
  (∫ x : WaveMap.X n, WaveMap.fluxDx u j (x, t)) = 0))
def __signature_T010 : Prop :=
  (∀ (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_T004 : (∀ t : ℝ, 0 < t → ∃ C : Set (WaveMap.X n), ∃ R : ℝ,
    WaveMap.supportGeometry u q t C R ∧ WaveMap.supportSections u t C R) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : WaveMap.X n => WaveMap.density u (x, t))) ∧
  ContinuousOn (WaveMap.density u) (WaveMap.domain n) ∧
  ContinuousOn (WaveMap.densityT u) (WaveMap.domain n)) (h_T009 : ∀ t : ℝ, 0 < t → ∀ j : Fin n,
  (∀ x : WaveMap.X n, WaveMap.fluxDx u j (x, t) =
    WaveMap.mixedProduct u j (x, t) + WaveMap.lapProduct u j (x, t)) ∧
  Integrable (fun x : WaveMap.X n => WaveMap.fluxDx u j (x, t)) ∧
  (∫ x : WaveMap.X n, WaveMap.fluxDx u j (x, t)) = 0), (∀ t : ℝ, 0 < t → ∀ j : Fin n,
  (∫ x : WaveMap.X n, WaveMap.mixedProduct u j (x, t)) =
    -(∫ x : WaveMap.X n, WaveMap.lapProduct u j (x, t)) ∧
  Integrable (fun x : WaveMap.X n => WaveMap.mixedProduct u j (x, t)) ∧
  Integrable (fun x : WaveMap.X n => WaveMap.lapProduct u j (x, t))))
def __signature_T011 : Prop :=
  (∀ (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_T002 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t →
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
  Integrable (fun x : WaveMap.X n => WaveMap.lapProduct u j (x, t))), (∀ t : ℝ, 0 < t →
  Integrable (fun x : WaveMap.X n => WaveMap.density u (x, t)) ∧
  DifferentiableAt ℝ (WaveMap.energy u) t ∧ deriv (WaveMap.energy u) t = 0))
def __signature_T012 : Prop :=
  (∀ (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_T011 : ∀ t : ℝ, 0 < t →
  Integrable (fun x : WaveMap.X n => WaveMap.density u (x, t)) ∧
  DifferentiableAt ℝ (WaveMap.energy u) t ∧ deriv (WaveMap.energy u) t = 0), ((∀ t : ℝ, 0 < t →
  Integrable (fun x : WaveMap.X n => WaveMap.density u (x, t)) ∧
  DifferentiableAt ℝ (WaveMap.energy u) t ∧ deriv (WaveMap.energy u) t = 0) ∧
  ∀ s t : ℝ, 0 < s → 0 < t → WaveMap.energy u s = WaveMap.energy u t))
def __signature_P : Prop :=
  (∀ (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_H003 : ‖q‖ = 1) (h_H004 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t → ‖u (x, t)‖ = 1) (h_H005 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t → ∃ a : ℝ, WaveMap.dt (WaveMap.dt u) (x, t) - WaveMap.lap u (x, t) = a • u (x, t)) (h_H006 : ∀ s t : ℝ, 0 < s → s < t → ∃ C : Set (WaveMap.X n), IsCompact C ∧ ∀ x : WaveMap.X n, x ∉ C → ∀ r ∈ Set.Icc s t, u (x, r) = q), ((∀ t : ℝ, 0 < t →
  Integrable (fun x : WaveMap.X n => WaveMap.density u (x, t)) ∧
  DifferentiableAt ℝ (WaveMap.energy u) t ∧ deriv (WaveMap.energy u) t = 0) ∧
  ∀ s t : ℝ, 0 < s → 0 < t → WaveMap.energy u s = WaveMap.energy u t))

end Translation
