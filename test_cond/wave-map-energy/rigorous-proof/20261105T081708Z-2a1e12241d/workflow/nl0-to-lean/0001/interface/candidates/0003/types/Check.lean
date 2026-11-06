import Mathlib
open scoped BigOperators ContDiff Topology
open MeasureTheory
namespace WaveMap
abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)
def timeDomain (n : ℕ) : Set (Space n × ℝ) := {p | 0 < p.2}
noncomputable def dt {n m : ℕ} (u : Space n → ℝ → Space m) (x : Space n) (t : ℝ) : Space m :=
  deriv (u x) t
noncomputable def dtt {n m : ℕ} (u : Space n → ℝ → Space m) (x : Space n) (t : ℝ) : Space m :=
  deriv (fun r => dt u x r) t
noncomputable def dx {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Space n → F) (j : Fin n) (x : Space n) : F :=
  fderiv ℝ f x (EuclideanSpace.single j 1)
noncomputable def du {n m : ℕ} (u : Space n → ℝ → Space m) (j : Fin n) (x : Space n) (t : ℝ) : Space m :=
  dx (fun y => u y t) j x
noncomputable def duu {n m : ℕ} (u : Space n → ℝ → Space m) (j : Fin n) (x : Space n) (t : ℝ) : Space m :=
  dx (fun y => du u j y t) j x
noncomputable def dut {n m : ℕ} (u : Space n → ℝ → Space m) (j : Fin n) (x : Space n) (t : ℝ) : Space m :=
  dx (fun y => dt u y t) j x
noncomputable def lap {n m : ℕ} (u : Space n → ℝ → Space m) (x : Space n) (t : ℝ) : Space m :=
  ∑ j, duu u j x t
noncomputable def density {n m : ℕ} (u : Space n → ℝ → Space m) (x : Space n) (t : ℝ) : ℝ :=
  ‖dt u x t‖ ^ 2 + ∑ j, ‖du u j x t‖ ^ 2
noncomputable def densityT {n m : ℕ} (u : Space n → ℝ → Space m) (x : Space n) (t : ℝ) : ℝ :=
  deriv (density u x) t
noncomputable def energy {n m : ℕ} (u : Space n → ℝ → Space m) (t : ℝ) : ℝ :=
  ∫ x, density u x t
noncomputable def flux {n m : ℕ} (u : Space n → ℝ → Space m) (j : Fin n) (t : ℝ) (x : Space n) : ℝ :=
  inner ℝ (dt u x t) (du u j x t)
def box {n : ℕ} (R : ℝ) : Set (Space n) := {x | ∀ j, x j ∈ Set.Icc (-R) R}
def openBox {n : ℕ} (R : ℝ) : Set (Space n) := {x | ∀ j, x j ∈ Set.Ioo (-R) R}
def sectionGood {n : ℕ} (f : Space n → ℝ) (C : Set (Space n)) (R : ℝ) : Prop :=
  Continuous f ∧ (∃ B : ℝ, ∀ x ∈ box (n := n) R, |f x| ≤ B) ∧
  (∀ x ∉ C, f x = 0) ∧ Integrable f
end WaveMap

open WaveMap

namespace Translation
set_option autoImplicit false

def __signature_T001 : Prop :=
  (∀ (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_H004 : ∀ (x : Space n) (t : ℝ), 0 < t → ‖u x t‖ = 1) (h_H005 : ∀ (x : Space n) (t : ℝ), 0 < t → ∃ a : ℝ, dtt u x t - lap u x t = a • u x t), (∀ (x : Space n) (t : ℝ), 0 < t → inner ℝ (u x t) (dt u x t) = 0 ∧ inner ℝ (dt u x t) (dtt u x t - lap u x t) = 0))
def __signature_T002 : Prop :=
  (∀ (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_H004 : ∀ (x : Space n) (t : ℝ), 0 < t → ‖u x t‖ = 1) (h_H005 : ∀ (x : Space n) (t : ℝ), 0 < t → ∃ a : ℝ, dtt u x t - lap u x t = a • u x t) (h_T001 : ∀ (x : Space n) (t : ℝ), 0 < t → inner ℝ (u x t) (dt u x t) = 0 ∧ inner ℝ (dt u x t) (dtt u x t - lap u x t) = 0), (∀ (x : Space n) (t : ℝ), 0 < t → (inner ℝ (u x t) (dt u x t) = 0 ∧ inner ℝ (dt u x t) (dtt u x t - lap u x t) = 0) ∧ inner ℝ (u x t) (dtt u x t) = -(‖dt u x t‖ ^ 2) ∧ (∀ j : Fin n, inner ℝ (u x t) (duu u j x t) = -(‖du u j x t‖ ^ 2)) ∧ (∀ a : ℝ, dtt u x t - lap u x t = a • u x t → a = (∑ j : Fin n, ‖du u j x t‖ ^ 2) - ‖dt u x t‖ ^ 2) ∧ dtt u x t - lap u x t = ((∑ j : Fin n, ‖du u j x t‖ ^ 2) - ‖dt u x t‖ ^ 2) • u x t))
def __signature_T003 : Prop :=
  (∀ (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_H006 : ∀ (s t : ℝ), 0 < s → s < t → ∃ C : Set (Space n), IsCompact C ∧ ∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc s t → u x r = q), ((∀ t0 : ℝ, 0 < t0 → ∃ C : Set (Space n), ∃ R : ℝ, IsCompact C ∧ 0 < R ∧ C ⊆ openBox (n := n) R ∧ (∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc (t0 / 2) (3 * t0 / 2) → u x r = q) ∧ volume (box (n := n) R) = ENNReal.ofReal ((2 * R) ^ n) ∧ volume (box (n := n) R) < ⊤ ∧ (∀ (k : ℕ) (x : Space n) (r : ℝ), 0 < k → x ∉ C → r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2) → iteratedFDeriv ℝ k (Function.uncurry u) (x, r) = 0) ∧ (∀ r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2), sectionGood (fun x => density u x r) C R ∧ sectionGood (fun x => densityT u x r) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (dtt u x r)) C R ∧ (∀ j : Fin n, sectionGood (flux u j r) C R ∧ sectionGood (fun x => inner ℝ (dut u j x r) (du u j x r)) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (duu u j x r)) C R ∧ sectionGood (fun x => dx (flux u j r) j x) C R))) ∧ (∀ t : ℝ, 0 < t → Integrable (fun x => density u x t))))
def __signature_T004 : Prop :=
  (∀ (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)), ((∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (density u x) (2 * inner ℝ (dt u x t) (dtt u x t) + 2 * ∑ j : Fin n, inner ℝ (du u j x t) (dut u j x t)) t ∧ densityT u x t = 2 * inner ℝ (dt u x t) (dtt u x t) + 2 * ∑ j : Fin n, inner ℝ (du u j x t) (dut u j x t)) ∧ ContinuousOn (Function.uncurry (densityT u)) (timeDomain n)))
def __signature_T005 : Prop :=
  (∀ (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_T003 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (Space n), ∃ R : ℝ, IsCompact C ∧ 0 < R ∧ C ⊆ openBox (n := n) R ∧ (∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc (t0 / 2) (3 * t0 / 2) → u x r = q) ∧ volume (box (n := n) R) = ENNReal.ofReal ((2 * R) ^ n) ∧ volume (box (n := n) R) < ⊤ ∧ (∀ (k : ℕ) (x : Space n) (r : ℝ), 0 < k → x ∉ C → r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2) → iteratedFDeriv ℝ k (Function.uncurry u) (x, r) = 0) ∧ (∀ r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2), sectionGood (fun x => density u x r) C R ∧ sectionGood (fun x => densityT u x r) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (dtt u x r)) C R ∧ (∀ j : Fin n, sectionGood (flux u j r) C R ∧ sectionGood (fun x => inner ℝ (dut u j x r) (du u j x r)) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (duu u j x r)) C R ∧ sectionGood (fun x => dx (flux u j r) j x) C R))) ∧ (∀ t : ℝ, 0 < t → Integrable (fun x => density u x t))) (h_T004 : (∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (density u x) (2 * inner ℝ (dt u x t) (dtt u x t) + 2 * ∑ j : Fin n, inner ℝ (du u j x t) (dut u j x t)) t ∧ densityT u x t = 2 * inner ℝ (dt u x t) (dtt u x t) + 2 * ∑ j : Fin n, inner ℝ (du u j x t) (dut u j x t)) ∧ ContinuousOn (Function.uncurry (densityT u)) (timeDomain n)), (∀ t : ℝ, 0 < t → (∀ x : Space n, densityT u x t = 2 * inner ℝ (dt u x t) (dtt u x t) + 2 * ∑ j : Fin n, inner ℝ (du u j x t) (dut u j x t)) ∧ Integrable (fun x => densityT u x t) ∧ Integrable (fun x => inner ℝ (dt u x t) (dtt u x t)) ∧ (∀ j : Fin n, Integrable (fun x => inner ℝ (du u j x t) (dut u j x t))) ∧ HasDerivAt (energy u) (∫ x, densityT u x t) t ∧ deriv (energy u) t = (∫ x, densityT u x t) ∧ deriv (energy u) t = 2 * (∫ x, inner ℝ (dt u x t) (dtt u x t)) + 2 * ∑ j : Fin n, (∫ x, inner ℝ (du u j x t) (dut u j x t))))
def __signature_T006 : Prop :=
  (∀ (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m), (∀ j : Fin n, ∃ e : Space n ≃ᵐ ((EuclideanSpace ℝ {i : Fin n // i ≠ j}) × ℝ), (∀ x : Space n, e x = (WithLp.toLp 2 (fun i : {i : Fin n // i ≠ j} => x i.val), x j)) ∧ MeasurePreserving e (volume : Measure (Space n)) ((volume : Measure (EuclideanSpace ℝ {i : Fin n // i ≠ j})).prod (volume : Measure ℝ))))
def __signature_T007 : Prop :=
  (∀ (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_T003 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (Space n), ∃ R : ℝ, IsCompact C ∧ 0 < R ∧ C ⊆ openBox (n := n) R ∧ (∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc (t0 / 2) (3 * t0 / 2) → u x r = q) ∧ volume (box (n := n) R) = ENNReal.ofReal ((2 * R) ^ n) ∧ volume (box (n := n) R) < ⊤ ∧ (∀ (k : ℕ) (x : Space n) (r : ℝ), 0 < k → x ∉ C → r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2) → iteratedFDeriv ℝ k (Function.uncurry u) (x, r) = 0) ∧ (∀ r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2), sectionGood (fun x => density u x r) C R ∧ sectionGood (fun x => densityT u x r) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (dtt u x r)) C R ∧ (∀ j : Fin n, sectionGood (flux u j r) C R ∧ sectionGood (fun x => inner ℝ (dut u j x r) (du u j x r)) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (duu u j x r)) C R ∧ sectionGood (fun x => dx (flux u j r) j x) C R))) ∧ (∀ t : ℝ, 0 < t → Integrable (fun x => density u x t))) (h_T006 : ∀ j : Fin n, ∃ e : Space n ≃ᵐ ((EuclideanSpace ℝ {i : Fin n // i ≠ j}) × ℝ), (∀ x : Space n, e x = (WithLp.toLp 2 (fun i : {i : Fin n // i ≠ j} => x i.val), x j)) ∧ MeasurePreserving e (volume : Measure (Space n)) ((volume : Measure (EuclideanSpace ℝ {i : Fin n // i ≠ j})).prod (volume : Measure ℝ))), (∀ t : ℝ, 0 < t → ∀ j : Fin n, Integrable (fun x => inner ℝ (du u j x t) (dut u j x t)) ∧ Integrable (fun x => inner ℝ (dt u x t) (duu u j x t)) ∧ (∫ x, inner ℝ (du u j x t) (dut u j x t)) = -(∫ x, inner ℝ (dt u x t) (duu u j x t))))
def __signature_T008 : Prop :=
  (∀ (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_T002 : ∀ (x : Space n) (t : ℝ), 0 < t → (inner ℝ (u x t) (dt u x t) = 0 ∧ inner ℝ (dt u x t) (dtt u x t - lap u x t) = 0) ∧ inner ℝ (u x t) (dtt u x t) = -(‖dt u x t‖ ^ 2) ∧ (∀ j : Fin n, inner ℝ (u x t) (duu u j x t) = -(‖du u j x t‖ ^ 2)) ∧ (∀ a : ℝ, dtt u x t - lap u x t = a • u x t → a = (∑ j : Fin n, ‖du u j x t‖ ^ 2) - ‖dt u x t‖ ^ 2) ∧ dtt u x t - lap u x t = ((∑ j : Fin n, ‖du u j x t‖ ^ 2) - ‖dt u x t‖ ^ 2) • u x t) (h_T003 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (Space n), ∃ R : ℝ, IsCompact C ∧ 0 < R ∧ C ⊆ openBox (n := n) R ∧ (∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc (t0 / 2) (3 * t0 / 2) → u x r = q) ∧ volume (box (n := n) R) = ENNReal.ofReal ((2 * R) ^ n) ∧ volume (box (n := n) R) < ⊤ ∧ (∀ (k : ℕ) (x : Space n) (r : ℝ), 0 < k → x ∉ C → r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2) → iteratedFDeriv ℝ k (Function.uncurry u) (x, r) = 0) ∧ (∀ r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2), sectionGood (fun x => density u x r) C R ∧ sectionGood (fun x => densityT u x r) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (dtt u x r)) C R ∧ (∀ j : Fin n, sectionGood (flux u j r) C R ∧ sectionGood (fun x => inner ℝ (dut u j x r) (du u j x r)) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (duu u j x r)) C R ∧ sectionGood (fun x => dx (flux u j r) j x) C R))) ∧ (∀ t : ℝ, 0 < t → Integrable (fun x => density u x t))) (h_T005 : ∀ t : ℝ, 0 < t → (∀ x : Space n, densityT u x t = 2 * inner ℝ (dt u x t) (dtt u x t) + 2 * ∑ j : Fin n, inner ℝ (du u j x t) (dut u j x t)) ∧ Integrable (fun x => densityT u x t) ∧ Integrable (fun x => inner ℝ (dt u x t) (dtt u x t)) ∧ (∀ j : Fin n, Integrable (fun x => inner ℝ (du u j x t) (dut u j x t))) ∧ HasDerivAt (energy u) (∫ x, densityT u x t) t ∧ deriv (energy u) t = (∫ x, densityT u x t) ∧ deriv (energy u) t = 2 * (∫ x, inner ℝ (dt u x t) (dtt u x t)) + 2 * ∑ j : Fin n, (∫ x, inner ℝ (du u j x t) (dut u j x t))) (h_T007 : ∀ t : ℝ, 0 < t → ∀ j : Fin n, Integrable (fun x => inner ℝ (du u j x t) (dut u j x t)) ∧ Integrable (fun x => inner ℝ (dt u x t) (duu u j x t)) ∧ (∫ x, inner ℝ (du u j x t) (dut u j x t)) = -(∫ x, inner ℝ (dt u x t) (duu u j x t))), (∀ t : ℝ, 0 < t → Integrable (fun x => density u x t) ∧ DifferentiableAt ℝ (energy u) t ∧ deriv (energy u) t = 0))
def __signature_T009 : Prop :=
  (∀ (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_T008 : ∀ t : ℝ, 0 < t → Integrable (fun x => density u x t) ∧ DifferentiableAt ℝ (energy u) t ∧ deriv (energy u) t = 0), ((∀ t : ℝ, 0 < t → Integrable (fun x => density u x t) ∧ DifferentiableAt ℝ (energy u) t ∧ deriv (energy u) t = 0) ∧ (∀ s t : ℝ, 0 < s → 0 < t → energy u t = energy u s)))
def __signature_P : Prop :=
  (∀ (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_H003 : ‖q‖ = 1) (h_H004 : ∀ (x : Space n) (t : ℝ), 0 < t → ‖u x t‖ = 1) (h_H005 : ∀ (x : Space n) (t : ℝ), 0 < t → ∃ a : ℝ, dtt u x t - lap u x t = a • u x t) (h_H006 : ∀ (s t : ℝ), 0 < s → s < t → ∃ C : Set (Space n), IsCompact C ∧ ∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc s t → u x r = q), ((∀ t : ℝ, 0 < t → Integrable (fun x => density u x t) ∧ DifferentiableAt ℝ (energy u) t ∧ deriv (energy u) t = 0) ∧ (∀ s t : ℝ, 0 < s → 0 < t → energy u t = energy u s)))

end Translation
