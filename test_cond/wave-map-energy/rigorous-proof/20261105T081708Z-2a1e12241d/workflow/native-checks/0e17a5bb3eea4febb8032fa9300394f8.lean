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

theorem T008 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_T002 : ∀ (x : Space n) (t : ℝ), 0 < t → (inner ℝ (u x t) (dt u x t) = 0 ∧ inner ℝ (dt u x t) (dtt u x t - lap u x t) = 0) ∧ inner ℝ (u x t) (dtt u x t) = -(‖dt u x t‖ ^ 2) ∧ (∀ j : Fin n, inner ℝ (u x t) (duu u j x t) = -(‖du u j x t‖ ^ 2)) ∧ (∀ a : ℝ, dtt u x t - lap u x t = a • u x t → a = (∑ j : Fin n, ‖du u j x t‖ ^ 2) - ‖dt u x t‖ ^ 2) ∧ dtt u x t - lap u x t = ((∑ j : Fin n, ‖du u j x t‖ ^ 2) - ‖dt u x t‖ ^ 2) • u x t) (h_T003 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (Space n), ∃ R : ℝ, IsCompact C ∧ 0 < R ∧ C ⊆ openBox (n := n) R ∧ (∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc (t0 / 2) (3 * t0 / 2) → u x r = q) ∧ volume (box (n := n) R) = ENNReal.ofReal ((2 * R) ^ n) ∧ volume (box (n := n) R) < ⊤ ∧ (∀ (k : ℕ) (x : Space n) (r : ℝ), 0 < k → x ∉ C → r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2) → iteratedFDeriv ℝ k (Function.uncurry u) (x, r) = 0) ∧ (∀ r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2), sectionGood (fun x => density u x r) C R ∧ sectionGood (fun x => densityT u x r) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (dtt u x r)) C R ∧ (∀ j : Fin n, sectionGood (flux u j r) C R ∧ sectionGood (fun x => inner ℝ (dut u j x r) (du u j x r)) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (duu u j x r)) C R ∧ sectionGood (fun x => dx (flux u j r) j x) C R))) ∧ (∀ t : ℝ, 0 < t → Integrable (fun x => density u x t))) (h_T005 : ∀ t : ℝ, 0 < t → (∀ x : Space n, densityT u x t = 2 * inner ℝ (dt u x t) (dtt u x t) + 2 * ∑ j : Fin n, inner ℝ (du u j x t) (dut u j x t)) ∧ Integrable (fun x => densityT u x t) ∧ Integrable (fun x => inner ℝ (dt u x t) (dtt u x t)) ∧ (∀ j : Fin n, Integrable (fun x => inner ℝ (du u j x t) (dut u j x t))) ∧ HasDerivAt (energy u) (∫ x, densityT u x t) t ∧ deriv (energy u) t = (∫ x, densityT u x t) ∧ deriv (energy u) t = 2 * (∫ x, inner ℝ (dt u x t) (dtt u x t)) + 2 * ∑ j : Fin n, (∫ x, inner ℝ (du u j x t) (dut u j x t))) (h_T007 : ∀ t : ℝ, 0 < t → ∀ j : Fin n, Integrable (fun x => inner ℝ (du u j x t) (dut u j x t)) ∧ Integrable (fun x => inner ℝ (dt u x t) (duu u j x t)) ∧ (∫ x, inner ℝ (du u j x t) (dut u j x t)) = -(∫ x, inner ℝ (dt u x t) (duu u j x t))) :
    ∀ t : ℝ, 0 < t → Integrable (fun x => density u x t) ∧ DifferentiableAt ℝ (energy u) t ∧ deriv (energy u) t = 0 := by
  intro t ht
  rcases h_T005 t ht with ⟨hpoint, hint, ha, hc, hderiv, hvalue, hformula⟩
  refine ⟨h_T003.2 t ht, hderiv.differentiableAt, ?_⟩
  have hb : ∀ j : Fin n, Integrable (fun x => inner ℝ (dt u x t) (duu u j x t)) :=
    fun j => (h_T007 t ht j).2.1
  have hsum : Integrable (fun x => ∑ j : Fin n,
      inner ℝ (dt u x t) (duu u j x t)) :=
    integrable_finsetSum Finset.univ (fun j _ => hb j)
  have hlin : (∫ x, inner ℝ (dt u x t) (dtt u x t) -
      ∑ j : Fin n, inner ℝ (dt u x t) (duu u j x t)) =
      (∫ x, inner ℝ (dt u x t) (dtt u x t)) -
      ∑ j : Fin n, (∫ x, inner ℝ (dt u x t) (duu u j x t)) := by
    rw [integral_sub ha hsum, integral_finsetSum Finset.univ (fun j _ => hb j)]
  have hz : (∫ x, inner ℝ (dt u x t) (dtt u x t) -
      ∑ j : Fin n, inner ℝ (dt u x t) (duu u j x t)) = 0 := by
    have hp : ∀ x : Space n, inner ℝ (dt u x t) (dtt u x t) -
        ∑ j : Fin n, inner ℝ (dt u x t) (duu u j x t) = 0 := by
      intro x
      have hzero := (h_T002 x t ht).1.2
      simpa only [lap, inner_sub_right, inner_sum] using hzero
    simp_rw [hp]
    simp
  rw [hformula]
  simp_rw [(h_T007 t ht _).2.2]
  rw [Finset.sum_neg_distrib]
  have hcancel := hlin.symm.trans hz
  linarith

#check @T008
#print axioms T008

end Translation
