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

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem yui_aux_0001 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_T003 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (Space n), ∃ R : ℝ, IsCompact C ∧ 0 < R ∧ C ⊆ openBox (n := n) R ∧ (∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc (t0 / 2) (3 * t0 / 2) → u x r = q) ∧ volume (box (n := n) R) = ENNReal.ofReal ((2 * R) ^ n) ∧ volume (box (n := n) R) < ⊤ ∧ (∀ (k : ℕ) (x : Space n) (r : ℝ), 0 < k → x ∉ C → r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2) → iteratedFDeriv ℝ k (Function.uncurry u) (x, r) = 0) ∧ (∀ r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2), sectionGood (fun x => density u x r) C R ∧ sectionGood (fun x => densityT u x r) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (dtt u x r)) C R ∧ (∀ j : Fin n, sectionGood (flux u j r) C R ∧ sectionGood (fun x => inner ℝ (dut u j x r) (du u j x r)) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (duu u j x r)) C R ∧ sectionGood (fun x => dx (flux u j r) j x) C R))) ∧ (∀ t : ℝ, 0 < t → Integrable (fun x => density u x t))) (h_T006 : ∀ j : Fin n, ∃ e : Space n ≃ᵐ ((EuclideanSpace ℝ {i : Fin n // i ≠ j}) × ℝ), (∀ x : Space n, e x = (WithLp.toLp 2 (fun i : {i : Fin n // i ≠ j} => x i.val), x j)) ∧ MeasurePreserving e (volume : Measure (Space n)) ((volume : Measure (EuclideanSpace ℝ {i : Fin n // i ≠ j})).prod (volume : Measure ℝ))) : yui_aux_type% "∀ t : ℝ, 0 < t → ContDiff ℝ ∞ (fun x => dt u x t) ∧ ContDiff ℝ ∞ (fun x => u x t) ∧ ∀ j : Fin n, ContDiff ℝ ∞ (fun x => du u j x t)" := by
  intro t ht
  have hopen : IsOpen (timeDomain n) := isOpen_lt continuous_const continuous_snd
  have hslice : ContDiff ℝ ∞ (fun x => u x t) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    exact (h_H002.contDiffAt (hopen.mem_nhds ht)).comp x
      (contDiffAt_id.prodMk contDiffAt_const)
  have hdt : ContDiff ℝ ∞ (fun x => dt u x t) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    have H : ContDiffAt ℝ ∞ (fun y => fderiv ℝ (u y) t) x :=
      (h_H002.contDiffAt (hopen.mem_nhds ht)).fderiv contDiffAt_const (by simp)
    change ContDiffAt ℝ ∞ (fun y => fderiv ℝ (u y) t 1) x
    exact H.clm_apply contDiffAt_const
  refine ⟨hdt, hslice, ?_⟩
  intro j
  exact (hslice.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem checked (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_T003 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (Space n), ∃ R : ℝ, IsCompact C ∧ 0 < R ∧ C ⊆ openBox (n := n) R ∧ (∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc (t0 / 2) (3 * t0 / 2) → u x r = q) ∧ volume (box (n := n) R) = ENNReal.ofReal ((2 * R) ^ n) ∧ volume (box (n := n) R) < ⊤ ∧ (∀ (k : ℕ) (x : Space n) (r : ℝ), 0 < k → x ∉ C → r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2) → iteratedFDeriv ℝ k (Function.uncurry u) (x, r) = 0) ∧ (∀ r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2), sectionGood (fun x => density u x r) C R ∧ sectionGood (fun x => densityT u x r) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (dtt u x r)) C R ∧ (∀ j : Fin n, sectionGood (flux u j r) C R ∧ sectionGood (fun x => inner ℝ (dut u j x r) (du u j x r)) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (duu u j x r)) C R ∧ sectionGood (fun x => dx (flux u j r) j x) C R))) ∧ (∀ t : ℝ, 0 < t → Integrable (fun x => density u x t))) (h_T006 : ∀ j : Fin n, ∃ e : Space n ≃ᵐ ((EuclideanSpace ℝ {i : Fin n // i ≠ j}) × ℝ), (∀ x : Space n, e x = (WithLp.toLp 2 (fun i : {i : Fin n // i ≠ j} => x i.val), x j)) ∧ MeasurePreserving e (volume : Measure (Space n)) ((volume : Measure (EuclideanSpace ℝ {i : Fin n // i ≠ j})).prod (volume : Measure ℝ))) : yui_aux_type% "∀ (j : Fin n) (e : Space n ≃ᵐ ((EuclideanSpace ℝ {i : Fin n // i ≠ j}) × ℝ)),\n(∀ x : Space n, e x = (WithLp.toLp 2 (fun i : {i : Fin n // i ≠ j} => x i.val), x j)) →\n∀ (y : EuclideanSpace ℝ {i : Fin n // i ≠ j}) (s : ℝ),\ne.symm (y,s) = e.symm (y,0) + s • EuclideanSpace.single j 1" := by
  intro j e he y s
  have coord (p : (EuclideanSpace ℝ {i : Fin n // i ≠ j}) × ℝ) :
      (WithLp.toLp 2 (fun i : {i : Fin n // i ≠ j} => (e.symm p) i.val), (e.symm p) j) = p := by
    rw [← he, e.apply_symm_apply]
  have hj (p : (EuclideanSpace ℝ {i : Fin n // i ≠ j}) × ℝ) :
      (e.symm p) j = p.2 := congrArg Prod.snd (coord p)
  have hi (p : (EuclideanSpace ℝ {i : Fin n // i ≠ j}) × ℝ) (i : {i : Fin n // i ≠ j}) :
      (e.symm p) i.val = p.1 i := congrArg (fun z => z.1 i) (coord p)
  ext i
  by_cases h : i = j
  · subst i
    simp [hj, EuclideanSpace.single_apply]
  · simp [hi (y,s) ⟨i,h⟩, hi (y,0) ⟨i,h⟩, EuclideanSpace.single_apply, h, Ne.symm h]
#check @checked
#print axioms checked
end YuiAuxiliary
