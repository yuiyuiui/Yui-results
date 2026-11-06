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

theorem yui_aux_0002 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_T003 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (Space n), ∃ R : ℝ, IsCompact C ∧ 0 < R ∧ C ⊆ openBox (n := n) R ∧ (∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc (t0 / 2) (3 * t0 / 2) → u x r = q) ∧ volume (box (n := n) R) = ENNReal.ofReal ((2 * R) ^ n) ∧ volume (box (n := n) R) < ⊤ ∧ (∀ (k : ℕ) (x : Space n) (r : ℝ), 0 < k → x ∉ C → r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2) → iteratedFDeriv ℝ k (Function.uncurry u) (x, r) = 0) ∧ (∀ r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2), sectionGood (fun x => density u x r) C R ∧ sectionGood (fun x => densityT u x r) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (dtt u x r)) C R ∧ (∀ j : Fin n, sectionGood (flux u j r) C R ∧ sectionGood (fun x => inner ℝ (dut u j x r) (du u j x r)) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (duu u j x r)) C R ∧ sectionGood (fun x => dx (flux u j r) j x) C R))) ∧ (∀ t : ℝ, 0 < t → Integrable (fun x => density u x t))) (h_T006 : ∀ j : Fin n, ∃ e : Space n ≃ᵐ ((EuclideanSpace ℝ {i : Fin n // i ≠ j}) × ℝ), (∀ x : Space n, e x = (WithLp.toLp 2 (fun i : {i : Fin n // i ≠ j} => x i.val), x j)) ∧ MeasurePreserving e (volume : Measure (Space n)) ((volume : Measure (EuclideanSpace ℝ {i : Fin n // i ≠ j})).prod (volume : Measure ℝ))) : yui_aux_type% "∀ (j : Fin n) (e : Space n ≃ᵐ ((EuclideanSpace ℝ {i : Fin n // i ≠ j}) × ℝ)),\n(∀ x : Space n, e x = (WithLp.toLp 2 (fun i : {i : Fin n // i ≠ j} => x i.val), x j)) →\n∀ (y : EuclideanSpace ℝ {i : Fin n // i ≠ j}) (s : ℝ),\ne.symm (y,s) = e.symm (y,0) + s • EuclideanSpace.single j 1" := by
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

theorem yui_aux_0003 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_T003 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (Space n), ∃ R : ℝ, IsCompact C ∧ 0 < R ∧ C ⊆ openBox (n := n) R ∧ (∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc (t0 / 2) (3 * t0 / 2) → u x r = q) ∧ volume (box (n := n) R) = ENNReal.ofReal ((2 * R) ^ n) ∧ volume (box (n := n) R) < ⊤ ∧ (∀ (k : ℕ) (x : Space n) (r : ℝ), 0 < k → x ∉ C → r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2) → iteratedFDeriv ℝ k (Function.uncurry u) (x, r) = 0) ∧ (∀ r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2), sectionGood (fun x => density u x r) C R ∧ sectionGood (fun x => densityT u x r) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (dtt u x r)) C R ∧ (∀ j : Fin n, sectionGood (flux u j r) C R ∧ sectionGood (fun x => inner ℝ (dut u j x r) (du u j x r)) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (duu u j x r)) C R ∧ sectionGood (fun x => dx (flux u j r) j x) C R))) ∧ (∀ t : ℝ, 0 < t → Integrable (fun x => density u x t))) (h_T006 : ∀ j : Fin n, ∃ e : Space n ≃ᵐ ((EuclideanSpace ℝ {i : Fin n // i ≠ j}) × ℝ), (∀ x : Space n, e x = (WithLp.toLp 2 (fun i : {i : Fin n // i ≠ j} => x i.val), x j)) ∧ MeasurePreserving e (volume : Measure (Space n)) ((volume : Measure (EuclideanSpace ℝ {i : Fin n // i ≠ j})).prod (volume : Measure ℝ))) : yui_aux_type% "∀ t : ℝ, 0 < t → ∀ (j : Fin n), ContDiff ℝ ∞ (flux u j t) ∧ ∀ x : Space n,\ndx (flux u j t) j x = inner ℝ (dut u j x t) (du u j x t) + inner ℝ (dt u x t) (duu u j x t)" := by
  intro t ht j
  obtain ⟨hdt, hu, hdu⟩ := (@yui_aux_0001 n m u q h_H001 h_H002 h_T003 h_T006) t ht
  refine ⟨hdt.inner ℝ (hdu j), ?_⟩
  intro x
  have hd := hdt.differentiable (by simp) x
  have he := (hdu j).differentiable (by simp) x
  unfold dx flux dut duu
  rw [(hd.hasFDerivAt.inner ℝ he.hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, fderivInnerCLM_apply]
  rw [add_comm]
  rfl

theorem yui_aux_0004 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_T003 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (Space n), ∃ R : ℝ, IsCompact C ∧ 0 < R ∧ C ⊆ openBox (n := n) R ∧ (∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc (t0 / 2) (3 * t0 / 2) → u x r = q) ∧ volume (box (n := n) R) = ENNReal.ofReal ((2 * R) ^ n) ∧ volume (box (n := n) R) < ⊤ ∧ (∀ (k : ℕ) (x : Space n) (r : ℝ), 0 < k → x ∉ C → r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2) → iteratedFDeriv ℝ k (Function.uncurry u) (x, r) = 0) ∧ (∀ r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2), sectionGood (fun x => density u x r) C R ∧ sectionGood (fun x => densityT u x r) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (dtt u x r)) C R ∧ (∀ j : Fin n, sectionGood (flux u j r) C R ∧ sectionGood (fun x => inner ℝ (dut u j x r) (du u j x r)) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (duu u j x r)) C R ∧ sectionGood (fun x => dx (flux u j r) j x) C R))) ∧ (∀ t : ℝ, 0 < t → Integrable (fun x => density u x t))) (h_T006 : ∀ j : Fin n, ∃ e : Space n ≃ᵐ ((EuclideanSpace ℝ {i : Fin n // i ≠ j}) × ℝ), (∀ x : Space n, e x = (WithLp.toLp 2 (fun i : {i : Fin n // i ≠ j} => x i.val), x j)) ∧ MeasurePreserving e (volume : Measure (Space n)) ((volume : Measure (EuclideanSpace ℝ {i : Fin n // i ≠ j})).prod (volume : Measure ℝ))) : yui_aux_type% "∀ (a v : Space n) (s : ℝ), HasDerivAt (fun r : ℝ => a + r • v) v s" := by
  intro a v s
  simpa only [id_eq, one_smul] using ((hasDerivAt_id s).smul_const v).const_add a

theorem yui_aux_0005 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_T003 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (Space n), ∃ R : ℝ, IsCompact C ∧ 0 < R ∧ C ⊆ openBox (n := n) R ∧ (∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc (t0 / 2) (3 * t0 / 2) → u x r = q) ∧ volume (box (n := n) R) = ENNReal.ofReal ((2 * R) ^ n) ∧ volume (box (n := n) R) < ⊤ ∧ (∀ (k : ℕ) (x : Space n) (r : ℝ), 0 < k → x ∉ C → r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2) → iteratedFDeriv ℝ k (Function.uncurry u) (x, r) = 0) ∧ (∀ r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2), sectionGood (fun x => density u x r) C R ∧ sectionGood (fun x => densityT u x r) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (dtt u x r)) C R ∧ (∀ j : Fin n, sectionGood (flux u j r) C R ∧ sectionGood (fun x => inner ℝ (dut u j x r) (du u j x r)) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (duu u j x r)) C R ∧ sectionGood (fun x => dx (flux u j r) j x) C R))) ∧ (∀ t : ℝ, 0 < t → Integrable (fun x => density u x t))) (h_T006 : ∀ j : Fin n, ∃ e : Space n ≃ᵐ ((EuclideanSpace ℝ {i : Fin n // i ≠ j}) × ℝ), (∀ x : Space n, e x = (WithLp.toLp 2 (fun i : {i : Fin n // i ≠ j} => x i.val), x j)) ∧ MeasurePreserving e (volume : Measure (Space n)) ((volume : Measure (EuclideanSpace ℝ {i : Fin n // i ≠ j})).prod (volume : Measure ℝ))) : yui_aux_type% "∀ (j : Fin n) (e : Space n ≃ᵐ ((EuclideanSpace ℝ {i : Fin n // i ≠ j}) × ℝ)),\n(∀ x : Space n, e x = (WithLp.toLp 2 (fun i : {i : Fin n // i ≠ j} => x i.val), x j)) →\n∀ (f : Space n → ℝ), Differentiable ℝ f →\n∀ (y : EuclideanSpace ℝ {i : Fin n // i ≠ j}) (s : ℝ),\nHasDerivAt (fun r => f (e.symm (y,r))) (dx f j (e.symm (y,s))) s" := by
  intro j e he f hf y s
  have ha := (@yui_aux_0002 n m u q h_H001 h_H002 h_T003 h_T006) j e he y
  have hline : HasDerivAt (fun r : ℝ => e.symm (y,r)) (EuclideanSpace.single j 1) s := by
    rw [show (fun r : ℝ => e.symm (y,r)) = (fun r => e.symm (y,0) + r • EuclideanSpace.single j 1) from funext ha]
    exact (@yui_aux_0004 n m u q h_H001 h_H002 h_T003 h_T006) _ _ s
  exact (hf (e.symm (y,s))).hasFDerivAt.comp_hasDerivAt s hline

theorem yui_aux_0006 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_T003 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (Space n), ∃ R : ℝ, IsCompact C ∧ 0 < R ∧ C ⊆ openBox (n := n) R ∧ (∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc (t0 / 2) (3 * t0 / 2) → u x r = q) ∧ volume (box (n := n) R) = ENNReal.ofReal ((2 * R) ^ n) ∧ volume (box (n := n) R) < ⊤ ∧ (∀ (k : ℕ) (x : Space n) (r : ℝ), 0 < k → x ∉ C → r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2) → iteratedFDeriv ℝ k (Function.uncurry u) (x, r) = 0) ∧ (∀ r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2), sectionGood (fun x => density u x r) C R ∧ sectionGood (fun x => densityT u x r) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (dtt u x r)) C R ∧ (∀ j : Fin n, sectionGood (flux u j r) C R ∧ sectionGood (fun x => inner ℝ (dut u j x r) (du u j x r)) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (duu u j x r)) C R ∧ sectionGood (fun x => dx (flux u j r) j x) C R))) ∧ (∀ t : ℝ, 0 < t → Integrable (fun x => density u x t))) (h_T006 : ∀ j : Fin n, ∃ e : Space n ≃ᵐ ((EuclideanSpace ℝ {i : Fin n // i ≠ j}) × ℝ), (∀ x : Space n, e x = (WithLp.toLp 2 (fun i : {i : Fin n // i ≠ j} => x i.val), x j)) ∧ MeasurePreserving e (volume : Measure (Space n)) ((volume : Measure (EuclideanSpace ℝ {i : Fin n // i ≠ j})).prod (volume : Measure ℝ))) : yui_aux_type% "∀ (j : Fin n) (e : Space n ≃ᵐ ((EuclideanSpace ℝ {i : Fin n // i ≠ j}) × ℝ)),\n(∀ x : Space n, e x = (WithLp.toLp 2 (fun i : {i : Fin n // i ≠ j} => x i.val), x j)) →\n∀ (f : Space n → ℝ) (C : Set (Space n)) (R : ℝ),\nDifferentiable ℝ f → Continuous (fun x => dx f j x) → 0 < R → C ⊆ openBox (n := n) R →\n(∀ x ∉ C, f x = 0) →\n∀ y : EuclideanSpace ℝ {i : Fin n // i ≠ j},\n(∫ s in Set.Icc (-R) R, dx f j (e.symm (y,s))) = 0" := by
  intro j e he f C R hf hd hR hC hz y
  have ha := (@yui_aux_0002 n m u q h_H001 h_H002 h_T003 h_T006) j e he y
  have hc : Continuous (fun s : ℝ => e.symm (y,s)) := by
    rw [show (fun s : ℝ => e.symm (y,s)) = (fun s => e.symm (y,0) + s • EuclideanSpace.single j 1) from funext ha]
    fun_prop
  have hder := (@yui_aux_0005 n m u q h_H001 h_H002 h_T003 h_T006) j e he f hf y
  have hj (s : ℝ) : (e.symm (y,s)) j = s := by
    exact congrArg Prod.snd ((he (e.symm (y,s))).symm.trans (e.apply_symm_apply (y,s)))
  have hend (s : ℝ) (hs : s = -R ∨ s = R) : f (e.symm (y,s)) = 0 := by
    apply hz
    intro hmem
    have hbounds := hC hmem j
    rw [hj] at hbounds
    rcases hs with hs | hs
    · rw [hs] at hbounds
      exact (lt_irrefl (-R)) hbounds.1
    · rw [hs] at hbounds
      exact (lt_irrefl R) hbounds.2
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := -R) (b := R) (fun s _ => hder s) ((hd.comp hc).intervalIntegrable _ _)
  rw [hend R (Or.inr rfl), hend (-R) (Or.inl rfl), sub_self] at hFTC
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : -R ≤ R)]
  exact hFTC

theorem checked (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_T003 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (Space n), ∃ R : ℝ, IsCompact C ∧ 0 < R ∧ C ⊆ openBox (n := n) R ∧ (∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc (t0 / 2) (3 * t0 / 2) → u x r = q) ∧ volume (box (n := n) R) = ENNReal.ofReal ((2 * R) ^ n) ∧ volume (box (n := n) R) < ⊤ ∧ (∀ (k : ℕ) (x : Space n) (r : ℝ), 0 < k → x ∉ C → r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2) → iteratedFDeriv ℝ k (Function.uncurry u) (x, r) = 0) ∧ (∀ r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2), sectionGood (fun x => density u x r) C R ∧ sectionGood (fun x => densityT u x r) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (dtt u x r)) C R ∧ (∀ j : Fin n, sectionGood (flux u j r) C R ∧ sectionGood (fun x => inner ℝ (dut u j x r) (du u j x r)) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (duu u j x r)) C R ∧ sectionGood (fun x => dx (flux u j r) j x) C R))) ∧ (∀ t : ℝ, 0 < t → Integrable (fun x => density u x t))) (h_T006 : ∀ j : Fin n, ∃ e : Space n ≃ᵐ ((EuclideanSpace ℝ {i : Fin n // i ≠ j}) × ℝ), (∀ x : Space n, e x = (WithLp.toLp 2 (fun i : {i : Fin n // i ≠ j} => x i.val), x j)) ∧ MeasurePreserving e (volume : Measure (Space n)) ((volume : Measure (EuclideanSpace ℝ {i : Fin n // i ≠ j})).prod (volume : Measure ℝ))) : yui_aux_type% "∀ (j : Fin n) (f : Space n → ℝ) (C : Set (Space n)) (R : ℝ),\n0 < R → C ⊆ openBox (n := n) R → Differentiable ℝ f →\nsectionGood f C R → sectionGood (fun x => dx f j x) C R →\n(∫ x, dx f j x) = 0" := by
  intro j f C R hR hC hf hgood hdgood
  obtain ⟨e, he, hmp⟩ := h_T006 j
  let Y := EuclideanSpace ℝ {i : Fin n // i ≠ j}
  let Qother : Set Y := {y | ∀ i, y i ∈ Set.Icc (-R) R}
  let P : Set (Y × ℝ) := Qother ×ˢ Set.Icc (-R) R
  have hebox : e ⁻¹' P = box (n := n) R := by
    ext x
    change e x ∈ P ↔ ∀ i, x i ∈ Set.Icc (-R) R
    rw [he]
    change ((∀ i : {i : Fin n // i ≠ j}, x i.val ∈ Set.Icc (-R) R) ∧ x j ∈ Set.Icc (-R) R) ↔ _
    constructor
    · rintro ⟨hother,hj⟩ i
      by_cases hi : i = j
      · simpa only [hi] using hj
      · exact hother ⟨i,hi⟩
    · intro hx
      exact ⟨fun i => hx i.val, hx j⟩
  have hmpR : MeasurePreserving e (volume.restrict (box (n := n) R))
      ((volume : Measure Y).prod volume |>.restrict P) := by
    rw [← hebox]
    exact hmp.restrict_preimage_emb e.measurableEmbedding P
  let w : Y × ℝ → ℝ := fun p => dx f j (e.symm p)
  have hw : IntegrableOn w P ((volume : Measure Y).prod volume) := by
    apply (hmpR.integrable_comp_emb e.measurableEmbedding).mp
    simpa only [Function.comp_def, w, e.symm_apply_apply] using hdgood.2.2.2.integrableOn (s := box (n := n) R)
  have hchange : (∫ x in box (n := n) R, dx f j x) =
      ∫ p in P, w p ∂((volume : Measure Y).prod volume) := by
    simpa only [w, e.symm_apply_apply] using hmpR.integral_comp' w
  have hslices := (@yui_aux_0006 n m u q h_H001 h_H002 h_T003 h_T006)
    j e he f C R hf hdgood.1 hR hC hgood.2.2.1
  have hbox : (∫ x in box (n := n) R, dx f j x) = 0 := by
    rw [hchange, setIntegral_prod w hw]
    change (∫ y in Qother, ∫ s in Set.Icc (-R) R, dx f j (e.symm (y,s))) = 0
    simp only [hslices, integral_zero]
  have hCbox : C ⊆ box (n := n) R := by
    intro x hx i
    exact ⟨(hC hx i).1.le, (hC hx i).2.le⟩
  have hextend : (∫ x in box (n := n) R, dx f j x) = ∫ x, dx f j x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => hdgood.2.2.1 x (fun hc => hx (hCbox hc)))
  exact hextend.symm.trans hbox
#check @checked
#print axioms checked
end YuiAuxiliary
