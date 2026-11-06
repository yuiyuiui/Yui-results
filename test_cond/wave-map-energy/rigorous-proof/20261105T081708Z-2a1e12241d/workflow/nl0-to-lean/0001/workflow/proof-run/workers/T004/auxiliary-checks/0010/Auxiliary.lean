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
theorem yui_aux_0001 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) : yui_aux_type% "∀ (f : Space n → ℝ → Space m), ContDiffOn ℝ ∞ (Function.uncurry f) (timeDomain n) → (∀ (x : Space n) (t : ℝ), 0 < t → dt f x t = fderiv ℝ (Function.uncurry f) (x,t) (0,1) ∧ ∀ j : Fin n, du f j x t = fderiv ℝ (Function.uncurry f) (x,t) (EuclideanSpace.single j 1,0))" := by
  intro f hf x t ht
  have ho : IsOpen (timeDomain n) := isOpen_lt continuous_const continuous_snd
  have hc : ContDiffAt ℝ ∞ (Function.uncurry f) (x,t) := (hf (x,t) ht).contDiffAt (ho.mem_nhds ht)
  have hd := hc.differentiableAt (by simp)
  constructor
  · have h := hd.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_const t x).prodMk (hasDerivAt_id t))
    exact h.deriv
  · intro j
    have hi : HasFDerivAt (fun y : Space n => (y,t)) ((ContinuousLinearMap.id ℝ (Space n)).prod 0) x := (hasFDerivAt_id x).prodMk (hasFDerivAt_const t x)
    have h := hd.hasFDerivAt.comp x hi
    simpa [du, dx, Function.comp_def] using congrArg (fun L : Space n →L[ℝ] Space m => L (EuclideanSpace.single j 1)) h.fderiv

theorem yui_aux_0002 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) : yui_aux_type% "∀ (f : Space n → ℝ → Space m), ContDiffOn ℝ ∞ (Function.uncurry f) (timeDomain n) → ContDiffOn ℝ ∞ (Function.uncurry (dt f)) (timeDomain n) ∧ ∀ j : Fin n, ContDiffOn ℝ ∞ (fun p : Space n × ℝ => du f j p.1 p.2) (timeDomain n)" := by
  intro f hf
  have ho : IsOpen (timeDomain n) := isOpen_lt continuous_const continuous_snd
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ (Function.uncurry f)) (timeDomain n) := hf.fderiv_of_isOpen ho (by simp)
  have hdir (v : Space n × ℝ) : ContDiffOn ℝ ∞ (fun p => fderiv ℝ (Function.uncurry f) p v) (timeDomain n) := hD.clm_apply contDiffOn_const
  constructor
  · apply (hdir (0,1)).congr
    intro p hp
    exact (yui_aux_0001 n m u q h_H002 f hf p.1 p.2 hp).1
  · intro j
    apply (hdir (EuclideanSpace.single j 1,0)).congr
    intro p hp
    exact (yui_aux_0001 n m u q h_H002 f hf p.1 p.2 hp).2 j

theorem yui_aux_0003 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) : yui_aux_type% "∀ (f : Space n → ℝ → Space m) (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (timeDomain n)) (p : Space n × ℝ), p ∈ timeDomain n → ∀ v w : Space n × ℝ, fderiv ℝ (fun z => fderiv ℝ (Function.uncurry f) z v) p w = fderiv ℝ (fderiv ℝ (Function.uncurry f)) p w v" := by
  intro f hf p hp v w
  have ho : IsOpen (timeDomain n) := isOpen_lt continuous_const continuous_snd
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ (Function.uncurry f)) (timeDomain n) := hf.fderiv_of_isOpen ho (by simp)
  have hd : DifferentiableAt ℝ (fderiv ℝ (Function.uncurry f)) p := ((hD p hp).contDiffAt (ho.mem_nhds hp)).differentiableAt (by simp)
  have he := hd.hasFDerivAt.clm_apply (hasFDerivAt_const v p)
  simpa using congrArg (fun L : (Space n × ℝ) →L[ℝ] Space m => L w) he.fderiv

theorem checked (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) : yui_aux_type% "minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω)" := by
  simp only [minSmoothness_of_isRCLikeNormedField]
  exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
#check @checked
#print axioms checked
end YuiAuxiliary
