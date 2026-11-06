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
theorem yui_aux_0001 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_H006 : ∀ (s t : ℝ), 0 < s → s < t → ∃ C : Set (Space n), IsCompact C ∧ ∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc s t → u x r = q) : yui_aux_type% "∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : Space n → ℝ → F), ContDiffOn ℝ ∞ (Function.uncurry f) (timeDomain n) → ContDiffOn ℝ ∞ (fun p : Space n × ℝ => deriv (f p.1) p.2) (timeDomain n) ∧ ∀ j : Fin n, ContDiffOn ℝ ∞ (fun p : Space n × ℝ => dx (fun y => f y p.2) j p.1) (timeDomain n)" := by
  intro F _ _ f hf
  have ho : IsOpen (timeDomain n) := isOpen_lt continuous_const continuous_snd
  have hat (x : Space n) (t : ℝ) (ht : 0 < t) :
      ContDiffAt ℝ ∞ (Function.uncurry f) (x,t) :=
    (hf (x,t) ht).contDiffAt (ho.mem_nhds ht)
  constructor
  · intro p hp
    apply ContDiffAt.contDiffWithinAt
    have hh : ContDiffAt ℝ ∞ (fun z : (Space n × ℝ) × ℝ => f z.1.1 z.2) (p, p.2) :=
      (hat p.1 p.2 hp).comp (p,p.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    have hd : ContDiffAt ℝ ∞ (fun z : Space n × ℝ => fderiv ℝ (f z.1) z.2) p :=
      hh.fderiv contDiffAt_snd (by simp)
    simpa only [deriv] using hd.clm_apply (contDiffAt_const (c := (1 : ℝ)))
  · intro j p hp
    apply ContDiffAt.contDiffWithinAt
    have hh : ContDiffAt ℝ ∞ (fun z : (Space n × ℝ) × Space n => f z.2 z.1.2) (p, p.1) :=
      (hat p.1 p.2 hp).comp (p,p.1) (contDiffAt_snd.prodMk contDiffAt_fst.snd)
    have hd : ContDiffAt ℝ ∞ (fun z : Space n × ℝ => fderiv ℝ (fun y => f y z.2) z.1) p :=
      hh.fderiv contDiffAt_fst (by simp)
    exact hd.clm_apply contDiffAt_const

theorem checked (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_H006 : ∀ (s t : ℝ), 0 < s → s < t → ∃ C : Set (Space n), IsCompact C ∧ ∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc s t → u x r = q) : yui_aux_type% "∀ r : ℝ, 0 < r →\nContinuous (fun x => density u x r) ∧\nContinuous (fun x => densityT u x r) ∧\nContinuous (fun x => inner ℝ (dt u x r) (dtt u x r)) ∧\n∀ j : Fin n, Continuous (flux u j r) ∧\nContinuous (fun x => inner ℝ (dut u j x r) (du u j x r)) ∧\nContinuous (fun x => inner ℝ (dt u x r) (duu u j x r)) ∧\nContinuous (fun x => dx (flux u j r) j x)" := by
  have ht : ContDiffOn ℝ ∞ (Function.uncurry (dt u)) (timeDomain n) :=
    (yui_aux_0001 n m u q h_H001 h_H002 h_H006 u h_H002).1
  have htt : ContDiffOn ℝ ∞ (Function.uncurry (dtt u)) (timeDomain n) :=
    (yui_aux_0001 n m u q h_H001 h_H002 h_H006 (dt u) ht).1
  have hx (j : Fin n) : ContDiffOn ℝ ∞ (Function.uncurry (du u j)) (timeDomain n) :=
    (yui_aux_0001 n m u q h_H001 h_H002 h_H006 u h_H002).2 j
  have hxt (j : Fin n) : ContDiffOn ℝ ∞ (Function.uncurry (dut u j)) (timeDomain n) :=
    (yui_aux_0001 n m u q h_H001 h_H002 h_H006 (dt u) ht).2 j
  have hxx (j : Fin n) : ContDiffOn ℝ ∞ (Function.uncurry (duu u j)) (timeDomain n) :=
    (yui_aux_0001 n m u q h_H001 h_H002 h_H006 (du u j) (hx j)).2 j
  have he : ContDiffOn ℝ ∞ (Function.uncurry (density u)) (timeDomain n) := by
    unfold density Function.uncurry
    simpa only [real_inner_self_eq_norm_sq] using
      (ht.inner ℝ ht).add (contDiffOn_sum (fun j _ => (hx j).inner ℝ (hx j)))
  have het : ContDiffOn ℝ ∞ (Function.uncurry (densityT u)) (timeDomain n) :=
    (yui_aux_0001 n m u q h_H001 h_H002 h_H006 (density u) he).1
  have hf (j : Fin n) : ContDiffOn ℝ ∞ (fun p : Space n × ℝ => flux u j p.2 p.1) (timeDomain n) :=
    ht.inner ℝ (hx j)
  have hfx (j : Fin n) : ContDiffOn ℝ ∞ (fun p : Space n × ℝ => dx (flux u j p.2) j p.1) (timeDomain n) :=
    (yui_aux_0001 n m u q h_H001 h_H002 h_H006 (fun x t => flux u j t x) (hf j)).2 j
  intro r hr
  have sec (f : Space n × ℝ → ℝ) (h : ContDiffOn ℝ ∞ f (timeDomain n)) :
      Continuous (fun x => f (x,r)) :=
    h.continuousOn.comp_continuous (continuous_id.prodMk continuous_const) (fun x => hr)
  refine ⟨sec _ he, sec _ het, sec _ (ht.inner ℝ htt), ?_⟩
  intro j
  exact ⟨sec _ (hf j), sec _ ((hxt j).inner ℝ (hx j)),
    sec _ (ht.inner ℝ (hxx j)), sec _ (hfx j)⟩
#check @checked
#print axioms checked
end YuiAuxiliary
