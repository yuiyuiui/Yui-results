import Mathlib
open scoped ContDiff Topology BigOperators
open Set MeasureTheory
noncomputable section
namespace WaveMap
abbrev V (n : ℕ) := Fin n → ℝ
abbrev W (m : ℕ) := EuclideanSpace ℝ (Fin m)
def domain (n : ℕ) : Set (V n × ℝ) := {p | 0 < p.2}
def box (n : ℕ) (R : ℝ) : Set (V n) := Set.Icc (fun _ => -R) (fun _ => R)
def innerBox (n : ℕ) (R : ℝ) : Set (V n) := {x | ∀ j, -R < x j ∧ x j < R}
def ut {n m : ℕ} (u : V n × ℝ → W m) (x : V n) (t : ℝ) : W m :=
  deriv (fun s => u (x,s)) t
def utt {n m : ℕ} (u : V n × ℝ → W m) (x : V n) (t : ℝ) : W m :=
  deriv (fun s => ut u x s) t
def ux {n m : ℕ} (u : V n × ℝ → W m) (j : Fin n) (x : V n) (t : ℝ) : W m :=
  fderiv ℝ (fun y => u (y,t)) x (Pi.single j 1)
def uxx {n m : ℕ} (u : V n × ℝ → W m) (j : Fin n) (x : V n) (t : ℝ) : W m :=
  fderiv ℝ (fun y => ux u j y t) x (Pi.single j 1)
def uxt {n m : ℕ} (u : V n × ℝ → W m) (j : Fin n) (x : V n) (t : ℝ) : W m :=
  fderiv ℝ (fun y => ut u y t) x (Pi.single j 1)
def lap {n m : ℕ} (u : V n × ℝ → W m) (x : V n) (t : ℝ) : W m :=
  ∑ j, uxx u j x t
def e {n m : ℕ} (u : V n × ℝ → W m) (x : V n) (t : ℝ) : ℝ :=
  ‖ut u x t‖ ^ 2 + ∑ j, ‖ux u j x t‖ ^ 2
def et {n m : ℕ} (u : V n × ℝ → W m) (x : V n) (t : ℝ) : ℝ :=
  deriv (fun s => e u x s) t
def A {n m : ℕ} (u : V n × ℝ → W m) (x : V n) (t : ℝ) : ℝ :=
  inner ℝ (ut u x t) (utt u x t)
def B {n m : ℕ} (u : V n × ℝ → W m) (j : Fin n) (x : V n) (t : ℝ) : ℝ :=
  inner ℝ (ux u j x t) (uxt u j x t)
def T {n m : ℕ} (u : V n × ℝ → W m) (j : Fin n) (x : V n) (t : ℝ) : ℝ :=
  inner ℝ (ut u x t) (uxx u j x t)
def g {n m : ℕ} (u : V n × ℝ → W m) (j : Fin n) (x : V n) (t : ℝ) : ℝ :=
  inner ℝ (ut u x t) (ux u j x t)
def dg {n m : ℕ} (u : V n × ℝ → W m) (j : Fin n) (x : V n) (t : ℝ) : ℝ :=
  fderiv ℝ (fun y => g u j y t) x (Pi.single j 1)
def energy {n m : ℕ} (u : V n × ℝ → W m) (t : ℝ) : ℝ :=
  ∫ x, e u x t
def fields {n m : ℕ} (u : V n × ℝ → W m) : Set ((V n × ℝ) → ℝ) :=
  {f | f = (fun p => e u p.1 p.2) ∨ f = (fun p => et u p.1 p.2) ∨
    f = (fun p => A u p.1 p.2) ∨
    (∃ j, f = (fun p => B u j p.1 p.2)) ∨
    (∃ j, f = (fun p => T u j p.1 p.2)) ∨
    (∃ j, f = (fun p => g u j p.1 p.2)) ∨
    (∃ j, f = (fun p => dg u j p.1 p.2))}
end WaveMap
open WaveMap

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem checked (n : ℕ) (m : ℕ) (u : V n × ℝ → W m) (q : W m) (h_T002 : ∀ t0 : ℝ, 0 < t0 → ∃ C : Set (V n), ∃ R : ℝ,
IsCompact C ∧ 0 < R ∧ C ⊆ innerBox n R ∧ C ⊆ interior (box n R) ∧
IsCompact (box n R) ∧ MeasurableSet (box n R) ∧
volume (box n R) = ENNReal.ofReal ((2*R)^n) ∧ volume (box n R) < ⊤ ∧
(∀ x, x ∉ C → ∀ r ∈ Set.Icc (t0/2) (3*t0/2), u (x,r) = q) ∧
(∀ k : ℕ, 0 < k → ∀ x, x ∉ C → ∀ r ∈ Set.Ioo (t0/2) (3*t0/2),
iteratedFDeriv ℝ k u (x,r) = 0)) (h_H002 : ContDiffOn ℝ ∞ u (domain n)) : yui_aux_type% "∀ (C Q : Set (V n)) (f : V n → ℝ), IsCompact C → C ⊆ interior Q →\nIsCompact Q → volume Q < ⊤ → Continuous f → (∀ x, x ∉ C → f x = 0) →\nHasCompactSupport f ∧ Integrable f ∧\n(∃ K : ℝ, 0 ≤ K ∧ (∀ x ∈ Q, |f x| ≤ K) ∧ (∫ x, |f x|) ≤ K * (volume Q).toReal) ∧\n(∃ U : Set (V n), IsOpen U ∧ frontier Q ⊆ U ∧ ∀ x ∈ U, f x = 0)" := by
  intro C Q f hC hCQ hQ hvol hf hz
  have hs : Function.support f ⊆ C := by
    intro x hx
    by_contra h
    exact hx (hz x h)
  have hc : HasCompactSupport f := HasCompactSupport.of_support_subset_isCompact hC hs
  refine ⟨hc, hf.integrable_of_hasCompactSupport hc, ?_, ?_⟩
  · obtain ⟨K, hK⟩ := hQ.exists_bound_of_continuousOn hf.continuousOn
    refine ⟨max K 0, le_max_right _ _, ?_, ?_⟩
    · intro x hx
      exact (show |f x| ≤ K by simpa [Real.norm_eq_abs] using hK x hx).trans (le_max_left _ _)
    · have hzQ : ∀ x, x ∉ Q → |f x| = 0 := by
        intro x hx
        rw [hz x (fun h => hx (interior_subset (hCQ h))), abs_zero]
      have hbound : ∀ x ∈ Q, ‖|f x|‖ ≤ max K 0 := by
        intro x hx
        simpa [Real.norm_eq_abs, abs_abs] using (hK x hx).trans (le_max_left K 0)
      have hb := norm_setIntegral_le_of_norm_le_const (μ := volume) hvol hbound
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzQ] at hb
      have hb' : |∫ x, |f x|| ≤ max K 0 * (volume Q).toReal := by
        simpa only [Real.norm_eq_abs, measureReal_def] using hb
      exact (le_abs_self _).trans hb'
  · refine ⟨Cᶜ, hC.isClosed.isOpen_compl, ?_, fun x hx => hz x hx⟩
    intro x hx hxC
    exact hx.2 (hCQ hxC)
#check @checked
#print axioms checked
end YuiAuxiliary
