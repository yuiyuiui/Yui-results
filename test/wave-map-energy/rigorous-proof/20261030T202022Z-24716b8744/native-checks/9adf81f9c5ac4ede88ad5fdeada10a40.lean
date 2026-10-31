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
iteratedFDeriv ℝ k u (x,r) = 0)) (h_H002 : ContDiffOn ℝ ∞ u (domain n)) : yui_aux_type% "∀ (C : Set (V n)) (a b : ℝ), IsClosed C → (∀ x, x ∉ C → ∀ r ∈ Set.Icc a b, u (x,r) = q) → ∀ f ∈ fields u, ∀ r ∈ Set.Ioo a b, ∀ x, x ∉ C → f (x,r) = 0" := by
  intro C a b hC hu
  have hut (x : V n) (hx : x ∉ C) (r : ℝ) (hr : r ∈ Ioo a b) : ut u x r = 0 := by
    have he : (fun s => u (x,s)) =ᶠ[𝓝 r] (fun _ => q) :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hr) (fun s hs => hu x hx s ⟨hs.1.le, hs.2.le⟩)
    simpa [ut] using he.deriv_eq
  have hux (j : Fin n) (x : V n) (hx : x ∉ C) (r : ℝ) (hr : r ∈ Ioo a b) : ux u j x r = 0 := by
    have he : (fun y => u (y,r)) =ᶠ[𝓝 x] (fun _ => q) :=
      Filter.eventually_of_mem (hC.isOpen_compl.mem_nhds hx) (fun y hy => hu y hy r ⟨hr.1.le, hr.2.le⟩)
    have hh := congrArg (fun L : V n →L[ℝ] W m => L (Pi.single j 1)) (he.fderiv_eq (𝕜 := ℝ))
    simpa [ux] using hh
  have he (x : V n) (hx : x ∉ C) (r : ℝ) (hr : r ∈ Ioo a b) : e u x r = 0 := by
    simp [e, hut x hx r hr, hux _ x hx r hr]
  have hg (j : Fin n) (x : V n) (hx : x ∉ C) (r : ℝ) (hr : r ∈ Ioo a b) : g u j x r = 0 := by
    simp [g, hut x hx r hr]
  intro f hf r hr x hx
  rcases hf with hf | hf | hf | ⟨j,hf⟩ | ⟨j,hf⟩ | ⟨j,hf⟩ | ⟨j,hf⟩
  · subst f; exact he x hx r hr
  · subst f
    have hh : (fun s => e u x s) =ᶠ[𝓝 r] (fun _ => (0 : ℝ)) :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hr) (fun s hs => he x hx s hs)
    simpa [et] using hh.deriv_eq
  · subst f; simp [A, hut x hx r hr]
  · subst f; simp [B, hux j x hx r hr]
  · subst f; simp [T, hut x hx r hr]
  · subst f; exact hg j x hx r hr
  · subst f
    have hh : (fun y => g u j y r) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) :=
      Filter.eventually_of_mem (hC.isOpen_compl.mem_nhds hx) (fun y hy => hg j y hy r hr)
    have hh' := congrArg (fun L : V n →L[ℝ] ℝ => L (Pi.single j 1)) (hh.fderiv_eq (𝕜 := ℝ))
    simpa [dg] using hh'
#check @checked
#print axioms checked
end YuiAuxiliary
