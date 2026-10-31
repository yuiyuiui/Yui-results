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
theorem checked (n : ℕ) (m : ℕ) (u : V n × ℝ → W m) (q : W m) (h_H002 : ContDiffOn ℝ ∞ u (domain n)) : yui_aux_type% "∀ x t, 0 < t → ∀ j : Fin n, deriv (fun s => ux u j x s) t = uxt u j x t" := by
  classical
  have ho : IsOpen (domain n) := isOpen_lt continuous_const continuous_snd
  have hd : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
      (f : V n × ℝ → F), ContDiffOn ℝ ∞ f (domain n) →
      ∀ p ∈ domain n, DifferentiableAt ℝ f p := by
    intro F _ _ f hf p hp
    exact (hf.contDiffAt (ho.mem_nhds hp)).differentiableAt (by simp)
  have bridge : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
      (f : V n × ℝ → F) (x : V n) (t : ℝ), DifferentiableAt ℝ f (x,t) →
      (deriv (fun s => f (x,s)) t = fderiv ℝ f (x,t) (0,1)) ∧
      (∀ v : V n, fderiv ℝ (fun y => f (y,t)) x v = fderiv ℝ f (x,t) (v,0)) := by
    intro F _ _ f x t hf
    constructor
    · exact (hf.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_const t x).prodMk (hasDerivAt_id t))).deriv
    · intro v
      have hi : HasFDerivAt (fun y : V n => (y,t)) ((ContinuousLinearMap.id ℝ (V n)).prod (0 : V n →L[ℝ] ℝ)) x := (hasFDerivAt_id x).prodMk (hasFDerivAt_const t x)
      have h := hf.hasFDerivAt.comp x hi
      exact congrArg (fun L : V n →L[ℝ] F => L v) h.fderiv
  have dt : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
      (f : V n × ℝ → F), ContDiffOn ℝ ∞ f (domain n) →
      ContDiffOn ℝ ∞ (fun p : V n × ℝ => deriv (fun s => f (p.1,s)) p.2) (domain n) := by
    intro F _ _ f hf
    have hf' : ContDiffOn ℝ ∞ (fderiv ℝ f) (domain n) :=
      hf.fderiv_of_isOpen ho (by simp)
    apply (hf'.clm_apply (contDiffOn_const (c := ((0 : V n), (1 : ℝ))))).congr
    intro p hp
    exact (bridge f p.1 p.2 (hd f hf p hp)).1
  have dx : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
      (f : V n × ℝ → F), ContDiffOn ℝ ∞ f (domain n) →
      ∀ v : V n, ContDiffOn ℝ ∞
        (fun p : V n × ℝ => fderiv ℝ (fun y => f (y,p.2)) p.1 v) (domain n) := by
    intro F _ _ f hf v
    have hf' : ContDiffOn ℝ ∞ (fderiv ℝ f) (domain n) :=
      hf.fderiv_of_isOpen ho (by simp)
    apply (hf'.clm_apply (contDiffOn_const (c := (v,(0 : ℝ))))).congr
    intro p hp
    exact (bridge f p.1 p.2 (hd f hf p hp)).2 v
  have hut : ContDiffOn ℝ ∞ (fun p : V n × ℝ => ut u p.1 p.2) (domain n) :=
    dt u h_H002
  have hux : ∀ j, ContDiffOn ℝ ∞ (fun p : V n × ℝ => ux u j p.1 p.2) (domain n) :=
    fun j => dx u h_H002 (Pi.single j 1)
  have hutt : ContDiffOn ℝ ∞ (fun p : V n × ℝ => utt u p.1 p.2) (domain n) :=
    dt _ hut
  have huxx : ∀ j, ContDiffOn ℝ ∞ (fun p : V n × ℝ => uxx u j p.1 p.2) (domain n) :=
    fun j => dx _ (hux j) (Pi.single j 1)
  have huxt : ∀ j, ContDiffOn ℝ ∞ (fun p : V n × ℝ => uxt u j p.1 p.2) (domain n) :=
    fun j => dx _ hut (Pi.single j 1)
  have he : ContDiffOn ℝ ∞ (fun p : V n × ℝ => e u p.1 p.2) (domain n) :=
    (hut.norm_sq (𝕜 := ℝ)).add (ContDiffOn.sum (fun j _ => (hux j).norm_sq (𝕜 := ℝ)))
  have hg : ∀ j, ContDiffOn ℝ ∞ (fun p : V n × ℝ => g u j p.1 p.2) (domain n) :=
    fun j => hut.inner ℝ (hux j)
  have hmix : ∀ x t, 0 < t → ∀ j : Fin n,
      deriv (fun s => ux u j x s) t = uxt u j x t := by
    intro x t ht j
    have hp : (x,t) ∈ domain n := ht
    have hdf : ContDiffOn ℝ ∞ (fderiv ℝ u) (domain n) :=
      h_H002.fderiv_of_isOpen ho (by simp)
    have dcoord : ∀ v w : V n × ℝ,
        fderiv ℝ (fun p => fderiv ℝ u p v) (x,t) w =
        fderiv ℝ (fderiv ℝ u) (x,t) w v := by
      intro v w
      have hh := (hd _ hdf (x,t) hp).hasFDerivAt.clm_apply (hasFDerivAt_const v (x,t))
      simpa using congrArg (fun L : (V n × ℝ) →L[ℝ] W m => L w) hh.fderiv
    have eut : (fun p : V n × ℝ => ut u p.1 p.2) =ᶠ[𝓝 (x,t)]
        (fun p => fderiv ℝ u p (0,1)) := by
      filter_upwards [ho.mem_nhds hp] with p h
      exact (bridge u p.1 p.2 (hd u h_H002 p h)).1
    have eux : (fun p : V n × ℝ => ux u j p.1 p.2) =ᶠ[𝓝 (x,t)]
        (fun p => fderiv ℝ u p (Pi.single j 1,0)) := by
      filter_upwards [ho.mem_nhds hp] with p h
      exact (bridge u p.1 p.2 (hd u h_H002 p h)).2 (Pi.single j 1)
    have htux := (bridge _ x t (hd _ (hux j) (x,t) hp)).1
    have hxut := (bridge _ x t (hd _ hut (x,t) hp)).2 (Pi.single j 1)
    change deriv (fun s => ux u j x s) t =
      fderiv ℝ (fun y => ut u y t) x (Pi.single j 1)
    rw [htux, hxut, eux.fderiv_eq, eut.fderiv_eq, dcoord, dcoord]
    exact (h_H002.contDiffAt (ho.mem_nhds hp)).isSymmSndFDerivAt (by simp)
      (0,1) (Pi.single j 1,0)
  exact hmix
#check @checked
#print axioms checked
end YuiAuxiliary
