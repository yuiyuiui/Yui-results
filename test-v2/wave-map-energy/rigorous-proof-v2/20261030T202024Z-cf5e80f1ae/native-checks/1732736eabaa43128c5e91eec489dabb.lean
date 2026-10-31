import Mathlib
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
namespace WaveEnergy
abbrev X (n : ℕ) := Fin n → ℝ
abbrev V (m : ℕ) := EuclideanSpace ℝ (Fin m)
def domain (n : ℕ) : Set (X n × ℝ) := {p | 0 < p.2}
noncomputable def mu (n : ℕ) : Measure (X n) := Measure.pi (fun _ : Fin n => (volume : Measure ℝ))
noncomputable def dt {n : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : X n × ℝ → F) (p : X n × ℝ) : F := deriv (fun r : ℝ => f (p.1, r)) p.2
noncomputable def dx {n : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : X n × ℝ → F) (j : Fin n) (p : X n × ℝ) : F :=
  fderiv ℝ (fun y : X n => f (y, p.2)) p.1 (Pi.single j 1)
noncomputable def lap {n m : ℕ} (u : X n × ℝ → V m) (p : X n × ℝ) : V m :=
  ∑ j : Fin n, dx (dx u j) j p
noncomputable def density {n m : ℕ} (u : X n × ℝ → V m) (p : X n × ℝ) : ℝ :=
  ‖dt u p‖ ^ 2 + ∑ j : Fin n, ‖dx u j p‖ ^ 2
noncomputable def energy {n m : ℕ} (u : X n × ℝ → V m) (t : ℝ) : ℝ :=
  ∫ x : X n, density u (x, t) ∂mu n
noncomputable def kinetic {n m : ℕ} (u : X n × ℝ → V m) (p : X n × ℝ) : ℝ :=
  inner ℝ (dt u p) (dt (dt u) p)
noncomputable def mixed {n m : ℕ} (u : X n × ℝ → V m) (j : Fin n) (p : X n × ℝ) : ℝ :=
  inner ℝ (dx u j p) (dx (dt u) j p)
noncomputable def lapTerm {n m : ℕ} (u : X n × ℝ → V m) (j : Fin n) (p : X n × ℝ) : ℝ :=
  inner ℝ (dt u p) (dx (dx u j) j p)
noncomputable def flux {n m : ℕ} (u : X n × ℝ → V m) (j : Fin n) (p : X n × ℝ) : ℝ :=
  inner ℝ (dt u p) (dx u j p)
def box {n : ℕ} (R : ℝ) : Set (X n) := {x | ∀ j, x j ∈ Icc (-R) R}
def scalarTerms {n m : ℕ} (u : X n × ℝ → V m) : Set (X n × ℝ → ℝ) :=
  {f | f = density u ∨ f = dt (density u) ∨ f = kinetic u ∨
    ∃ j : Fin n, f = mixed u j ∨ f = lapTerm u j ∨ f = flux u j ∨ f = dx (flux u j) j}
structure Window {n m : ℕ} (u : X n × ℝ → V m) (q : V m)
    (t0 : ℝ) (C : Set (X n)) (R : ℝ) : Prop where
  compact : IsCompact C
  radius_pos : 0 < R
  inside : ∀ x ∈ C, ∀ j : Fin n, x j ∈ Ioo (-R) R
  constant : ∀ x, x ∉ C → ∀ r ∈ Icc (t0 / 2) (3 * t0 / 2), u (x, r) = q
  box_volume : mu n (box R) = ENNReal.ofReal ((2 * R) ^ n)
  box_finite : mu n (box R) < ⊤
  derivatives_zero : ∀ k : ℕ, 0 < k → ∀ x, x ∉ C →
    ∀ r ∈ Ioo (t0 / 2) (3 * t0 / 2), iteratedFDeriv ℝ k u (x, r) = 0
  sections : ∀ f ∈ scalarTerms u, ∀ r ∈ Ioo (t0 / 2) (3 * t0 / 2),
    Continuous (fun x => f (x, r)) ∧ (∀ x, x ∉ C → f (x, r) = 0) ∧
    Integrable (fun x => f (x, r)) (mu n)
  uniform : ∀ f ∈ scalarTerms u, ∀ a b : ℝ,
    Icc a b ⊆ Ioo (t0 / 2) (3 * t0 / 2) →
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ box R, ∀ r ∈ Icc a b, |f (x, r)| ≤ B
abbrev Other (n : ℕ) (j : Fin n) := {i : Fin n // i ≠ j} → ℝ
noncomputable def otherMu {n : ℕ} (j : Fin n) : Measure (Other n j) :=
  Measure.pi (fun _ : {i : Fin n // i ≠ j} => (volume : Measure ℝ))
def otherBox {n : ℕ} (j : Fin n) (R : ℝ) : Set (Other n j) :=
  {y | ∀ i, y i ∈ Icc (-R) R}
def insert {n : ℕ} (j : Fin n) (p : Other n j × ℝ) : X n :=
  fun i => if h : i = j then p.2 else p.1 ⟨i,h⟩
end WaveEnergy
open WaveEnergy

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem checked (n : ℕ) (m : ℕ) (u : X n × ℝ → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ u (domain n)) (h_H003 : ‖q‖ = 1) (h_H006 : ∀ s t : ℝ, 0 < s → s < t → ∃ C : Set (X n), IsCompact C ∧ ∀ x : X n, x ∉ C → ∀ r : ℝ, r ∈ Icc s t → u (x,r) = q) (h_T003 : ∀ t0 : ℝ, 0 < t0 →
  ∃ C : Set (X n), ∃ R : ℝ, IsCompact C ∧ 0 < R ∧
    (∀ x ∈ C, ∀ j : Fin n, x j ∈ Ioo (-R) R) ∧
    (∀ x, x ∉ C → ∀ r ∈ Icc (t0/2) (3*t0/2), u (x,r) = q)) : yui_aux_type% "∀ f ∈ scalarTerms u, ContDiffOn ℝ ∞ f (domain n)" := by
  classical
  have hop : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : X n × ℝ → F),
      ContDiffOn ℝ ∞ f (domain n) → ContDiffOn ℝ ∞ (dt f) (domain n) ∧
      ∀ j, ContDiffOn ℝ ∞ (dx f j) (domain n) := by
    intro F _ _ f hf
    have ho : IsOpen (domain n) := isOpen_lt continuous_const continuous_snd
    constructor
    · intro p hp
      have hf' : ContDiffAt ℝ ∞ (fun z : (X n × ℝ) × ℝ => f (z.1.1, z.2)) (p, p.2) :=
        (hf.contDiffAt (ho.mem_nhds hp)).comp _ (contDiffAt_fst.fst.prodMk contDiffAt_snd)
      have hh : ContDiffAt ℝ ∞ (fun p : X n × ℝ => fderiv ℝ (fun r : ℝ => f (p.1,r)) p.2) p :=
        hf'.fderiv contDiffAt_snd (by simp)
      have he : (fun p : X n × ℝ => (fderiv ℝ (fun r : ℝ => f (p.1,r)) p.2) 1) = dt f := by
        funext p
        exact fderiv_apply_one_eq_deriv
      rw [← he]
      exact (hh.clm_apply contDiffAt_const).contDiffWithinAt
    · intro j p hp
      have hf' : ContDiffAt ℝ ∞ (fun z : (X n × ℝ) × X n => f (z.2, z.1.2)) (p, p.1) :=
        (hf.contDiffAt (ho.mem_nhds hp)).comp _ (contDiffAt_snd.prodMk contDiffAt_fst.snd)
      exact ((hf'.fderiv contDiffAt_fst (by simp)).clm_apply contDiffAt_const).contDiffWithinAt
  have ht := (hop u h_H002).1
  have hx := (hop u h_H002).2
  have htt := (hop (dt u) ht).1
  have hxt := (hop (dt u) ht).2
  have hxx := fun j => (hop (dx u j) (hx j)).2 j
  have he : ContDiffOn ℝ ∞ (density u) (domain n) := by
    exact (ht.norm_sq ℝ).add (ContDiffOn.sum (fun j _ => (hx j).norm_sq ℝ))
  have het := (hop (density u) he).1
  have hk : ContDiffOn ℝ ∞ (kinetic u) (domain n) := ht.inner htt
  have hm : ∀ j, ContDiffOn ℝ ∞ (mixed u j) (domain n) := fun j => (hx j).inner (hxt j)
  have hl : ∀ j, ContDiffOn ℝ ∞ (lapTerm u j) (domain n) := fun j => ht.inner (hxx j)
  have hf : ∀ j, ContDiffOn ℝ ∞ (flux u j) (domain n) := fun j => ht.inner (hx j)
  have hdf : ∀ j, ContDiffOn ℝ ∞ (dx (flux u j) j) (domain n) := fun j => (hop _ (hf j)).2 j
  intro f h
  rcases h with rfl | rfl | rfl | ⟨j, rfl | rfl | rfl | rfl⟩
  · exact he
  · exact het
  · exact hk
  · exact hm j
  · exact hl j
  · exact hf j
  · exact hdf j
#check @checked
#print axioms checked
end YuiAuxiliary
