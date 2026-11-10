import Mathlib

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace WaveMap

abbrev X (n : ℕ) := Fin n → ℝ
abbrev V (m : ℕ) := EuclideanSpace ℝ (Fin m)

def domain (n : ℕ) : Set (X n × ℝ) := {p | 0 < p.2}
def box (n : ℕ) (R : ℝ) : Set (X n) :=
  Set.pi Set.univ (fun _ => Set.Icc (-R) R)
def openBox (n : ℕ) (R : ℝ) : Set (X n) :=
  Set.pi Set.univ (fun _ => Set.Ioo (-R) R)
def slab (t : ℝ) : Set ℝ := Set.Icc (t / 2) (3 * t / 2)

noncomputable def dt {n m : ℕ} (u : X n × ℝ → V m) : X n × ℝ → V m :=
  fun p => deriv (fun r : ℝ => u (p.1, r)) p.2
noncomputable def dx {n m : ℕ} (u : X n × ℝ → V m) (j : Fin n) :
    X n × ℝ → V m :=
  fun p => fderiv ℝ (fun x : X n => u (x, p.2)) p.1 (Pi.single j 1)
noncomputable def lap {n m : ℕ} (u : X n × ℝ → V m) : X n × ℝ → V m :=
  fun p => ∑ j : Fin n, dx (dx u j) j p
noncomputable def density {n m : ℕ} (u : X n × ℝ → V m) :
    X n × ℝ → ℝ :=
  fun p => ‖dt u p‖ ^ 2 + ∑ j : Fin n, ‖dx u j p‖ ^ 2
noncomputable def densityT {n m : ℕ} (u : X n × ℝ → V m) :
    X n × ℝ → ℝ :=
  fun p => deriv (fun r : ℝ => density u (p.1, r)) p.2
noncomputable def energy {n m : ℕ} (u : X n × ℝ → V m) (t : ℝ) : ℝ :=
  ∫ x : X n, density u (x, t)
noncomputable def timeProduct {n m : ℕ} (u : X n × ℝ → V m) :
    X n × ℝ → ℝ :=
  fun p => inner ℝ (dt u p) (dt (dt u) p)
noncomputable def mixedProduct {n m : ℕ} (u : X n × ℝ → V m) (j : Fin n) :
    X n × ℝ → ℝ :=
  fun p => inner ℝ (dx u j p) (dx (dt u) j p)
noncomputable def lapProduct {n m : ℕ} (u : X n × ℝ → V m) (j : Fin n) :
    X n × ℝ → ℝ :=
  fun p => inner ℝ (dt u p) (dx (dx u j) j p)
noncomputable def flux {n m : ℕ} (u : X n × ℝ → V m) (j : Fin n) :
    X n × ℝ → ℝ :=
  fun p => inner ℝ (dt u p) (dx u j p)
noncomputable def fluxDx {n m : ℕ} (u : X n × ℝ → V m) (j : Fin n) :
    X n × ℝ → ℝ :=
  fun p => fderiv ℝ (fun x : X n => flux u j (x, p.2)) p.1 (Pi.single j 1)

def sectionGood {n : ℕ} (C : Set (X n)) (R : ℝ) (f : X n → ℝ) : Prop :=
  Continuous f ∧ (∀ x, x ∉ C → f x = 0) ∧
  (∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ box n R, |f x| ≤ B) ∧ Integrable f

def supportGeometry {n m : ℕ} (u : X n × ℝ → V m) (q : V m)
    (t : ℝ) (C : Set (X n)) (R : ℝ) : Prop :=
  IsCompact C ∧ 0 < R ∧ C ⊆ openBox n R ∧
  (∀ x, x ∉ C → ∀ r ∈ slab t, u (x, r) = q) ∧
  volume (box n R) = ENNReal.ofReal ((2 * R) ^ n) ∧
  volume (box n R) < ⊤ ∧
  (∀ k : ℕ, ∀ x, x ∉ C → ∀ r ∈ interior (slab t),
    iteratedFDeriv ℝ (k + 1) u (x, r) = 0)

def supportSections {n m : ℕ} (u : X n × ℝ → V m)
    (t : ℝ) (C : Set (X n)) (R : ℝ) : Prop :=
  ∀ r ∈ interior (slab t),
    sectionGood C R (fun x => density u (x, r)) ∧
    sectionGood C R (fun x => densityT u (x, r)) ∧
    sectionGood C R (fun x => timeProduct u (x, r)) ∧
    (∀ j : Fin n,
      sectionGood C R (fun x => mixedProduct u j (x, r)) ∧
      sectionGood C R (fun x => lapProduct u j (x, r)) ∧
      sectionGood C R (fun x => fluxDx u j (x, r)))

noncomputable def quotient {n m : ℕ} (u : X n × ℝ → V m)
    (t h : ℝ) (x : X n) : ℝ :=
  (density u (x, t + h) - density u (x, t)) / h

abbrev Other {n : ℕ} (j : Fin n) := {i : Fin n // i ≠ j}
def insertCoord {n : ℕ} (j : Fin n) (y : Other j → ℝ) (z : ℝ) : X n :=
  fun i => if h : i = j then z else y ⟨i, h⟩
def otherBox {n : ℕ} (j : Fin n) (R : ℝ) : Set (Other j → ℝ) :=
  Set.pi Set.univ (fun _ => Set.Icc (-R) R)

end WaveMap

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem yui_aux_0001 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_H004 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t → ‖u (x, t)‖ = 1) (h_H005 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t → ∃ a : ℝ, WaveMap.dt (WaveMap.dt u) (x, t) - WaveMap.lap u (x, t) = a • u (x, t)) (h_T001 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t → inner ℝ (u (x, t)) (WaveMap.dt u (x, t)) = 0 ∧ inner ℝ (WaveMap.dt u (x, t)) (WaveMap.dt (WaveMap.dt u) (x, t) - WaveMap.lap u (x, t)) = 0) : yui_aux_type% "∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (x v : E) (c : ℝ), (fderiv ℝ (fun _ : E => c) x) v = 0" := by
  intro E _ _ x v c
  simp

theorem yui_aux_0002 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_H004 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t → ‖u (x, t)‖ = 1) (h_H005 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t → ∃ a : ℝ, WaveMap.dt (WaveMap.dt u) (x, t) - WaveMap.lap u (x, t) = a • u (x, t)) (h_T001 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t → inner ℝ (u (x, t)) (WaveMap.dt u (x, t)) = 0 ∧ inner ℝ (WaveMap.dt u (x, t)) (WaveMap.dt (WaveMap.dt u) (x, t) - WaveMap.lap u (x, t)) = 0) : yui_aux_type% "∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → WaveMap.V m) (s : Set E), IsOpen s → ContDiffOn ℝ 2 f s → (∀ y ∈ s, ‖f y‖ = 1) → ∀ x ∈ s, ∀ v : E, inner ℝ (f x) (fderiv ℝ (fun y => fderiv ℝ f y v) x v) = - ‖fderiv ℝ f x v‖ ^ 2" := by
  intro E _ _ f s hs hf hn
  have hd (y : E) (hy : y ∈ s) : DifferentiableAt ℝ f y :=
    (hf.contDiffAt (hs.mem_nhds hy)).differentiableAt (by norm_num)
  have hfirst (y : E) (hy : y ∈ s) (v : E) :
      inner ℝ (f y) (fderiv ℝ f y v) = 0 := by
    have he : (fun z => inner ℝ (f z) (f z)) =ᶠ[𝓝 y] (fun _ => (1 : ℝ)) := by
      filter_upwards [hs.mem_nhds hy] with z hz
      rw [real_inner_self_eq_norm_sq, hn z hz]
      norm_num
    have hh := congrArg (fun L : E →L[ℝ] ℝ => L v) (he.fderiv_eq (𝕜 := ℝ))
    rw [fderiv_inner_apply ℝ (hd y hy) (hd y hy),
      yui_aux_0001 n m u q h_H001 h_H002 h_H004 h_H005 h_T001 E y v 1] at hh
    have hc : inner ℝ (f y) (fderiv ℝ f y v) = inner ℝ (fderiv ℝ f y v) (f y) := real_inner_comm _ _
    linarith
  intro x hx v
  have hg : ContDiffOn ℝ 1 (fun y => fderiv ℝ f y v) s :=
    (hf.fderiv_of_isOpen hs (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply contDiffOn_const
  have he : (fun y => inner ℝ (f y) (fderiv ℝ f y v)) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [hs.mem_nhds hx] with y hy using hfirst y hy v
  have hh := congrArg (fun L : E →L[ℝ] ℝ => L v) (he.fderiv_eq (𝕜 := ℝ))
  rw [fderiv_inner_apply ℝ (hd x hx) ((hg.contDiffAt (hs.mem_nhds hx)).differentiableAt (by norm_num)),
    yui_aux_0001 n m u q h_H001 h_H002 h_H004 h_H005 h_T001 E x v 0,
    real_inner_self_eq_norm_sq] at hh
  linarith

theorem checked (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_H004 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t → ‖u (x, t)‖ = 1) (h_H005 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t → ∃ a : ℝ, WaveMap.dt (WaveMap.dt u) (x, t) - WaveMap.lap u (x, t) = a • u (x, t)) (h_T001 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t → inner ℝ (u (x, t)) (WaveMap.dt u (x, t)) = 0 ∧ inner ℝ (WaveMap.dt u (x, t)) (WaveMap.dt (WaveMap.dt u) (x, t) - WaveMap.lap u (x, t)) = 0) : yui_aux_type% "(2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)" := by
  change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
  exact WithTop.coe_le_coe.mpr le_top
#check @checked
#print axioms checked
end YuiAuxiliary
