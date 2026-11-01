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
theorem yui_aux_0001 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_T003 : ∀ t : ℝ, 0 < t → ∃ C : Set (WaveMap.X n), ∃ R : ℝ, WaveMap.supportGeometry u q t C R) : yui_aux_type% "∀ (F : Type) (inst : NormedAddCommGroup F) (inst' : NormedSpace ℝ F) (f : WaveMap.X n × ℝ → F), ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (WaveMap.domain n) → (ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : WaveMap.X n × ℝ => deriv (fun r : ℝ => f (p.1, r)) p.2) (WaveMap.domain n)) ∧ (∀ j : Fin n, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : WaveMap.X n × ℝ => fderiv ℝ (fun x : WaveMap.X n => f (x, p.2)) p.1 (Pi.single j 1)) (WaveMap.domain n))" := by
  intro F inst inst' f hf
  have ho : IsOpen (WaveMap.domain n) := isOpen_lt continuous_const continuous_snd
  have hd := (contDiffOn_infty_iff_fderiv_of_isOpen ho).mp hf
  have hD (v : WaveMap.X n × ℝ) : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p => fderiv ℝ f p v) (WaveMap.domain n) :=
    hd.2.clm_apply contDiffOn_const
  constructor
  · refine (hD (0, 1)).congr ?_
    intro p hp
    have hfp := (hd.1 p hp).differentiableAt (ho.mem_nhds hp)
    have hi : HasDerivAt (fun r : ℝ => (p.1, r)) (0, 1) p.2 :=
      (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
    exact (hfp.hasFDerivAt.comp_hasDerivAt p.2 hi).deriv
  · intro j
    refine (hD (Pi.single j 1, 0)).congr ?_
    intro p hp
    have hfp := (hd.1 p hp).differentiableAt (ho.mem_nhds hp)
    have hi : HasFDerivAt (fun x : WaveMap.X n => (x, p.2))
        ((ContinuousLinearMap.id ℝ (WaveMap.X n)).prod 0) p.1 :=
      (hasFDerivAt_id p.1).prodMk (hasFDerivAt_const p.2 p.1)
    have he := (hfp.hasFDerivAt.comp p.1 hi).fderiv
    change fderiv ℝ (fun x : WaveMap.X n => f (x, p.2)) p.1 (Pi.single j 1) = _
    exact congrArg (fun L : WaveMap.X n →L[ℝ] F => L (Pi.single j 1)) he

theorem checked (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_T003 : ∀ t : ℝ, 0 < t → ∃ C : Set (WaveMap.X n), ∃ R : ℝ, WaveMap.supportGeometry u q t C R) : yui_aux_type% "ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (WaveMap.density u) (WaveMap.domain n) ∧\nContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (WaveMap.densityT u) (WaveMap.domain n) ∧\nContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (WaveMap.timeProduct u) (WaveMap.domain n) ∧\n∀ j : Fin n, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (WaveMap.mixedProduct u j) (WaveMap.domain n) ∧\nContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (WaveMap.lapProduct u j) (WaveMap.domain n) ∧\nContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (WaveMap.fluxDx u j) (WaveMap.domain n)" := by
  have parts := @yui_aux_0001 n m u q h_H001 h_H002 h_T003
  have ht : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (WaveMap.dt u) (WaveMap.domain n) :=
    (parts (WaveMap.V m) inferInstance inferInstance u h_H002).1
  have hx (j : Fin n) : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (WaveMap.dx u j) (WaveMap.domain n) :=
    (parts (WaveMap.V m) inferInstance inferInstance u h_H002).2 j
  have htt : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (WaveMap.dt (WaveMap.dt u)) (WaveMap.domain n) :=
    (parts (WaveMap.V m) inferInstance inferInstance _ ht).1
  have hxt (j : Fin n) : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (WaveMap.dx (WaveMap.dt u) j) (WaveMap.domain n) :=
    (parts (WaveMap.V m) inferInstance inferInstance _ ht).2 j
  have hxx (j : Fin n) : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (WaveMap.dx (WaveMap.dx u j) j) (WaveMap.domain n) :=
    (parts (WaveMap.V m) inferInstance inferInstance _ (hx j)).2 j
  have he : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (WaveMap.density u) (WaveMap.domain n) :=
    ht.norm_sq.add (ContDiffOn.sum (fun j _ => (hx j).norm_sq))
  refine ⟨he, (parts ℝ inferInstance inferInstance _ he).1, ht.inner ℝ htt, ?_⟩
  intro j
  exact ⟨(hx j).inner ℝ (hxt j), ht.inner ℝ (hxx j),
    (parts ℝ inferInstance inferInstance (WaveMap.flux u j) (ht.inner ℝ (hx j))).2 j⟩
#check @checked
#print axioms checked
end YuiAuxiliary
