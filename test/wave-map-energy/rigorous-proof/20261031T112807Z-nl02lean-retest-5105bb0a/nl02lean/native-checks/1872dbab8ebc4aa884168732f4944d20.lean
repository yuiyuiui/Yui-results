import Mathlib
open MeasureTheory Set Filter
open scoped BigOperators ContDiff
noncomputable section
namespace WaveMap
abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)
def positive (n : ℕ) : Set (Space n × ℝ) := {p | 0 < p.2}
def box (n : ℕ) (R : ℝ) : Set (Space n) := {x | ∀ j, x j ∈ Icc (-R) R}
def openBox (n : ℕ) (R : ℝ) : Set (Space n) := {x | ∀ j, x j ∈ Ioo (-R) R}
def timeInterval (t : ℝ) : Set ℝ := Icc (t / 2) (3 * t / 2)
def timeInterior (t : ℝ) : Set ℝ := Ioo (t / 2) (3 * t / 2)
def spatial {n : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Space n → F) (j : Fin n) (x : Space n) : F :=
  fderiv ℝ f x (PiLp.single 2 j 1)
def ut {n m : ℕ} (u : Space n × ℝ → Space m) (x : Space n) (t : ℝ) : Space m :=
  deriv (fun r => u (x, r)) t
def utt {n m : ℕ} (u : Space n × ℝ → Space m) (x : Space n) (t : ℝ) : Space m :=
  deriv (ut u x) t
def ux {n m : ℕ} (u : Space n × ℝ → Space m) (j : Fin n) (x : Space n) (t : ℝ) : Space m :=
  spatial (fun y => u (y, t)) j x
def uxx {n m : ℕ} (u : Space n × ℝ → Space m) (j : Fin n) (x : Space n) (t : ℝ) : Space m :=
  spatial (fun y => ux u j y t) j x
def utx {n m : ℕ} (u : Space n × ℝ → Space m) (j : Fin n) (x : Space n) (t : ℝ) : Space m :=
  spatial (fun y => ut u y t) j x
def laplace {n m : ℕ} (u : Space n × ℝ → Space m) (x : Space n) (t : ℝ) : Space m :=
  ∑ j, uxx u j x t
def density {n m : ℕ} (u : Space n × ℝ → Space m) (x : Space n) (t : ℝ) : ℝ :=
  ‖ut u x t‖ ^ 2 + ∑ j, ‖ux u j x t‖ ^ 2
def densityTime {n m : ℕ} (u : Space n × ℝ → Space m) (x : Space n) (t : ℝ) : ℝ :=
  deriv (density u x) t
def energy {n m : ℕ} (u : Space n × ℝ → Space m) (t : ℝ) : ℝ :=
  ∫ x, density u x t
def kineticProduct {n m : ℕ} (u : Space n × ℝ → Space m) (t : ℝ) (x : Space n) : ℝ :=
  inner ℝ (ut u x t) (utt u x t)
def gradientProduct {n m : ℕ} (u : Space n × ℝ → Space m) (j : Fin n) (t : ℝ) (x : Space n) : ℝ :=
  inner ℝ (ux u j x t) (utx u j x t)
def laplaceProduct {n m : ℕ} (u : Space n × ℝ → Space m) (j : Fin n) (t : ℝ) (x : Space n) : ℝ :=
  inner ℝ (ut u x t) (uxx u j x t)
def flux {n m : ℕ} (u : Space n × ℝ → Space m) (j : Fin n) (t : ℝ) (x : Space n) : ℝ :=
  inner ℝ (ut u x t) (ux u j x t)
def terms {n m : ℕ} (u : Space n × ℝ → Space m) (t : ℝ) (j : Fin n) : List (Space n → ℝ) :=
  [fun x => density u x t, fun x => densityTime u x t, kineticProduct u t,
   gradientProduct u j t, laplaceProduct u j t, flux u j t, spatial (flux u j t) j]
def quotient {n m : ℕ} (u : Space n × ℝ → Space m) (t h : ℝ) (x : Space n) : ℝ :=
  (density u x (t + h) - density u x t) / h
def bound (n : ℕ) (R B : ℝ) : Space n → ℝ :=
  (box n R).indicator (fun _ => B)
end WaveMap

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem checked (n : ℕ) (m : ℕ) (u : WaveMap.Space n × ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ (∞ : ℕ∞ω) u (WaveMap.positive n)) (h_T002 : ∀ t0 : ℝ, 0 < t0 → ∃ (C : Set (WaveMap.Space n)) (R : ℝ),
  IsCompact C ∧ 0 < R ∧ C ⊆ WaveMap.openBox n R ∧
  (∀ x : WaveMap.Space n, x ∉ C → ∀ r ∈ WaveMap.timeInterval t0, u (x,r) = q) ∧
  (∀ (k : ℕ) (x : WaveMap.Space n) (r : ℝ), 0 < k → x ∉ C →
    r ∈ WaveMap.timeInterior t0 → iteratedFDeriv ℝ k u (x,r) = 0)) : yui_aux_type% "ContDiffOn ℝ (∞ : ℕ∞ω) (fun p => WaveMap.density u p.1 p.2) (WaveMap.positive n) ∧ ContDiffOn ℝ (∞ : ℕ∞ω) (fun p => WaveMap.densityTime u p.1 p.2) (WaveMap.positive n) ∧ ∀ (r : ℝ), 0 < r → ∀ (j : Fin n) (f : WaveMap.Space n → ℝ), f ∈ WaveMap.terms u r j → Continuous f" := by
  have smoothD : ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (f : WaveMap.Space n × ℝ → F), ContDiffOn ℝ (∞ : ℕ∞ω) f (WaveMap.positive n) → ContDiffOn ℝ (∞ : ℕ∞ω) (fun p : WaveMap.Space n × ℝ => deriv (fun r => f (p.1,r)) p.2) (WaveMap.positive n) ∧ ∀ j : Fin n, ContDiffOn ℝ (∞ : ℕ∞ω) (fun p : WaveMap.Space n × ℝ => WaveMap.spatial (fun y => f (y,p.2)) j p.1) (WaveMap.positive n) := by
    intro F _ _ f hf
    have ho : IsOpen (WaveMap.positive n) := isOpen_lt continuous_const continuous_snd
    constructor
    · intro p hp
      have h : ContDiffAt ℝ (∞ : ℕ∞ω) (Function.uncurry (fun (z : WaveMap.Space n × ℝ) (r : ℝ) => f (z.1,r))) (p,p.2) :=
        (hf.contDiffAt (ho.mem_nhds hp)).comp _ (contDiffAt_fst.fst.prodMk contDiffAt_snd)
      have hh : ContDiffAt ℝ (∞ : ℕ∞ω) (fun z : WaveMap.Space n × ℝ => fderiv ℝ (fun r => f (z.1,r)) z.2) p :=
        ContDiffAt.fderiv (f := fun (z : WaveMap.Space n × ℝ) (r : ℝ) => f (z.1,r)) (g := fun z => z.2) h contDiffAt_snd (by simp)
      exact (hh.clm_apply (contDiffAt_const (c := (1 : ℝ)))).contDiffWithinAt
    · intro j p hp
      have h : ContDiffAt ℝ (∞ : ℕ∞ω) (Function.uncurry (fun (z : WaveMap.Space n × ℝ) (y : WaveMap.Space n) => f (y,z.2))) (p,p.1) :=
        (hf.contDiffAt (ho.mem_nhds hp)).comp _ (contDiffAt_snd.prodMk contDiffAt_fst.snd)
      have hh : ContDiffAt ℝ (∞ : ℕ∞ω) (fun z : WaveMap.Space n × ℝ => fderiv ℝ (fun y => f (y,z.2)) z.1) p :=
        ContDiffAt.fderiv (f := fun (z : WaveMap.Space n × ℝ) (y : WaveMap.Space n) => f (y,z.2)) (g := fun z => z.1) h contDiffAt_fst (by simp)
      exact (hh.clm_apply (contDiffAt_const (c := PiLp.single 2 j 1))).contDiffWithinAt
  have sut : ContDiffOn ℝ (∞ : ℕ∞ω) (fun p => WaveMap.ut u p.1 p.2) (WaveMap.positive n) := (smoothD _ u h_H002).1
  have sux (j : Fin n) : ContDiffOn ℝ (∞ : ℕ∞ω) (fun p => WaveMap.ux u j p.1 p.2) (WaveMap.positive n) := (smoothD _ u h_H002).2 j
  have sutt : ContDiffOn ℝ (∞ : ℕ∞ω) (fun p => WaveMap.utt u p.1 p.2) (WaveMap.positive n) := (smoothD _ _ sut).1
  have sutx (j : Fin n) : ContDiffOn ℝ (∞ : ℕ∞ω) (fun p => WaveMap.utx u j p.1 p.2) (WaveMap.positive n) := (smoothD _ _ sut).2 j
  have suxx (j : Fin n) : ContDiffOn ℝ (∞ : ℕ∞ω) (fun p => WaveMap.uxx u j p.1 p.2) (WaveMap.positive n) := (smoothD _ _ (sux j)).2 j
  have se : ContDiffOn ℝ (∞ : ℕ∞ω) (fun p => WaveMap.density u p.1 p.2) (WaveMap.positive n) := by
    exact sut.norm_sq.add (ContDiffOn.sum (fun j _ => (sux j).norm_sq))
  have set : ContDiffOn ℝ (∞ : ℕ∞ω) (fun p => WaveMap.densityTime u p.1 p.2) (WaveMap.positive n) := (smoothD _ _ se).1
  have sk : ContDiffOn ℝ (∞ : ℕ∞ω) (fun p => WaveMap.kineticProduct u p.2 p.1) (WaveMap.positive n) := sut.inner sutt
  have sg (j : Fin n) : ContDiffOn ℝ (∞ : ℕ∞ω) (fun p => WaveMap.gradientProduct u j p.2 p.1) (WaveMap.positive n) := (sux j).inner (sutx j)
  have sl (j : Fin n) : ContDiffOn ℝ (∞ : ℕ∞ω) (fun p => WaveMap.laplaceProduct u j p.2 p.1) (WaveMap.positive n) := sut.inner (suxx j)
  have sf (j : Fin n) : ContDiffOn ℝ (∞ : ℕ∞ω) (fun p => WaveMap.flux u j p.2 p.1) (WaveMap.positive n) := sut.inner (sux j)
  have sdf (j : Fin n) : ContDiffOn ℝ (∞ : ℕ∞ω) (fun p => WaveMap.spatial (WaveMap.flux u j p.2) j p.1) (WaveMap.positive n) := (smoothD _ _ (sf j)).2 j

  refine ⟨se, set, ?_⟩
  intro r hr j f hf
  have slice (g : WaveMap.Space n × ℝ → ℝ) (hg : ContDiffOn ℝ (∞ : ℕ∞ω) g (WaveMap.positive n)) : Continuous (fun x => g (x,r)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (hg.contDiffAt ((isOpen_lt continuous_const continuous_snd : IsOpen (WaveMap.positive n)).mem_nhds hr)).continuousAt.comp (continuousAt_id.prodMk continuousAt_const)
  simp only [WaveMap.terms, List.mem_cons, List.mem_singleton] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact slice _ se
  · exact slice _ set
  · exact slice _ sk
  · exact slice _ (sg j)
  · exact slice _ (sl j)
  · exact slice _ (sf j)
  · exact slice _ (sdf j)
#check @checked
#print axioms checked
end YuiAuxiliary
