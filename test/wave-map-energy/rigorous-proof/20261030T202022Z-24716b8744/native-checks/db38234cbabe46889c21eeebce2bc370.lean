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

namespace Translation
set_option autoImplicit false

theorem T008 (n : ℕ) (m : ℕ) (u : V n × ℝ → W m) (q : W m) (h_T003 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (V n), ∃ R : ℝ,
IsCompact C ∧ 0 < R ∧ C ⊆ innerBox n R ∧ C ⊆ interior (box n R) ∧
IsCompact (box n R) ∧ MeasurableSet (box n R) ∧
volume (box n R) = ENNReal.ofReal ((2*R)^n) ∧ volume (box n R) < ⊤ ∧
(∀ x, x ∉ C → ∀ r ∈ Set.Icc (t0/2) (3*t0/2), u (x,r) = q) ∧
(∀ k : ℕ, 0 < k → ∀ x, x ∉ C → ∀ r ∈ Set.Ioo (t0/2) (3*t0/2),
iteratedFDeriv ℝ k u (x,r) = 0 ) ∧ (∀ f ∈ fields u, ∀ r ∈ Set.Ioo (t0/2) (3*t0/2),
Continuous (fun x => f (x,r)) ∧
(∀ x, x ∉ C → f (x,r) = 0) ∧
HasCompactSupport (fun x => f (x,r)) ∧ Integrable (fun x => f (x,r)) ∧
(∃ K : ℝ, 0 ≤ K ∧ (∀ x ∈ box n R, |f (x,r)| ≤ K) ∧
(∫ x, |f (x,r)|) ≤ K * (volume (box n R)).toReal) ∧
(∃ U : Set (V n), IsOpen U ∧ frontier (box n R) ⊆ U ∧ ∀ x ∈ U, f (x,r) = 0))) ∧ (∀ r : ℝ, 0 < r → Integrable (fun x => e u x r))) (h_T004 : ContDiffOn ℝ ∞ (fun p : V n × ℝ => e u p.1 p.2) (domain n) ∧
(∀ j : Fin n, ContDiffOn ℝ ∞ (fun p : V n × ℝ => g u j p.1 p.2) (domain n)) ∧
(∀ x t, 0 < t →
(∀ j : Fin n, deriv (fun s => ux u j x s) t = uxt u j x t) ∧
et u x t = 2*A u x t + 2*(∑ j, B u j x t) ∧
(∀ j : Fin n, dg u j x t = B u j x t + T u j x t)) ∧
(∀ f ∈ fields u, ContinuousOn f (domain n)) ∧
(∀ j : Fin n, ContinuousOn (fun p : V n × ℝ => uxt u j p.1 p.2) (domain n))) (h_T007 : ∀ t0 : ℝ, 0 < t0 → ∀ j : Fin n,
Integrable (fun x => dg u j x t0) ∧ (∫ x, dg u j x t0) = 0) :
    ∀ t0 : ℝ, 0 < t0 → ∀ j : Fin n,
Integrable (fun x => dg u j x t0) ∧ Integrable (fun x => B u j x t0) ∧
Integrable (fun x => T u j x t0) ∧
(∫ x, dg u j x t0) = 0 ∧
(∫ x, B u j x t0) = -(∫ x, T u j x t0) ∧
(∫ x, inner ℝ (ux u j x t0) (uxt u j x t0)) =
-(∫ x, inner ℝ (ut u x t0) (uxx u j x t0)) := by
  intro t0 ht0 j
  rcases h_T003.1 t0 ht0 with
    ⟨C, R, hC, hR, hCi, hCb, hbox, hmeas, hvol, hfin, hu, hder, hfields⟩
  have htime : t0 ∈ Set.Ioo (t0 / 2) (3 * t0 / 2) := by
    constructor <;> linarith
  have hf : ∀ f ∈ fields u, Integrable (fun x => f (x, t0)) := by
    intro f hmem
    exact (hfields f hmem t0 htime).2.2.2.1
  have hB : Integrable (fun x => B u j x t0) := by
    apply hf (fun p => B u j p.1 p.2)
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨j, rfl⟩)))
  have hT : Integrable (fun x => T u j x t0) := by
    apply hf (fun p => T u j p.1 p.2)
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j, rfl⟩))))
  have hdg : Integrable (fun x => dg u j x t0) := by
    apply hf (fun p => dg u j p.1 p.2)
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨j, rfl⟩)))))
  have hzero : (∫ x, dg u j x t0) = 0 := (h_T007 t0 ht0 j).2
  have hid : (fun x => dg u j x t0) =
      (fun x => B u j x t0 + T u j x t0) := by
    funext x
    exact (h_T004.2.2.1 x t0 ht0).2.2 j
  have hsum : (∫ x, B u j x t0) + (∫ x, T u j x t0) = 0 := by
    rw [← MeasureTheory.integral_add hB hT, ← hid]
    exact hzero
  have hneg : (∫ x, B u j x t0) = -(∫ x, T u j x t0) := by
    linarith
  exact ⟨hdg, hB, hT, hzero, hneg, by simpa only [B, T] using hneg⟩

#check @T008
#print axioms T008

end Translation
