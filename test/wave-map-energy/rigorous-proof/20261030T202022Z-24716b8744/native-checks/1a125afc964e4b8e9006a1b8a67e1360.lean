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

theorem T010 (n : ℕ) (m : ℕ) (u : V n × ℝ → W m) (q : W m) (h_T003 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (V n), ∃ R : ℝ,
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
(∃ U : Set (V n), IsOpen U ∧ frontier (box n R) ⊆ U ∧ ∀ x ∈ U, f (x,r) = 0))) ∧ (∀ r : ℝ, 0 < r → Integrable (fun x => e u x r))) (h_T006 : (∀ t0 : ℝ, 0 < t0 →
HasDerivAt (energy u) (∫ x, et u x t0) t0 ∧
deriv (energy u) t0 = ∫ x, et u x t0) ∧ DifferentiableOn ℝ (energy u) (Set.Ioi 0)) (h_T009 : ∀ t0 : ℝ, 0 < t0 →
deriv (energy u) t0 = 2*(∫ x, A u x t0) + 2*(∑ j, ∫ x, B u j x t0) ∧
deriv (energy u) t0 = 2*(∫ x, A u x t0) - 2*(∑ j, ∫ x, T u j x t0) ∧
deriv (energy u) t0 = 2*(∫ x, inner ℝ (ut u x t0) (utt u x t0 - lap u x t0)) ∧
HasDerivAt (energy u) 0 t0) :
    (∀ r : ℝ, 0 < r → Integrable (fun x => e u x r)) ∧
DifferentiableOn ℝ (energy u) (Set.Ioi 0) ∧
(∀ r : ℝ, 0 < r → deriv (energy u) r = 0) ∧
(∀ s t : ℝ, 0 < s → 0 < t → energy u s = energy u t) := by
  have hzero : ∀ r : ℝ, 0 < r → deriv (energy u) r = 0 := by
    intro r hr
    exact (h_T009 r hr).2.2.2.deriv
  refine ⟨h_T003.2, h_T006.2, hzero, ?_⟩
  have hinterval : ∀ a b : ℝ, 0 < a → a < b → energy u b = energy u a := by
    intro a b ha hab
    have hdiff : DifferentiableOn ℝ (energy u) (Set.Icc a b) := by
      intro x hx
      exact ((h_T009 x (lt_of_lt_of_le ha hx.1)).2.2.2).differentiableAt.differentiableWithinAt
    have hwithin : ∀ x ∈ Set.Icc a b, derivWithin (energy u) (Set.Icc a b) x = 0 := by
      intro x hx
      exact ((h_T009 x (lt_of_lt_of_le ha hx.1)).2.2.2).hasDerivWithinAt.derivWithin
        (uniqueDiffOn_Icc hab x hx)
    have hbound : ∀ x ∈ Set.Ico a b, ‖derivWithin (energy u) (Set.Icc a b) x‖ ≤ (0 : ℝ) := by
      intro x hx
      rw [hwithin x ⟨hx.1, le_of_lt hx.2⟩, norm_zero]
    have h := norm_image_sub_le_of_norm_deriv_le_segment hdiff hbound b ⟨le_of_lt hab, le_rfl⟩
    simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using h
  intro s t hs ht
  rcases lt_trichotomy s t with hst | hst | hts
  · exact (hinterval s t hs hst).symm
  · rw [hst]
  · exact hinterval t s ht hts

#check @T010
#print axioms T010

end Translation
