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

theorem T006 (n : ℕ) (m : ℕ) (u : V n × ℝ → W m) (q : W m) (h_T003 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (V n), ∃ R : ℝ,
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
(∀ j : Fin n, ContinuousOn (fun p : V n × ℝ => uxt u j p.1 p.2) (domain n))) (h_T005 : ∀ t0 : ℝ, 0 < t0 → ∃ η R K : ℝ,
0 < η ∧ η < t0 ∧ 0 < R ∧ 0 ≤ K ∧
Integrable ((box n R).indicator (fun _ : V n => K)) ∧
(∀ h : ℝ, 0 < |h| → |h| < η →
Integrable (fun x => (e u x (t0+h) - e u x t0)/h) ∧
(∀ x : V n, |(e u x (t0+h) - e u x t0)/h| ≤
(box n R).indicator (fun _ : V n => K) x)) ∧
(∀ x : V n, Filter.Tendsto
(fun h : ℝ => (e u x (t0+h) - e u x t0)/h)
(nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (et u x t0)))) :
    (∀ t0 : ℝ, 0 < t0 →
HasDerivAt (energy u) (∫ x, et u x t0) t0 ∧
deriv (energy u) t0 = ∫ x, et u x t0) ∧ DifferentiableOn ℝ (energy u) (Set.Ioi 0) := by
  have hderiv : ∀ t0 : ℝ, 0 < t0 → HasDerivAt (energy u) (∫ x, et u x t0) t0 := by
    intro t0 ht0
    obtain ⟨η, R, K, hη, hηt, hR, hK, hbound, hquot, hpoint⟩ := h_T005 t0 ht0
    have hsmall : ∀ᶠ h : ℝ in nhdsWithin 0 ({0}ᶜ), 0 < |h| ∧ |h| < η := by
      rw [eventually_nhdsWithin_iff]
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hη] with h hh hn
      have hh' : |h| < η := by simpa [Metric.mem_ball, Real.dist_eq] using hh
      have hn' : h ≠ 0 := by simpa using hn
      exact ⟨abs_pos.mpr hn', hh'⟩
    have hmeas : ∀ᶠ h : ℝ in nhdsWithin 0 ({0}ᶜ),
        AEStronglyMeasurable (fun x : V n => (e u x (t0+h) - e u x t0)/h) volume := by
      filter_upwards [hsmall] with h hh
      exact (hquot h hh.1 hh.2).1.aestronglyMeasurable
    have hdom : ∀ᶠ h : ℝ in nhdsWithin 0 ({0}ᶜ), ∀ᵐ x : V n,
        ‖(e u x (t0+h) - e u x t0)/h‖ ≤ (box n R).indicator (fun _ : V n => K) x := by
      filter_upwards [hsmall] with h hh
      exact Filter.Eventually.of_forall (fun x => by
        simpa only [Real.norm_eq_abs] using (hquot h hh.1 hh.2).2 x)
    have hlim : Filter.Tendsto
        (fun h : ℝ => ∫ x : V n, (e u x (t0+h) - e u x t0)/h)
        (nhdsWithin 0 ({0}ᶜ)) (nhds (∫ x : V n, et u x t0)) :=
      tendsto_integral_filter_of_dominated_convergence
        ((box n R).indicator (fun _ : V n => K)) hmeas hdom hbound
        (Filter.Eventually.of_forall hpoint)
    have heq : (fun h : ℝ => ∫ x : V n, (e u x (t0+h) - e u x t0)/h)
        =ᶠ[nhdsWithin 0 ({0}ᶜ)] (fun h : ℝ => (energy u (t0+h) - energy u t0)/h) := by
      filter_upwards [hsmall] with h hh
      have hpos : 0 < t0 + h := by
        have hneg := neg_abs_le h
        linarith [hh.2]
      rw [integral_div, integral_sub (h_T003.2 (t0+h) hpos) (h_T003.2 t0 ht0)]
      rfl
    apply hasDerivAt_iff_tendsto_slope_zero.mpr
    simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using (hlim.congr' heq)
  constructor
  · intro t0 ht0
    exact ⟨hderiv t0 ht0, (hderiv t0 ht0).deriv⟩
  · intro t0 ht0
    exact (hderiv t0 ht0).differentiableAt.differentiableWithinAt

#check @T006
#print axioms T006

end Translation
