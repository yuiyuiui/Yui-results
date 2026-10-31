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

theorem T005 (n : ℕ) (m : ℕ) (u : V n × ℝ → W m) (q : W m) (h_T003 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (V n), ∃ R : ℝ,
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
(∀ j : Fin n, ContinuousOn (fun p : V n × ℝ => uxt u j p.1 p.2) (domain n))) :
    ∀ t0 : ℝ, 0 < t0 → ∃ η R K : ℝ,
0 < η ∧ η < t0 ∧ 0 < R ∧ 0 ≤ K ∧
Integrable ((box n R).indicator (fun _ : V n => K)) ∧
(∀ h : ℝ, 0 < |h| → |h| < η →
Integrable (fun x => (e u x (t0+h) - e u x t0)/h) ∧
(∀ x : V n, |(e u x (t0+h) - e u x t0)/h| ≤
(box n R).indicator (fun _ : V n => K) x)) ∧
(∀ x : V n, Filter.Tendsto
(fun h : ℝ => (e u x (t0+h) - e u x t0)/h)
(nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (et u x t0))) := by
  classical
  intro t0 ht0
  obtain ⟨C, R, hC, hR, hCi, hCQ, hQ, hQm, hvol, hfin, hu, hder, hf⟩ :=
    h_T003.1 t0 ht0
  let η : ℝ := t0 / 4
  have hη : 0 < η := by dsimp [η]; linarith
  have hηt : η < t0 := by dsimp [η]; linarith
  have hI : ∀ r ∈ Set.Icc (t0-η) (t0+η),
      r ∈ Set.Ioo (t0/2) (3*t0/2) := by
    intro r hr
    dsimp [η] at hr
    constructor <;> linarith [hr.1, hr.2]
  have hpos : ∀ r ∈ Set.Icc (t0-η) (t0+η), 0 < r := by
    intro r hr
    have := (hI r hr).1
    linarith
  have htime : ∀ x : V n, ∀ t : ℝ, 0 < t →
      HasDerivAt (fun s => e u x s) (et u x t) t := by
    intro x t ht
    have hopen : IsOpen (domain n) := isOpen_lt continuous_const continuous_snd
    have hd : DifferentiableAt ℝ (fun p : V n × ℝ => e u p.1 p.2) (x,t) :=
      (h_T004.1.contDiffAt (hopen.mem_nhds ht)).differentiableAt (by simp)
    have hc : DifferentiableAt ℝ (fun s : ℝ => (x,s)) t :=
      (differentiableAt_const x).prodMk differentiableAt_id
    exact (hd.comp t hc).hasDerivAt
  have hefield : (fun p : V n × ℝ => e u p.1 p.2) ∈ fields u := by
    exact Or.inl rfl
  have hetfield : (fun p : V n × ℝ => et u p.1 p.2) ∈ fields u := by
    exact Or.inr (Or.inl rfl)
  have hct : ContinuousOn (fun p : V n × ℝ => et u p.1 p.2)
      ((box n R) ×ˢ Set.Icc (t0-η) (t0+η)) :=
    (h_T004.2.2.2.1 _ hetfield).mono (by
      intro p hp
      exact hpos p.2 hp.2)
  obtain ⟨L, hL⟩ := (hQ.prod isCompact_Icc).bddAbove_image hct.abs
  let K : ℝ := max L 0
  have hK : 0 ≤ K := le_max_right _ _
  have hbound : ∀ x ∈ box n R, ∀ r ∈ Set.Icc (t0-η) (t0+η),
      |et u x r| ≤ K := by
    intro x hx r hr
    exact le_trans (hL ⟨(x,r), ⟨hx,hr⟩, rfl⟩) (le_max_left _ _)
  have hind : Integrable ((box n R).indicator (fun _ : V n => K)) :=
    (integrable_indicator_iff hQm).2 (integrableOn_const hfin.ne)
  refine ⟨η, R, K, hη, hηt, hR, hK, hind, ?_, ?_⟩
  · intro h hh hsmall
    have habs : -η < h ∧ h < η := abs_lt.mp hsmall
    have htI : t0 ∈ Set.Icc (t0-η) (t0+η) := by constructor <;> linarith
    have hthI : t0+h ∈ Set.Icc (t0-η) (t0+η) := by constructor <;> linarith [habs.1,habs.2]
    refine ⟨((h_T003.2 (t0+h) (hpos _ hthI)).sub (h_T003.2 t0 ht0)).div_const h, ?_⟩
    intro x
    by_cases hx : x ∈ box n R
    · rw [Set.indicator_of_mem hx]
      have hest : |e u x (t0+h) - e u x t0| ≤ K * |h| := by
        rcases lt_or_gt_of_ne (abs_pos.mp hh) with hneg | hpositive
        · have hstep := norm_image_sub_le_of_norm_deriv_le_segment'
            (f := fun r : ℝ => e u x r) (f' := fun r => et u x r)
            (a := t0+h) (b := t0) (C := K)
            (fun r hr => (htime x r (hpos r (by
              constructor <;> linarith [hr.1, hr.2, habs.1, habs.2]))).hasDerivWithinAt)
            (fun r hr => by
              rw [Real.norm_eq_abs]
              exact hbound x hx r (by constructor <;> linarith [hr.1, hr.2, habs.1, habs.2]))
            t0 (by constructor <;> linarith)
          rw [Real.norm_eq_abs, abs_sub_comm] at hstep
          rw [abs_of_neg hneg]
          convert hstep using 1 <;> ring
        · have hstep := norm_image_sub_le_of_norm_deriv_le_segment'
            (f := fun r : ℝ => e u x r) (f' := fun r => et u x r)
            (a := t0) (b := t0+h) (C := K)
            (fun r hr => (htime x r (hpos r (by
              constructor <;> linarith [hr.1, hr.2, habs.1, habs.2]))).hasDerivWithinAt)
            (fun r hr => by
              rw [Real.norm_eq_abs]
              exact hbound x hx r (by constructor <;> linarith [hr.1, hr.2, habs.1, habs.2]))
            (t0+h) (by constructor <;> linarith)
          simpa only [Real.norm_eq_abs, add_sub_cancel_left, abs_of_pos hpositive] using hstep
      rw [abs_div]
      exact (div_le_iff₀ hh).2 hest
    · rw [Set.indicator_of_notMem hx]
      have hxC : x ∉ C := fun hc => hx (interior_subset (hCQ hc))
      have hz1 : e u x (t0+h) = 0 := (hf _ hefield _ (hI _ hthI)).2.1 x hxC
      have hz0 : e u x t0 = 0 := (hf _ hefield _ (hI _ htI)).2.1 x hxC
      simp [hz1,hz0]
  · intro x
    simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using
      (htime x t0 ht0).tendsto_slope_zero

#check @T005
#print axioms T005

end Translation
