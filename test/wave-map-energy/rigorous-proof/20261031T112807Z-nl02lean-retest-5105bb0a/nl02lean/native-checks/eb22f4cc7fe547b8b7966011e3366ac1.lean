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

namespace Translation
set_option autoImplicit false

theorem T005 (n : ℕ) (m : ℕ) (u : WaveMap.Space n × ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_T003 : (∀ t : ℝ, 0 < t → Integrable (fun x => WaveMap.density u x t)) ∧
  ContDiffOn ℝ (∞ : ℕ∞ω) (fun p => WaveMap.density u p.1 p.2) (WaveMap.positive n) ∧
  ContDiffOn ℝ (∞ : ℕ∞ω) (fun p => WaveMap.densityTime u p.1 p.2) (WaveMap.positive n) ∧
  ∀ t0 : ℝ, 0 < t0 → ∃ (C : Set (WaveMap.Space n)) (R η B : ℝ),
    IsCompact C ∧ 0 < R ∧ 0 < η ∧ 0 ≤ B ∧
    C ⊆ WaveMap.openBox n R ∧ IsCompact (WaveMap.box n R) ∧
    volume (WaveMap.box n R) = ENNReal.ofReal ((2 * R) ^ n) ∧
    volume (WaveMap.box n R) ≠ ⊤ ∧
    Icc (t0 - η) (t0 + η) ⊆ WaveMap.timeInterior t0 ∧
    (∀ x : WaveMap.Space n, x ∉ C → ∀ r ∈ WaveMap.timeInterval t0, u (x,r) = q) ∧
    (∀ (k : ℕ) (x : WaveMap.Space n) (r : ℝ), 0 < k → x ∉ C →
      r ∈ WaveMap.timeInterior t0 → iteratedFDeriv ℝ k u (x,r) = 0) ∧
    (∀ r ∈ WaveMap.timeInterior t0, ∀ (j : Fin n) (f : WaveMap.Space n → ℝ),
      f ∈ WaveMap.terms u r j →
      Continuous f ∧ Function.support f ⊆ C ∧
      (∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ WaveMap.box n R, |f x| ≤ K) ∧
      Measurable f ∧ Integrable f) ∧
    (∀ x ∈ WaveMap.box n R, ∀ r ∈ Icc (t0 - η) (t0 + η), |WaveMap.densityTime u x r| ≤ B)) (h_T004 : ∀ (x : WaveMap.Space n) (t : ℝ), 0 < t →
  HasDerivAt (WaveMap.density u x) (WaveMap.densityTime u x t) t ∧
  WaveMap.densityTime u x t = 2 * WaveMap.kineticProduct u t x +
    2 * ∑ j, WaveMap.gradientProduct u j t x) :
    ∀ t0 : ℝ, 0 < t0 → ∃ R η B : ℝ,
  0 < R ∧ 0 < η ∧ 0 ≤ B ∧ Icc (t0 - η) (t0 + η) ⊆ Ioi (0 : ℝ) ∧
  Integrable (WaveMap.bound n R B) ∧
  ∀ h : ℝ, 0 < |h| → |h| < η → ∀ x : WaveMap.Space n,
    |WaveMap.quotient u t0 h x| ≤ WaveMap.bound n R B x := by
  classical
  intro t0 ht0
  rcases h_T003.2.2.2 t0 ht0 with
    ⟨C, R, η, B, hC, hR, hη, hB, hCopen, hbox, hvol, hfinite,
      htime, hu, hiter, hterms, hbound⟩
  have hpositive : Icc (t0 - η) (t0 + η) ⊆ Ioi (0 : ℝ) := by
    intro r hr
    have hr' := (htime hr).1
    change t0 / 2 < r at hr'
    change 0 < r
    linarith
  have hint : Integrable (WaveMap.bound n R B) := by
    exact (integrable_indicator_iff hbox.measurableSet).2
      (integrableOn_const (C := B) hfinite)
  refine ⟨R, η, B, hR, hη, hB, hpositive, hint, ?_⟩
  intro h hh hhη x
  have hbounds := abs_lt.mp hhη
  have htmem : t0 ∈ Icc (t0 - η) (t0 + η) := ⟨by linarith, by linarith⟩
  have hthmem : t0 + h ∈ Icc (t0 - η) (t0 + η) := ⟨by linarith, by linarith⟩
  by_cases hx : x ∈ WaveMap.box n R
  · rw [WaveMap.bound, Set.indicator_of_mem hx]
    change |(WaveMap.density u x (t0 + h) - WaveMap.density u x t0) / h| ≤ B
    have hne : h ≠ 0 := by intro he; simp [he] at hh
    have hseg : Icc (min t0 (t0 + h)) (max t0 (t0 + h)) ⊆
        Icc (t0 - η) (t0 + η) := by
      intro r hr
      exact ⟨le_trans (le_min htmem.1 hthmem.1) hr.1,
        le_trans hr.2 (max_le htmem.2 hthmem.2)⟩
    have hab : min t0 (t0 + h) < max t0 (t0 + h) := by
      rcases lt_or_gt_of_ne hne with hn | hp
      · rw [min_eq_right (by linarith), max_eq_left (by linarith)]
        linarith
      · rw [min_eq_left (by linarith), max_eq_right (by linarith)]
        linarith
    have hc : ContinuousOn (WaveMap.density u x)
        (Icc (min t0 (t0 + h)) (max t0 (t0 + h))) :=
      fun r hr => (h_T004 x r (hpositive (hseg hr))).1.continuousAt.continuousWithinAt
    obtain ⟨c, hcmem, heq⟩ := exists_hasDerivAt_eq_slope
      (WaveMap.density u x) (WaveMap.densityTime u x) hab hc
      (fun r hr => (h_T004 x r (hpositive (hseg ⟨hr.1.le, hr.2.le⟩))).1)
    have hcB := hbound x hx c (hseg ⟨hcmem.1.le, hcmem.2.le⟩)
    have hslope :
        (WaveMap.density u x (max t0 (t0 + h)) -
          WaveMap.density u x (min t0 (t0 + h))) /
        (max t0 (t0 + h) - min t0 (t0 + h)) =
        (WaveMap.density u x (t0 + h) - WaveMap.density u x t0) / h := by
      rcases lt_or_gt_of_ne hne with hn | hp
      · rw [min_eq_right (by linarith), max_eq_left (by linarith)]
        have he : t0 - (t0 + h) = -h := by ring
        rw [he, div_neg, ← neg_div, neg_sub]
      · rw [min_eq_left (by linarith), max_eq_right (by linarith)]
        congr 1
        ring
    rw [heq, hslope] at hcB
    exact hcB
  · have hxC : x ∉ C := by
      intro hxc
      apply hx
      intro j
      exact ⟨(hCopen hxc j).1.le, (hCopen hxc j).2.le⟩
    have hex : ∃ j : Fin n, x j ∉ Icc (-R) R := by
      simpa only [WaveMap.box, mem_setOf_eq, not_forall] using hx
    obtain ⟨j, hj⟩ := hex
    have hzero : ∀ r ∈ Icc (t0 - η) (t0 + η), WaveMap.density u x r = 0 := by
      intro r hr
      have hs : Function.support (fun y => WaveMap.density u y r) ⊆ C :=
        (hterms r (htime hr) j (fun y => WaveMap.density u y r)
          (by simp [WaveMap.terms])).2.1
      by_contra hn
      exact hxC (hs hn)
    simp [WaveMap.bound, Set.indicator_of_notMem hx, WaveMap.quotient,
      hzero t0 htmem, hzero (t0 + h) hthmem]

#check @T005
#print axioms T005

end Translation
