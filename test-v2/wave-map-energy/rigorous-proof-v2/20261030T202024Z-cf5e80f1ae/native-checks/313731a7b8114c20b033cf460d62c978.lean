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

namespace Translation
set_option autoImplicit false

theorem T006 (n : ℕ) (m : ℕ) (u : X n × ℝ → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ u (domain n)) (h_T004 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (X n), ∃ R : ℝ, Window u q t0 C R) ∧
  ContDiffOn ℝ ∞ (density u) (domain n) ∧
  ContDiffOn ℝ ∞ (dt (density u)) (domain n) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : X n => density u (x,t)) (mu n))) (h_T005 : ∀ x : X n, ∀ t : ℝ, 0 < t →
  HasDerivAt (fun r : ℝ => density u (x,r)) (dt (density u) (x,t)) t ∧
  dt (density u) (x,t) = 2 * kinetic u (x,t) + 2 * ∑ j : Fin n, mixed u j (x,t)) :
    ∀ t0 : ℝ, 0 < t0 → ∃ R B : ℝ, 0 < R ∧ 0 ≤ B ∧
  Integrable ((box R).indicator (fun _ : X n => B)) (mu n) ∧
  (∀ x ∈ box R, ∀ r ∈ Icc (t0-t0/4) (t0+t0/4), |dt (density u) (x,r)| ≤ B) ∧
  (∀ x : X n, ∀ h : ℝ, 0 < |h| → |h| < t0/4 →
    |(density u (x,t0+h) - density u (x,t0))/h| ≤
      (box R).indicator (fun _ : X n => B) x) := by
  intro t0 ht0
  obtain ⟨C, R, w⟩ := h_T004.1 t0 ht0
  have hK : Icc (t0 - t0 / 4) (t0 + t0 / 4) ⊆
      Ioo (t0 / 2) (3 * t0 / 2) := by
    intro r hr
    constructor <;> linarith [hr.1, hr.2]
  obtain ⟨B, hB0, hB⟩ := w.uniform (dt (density u))
    (Or.inr (Or.inl rfl)) (t0 - t0 / 4) (t0 + t0 / 4) hK
  have hbox : MeasurableSet (box (n := n) R) := by
    change MeasurableSet {x : X n | ∀ j : Fin n, x j ∈ Icc (-R) R}
    simp only [setOf_forall]
    exact MeasurableSet.iInter (fun j => (measurable_pi_apply j) measurableSet_Icc)
  have hint : Integrable ((box R).indicator (fun _ : X n => B)) (mu n) :=
    (integrableOn_const (C := B) w.box_finite.ne).integrable_indicator hbox
  refine ⟨R, B, w.radius_pos, hB0, hint, hB, ?_⟩
  intro x h hh0 hh
  have hsmall := abs_lt.mp hh
  have htmem : t0 ∈ Icc (t0 - t0 / 4) (t0 + t0 / 4) := by
    constructor <;> linarith
  have hthmem : t0 + h ∈ Icc (t0 - t0 / 4) (t0 + t0 / 4) := by
    constructor <;> linarith [hsmall.1, hsmall.2]
  by_cases hx : x ∈ box R
  · rw [Set.indicator_of_mem hx]
    have hder : ∀ r ∈ Icc (t0 - t0 / 4) (t0 + t0 / 4),
        HasDerivAt (fun s : ℝ => density u (x, s)) (dt (density u) (x, r)) r := by
      intro r hr
      exact (h_T005 x r (by have := (hK hr).1; linarith)).1
    have hslope : ∀ a b : ℝ,
        a ∈ Icc (t0 - t0 / 4) (t0 + t0 / 4) →
        b ∈ Icc (t0 - t0 / 4) (t0 + t0 / 4) → a < b →
        |(density u (x, b) - density u (x, a)) / (b - a)| ≤ B := by
      intro a b ha hb hab
      have hsub : Icc a b ⊆ Icc (t0 - t0 / 4) (t0 + t0 / 4) := by
        intro r hr
        exact ⟨ha.1.trans hr.1, hr.2.trans hb.2⟩
      obtain ⟨c, hc, heq⟩ := exists_hasDerivAt_eq_slope
        (fun r : ℝ => density u (x, r)) (fun r : ℝ => dt (density u) (x, r))
        hab
        (fun r hr => (hder r (hsub hr)).continuousAt.continuousWithinAt)
        (fun r hr => hder r (hsub ⟨hr.1.le, hr.2.le⟩))
      rw [← heq]
      exact hB x hx c (hsub ⟨hc.1.le, hc.2.le⟩)
    have hne : h ≠ 0 := by intro hz; simp [hz] at hh0
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have hs := hslope (t0 + h) t0 hthmem htmem (by linarith)
      have heq : (density u (x, t0 + h) - density u (x, t0)) / h =
          (density u (x, t0) - density u (x, t0 + h)) / (t0 - (t0 + h)) := by
        rw [show t0 - (t0 + h) = -h by ring]
        rw [show density u (x, t0) - density u (x, t0 + h) =
          -(density u (x, t0 + h) - density u (x, t0)) by ring]
        exact (neg_div_neg_eq _ _).symm
      rw [heq]
      exact hs
    · simpa only [add_sub_cancel_left] using
        hslope t0 (t0 + h) htmem hthmem (by linarith)
  · rw [Set.indicator_of_notMem hx]
    have hxC : x ∉ C := by
      intro hxC
      apply hx
      intro j
      exact ⟨(w.inside x hxC j).1.le, (w.inside x hxC j).2.le⟩
    have hz : ∀ r ∈ Icc (t0 - t0 / 4) (t0 + t0 / 4), density u (x, r) = 0 := by
      intro r hr
      exact (w.sections (density u) (Or.inl rfl) r (hK hr)).2.1 x hxC
    rw [hz (t0 + h) hthmem, hz t0 htmem]
    simp

#check @T006
#print axioms T006

end Translation
