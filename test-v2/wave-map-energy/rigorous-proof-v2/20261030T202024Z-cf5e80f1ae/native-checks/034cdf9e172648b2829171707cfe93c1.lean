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

theorem T008 (n : ℕ) (m : ℕ) (u : X n × ℝ → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ u (domain n)) (h_T004 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (X n), ∃ R : ℝ, Window u q t0 C R) ∧
  ContDiffOn ℝ ∞ (density u) (domain n) ∧
  ContDiffOn ℝ ∞ (dt (density u)) (domain n) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : X n => density u (x,t)) (mu n))) (h_T005 : ∀ x : X n, ∀ t : ℝ, 0 < t →
  HasDerivAt (fun r : ℝ => density u (x,r)) (dt (density u) (x,t)) t ∧
  dt (density u) (x,t) = 2 * kinetic u (x,t) + 2 * ∑ j : Fin n, mixed u j (x,t)) (h_T007 : ∀ t0 : ℝ, 0 < t0 → ∀ h : ℕ → ℝ,
  (∀ k : ℕ, 0 < |h k| ∧ |h k| < t0/4) →
  Tendsto h atTop (nhds 0) →
  Tendsto (fun k : ℕ => (energy u (t0+h k) - energy u t0)/h k) atTop
    (nhds (∫ x : X n, dt (density u) (x,t0) ∂mu n))) :
    ∀ t : ℝ, 0 < t →
  DifferentiableAt ℝ (energy u) t ∧
  deriv (energy u) t = (∫ x : X n, dt (density u) (x,t) ∂mu n) ∧
  deriv (energy u) t =
    2 * (∫ x : X n, kinetic u (x,t) ∂mu n) +
    2 * ∑ j : Fin n, (∫ x : X n, mixed u j (x,t) ∂mu n) ∧
  Integrable (fun x : X n => dt (density u) (x,t)) (mu n) ∧
  Integrable (fun x : X n => kinetic u (x,t)) (mu n) ∧
  (∀ j : Fin n, Integrable (fun x : X n => mixed u j (x,t)) (mu n)) ∧
  (∀ x : X n, dt (density u) (x,t) =
    2 * kinetic u (x,t) + 2 * ∑ j : Fin n, mixed u j (x,t)) := by
  intro t ht
  have hder : HasDerivAt (energy u) (∫ x : X n, dt (density u) (x,t) ∂mu n) t := by
    apply hasDerivAt_iff_tendsto_slope_zero.mpr
    have hlim : Tendsto (fun h : ℝ => (energy u (t+h) - energy u t)/h)
        (nhdsWithin 0 ({0}ᶜ)) (nhds (∫ x : X n, dt (density u) (x,t) ∂mu n)) := by
      apply Filter.tendsto_iff_seq_tendsto.mpr
      intro h hh
      have hh0 : Tendsto h atTop (nhds (0 : ℝ)) :=
        (tendsto_nhdsWithin_iff.mp hh).1
      have hne : ∀ᶠ k in atTop, h k ≠ 0 := by
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
          (tendsto_nhdsWithin_iff.mp hh).2
      have hsmall : ∀ᶠ k in atTop, |h k| < t/4 := by
        have ha : Tendsto (fun k => |h k|) atTop (nhds (0 : ℝ)) := by
          simpa using hh0.abs
        exact ha.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < t/4))
      obtain ⟨N, hN⟩ := eventually_atTop.mp (hne.and hsmall)
      have hs := h_T007 t ht (fun k => h (k+N))
        (fun k => ⟨abs_pos.mpr (hN (k+N) (Nat.le_add_left N k)).1,
          (hN (k+N) (Nat.le_add_left N k)).2⟩)
        (hh0.comp (tendsto_add_atTop_nat N))
      exact (tendsto_add_atTop_iff_nat N).mp hs
    simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using hlim
  obtain ⟨C, R, hw⟩ := h_T004.1 t ht
  have htwin : t ∈ Ioo (t/2) (3*t/2) := by constructor <;> linarith
  have hid : Integrable (fun x : X n => dt (density u) (x,t)) (mu n) :=
    (hw.sections (dt (density u)) (by simp [scalarTerms]) t htwin).2.2
  have hik : Integrable (fun x : X n => kinetic u (x,t)) (mu n) :=
    (hw.sections (kinetic u) (by simp [scalarTerms]) t htwin).2.2
  have him : ∀ j : Fin n, Integrable (fun x : X n => mixed u j (x,t)) (mu n) := by
    intro j
    exact (hw.sections (mixed u j)
      (by
        change _ = density u ∨ _ = dt (density u) ∨ _ = kinetic u ∨ _
        exact Or.inr (Or.inr (Or.inr ⟨j, Or.inl rfl⟩)))
      t htwin).2.2
  have hp : ∀ x : X n, dt (density u) (x,t) =
      2 * kinetic u (x,t) + 2 * ∑ j : Fin n, mixed u j (x,t) :=
    fun x => (h_T005 x t ht).2
  have his : Integrable (fun x : X n => ∑ j : Fin n, mixed u j (x,t)) (mu n) :=
    integrable_finsetSum Finset.univ (fun j _ => him j)
  have heq : (∫ x : X n, dt (density u) (x,t) ∂mu n) =
      2 * (∫ x : X n, kinetic u (x,t) ∂mu n) +
        2 * ∑ j : Fin n, (∫ x : X n, mixed u j (x,t) ∂mu n) := by
    calc
      _ = ∫ x : X n, (2 * kinetic u (x,t) +
          2 * ∑ j : Fin n, mixed u j (x,t)) ∂mu n :=
        integral_congr_ae (Filter.Eventually.of_forall hp)
      _ = _ := by
        rw [integral_add (hik.const_mul 2) (his.const_mul 2),
          integral_const_mul, integral_const_mul,
          integral_finsetSum Finset.univ (fun j _ => him j)]
  exact ⟨hder.differentiableAt, hder.deriv, hder.deriv.trans heq,
    hid, hik, him, hp⟩

#check @T008
#print axioms T008

end Translation
