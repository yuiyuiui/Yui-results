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
theorem yui_aux_0001 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_T004 : (∀ t : ℝ, 0 < t → ∃ C : Set (WaveMap.X n), ∃ R : ℝ,
    WaveMap.supportGeometry u q t C R ∧ WaveMap.supportSections u t C R) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : WaveMap.X n => WaveMap.density u (x, t))) ∧
  ContinuousOn (WaveMap.density u) (WaveMap.domain n) ∧
  ContinuousOn (WaveMap.densityT u) (WaveMap.domain n)) (h_T005 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t →
  HasDerivAt (fun r : ℝ => WaveMap.density u (x, r)) (WaveMap.densityT u (x, t)) t ∧
  WaveMap.densityT u (x, t) =
    2 * WaveMap.timeProduct u (x, t) + 2 * ∑ j : Fin n, WaveMap.mixedProduct u j (x, t)) (h_T006 : ∀ t : ℝ, 0 < t → ∃ η B R : ℝ,
  0 < η ∧ 0 ≤ B ∧ 0 < R ∧ η < t ∧
  Integrable ((WaveMap.box n R).indicator (fun _ => B)) ∧
  ∀ h : ℝ, 0 < |h| → |h| < η → ∀ x : WaveMap.X n,
    |WaveMap.quotient u t h x| ≤ (WaveMap.box n R).indicator (fun _ => B) x) : yui_aux_type% "∀ t : ℝ, 0 < t → ∀ h : ℝ, 0 < t + h → Continuous (WaveMap.quotient u t h) ∧ Integrable (WaveMap.quotient u t h) ∧ (∫ x : WaveMap.X n, WaveMap.quotient u t h x) = (WaveMap.energy u (t + h) - WaveMap.energy u t) / h" := by
  intro t ht h hth
  have hc : ∀ r : ℝ, 0 < r → Continuous (fun x : WaveMap.X n => WaveMap.density u (x, r)) := by
    intro r hr
    exact h_T004.2.2.1.comp_continuous (continuous_id.prodMk continuous_const) (fun x => hr)
  refine ⟨((hc (t+h) hth).sub (hc t ht)).div_const h, ((h_T004.2.1 (t+h) hth).sub (h_T004.2.1 t ht)).div_const h, ?_⟩
  unfold WaveMap.quotient
  rw [MeasureTheory.integral_div, MeasureTheory.integral_sub (h_T004.2.1 (t+h) hth) (h_T004.2.1 t ht)]
  rfl

theorem checked (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_T004 : (∀ t : ℝ, 0 < t → ∃ C : Set (WaveMap.X n), ∃ R : ℝ,
    WaveMap.supportGeometry u q t C R ∧ WaveMap.supportSections u t C R) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : WaveMap.X n => WaveMap.density u (x, t))) ∧
  ContinuousOn (WaveMap.density u) (WaveMap.domain n) ∧
  ContinuousOn (WaveMap.densityT u) (WaveMap.domain n)) (h_T005 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t →
  HasDerivAt (fun r : ℝ => WaveMap.density u (x, r)) (WaveMap.densityT u (x, t)) t ∧
  WaveMap.densityT u (x, t) =
    2 * WaveMap.timeProduct u (x, t) + 2 * ∑ j : Fin n, WaveMap.mixedProduct u j (x, t)) (h_T006 : ∀ t : ℝ, 0 < t → ∃ η B R : ℝ,
  0 < η ∧ 0 ≤ B ∧ 0 < R ∧ η < t ∧
  Integrable ((WaveMap.box n R).indicator (fun _ => B)) ∧
  ∀ h : ℝ, 0 < |h| → |h| < η → ∀ x : WaveMap.X n,
    |WaveMap.quotient u t h x| ≤ (WaveMap.box n R).indicator (fun _ => B) x) : yui_aux_type% "∀ t : ℝ, 0 < t → ∀ η B R : ℝ, η < t → Integrable ((WaveMap.box n R).indicator (fun _ => B)) → (∀ h : ℝ, 0 < |h| → |h| < η → ∀ x : WaveMap.X n, |WaveMap.quotient u t h x| ≤ (WaveMap.box n R).indicator (fun _ => B) x) → ∀ a : ℕ → ℝ, (∀ k, 0 < |a k| ∧ |a k| < η) → Tendsto a atTop (𝓝 (0 : ℝ)) → Tendsto (fun k => (WaveMap.energy u (t + a k) - WaveMap.energy u t) / a k) atTop (𝓝 (∫ x : WaveMap.X n, WaveMap.densityT u (x,t)))" := by
  intro t ht η B R hηt hb hbound a ha halim
  have hpos : ∀ k, 0 < t + a k := by
    intro k
    have hlow := neg_abs_le (a k)
    have hu := (ha k).2
    linarith
  have hane : ∀ k, a k ≠ 0 := fun k => abs_pos.mp (ha k).1
  have haneLim : Tendsto a atTop (𝓝[≠] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨halim, Filter.Eventually.of_forall (fun k => hane k)⟩
  have hd : Tendsto (fun k => ∫ x : WaveMap.X n, WaveMap.quotient u t (a k) x) atTop (𝓝 (∫ x : WaveMap.X n, WaveMap.densityT u (x,t))) := by
    apply MeasureTheory.tendsto_integral_of_dominated_convergence ((WaveMap.box n R).indicator (fun _ => B))
    · intro k
      exact ((yui_aux_0001 n m u q h_H001 h_H002 h_T004 h_T005 h_T006 t ht (a k) (hpos k)).1).aestronglyMeasurable
    · exact hb
    · intro k
      exact Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hbound (a k) (ha k).1 (ha k).2 x)
    · apply Filter.Eventually.of_forall
      intro x
      have hx := ((h_T005 x t ht).1.tendsto_slope_zero).comp haneLim
      simpa only [WaveMap.quotient, smul_eq_mul, div_eq_mul_inv, mul_comm] using hx
  have hid : (fun k => ∫ x : WaveMap.X n, WaveMap.quotient u t (a k) x) = (fun k => (WaveMap.energy u (t + a k) - WaveMap.energy u t) / a k) := by
    funext k
    exact (yui_aux_0001 n m u q h_H001 h_H002 h_T004 h_T005 h_T006 t ht (a k) (hpos k)).2.2
  rw [hid] at hd
  exact hd
#check @checked
#print axioms checked
end YuiAuxiliary
