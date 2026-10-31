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

theorem T012 (n : ℕ) (m : ℕ) (u : X n × ℝ → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ u (domain n)) (h_T004 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (X n), ∃ R : ℝ, Window u q t0 C R) ∧
  ContDiffOn ℝ ∞ (density u) (domain n) ∧
  ContDiffOn ℝ ∞ (dt (density u)) (domain n) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : X n => density u (x,t)) (mu n))) (h_T009 : ∀ t0 : ℝ, 0 < t0 → ∀ j : Fin n,
  ContDiff ℝ ∞ (fun x : X n => flux u j (x,t0)) ∧
  (∀ x : X n, dx (flux u j) j (x,t0) =
    inner ℝ (dx (dt u) j (x,t0)) (dx u j (x,t0)) + lapTerm u j (x,t0)) ∧
  (∀ x : X n, HasDerivAt (fun z : ℝ => flux u j (Function.update x j z,t0))
    (dx (flux u j) j (x,t0)) (x j)) ∧
  (∀ C : Set (X n), ∀ R : ℝ, Window u q t0 C R →
    ∀ x : X n, x j = -R ∨ x j = R → flux u j (x,t0) = 0)) (h_T011 : ∀ t0 : ℝ, 0 < t0 → ∀ j : Fin n,
  ∀ C : Set (X n), ∀ R : ℝ, Window u q t0 C R →
  MeasurePreserving (insert j)
    (((otherMu j).restrict (otherBox j R)).prod (volume.restrict (Icc (-R) R)))
    ((mu n).restrict (box R)) ∧
  (∫ x in box R, dx (flux u j) j (x,t0) ∂mu n) = 0) :
    ∀ t : ℝ, 0 < t → ∀ j : Fin n,
  (∫ x : X n, mixed u j (x,t) ∂mu n) = -(∫ x : X n, lapTerm u j (x,t) ∂mu n) ∧
  Integrable (fun x : X n => mixed u j (x,t)) (mu n) ∧
  Integrable (fun x : X n => lapTerm u j (x,t)) (mu n) := by
  intro t ht j
  obtain ⟨C, R, hW⟩ := h_T004.1 t ht
  have htime : t ∈ Ioo (t / 2) (3 * t / 2) := by
    constructor <;> linarith
  have hm_mem : mixed u j ∈ scalarTerms u := by
    change mixed u j = density u ∨ mixed u j = dt (density u) ∨
      mixed u j = kinetic u ∨ ∃ k : Fin n,
        mixed u j = mixed u k ∨ mixed u j = lapTerm u k ∨
          mixed u j = flux u k ∨ mixed u j = dx (flux u k) k
    exact Or.inr (Or.inr (Or.inr ⟨j, Or.inl rfl⟩))
  have hl_mem : lapTerm u j ∈ scalarTerms u := by
    change lapTerm u j = density u ∨ lapTerm u j = dt (density u) ∨
      lapTerm u j = kinetic u ∨ ∃ k : Fin n,
        lapTerm u j = mixed u k ∨ lapTerm u j = lapTerm u k ∨
          lapTerm u j = flux u k ∨ lapTerm u j = dx (flux u k) k
    exact Or.inr (Or.inr (Or.inr ⟨j, Or.inr (Or.inl rfl)⟩))
  have hd_mem : dx (flux u j) j ∈ scalarTerms u := by
    change dx (flux u j) j = density u ∨ dx (flux u j) j = dt (density u) ∨
      dx (flux u j) j = kinetic u ∨ ∃ k : Fin n,
        dx (flux u j) j = mixed u k ∨ dx (flux u j) j = lapTerm u k ∨
          dx (flux u j) j = flux u k ∨ dx (flux u j) j = dx (flux u k) k
    exact Or.inr (Or.inr (Or.inr ⟨j, Or.inr (Or.inr (Or.inr rfl))⟩))
  have hm : Integrable (fun x : X n => mixed u j (x,t)) (mu n) :=
    (hW.sections (mixed u j) hm_mem t htime).2.2
  have hl : Integrable (fun x : X n => lapTerm u j (x,t)) (mu n) :=
    (hW.sections (lapTerm u j) hl_mem t htime).2.2
  have hCbox : C ⊆ box R := by
    intro x hx
    exact fun k => ⟨(hW.inside x hx k).1.le, (hW.inside x hx k).2.le⟩
  have hzero : ∀ x : X n, x ∉ box R → dx (flux u j) j (x,t) = 0 := by
    intro x hx
    exact (hW.sections (dx (flux u j) j) hd_mem t htime).2.1 x
      (fun hxC => hx (hCbox hxC))
  have hfull : (∫ x : X n, dx (flux u j) j (x,t) ∂mu n) = 0 := by
    calc
      (∫ x : X n, dx (flux u j) j (x,t) ∂mu n) =
          ∫ x in box R, dx (flux u j) j (x,t) ∂mu n :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
      _ = 0 := (h_T011 t ht j C R hW).2
  have hprod : ∀ x : X n, dx (flux u j) j (x,t) =
      mixed u j (x,t) + lapTerm u j (x,t) := by
    intro x
    rw [(h_T009 t ht j).2.1 x]
    unfold mixed
    rw [real_inner_comm (dx u j (x,t)) (dx (dt u) j (x,t))]
  have hsum : (∫ x : X n, mixed u j (x,t) ∂mu n) +
      (∫ x : X n, lapTerm u j (x,t) ∂mu n) = 0 := by
    calc
      (∫ x : X n, mixed u j (x,t) ∂mu n) +
          (∫ x : X n, lapTerm u j (x,t) ∂mu n) =
          ∫ x : X n, mixed u j (x,t) + lapTerm u j (x,t) ∂mu n :=
        (integral_add hm hl).symm
      _ = ∫ x : X n, dx (flux u j) j (x,t) ∂mu n :=
        integral_congr_ae (Filter.Eventually.of_forall (fun x => (hprod x).symm))
      _ = 0 := hfull
  exact ⟨by linarith, hm, hl⟩

#check @T012
#print axioms T012

end Translation
