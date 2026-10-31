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

theorem T009 (n : ℕ) (m : ℕ) (u : X n × ℝ → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ u (domain n)) (h_T004 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (X n), ∃ R : ℝ, Window u q t0 C R) ∧
  ContDiffOn ℝ ∞ (density u) (domain n) ∧
  ContDiffOn ℝ ∞ (dt (density u)) (domain n) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : X n => density u (x,t)) (mu n))) :
    ∀ t0 : ℝ, 0 < t0 → ∀ j : Fin n,
  ContDiff ℝ ∞ (fun x : X n => flux u j (x,t0)) ∧
  (∀ x : X n, dx (flux u j) j (x,t0) =
    inner ℝ (dx (dt u) j (x,t0)) (dx u j (x,t0)) + lapTerm u j (x,t0)) ∧
  (∀ x : X n, HasDerivAt (fun z : ℝ => flux u j (Function.update x j z,t0))
    (dx (flux u j) j (x,t0)) (x j)) ∧
  (∀ C : Set (X n), ∀ R : ℝ, Window u q t0 C R →
    ∀ x : X n, x j = -R ∨ x j = R → flux u j (x,t0) = 0) := by
  intro t0 ht0 j
  have hopen : IsOpen (domain n) := isOpen_lt continuous_const continuous_snd
  have hu : ∀ x : X n, ContDiffAt ℝ ∞ u (x,t0) :=
    fun x => h_H002.contDiffAt (hopen.mem_nhds ht0)
  have hut : ContDiff ℝ ∞ (fun x : X n => dt u (x,t0)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    have hf : ContDiffAt ℝ ∞ (Function.uncurry (fun (y : X n) (r : ℝ) => u (y,r))) (x,t0) := hu x
    have hd : ContDiffAt ℝ ∞ (fun y : X n => fderiv ℝ (fun r : ℝ => u (y,r)) t0) x :=
      hf.fderiv (g := fun _ : X n => t0) contDiffAt_const (by simp)
    simpa only [dt, fderiv_apply_one_eq_deriv] using
      hd.clm_apply (contDiffAt_const (c := (1 : ℝ)))
  have hus : ContDiff ℝ ∞ (fun x : X n => u (x,t0)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    exact (hu x).comp x (contDiffAt_id.prodMk contDiffAt_const)
  have hux : ContDiff ℝ ∞ (fun x : X n => dx u j (x,t0)) := by
    exact (hus.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hg : ContDiff ℝ ∞ (fun x : X n => flux u j (x,t0)) :=
    hut.inner ℝ hux
  refine ⟨hg, ?_, ?_, ?_⟩
  · intro x
    have ht : DifferentiableAt ℝ (fun y : X n => dt u (y,t0)) x :=
      hut.differentiable (by simp) x
    have hx : DifferentiableAt ℝ (fun y : X n => dx u j (y,t0)) x :=
      hux.differentiable (by simp) x
    simpa only [dx, flux, lapTerm, add_comm] using
      fderiv_inner_apply ℝ ht hx (Pi.single j 1)
  · intro x
    have hf : HasFDerivAt (fun y : X n => flux u j (y,t0))
        (fderiv ℝ (fun y : X n => flux u j (y,t0)) x) x :=
      (hg.differentiable (by simp) x).hasFDerivAt
    have hc := hf.comp_hasDerivAt_of_eq (hasDerivAt_update x j (x j))
      (by simp : x = Function.update x j (x j))
    simpa only [Function.comp_def, dx] using hc
  · intro C R hw x hx
    have hnot : x ∉ C := by
      intro hmem
      have hi := hw.inside x hmem j
      rcases hx with hx | hx
      · rw [hx] at hi
        exact (lt_irrefl (-R)) hi.1
      · rw [hx] at hi
        exact (lt_irrefl R) hi.2
    have htime : t0 ∈ Ioo (t0 / 2) (3 * t0 / 2) := by
      constructor <;> linarith
    have hflux : flux u j ∈ scalarTerms u := by
      exact Or.inr (Or.inr (Or.inr ⟨j, Or.inr (Or.inr (Or.inl rfl))⟩))
    exact (hw.sections (flux u j) hflux t0 htime).2.1 x hnot

#check @T009
#print axioms T009

end Translation
