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

theorem T005 (n : ℕ) (m : ℕ) (u : X n × ℝ → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ u (domain n)) (h_T004 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (X n), ∃ R : ℝ, Window u q t0 C R) ∧
  ContDiffOn ℝ ∞ (density u) (domain n) ∧
  ContDiffOn ℝ ∞ (dt (density u)) (domain n) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : X n => density u (x,t)) (mu n))) :
    ∀ x : X n, ∀ t : ℝ, 0 < t →
  HasDerivAt (fun r : ℝ => density u (x,r)) (dt (density u) (x,t)) t ∧
  dt (density u) (x,t) = 2 * kinetic u (x,t) + 2 * ∑ j : Fin n, mixed u j (x,t) := by
  have repr : ∀ (f : X n × ℝ → V m) (p : X n × ℝ),
      DifferentiableAt ℝ f p →
      dt f p = fderiv ℝ f p (0, 1) ∧
      ∀ j, dx f j p = fderiv ℝ f p (Pi.single j 1, 0) := by
    intro f p hf
    have ht := hf.hasFDerivAt.comp_hasDerivAt p.2
      ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
    refine ⟨ht.deriv, ?_⟩
    intro j
    have hs := hf.hasFDerivAt.comp p.1
      ((hasFDerivAt_id (𝕜 := ℝ) p.1).prodMk (hasFDerivAt_const p.2 p.1))
    exact congrArg (fun L : X n →L[ℝ] V m => L (Pi.single j 1)) hs.fderiv
  have hopen : IsOpen (domain n) := isOpen_lt continuous_const continuous_snd
  have hc : ∀ p : X n × ℝ, 0 < p.2 → ContDiffAt ℝ ∞ u p := by
    intro p hp
    exact h_H002.contDiffAt (hopen.mem_nhds hp)
  have hd : ∀ p : X n × ℝ, 0 < p.2 → DifferentiableAt ℝ u p :=
    fun p hp => (hc p hp).differentiableAt (by simp)
  have heval : ∀ (p : X n × ℝ), 0 < p.2 → ∀ v : X n × ℝ,
      HasFDerivAt (fun z => fderiv ℝ u z v)
        ((fderiv ℝ (fderiv ℝ u) p).flip v) p := by
    intro p hp v
    have hD : DifferentiableAt ℝ (fderiv ℝ u) p :=
      ((hc p hp).fderiv_right (m := 1) (by exact WithTop.coe_le_coe.mpr le_top)).differentiableAt one_ne_zero
    simpa only [ContinuousLinearMap.comp_zero, zero_add] using
      hD.hasFDerivAt.clm_apply (hasFDerivAt_const v p)
  have hdt : ∀ p : X n × ℝ, 0 < p.2 →
      HasFDerivAt (dt u) ((fderiv ℝ (fderiv ℝ u) p).flip (0, 1)) p := by
    intro p hp
    apply (heval p hp (0, 1)).congr_of_eventuallyEq
    filter_upwards [hopen.mem_nhds hp] with z hz
    exact (repr u z (hd z hz)).1
  have hdx : ∀ (p : X n × ℝ), 0 < p.2 → ∀ j : Fin n,
      HasFDerivAt (dx u j)
        ((fderiv ℝ (fderiv ℝ u) p).flip (Pi.single j 1, 0)) p := by
    intro p hp j
    apply (heval p hp (Pi.single j 1, 0)).congr_of_eventuallyEq
    filter_upwards [hopen.mem_nhds hp] with z hz
    exact (repr u z (hd z hz)).2 j
  have hmix : ∀ p : X n × ℝ, 0 < p.2 → ∀ j : Fin n,
      dt (dx u j) p = dx (dt u) j p := by
    intro p hp j
    calc
      dt (dx u j) p = fderiv ℝ (dx u j) p (0,1) :=
        (repr (dx u j) p (hdx p hp j).differentiableAt).1
      _ = fderiv ℝ (fderiv ℝ u) p (0,1) (Pi.single j 1,0) :=
        congrArg (fun L : (X n × ℝ) →L[ℝ] V m => L (0,1)) (hdx p hp j).fderiv
      _ = fderiv ℝ (fderiv ℝ u) p (Pi.single j 1,0) (0,1) :=
        ((hc p hp).isSymmSndFDerivAt (by
          simp only [minSmoothness, if_pos (show IsRCLikeNormedField ℝ from inferInstance)]
          exact WithTop.coe_le_coe.mpr le_top)).eq _ _
      _ = fderiv ℝ (dt u) p (Pi.single j 1,0) :=
        (congrArg (fun L : (X n × ℝ) →L[ℝ] V m => L (Pi.single j 1,0))
          (hdt p hp).fderiv).symm
      _ = dx (dt u) j p :=
        ((repr (dt u) p (hdt p hp).differentiableAt).2 j).symm
  have hsection : ∀ (f : X n × ℝ → V m) (p : X n × ℝ),
      DifferentiableAt ℝ f p →
      HasDerivAt (fun r => f (p.1,r)) (dt f p) p.2 := by
    intro f p hf
    rw [(repr f p hf).1]
    exact hf.hasFDerivAt.comp_hasDerivAt p.2
      ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
  intro x t ht
  have hv := (hsection (dt u) (x,t) (hdt (x,t) ht).differentiableAt).norm_sq
  have hs : ∀ j : Fin n, HasDerivAt (fun r => ‖dx u j (x,r)‖ ^ 2)
      (2 * mixed u j (x,t)) t := by
    intro j
    have hj := (hsection (dx u j) (x,t) (hdx (x,t) ht j).differentiableAt).norm_sq
    rw [hmix (x,t) ht j] at hj
    exact hj
  have hall : HasDerivAt (fun r => density u (x,r))
      (2 * kinetic u (x,t) + 2 * ∑ j : Fin n, mixed u j (x,t)) t := by
    simpa only [density, kinetic, Finset.mul_sum, Pi.add_def] using
      hv.add (HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => hs j))
  have heq : dt (density u) (x,t) =
      2 * kinetic u (x,t) + 2 * ∑ j : Fin n, mixed u j (x,t) := hall.deriv
  exact ⟨by rw [heq]; exact hall, heq⟩

#check @T005
#print axioms T005

end Translation
