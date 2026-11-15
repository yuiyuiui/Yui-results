import Mathlib
open MeasureTheory Set Filter
open scoped Topology ContDiff BigOperators

namespace WaveEnergy
abbrev X (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev V (m : ℕ) := EuclideanSpace ℝ (Fin m)
abbrev Z (n : ℕ) := X n × ℝ
def omega (n : ℕ) : Set (Z n) := {z | 0 < z.2}
def tau (n : ℕ) : Z n := (0, 1)
noncomputable def basis (n : ℕ) (j : Fin n) : X n := EuclideanSpace.single j 1
noncomputable def sigma (n : ℕ) (j : Fin n) : Z n := (basis n j, 0)
noncomputable def D {n : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (v : Z n) (f : Z n → F) (z : Z n) : F := fderiv ℝ f z v
noncomputable def ordered {n m : ℕ} (U : Z n → V m) : List (Z n) → Z n → V m
  | [] => U
  | v :: vs => D v (ordered U vs)
noncomputable def ut {n m : ℕ} (U : Z n → V m) := D (tau n) U
noncomputable def uj {n m : ℕ} (U : Z n → V m) (j : Fin n) := D (sigma n j) U
noncomputable def utt {n m : ℕ} (U : Z n → V m) := D (tau n) (ut U)
noncomputable def ujj {n m : ℕ} (U : Z n → V m) (j : Fin n) := D (sigma n j) (uj U j)
noncomputable def utj {n m : ℕ} (U : Z n → V m) (j : Fin n) := D (sigma n j) (ut U)
noncomputable def lap {n m : ℕ} (U : Z n → V m) (z : Z n) := ∑ j, ujj U j z
noncomputable def density {n m : ℕ} (U : Z n → V m) (z : Z n) : ℝ :=
  ‖ut U z‖ ^ 2 + ∑ j, ‖uj U j z‖ ^ 2
noncomputable def energy {n m : ℕ} (U : Z n → V m) (t : ℝ) : ℝ :=
  ∫ x, density U (x, t)
noncomputable def timeProd {n m : ℕ} (U : Z n → V m) (z : Z n) : ℝ :=
  inner ℝ (ut U z) (utt U z)
noncomputable def gradProd {n m : ℕ} (U : Z n → V m) (j : Fin n) (z : Z n) : ℝ :=
  inner ℝ (uj U j z) (utj U j z)
noncomputable def lapProd {n m : ℕ} (U : Z n → V m) (j : Fin n) (z : Z n) : ℝ :=
  inner ℝ (ut U z) (ujj U j z)
noncomputable def flux {n m : ℕ} (U : Z n → V m) (j : Fin n) (z : Z n) : ℝ :=
  inner ℝ (ut U z) (uj U j z)
noncomputable def densityTime {n m : ℕ} (U : Z n → V m) := D (tau n) (density U)
noncomputable def rate {n m : ℕ} (U : Z n → V m) (z : Z n) : ℝ :=
  2 * timeProd U z + 2 * ∑ j, gradProd U j z
def ScalarField {n m : ℕ} (U : Z n → V m) (f : Z n → ℝ) : Prop :=
  f = density U ∨ f = densityTime U ∨ f = timeProd U ∨
    ∃ j, f = gradProd U j ∨ f = lapProd U j ∨ f = flux U j
def SectionFacts {n : ℕ} {F : Type} [NormedAddCommGroup F]
    (f : Z n → F) (C : Set (X n)) (r : ℝ) : Prop :=
  Continuous (fun x => f (x, r)) ∧
  tsupport (fun x => f (x, r)) ⊆ C ∧
  HasCompactSupport (fun x => f (x, r)) ∧
  Integrable (fun x => f (x, r)) volume
def Regular {n m : ℕ} (U : Z n → V m) : Prop :=
  (∀ ds, ContDiffOn ℝ ∞ (ordered U ds) (omega n)) ∧
  (∀ k : ℕ, ContDiffOn ℝ ∞ (iteratedFDeriv ℝ k U) (omega n)) ∧
  (∀ f, ScalarField U f → ContDiffOn ℝ ∞ f (omega n))
def Localized {n m : ℕ} (U : Z n → V m) (C : Set (X n)) (r : ℝ) : Prop :=
  (∀ ds, ds ≠ [] →
    (∀ x, x ∉ C → ordered U ds (x, r) = 0) ∧ SectionFacts (ordered U ds) C r) ∧
  (∀ k : ℕ, 0 < k →
    (∀ x, x ∉ C → iteratedFDeriv ℝ k U (x, r) = 0) ∧
      SectionFacts (iteratedFDeriv ℝ k U) C r) ∧
  (∀ f, ScalarField U f →
    (∀ x, x ∉ C → f (x, r) = 0) ∧ SectionFacts f C r)
def LocalData {n m : ℕ} (U : Z n → V m) : Prop :=
  ∀ t₀ : ℝ, 0 < t₀ → ∃ C : Set (X n), IsCompact C ∧
    ∀ r ∈ Ioo (t₀ / 2) (3 * t₀ / 2), Localized U C r
end WaveEnergy
open WaveEnergy

namespace YuiClosed
set_option autoImplicit false
theorem P : ∀ (n : ℕ) (m : ℕ) (U : Z n → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m ∧ ‖q‖ = 1 ∧ ContDiffOn ℝ ∞ U (omega n)) (h_H002 : ∀ x : X n, ∀ t : ℝ, 0 < t → ‖U (x, t)‖ = 1 ∧ ∃ a : ℝ, utt U (x, t) - lap U (x, t) = a • U (x, t)) (h_H003 : ∀ s t : ℝ, 0 < s → s < t → ∃ C : Set (X n), IsCompact C ∧ ∀ x : X n, x ∉ C → ∀ r ∈ Icc s t, U (x, r) = q), ∀ t : ℝ, 0 < t → Integrable (fun x : X n => density U (x, t)) volume ∧ DifferentiableAt ℝ (energy U) t ∧ deriv (energy U) t = 0 := by sorry
end YuiClosed
