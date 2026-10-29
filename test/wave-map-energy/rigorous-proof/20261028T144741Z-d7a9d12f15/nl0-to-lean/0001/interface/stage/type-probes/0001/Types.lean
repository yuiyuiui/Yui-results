import Mathlib
open MeasureTheory Set Filter
noncomputable abbrev WSpace (n : ℕ) := Fin n → ℝ
noncomputable abbrev WTarget (m : ℕ) := EuclideanSpace ℝ (Fin m)
noncomputable def wDx {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : WSpace n → F) (j : Fin n) (x : WSpace n) : F := fderiv ℝ f x (Pi.single j 1)
noncomputable def wT {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : WSpace n × ℝ → F) (p : WSpace n × ℝ) : F := deriv (fun r => f (p.1,r)) p.2
noncomputable def wX {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : WSpace n × ℝ → F) (j : Fin n) (p : WSpace n × ℝ) : F := wDx (fun x => f (x,p.2)) j p.1
noncomputable def wLap {n m : ℕ} (u : WSpace n × ℝ → WTarget m) (p : WSpace n × ℝ) : WTarget m := ∑ j : Fin n, wX (wX u j) j p
noncomputable def wDensity {n m : ℕ} (u : WSpace n × ℝ → WTarget m) (p : WSpace n × ℝ) : ℝ := ‖wT u p‖^2 + ∑ j : Fin n, ‖wX u j p‖^2
noncomputable def wEnergy {n m : ℕ} (u : WSpace n × ℝ → WTarget m) (t : ℝ) : ℝ := ∫ x : WSpace n, wDensity u (x,t)
def wDomain (n : ℕ) : Set (WSpace n × ℝ) := {p | 0 < p.2}
def wBox (n : ℕ) (R : ℝ) : Set (WSpace n) := Set.Icc (fun _ => -R) (fun _ => R)
def wOpenBox (n : ℕ) (R : ℝ) : Set (WSpace n) := {x | ∀ j, -R < x j ∧ x j < R}

set_option autoImplicit false
#check (fun (n : ℕ) (m : ℕ) (u : WSpace n × ℝ → WTarget m) => ContDiffOn ℝ ∞ u (wDomain n))
#check (fun (n : ℕ) (m : ℕ) (u : WSpace n × ℝ → WTarget m) => ∀ (k : ℕ) (x : WSpace n) (r : ℝ), 0 < k → iteratedFDeriv ℝ k u (x,r) = 0)
#check (fun (n : ℕ) (m : ℕ) (u : WSpace n × ℝ → WTarget m) => ∀ R : ℝ, volume (wBox n R) = ENNReal.ofReal ((2*R)^n))
#check (fun (n : ℕ) (m : ℕ) (u : WSpace n × ℝ → WTarget m) => ∀ t : ℝ, HasDerivAt (wEnergy u) (∫ x : WSpace n, wT (wDensity u) (x,t)) t)
#check (fun (n : ℕ) (m : ℕ) (u : WSpace n × ℝ → WTarget m) => ∀ t : ℝ, Filter.Tendsto (fun h : ℝ => ∫ x : WSpace n, (wDensity u (x,t+h)-wDensity u (x,t))/h) (nhdsWithin 0 ({0}ᶜ)) (nhds (∫ x : WSpace n, wT (wDensity u) (x,t))))
