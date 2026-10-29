import Mathlib
open MeasureTheory Set Filter
open scoped ContDiff
noncomputable abbrev WSpace (n : ℕ) := Fin n → ℝ
def wBox (n : ℕ) (R : ℝ) : Set (WSpace n) := Set.Icc (fun _ => -R) (fun _ => R)

set_option autoImplicit false
#check (fun (n : ℕ) (m : ℕ) => ∀ (f : WSpace n × ℝ → EuclideanSpace ℝ (Fin m)), ContDiffOn ℝ ∞ f {p | 0 < p.2})
#check (fun (n : ℕ) (m : ℕ) => ∀ (d : ℕ) (j : Fin (d+1)) (R : ℝ), MeasureTheory.MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => ℝ) j) (volume.restrict (wBox (d+1) R)) ((volume.restrict (Set.Icc (-R) R)).prod (volume.restrict (wBox d R))))
