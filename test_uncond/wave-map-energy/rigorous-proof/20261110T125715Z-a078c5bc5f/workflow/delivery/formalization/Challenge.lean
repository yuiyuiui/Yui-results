import Mathlib
open MeasureTheory Filter Set
open scoped Topology BigOperators ContDiff

abbrev WMX (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev WMZ (n : ℕ) := WMX n × ℝ
def WMOmega (n : ℕ) : Set (WMZ n) := {z | 0 < z.2}
def WMT (n : ℕ) : WMZ n := (0, 1)
noncomputable def WMBasis (n : ℕ) (j : Fin n) : WMX n :=
  EuclideanSpace.basisFun (Fin n) ℝ j
noncomputable def WMS (n : ℕ) (j : Fin n) : WMZ n := (WMBasis n j, 0)
noncomputable def WMV {n m : ℕ} (u : WMZ n → WMX m) (z : WMZ n) : WMX m :=
  fderiv ℝ u z (WMT n)
noncomputable def WMW {n m : ℕ} (u : WMZ n → WMX m) (j : Fin n) (z : WMZ n) : WMX m :=
  fderiv ℝ u z (WMS n j)
noncomputable def WMA {n m : ℕ} (u : WMZ n → WMX m) (z : WMZ n) : WMX m :=
  fderiv ℝ (WMV u) z (WMT n)
noncomputable def WMB {n m : ℕ} (u : WMZ n → WMX m) (j : Fin n) (z : WMZ n) : WMX m :=
  fderiv ℝ (WMW u j) z (WMS n j)
noncomputable def WMMixed {n m : ℕ} (u : WMZ n → WMX m) (j : Fin n) (z : WMZ n) : WMX m :=
  fderiv ℝ (WMV u) z (WMS n j)
noncomputable def WME {n m : ℕ} (u : WMZ n → WMX m) (z : WMZ n) : ℝ :=
  if 0 < z.2 then ‖WMV u z‖ ^ 2 + ∑ j : Fin n, ‖WMW u j z‖ ^ 2 else 0
noncomputable def WMG {n m : ℕ} (u : WMZ n → WMX m) (j : Fin n) (z : WMZ n) : ℝ :=
  if 0 < z.2 then inner ℝ (WMV u z) (WMW u j z) else 0
noncomputable def WMET {n m : ℕ} (u : WMZ n → WMX m) (z : WMZ n) : ℝ :=
  fderiv ℝ (WME u) z (WMT n)
noncomputable def WMGX {n m : ℕ} (u : WMZ n → WMX m) (j : Fin n) (z : WMZ n) : ℝ :=
  fderiv ℝ (WMG u j) z (WMS n j)
noncomputable def WMEnergy {n m : ℕ} (u : WMZ n → WMX m) (t : ℝ) : ℝ :=
  ∫ x : WMX n, WME u (x, t)
inductive WMTerm (n : ℕ) where
  | density | densityTime | kineticPair
  | flux (j : Fin n) | fluxSpace (j : Fin n)
  | mixedPair (j : Fin n) | laplacePair (j : Fin n)
noncomputable def WMField {n m : ℕ} (u : WMZ n → WMX m) : WMTerm n → WMZ n → ℝ
  | .density => WME u
  | .densityTime => WMET u
  | .kineticPair => fun z => inner ℝ (WMV u z) (WMA u z)
  | .flux j => WMG u j
  | .fluxSpace j => WMGX u j
  | .mixedPair j => fun z => inner ℝ (WMW u j z) (WMMixed u j z)
  | .laplacePair j => fun z => inner ℝ (WMV u z) (WMB u j z)

namespace YuiClosed
set_option autoImplicit false
theorem P : ∀ (n : ℕ) (m : ℕ) (u : WMZ n → WMX m) (q : WMX m) (h_H001 : 1 ≤ n ∧ 1 ≤ m ∧ ContDiffOn ℝ ∞ u (WMOmega n)) (h_H002 : ‖q‖ = 1) (h_H003 : ∀ (x : WMX n) (t : ℝ), 0 < t → ‖u (x, t)‖ = 1) (h_H004 : ∀ (x : WMX n) (t : ℝ), 0 < t → ∃ a : ℝ, WMA u (x, t) - (∑ j : Fin n, WMB u j (x, t)) = a • u (x, t)) (h_H005 : ∀ s t : ℝ, 0 < s → s < t → ∃ C : Set (WMX n), IsCompact C ∧ ∀ (x : WMX n) (r : ℝ), x ∉ C → r ∈ Icc s t → u (x, r) = q), ∀ t : ℝ, 0 < t → Integrable (fun x : WMX n => WME u (x, t)) ∧ HasDerivAt (WMEnergy u) 0 t := by sorry
end YuiClosed
