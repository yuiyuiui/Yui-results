import Mathlib
open scoped Topology ContDiff
open MeasureTheory Filter
namespace WaveMapEnergy
abbrev Space (n : ℕ) := Fin n → ℝ
abbrev Value (m : ℕ) := Fin m → ℝ
def dot {m : ℕ} (v w : Value m) : ℝ := ∑ k, v k * w k
def normSq {m : ℕ} (v : Value m) : ℝ := dot v v
noncomputable def velocity {n m : ℕ} (u : Space n × ℝ → Value m)
    (x : Space n) (t : ℝ) : Value m :=
  fun k => deriv (fun r => u (x, r) k) t
noncomputable def acceleration {n m : ℕ} (u : Space n × ℝ → Value m)
    (x : Space n) (t : ℝ) : Value m :=
  fun k => deriv (fun r => velocity u x r k) t
noncomputable def spatial {n m : ℕ} (u : Space n × ℝ → Value m)
    (j : Fin n) (x : Space n) (t : ℝ) : Value m :=
  fun k => fderiv ℝ (fun y => u (y, t) k) x (Pi.single j 1)
noncomputable def spatialSecond {n m : ℕ} (u : Space n × ℝ → Value m)
    (j : Fin n) (x : Space n) (t : ℝ) : Value m :=
  fun k => fderiv ℝ (fun y => spatial u j y t k) x (Pi.single j 1)
noncomputable def laplacian {n m : ℕ} (u : Space n × ℝ → Value m)
    (x : Space n) (t : ℝ) : Value m := ∑ j, spatialSecond u j x t
noncomputable def density {n m : ℕ} (u : Space n × ℝ → Value m)
    (x : Space n) (t : ℝ) : ℝ :=
  normSq (velocity u x t) + ∑ j, normSq (spatial u j x t)
noncomputable def energy {n m : ℕ} (u : Space n × ℝ → Value m) (t : ℝ) : ℝ :=
  ∫ x, density u x t
def Smooth {n m : ℕ} (u : Space n × ℝ → Value m) : Prop :=
  ContDiffOn ℝ ∞ u {p | 0 < p.2}
def UnitValued {n m : ℕ} (u : Space n × ℝ → Value m) : Prop :=
  ∀ x t, 0 < t → normSq (u (x, t)) = 1
def Normal {n m : ℕ} (u : Space n × ℝ → Value m) : Prop :=
  ∀ x t, 0 < t → ∃ a : ℝ, acceleration u x t - laplacian u x t = a • u (x, t)
def CompactPerturbation {n m : ℕ} (u : Space n × ℝ → Value m) (q : Value m) : Prop :=
  ∀ s t : ℝ, 0 < s → s < t → ∃ C : Set (Space n), IsCompact C ∧
    ∀ x r, x ∉ C → r ∈ Set.Icc s t → u (x, r) = q
end WaveMapEnergy

namespace WaveMapEnergy
noncomputable def ubar {n m : ℕ}
    (u : Space n × Set.Ioi (0 : ℝ) → Value m) (q : Value m)
    (p : Space n × ℝ) : Value m :=
  if h : 0 < p.2 then u (p.1, ⟨p.2, h⟩) else q
noncomputable def mixed {n m : ℕ} (v : Space n × ℝ → Value m)
    (j : Fin n) (x : Space n) (t : ℝ) : Value m :=
  fun k => fderiv ℝ (fun y => velocity v y t k) x (Pi.single j 1)
noncomputable def densityRate {n m : ℕ} (v : Space n × ℝ → Value m)
    (x : Space n) (t : ℝ) : ℝ :=
  2 * dot (velocity v x t) (acceleration v x t) +
    2 * ∑ j, dot (spatial v j x t) (mixed v j x t)
def FirstCalculus {n m : ℕ} (v : Space n × ℝ → Value m) : Prop :=
  Smooth v ∧
  ContDiffOn ℝ ∞ (fun p : Space n × ℝ => velocity v p.1 p.2) {p | 0 < p.2} ∧
  (∀ j : Fin n, ContDiffOn ℝ ∞
    (fun p : Space n × ℝ => spatial v j p.1 p.2) {p | 0 < p.2}) ∧
  (∀ (x : Space n) (t : ℝ), 0 < t → ∀ k : Fin m,
    HasDerivAt (fun r => v (x,r) k) (velocity v x t k) t) ∧
  (∀ (x : Space n) (t : ℝ), 0 < t → ∀ k : Fin m,
    HasFDerivAt (fun y => v (y,t) k) (fderiv ℝ (fun y => v (y,t) k) x) x)
def SecondCalculus {n m : ℕ} (v : Space n × ℝ → Value m) : Prop :=
  ContDiffOn ℝ ∞ (fun p : Space n × ℝ => acceleration v p.1 p.2) {p | 0 < p.2} ∧
  (∀ j : Fin n, ContDiffOn ℝ ∞
    (fun p : Space n × ℝ => spatialSecond v j p.1 p.2) {p | 0 < p.2}) ∧
  (∀ j : Fin n, ContDiffOn ℝ ∞
    (fun p : Space n × ℝ => mixed v j p.1 p.2) {p | 0 < p.2}) ∧
  (∀ (x : Space n) (t : ℝ), 0 < t → ∀ k : Fin m,
    HasDerivAt (fun r => velocity v x r k) (acceleration v x t k) t) ∧
  (∀ (j : Fin n) (x : Space n) (t : ℝ), 0 < t → ∀ k : Fin m,
    HasDerivAt (fun r => spatial v j x r k) (mixed v j x t k) t) ∧
  (∀ (j : Fin n) (x : Space n) (t : ℝ), 0 < t → ∀ k : Fin m,
    HasFDerivAt (fun y => velocity v y t k)
      (fderiv ℝ (fun y => velocity v y t k) x) x ∧
    HasFDerivAt (fun y => spatial v j y t k)
      (fderiv ℝ (fun y => spatial v j y t k) x) x)
noncomputable def sections {n m : ℕ} (v : Space n × ℝ → Value m)
    (t : ℝ) : Set (Space n → ℝ) :=
  {h | h = (fun x => density v x t) ∨ h = (fun x => densityRate v x t) ∨
    (∃ k : Fin m, h = (fun x => velocity v x t k) ∨
      h = (fun x => acceleration v x t k) ∨
      h = (fun x => velocity v x t k * acceleration v x t k)) ∨
    (∃ (j : Fin n) (k : Fin m),
      h = (fun x => spatial v j x t k) ∨
      h = (fun x => spatialSecond v j x t k) ∨
      h = (fun x => mixed v j x t k) ∨
      h = (fun x => spatial v j x t k * mixed v j x t k) ∨
      h = (fun x => velocity v x t k * spatialSecond v j x t k) ∨
      h = (fun x => velocity v x t k * spatial v j x t k) ∨
      h = (fun x => mixed v j x t k * spatial v j x t k)) ∨
    h = (fun x => dot (velocity v x t) (acceleration v x t)) ∨
    (∃ j : Fin n,
      h = (fun x => dot (spatial v j x t) (mixed v j x t)) ∨
      h = (fun x => dot (velocity v x t) (spatialSecond v j x t)) ∨
      h = (fun x => dot (velocity v x t) (spatial v j x t)) ∨
      h = (fun x => dot (mixed v j x t) (spatial v j x t)))}
def SupportedSection {n : ℕ} (C : Set (Space n)) (h : Space n → ℝ) : Prop :=
  Continuous h ∧ tsupport h ⊆ C ∧ HasCompactSupport h ∧ Integrable h
def SlabVanishing {n m : ℕ} (v : Space n × ℝ → Value m) (q : Value m)
    (t₀ : ℝ) (C : Set (Space n)) : Prop :=
  IsCompact C ∧
  (∀ x r, x ∉ C → r ∈ Set.Icc (t₀/2) (3*t₀/2) → v (x,r) = q) ∧
  (∀ (ell : ℕ), 0 < ell → ∀ x r,
    x ∉ C → r ∈ Set.Ioo (t₀/2) (3*t₀/2) → iteratedFDeriv ℝ ell v (x,r) = 0) ∧
  (∀ x r, x ∉ C → r ∈ Set.Ioo (t₀/2) (3*t₀/2) →
    velocity v x r = 0 ∧ acceleration v x r = 0 ∧
    (∀ j, spatial v j x r = 0 ∧ spatialSecond v j x r = 0 ∧ mixed v j x r = 0) ∧
    density v x r = 0 ∧ densityRate v x r = 0)
end WaveMapEnergy
open WaveMapEnergy

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace Translation
set_option autoImplicit false

namespace Local_T001
theorem yui_aux_0001 (n : ℕ) (m : ℕ) (u : Space n × Set.Ioi (0 : ℝ) → Value m) (q : Value m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : Smooth (ubar u q)) : yui_aux_type% "∀ (k : Fin m) (x : Space n) (t : ℝ), DifferentiableAt ℝ (fun p : Space n × ℝ => ubar u q p k) (x,t) → HasDerivAt (fun r => ubar u q (x,r) k) (fderiv ℝ (fun p : Space n × ℝ => ubar u q p k) (x,t) (0,1)) t ∧ HasFDerivAt (fun y => ubar u q (y,t) k) ((fderiv ℝ (fun p : Space n × ℝ => ubar u q p k) (x,t)).comp (ContinuousLinearMap.inl ℝ (Space n) ℝ)) x" := by
  intro k x t hd
  constructor
  · have hc := hd.hasFDerivAt.comp t (hasFDerivAt_prodMk_right (𝕜 := ℝ) x t)
    simpa [Function.comp_def] using hc.hasDerivAt
  · exact hd.hasFDerivAt.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x t)

end Local_T001
open Local_T001 in
theorem T001 (n : ℕ) (m : ℕ) (u : Space n × Set.Ioi (0 : ℝ) → Value m) (q : Value m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : Smooth (ubar u q)) :
    FirstCalculus (ubar u q) := by
  have hs : IsOpen {p : Space n × ℝ | 0 < p.2} := isOpen_lt continuous_const continuous_snd
  have hk : ∀ k : Fin m, ContDiffOn ℝ ∞ (fun p : Space n × ℝ => ubar u q p k) {p | 0 < p.2} := contDiffOn_pi.mp h_H002
  have hd : ∀ (k : Fin m) (x : Space n) (t : ℝ), 0 < t → DifferentiableAt ℝ (fun p : Space n × ℝ => ubar u q p k) (x,t) := by
    intro k x t ht
    exact ((hk k).contDiffAt (hs.mem_nhds ht)).differentiableAt (by simp)
  have hslice := fun k x t ht => (@yui_aux_0001 n m u q h_H001 h_H002 k x t (hd k x t ht))
  have hdf : ∀ k : Fin m, ContDiffOn ℝ ∞ (fderiv ℝ (fun p : Space n × ℝ => ubar u q p k)) {p | 0 < p.2} := by
    intro k
    exact ((contDiffOn_infty_iff_fderiv_of_isOpen hs).mp (hk k)).2
  have hv : ∀ (x : Space n) (t : ℝ), 0 < t → ∀ k : Fin m, velocity (ubar u q) x t k = fderiv ℝ (fun p : Space n × ℝ => ubar u q p k) (x,t) (0,1) := by
    intro x t ht k
    exact (hslice k x t ht).1.deriv
  have hp : ∀ (j : Fin n) (x : Space n) (t : ℝ), 0 < t → ∀ k : Fin m, spatial (ubar u q) j x t k = fderiv ℝ (fun p : Space n × ℝ => ubar u q p k) (x,t) (Pi.single j 1,0) := by
    intro j x t ht k
    change (fderiv ℝ (fun y => ubar u q (y,t) k) x) (Pi.single j 1) = _
    rw [(hslice k x t ht).2.fderiv]
    rfl
  refine ⟨h_H002, ?_, ?_, ?_, ?_⟩
  · apply contDiffOn_pi.mpr
    intro k
    exact ((hdf k).clm_apply (contDiffOn_const (c := ((0 : Space n), (1 : ℝ))))).congr (fun p ht => hv p.1 p.2 ht k)
  · intro j
    apply contDiffOn_pi.mpr
    intro k
    exact ((hdf k).clm_apply (contDiffOn_const (c := (Pi.single j (1 : ℝ), (0 : ℝ))))).congr (fun p ht => hp j p.1 p.2 ht k)
  · intro x t ht k
    rw [hv x t ht k]
    exact (hslice k x t ht).1
  · intro x t ht k
    exact (hslice k x t ht).2.differentiableAt.hasFDerivAt

#check @T001
#print axioms T001

end Translation
