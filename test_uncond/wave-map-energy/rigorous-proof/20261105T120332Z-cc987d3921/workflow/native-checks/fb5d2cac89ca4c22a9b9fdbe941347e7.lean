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

namespace Local_T004
theorem yui_aux_0001 (n : ℕ) (m : ℕ) (u : Space n × Set.Ioi (0 : ℝ) → Value m) (q : Value m) (h_H006 : CompactPerturbation (ubar u q) q) (h_T003 : FirstCalculus (ubar u q) ∧ SecondCalculus (ubar u q) ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => density (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => densityRate (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
(∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (fun r => density (ubar u q) x r) (densityRate (ubar u q) x t) t) ∧
(∀ (j : Fin n) (x : Space n) (t : ℝ), 0 < t → ∀ k : Fin m,
 fderiv ℝ (fun y => (ubar u q) (y,t) k) x (Pi.single j 1) = spatial (ubar u q) j x t k ∧
 fderiv ℝ (fun y => velocity (ubar u q) y t k) x (Pi.single j 1) = mixed (ubar u q) j x t k ∧
 fderiv ℝ (fun y => spatial (ubar u q) j y t k) x (Pi.single j 1) = spatialSecond (ubar u q) j x t k) ∧
(∀ (x : Space n) (t : Set.Ioi (0 : ℝ)), (ubar u q) (x,t) = u (x,t)) ∧
(∀ (x : Space n) (t : ℝ), t ≤ 0 → (ubar u q) (x,t) = q)) : yui_aux_type% "∀ (f : Space n → ℝ) (x : Space n) (c : ℝ), f =ᶠ[𝓝 x] (fun _ => c) → fderiv ℝ f x = 0" := by
  intro f x c he
  rw [he.fderiv_eq, fderiv_const_apply]

theorem yui_aux_0002 (n : ℕ) (m : ℕ) (u : Space n × Set.Ioi (0 : ℝ) → Value m) (q : Value m) (h_H006 : CompactPerturbation (ubar u q) q) (h_T003 : FirstCalculus (ubar u q) ∧ SecondCalculus (ubar u q) ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => density (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => densityRate (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
(∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (fun r => density (ubar u q) x r) (densityRate (ubar u q) x t) t) ∧
(∀ (j : Fin n) (x : Space n) (t : ℝ), 0 < t → ∀ k : Fin m,
 fderiv ℝ (fun y => (ubar u q) (y,t) k) x (Pi.single j 1) = spatial (ubar u q) j x t k ∧
 fderiv ℝ (fun y => velocity (ubar u q) y t k) x (Pi.single j 1) = mixed (ubar u q) j x t k ∧
 fderiv ℝ (fun y => spatial (ubar u q) j y t k) x (Pi.single j 1) = spatialSecond (ubar u q) j x t k) ∧
(∀ (x : Space n) (t : Set.Ioi (0 : ℝ)), (ubar u q) (x,t) = u (x,t)) ∧
(∀ (x : Space n) (t : ℝ), t ≤ 0 → (ubar u q) (x,t) = q)) : yui_aux_type% "∀ (C : Set (Space n)) (a b : ℝ), IsClosed C → (∀ x r, x ∉ C → r ∈ Set.Ioo a b → (ubar u q) (x,r) = q) → ∀ x r, x ∉ C → r ∈ Set.Ioo a b → velocity (ubar u q) x r = 0 ∧ ∀ j, spatial (ubar u q) j x r = 0" := by
  intro C a b hC hv x r hx hr
  constructor
  · funext k
    have he : (fun s => (ubar u q) (x,s) k) =ᶠ[𝓝 r] (fun _ => q k) := by
      filter_upwards [isOpen_Ioo.mem_nhds hr] with s hs
      exact congrFun (hv x s hx hs) k
    change deriv (fun s => (ubar u q) (x,s) k) r = 0
    rw [he.deriv_eq, deriv_const]
  · intro j
    funext k
    have he : (fun y => (ubar u q) (y,r) k) =ᶠ[𝓝 x] (fun _ => q k) := by
      filter_upwards [hC.isOpen_compl.mem_nhds hx] with y hy
      exact congrFun (hv y r hy hr) k
    change fderiv ℝ (fun y => (ubar u q) (y,r) k) x (Pi.single j 1) = 0
    rw [@yui_aux_0001 n m u q h_H006 h_T003 _ x (q k) he]
    rfl

end Local_T004
open Local_T004 in
theorem T004 (n : ℕ) (m : ℕ) (u : Space n × Set.Ioi (0 : ℝ) → Value m) (q : Value m) (h_H006 : CompactPerturbation (ubar u q) q) (h_T003 : FirstCalculus (ubar u q) ∧ SecondCalculus (ubar u q) ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => density (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => densityRate (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
(∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (fun r => density (ubar u q) x r) (densityRate (ubar u q) x t) t) ∧
(∀ (j : Fin n) (x : Space n) (t : ℝ), 0 < t → ∀ k : Fin m,
 fderiv ℝ (fun y => (ubar u q) (y,t) k) x (Pi.single j 1) = spatial (ubar u q) j x t k ∧
 fderiv ℝ (fun y => velocity (ubar u q) y t k) x (Pi.single j 1) = mixed (ubar u q) j x t k ∧
 fderiv ℝ (fun y => spatial (ubar u q) j y t k) x (Pi.single j 1) = spatialSecond (ubar u q) j x t k) ∧
(∀ (x : Space n) (t : Set.Ioi (0 : ℝ)), (ubar u q) (x,t) = u (x,t)) ∧
(∀ (x : Space n) (t : ℝ), t ≤ 0 → (ubar u q) (x,t) = q)) :
    ∀ t₀ : ℝ, 0 < t₀ → ∃ C : Set (Space n), SlabVanishing (ubar u q) q t₀ C := by
  intro t₀ ht₀
  obtain ⟨C, hC, hv⟩ := h_H006 (t₀ / 2) (3 * t₀ / 2) (by linarith) (by linarith)
  have hv' : ∀ x r, x ∉ C → r ∈ Set.Ioo (t₀ / 2) (3 * t₀ / 2) →
      (ubar u q) (x,r) = q := by
    intro x r hx hr
    exact hv x r hx ⟨hr.1.le, hr.2.le⟩
  have hfirst := @yui_aux_0002 n m u q h_H006 h_T003 C (t₀ / 2) (3 * t₀ / 2)
    hC.isClosed hv'
  refine ⟨C, hC, hv, ?_, ?_⟩
  · intro ell hell x r hx hr
    have hO : IsOpen (Cᶜ ×ˢ Set.Ioo (t₀ / 2) (3 * t₀ / 2)) :=
      hC.isClosed.isOpen_compl.prod isOpen_Ioo
    have he : ubar u q =ᶠ[𝓝 (x,r)] (fun _ => q) := by
      filter_upwards [hO.mem_nhds ⟨hx, hr⟩] with p hp
      exact hv' p.1 p.2 hp.1 hp.2
    rw [(he.iteratedFDeriv ℝ ell).self_of_nhds,
      iteratedFDeriv_const_of_ne (Nat.ne_of_gt hell)]
    rfl
  · intro x r hx hr
    obtain ⟨hV, hP⟩ := hfirst x r hx hr
    have hA : acceleration (ubar u q) x r = 0 := by
      funext k
      have he : (fun s => velocity (ubar u q) x s k) =ᶠ[𝓝 r] (fun _ => (0 : ℝ)) := by
        filter_upwards [isOpen_Ioo.mem_nhds hr] with s hs
        exact congrFun (hfirst x s hx hs).1 k
      change deriv (fun s => velocity (ubar u q) x s k) r = 0
      rw [he.deriv_eq, deriv_const]
    have hS : ∀ j, spatialSecond (ubar u q) j x r = 0 := by
      intro j
      funext k
      have he : (fun y => spatial (ubar u q) j y r k) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
        filter_upwards [hC.isClosed.isOpen_compl.mem_nhds hx] with y hy
        exact congrFun ((hfirst y r hy hr).2 j) k
      change fderiv ℝ (fun y => spatial (ubar u q) j y r k) x (Pi.single j 1) = 0
      rw [@yui_aux_0001 n m u q h_H006 h_T003 _ x 0 he]
      rfl
    have hW : ∀ j, mixed (ubar u q) j x r = 0 := by
      intro j
      funext k
      have he : (fun y => velocity (ubar u q) y r k) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
        filter_upwards [hC.isClosed.isOpen_compl.mem_nhds hx] with y hy
        exact congrFun (hfirst y r hy hr).1 k
      change fderiv ℝ (fun y => velocity (ubar u q) y r k) x (Pi.single j 1) = 0
      rw [@yui_aux_0001 n m u q h_H006 h_T003 _ x 0 he]
      rfl
    refine ⟨hV, hA, (fun j => ⟨hP j, hS j, hW j⟩), ?_, ?_⟩
    · simp [density, hV, hP, normSq, dot]
    · simp [densityRate, hV, hP, dot]

#check @T004
#print axioms T004

end Translation
