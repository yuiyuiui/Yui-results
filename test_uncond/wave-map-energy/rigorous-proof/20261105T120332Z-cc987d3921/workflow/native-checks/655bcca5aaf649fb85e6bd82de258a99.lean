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

namespace YuiAuxiliary
set_option autoImplicit false
theorem yui_aux_0001 (n : ℕ) (m : ℕ) (u : Space n × Set.Ioi (0 : ℝ) → Value m) (q : Value m) (h_T003 : FirstCalculus (ubar u q) ∧ SecondCalculus (ubar u q) ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => density (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => densityRate (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
(∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (fun r => density (ubar u q) x r) (densityRate (ubar u q) x t) t) ∧
(∀ (j : Fin n) (x : Space n) (t : ℝ), 0 < t → ∀ k : Fin m,
 fderiv ℝ (fun y => (ubar u q) (y,t) k) x (Pi.single j 1) = spatial (ubar u q) j x t k ∧
 fderiv ℝ (fun y => velocity (ubar u q) y t k) x (Pi.single j 1) = mixed (ubar u q) j x t k ∧
 fderiv ℝ (fun y => spatial (ubar u q) j y t k) x (Pi.single j 1) = spatialSecond (ubar u q) j x t k) ∧
(∀ (x : Space n) (t : Set.Ioi (0 : ℝ)), (ubar u q) (x,t) = u (x,t)) ∧
(∀ (x : Space n) (t : ℝ), t ≤ 0 → (ubar u q) (x,t) = q)) (h_T004 : ∀ t₀ : ℝ, 0 < t₀ → ∃ C : Set (Space n), SlabVanishing (ubar u q) q t₀ C) : yui_aux_type% "∀ r : ℝ, 0 < r → Continuous (fun x : Space n => velocity (ubar u q) x r)" := by
  intro r hr
  exact h_T003.1.2.1.continuousOn.comp_continuous
    (continuous_id.prodMk continuous_const) (fun x => hr)

theorem yui_aux_0002 (n : ℕ) (m : ℕ) (u : Space n × Set.Ioi (0 : ℝ) → Value m) (q : Value m) (h_T003 : FirstCalculus (ubar u q) ∧ SecondCalculus (ubar u q) ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => density (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => densityRate (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
(∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (fun r => density (ubar u q) x r) (densityRate (ubar u q) x t) t) ∧
(∀ (j : Fin n) (x : Space n) (t : ℝ), 0 < t → ∀ k : Fin m,
 fderiv ℝ (fun y => (ubar u q) (y,t) k) x (Pi.single j 1) = spatial (ubar u q) j x t k ∧
 fderiv ℝ (fun y => velocity (ubar u q) y t k) x (Pi.single j 1) = mixed (ubar u q) j x t k ∧
 fderiv ℝ (fun y => spatial (ubar u q) j y t k) x (Pi.single j 1) = spatialSecond (ubar u q) j x t k) ∧
(∀ (x : Space n) (t : Set.Ioi (0 : ℝ)), (ubar u q) (x,t) = u (x,t)) ∧
(∀ (x : Space n) (t : ℝ), t ≤ 0 → (ubar u q) (x,t) = q)) (h_T004 : ∀ t₀ : ℝ, 0 < t₀ → ∃ C : Set (Space n), SlabVanishing (ubar u q) q t₀ C) : yui_aux_type% "∀ (r : ℝ), 0 < r → ∀ h ∈ sections (ubar u q) r, Continuous h" := by
  intro r hr
  have slice {F : Type} [TopologicalSpace F] (f : Space n × ℝ → F)
      (hf : ContinuousOn f {p | 0 < p.2}) :
      Continuous (fun x : Space n => f (x,r)) :=
    hf.comp_continuous (continuous_id.prodMk continuous_const) (fun x => hr)
  have hv := yui_aux_0001 n m u q h_T003 h_T004 r hr
  have ha := slice _ h_T003.2.1.1.continuousOn
  have hs (j : Fin n) := slice _ (h_T003.1.2.2.1 j).continuousOn
  have hss (j : Fin n) := slice _ (h_T003.2.1.2.1 j).continuousOn
  have hm (j : Fin n) := slice _ (h_T003.2.1.2.2.1 j).continuousOn
  have he := slice _ h_T003.2.2.1.continuousOn
  have hd := slice _ h_T003.2.2.2.1.continuousOn
  have hvk (k : Fin m) := (continuous_apply k).comp hv
  have hak (k : Fin m) := (continuous_apply k).comp ha
  have hsk (j : Fin n) (k : Fin m) := (continuous_apply k).comp (hs j)
  have hssk (j : Fin n) (k : Fin m) := (continuous_apply k).comp (hss j)
  have hmk (j : Fin n) (k : Fin m) := (continuous_apply k).comp (hm j)
  intro h hh
  rcases hh with hh | hh | ⟨k,hh⟩ | ⟨j,k,hh⟩ | hh | ⟨j,hh⟩
  · subst h; exact he
  · subst h; exact hd
  · rcases hh with hh | hh | hh <;> subst h <;> fun_prop
  · rcases hh with hh | hh | hh | hh | hh | hh | hh <;> subst h <;> fun_prop
  · subst h
    unfold dot
    fun_prop
  · rcases hh with hh | hh | hh | hh <;> subst h <;> unfold dot <;> fun_prop

theorem yui_aux_0003 (n : ℕ) (m : ℕ) (u : Space n × Set.Ioi (0 : ℝ) → Value m) (q : Value m) (h_T003 : FirstCalculus (ubar u q) ∧ SecondCalculus (ubar u q) ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => density (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => densityRate (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
(∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (fun r => density (ubar u q) x r) (densityRate (ubar u q) x t) t) ∧
(∀ (j : Fin n) (x : Space n) (t : ℝ), 0 < t → ∀ k : Fin m,
 fderiv ℝ (fun y => (ubar u q) (y,t) k) x (Pi.single j 1) = spatial (ubar u q) j x t k ∧
 fderiv ℝ (fun y => velocity (ubar u q) y t k) x (Pi.single j 1) = mixed (ubar u q) j x t k ∧
 fderiv ℝ (fun y => spatial (ubar u q) j y t k) x (Pi.single j 1) = spatialSecond (ubar u q) j x t k) ∧
(∀ (x : Space n) (t : Set.Ioi (0 : ℝ)), (ubar u q) (x,t) = u (x,t)) ∧
(∀ (x : Space n) (t : ℝ), t ≤ 0 → (ubar u q) (x,t) = q)) (h_T004 : ∀ t₀ : ℝ, 0 < t₀ → ∃ C : Set (Space n), SlabVanishing (ubar u q) q t₀ C) : yui_aux_type% "∀ (t₀ : ℝ) (C : Set (Space n)), SlabVanishing (ubar u q) q t₀ C → ∀ r ∈ Set.Ioo (t₀/2) (3*t₀/2), ∀ h ∈ sections (ubar u q) r, ∀ x, x ∉ C → h x = 0" := by
  intro t₀ C hC r hr h hh x hx
  obtain ⟨hv, ha, hs, he, hd⟩ := hC.2.2.2 x r hx hr
  have hsp (j : Fin n) := (hs j).1
  have hss (j : Fin n) := (hs j).2.1
  have hm (j : Fin n) := (hs j).2.2
  rcases hh with hh | hh | ⟨k,hh⟩ | ⟨j,k,hh⟩ | hh | ⟨j,hh⟩
  · subst h; exact he
  · subst h; exact hd
  · rcases hh with hh | hh | hh <;> subst h <;> simp [hv, ha]
  · rcases hh with hh | hh | hh | hh | hh | hh | hh <;> subst h <;>
      simp [hv, ha, hsp, hss, hm]
  · subst h; simp [dot, hv, ha]
  · rcases hh with hh | hh | hh | hh <;> subst h <;> simp [dot, hv, hsp, hss, hm]

theorem checked (n : ℕ) (m : ℕ) (u : Space n × Set.Ioi (0 : ℝ) → Value m) (q : Value m) (h_T003 : FirstCalculus (ubar u q) ∧ SecondCalculus (ubar u q) ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => density (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => densityRate (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
(∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (fun r => density (ubar u q) x r) (densityRate (ubar u q) x t) t) ∧
(∀ (j : Fin n) (x : Space n) (t : ℝ), 0 < t → ∀ k : Fin m,
 fderiv ℝ (fun y => (ubar u q) (y,t) k) x (Pi.single j 1) = spatial (ubar u q) j x t k ∧
 fderiv ℝ (fun y => velocity (ubar u q) y t k) x (Pi.single j 1) = mixed (ubar u q) j x t k ∧
 fderiv ℝ (fun y => spatial (ubar u q) j y t k) x (Pi.single j 1) = spatialSecond (ubar u q) j x t k) ∧
(∀ (x : Space n) (t : Set.Ioi (0 : ℝ)), (ubar u q) (x,t) = u (x,t)) ∧
(∀ (x : Space n) (t : ℝ), t ≤ 0 → (ubar u q) (x,t) = q)) (h_T004 : ∀ t₀ : ℝ, 0 < t₀ → ∃ C : Set (Space n), SlabVanishing (ubar u q) q t₀ C) : yui_aux_type% "∀ (C : Set (Space n)) (h : Space n → ℝ), IsCompact C → Continuous h → (∀ x, x ∉ C → h x = 0) → SupportedSection C h" := by
  intro C h hC hc hz
  have hs : Function.support h ⊆ C := by
    intro x hx
    by_contra hn
    exact hx (hz x hn)
  have ht : tsupport h ⊆ C := closure_minimal hs hC.isClosed
  have hk : HasCompactSupport h := hC.of_isClosed_subset (isClosed_tsupport h) ht
  exact ⟨hc, ht, hk, hc.integrable_of_hasCompactSupport hk⟩
#check @checked
#print axioms checked
end YuiAuxiliary
