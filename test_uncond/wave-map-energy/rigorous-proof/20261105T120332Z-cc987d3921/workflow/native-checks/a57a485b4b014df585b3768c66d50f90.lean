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

namespace Local_T011
theorem yui_aux_0001 (n : ℕ) (m : ℕ) (u : Space n × Set.Ioi (0 : ℝ) → Value m) (q : Value m) (h_T003 : FirstCalculus (ubar u q) ∧ SecondCalculus (ubar u q) ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => density (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => densityRate (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
(∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (fun r => density (ubar u q) x r) (densityRate (ubar u q) x t) t) ∧
(∀ (j : Fin n) (x : Space n) (t : ℝ), 0 < t → ∀ k : Fin m,
 fderiv ℝ (fun y => (ubar u q) (y,t) k) x (Pi.single j 1) = spatial (ubar u q) j x t k ∧
 fderiv ℝ (fun y => velocity (ubar u q) y t k) x (Pi.single j 1) = mixed (ubar u q) j x t k ∧
 fderiv ℝ (fun y => spatial (ubar u q) j y t k) x (Pi.single j 1) = spatialSecond (ubar u q) j x t k) ∧
(∀ (x : Space n) (t : Set.Ioi (0 : ℝ)), (ubar u q) (x,t) = u (x,t)) ∧
(∀ (x : Space n) (t : ℝ), t ≤ 0 → (ubar u q) (x,t) = q)) (h_T005 : (∀ t₀ : ℝ, 0 < t₀ → ∃ C : Set (Space n),
 SlabVanishing (ubar u q) q t₀ C ∧
 ∀ r ∈ Set.Ioo (t₀/2) (3*t₀/2),
 ∀ h ∈ Submodule.span ℝ (sections (ubar u q) r), SupportedSection C h) ∧
(∀ t : ℝ, 0 < t → Integrable (fun x => density (ubar u q) x t))) (h_T007 : ∀ t₀ : ℝ, 0 < t₀ → HasDerivAt (energy (ubar u q)) (∫ x, densityRate (ubar u q) x t₀) t₀) (h_T009 : ∀ (x : Space n) (t : ℝ), 0 < t →
 dot ((ubar u q) (x,t)) (velocity (ubar u q) x t) = 0 ∧
 dot (velocity (ubar u q) x t) ((ubar u q) (x,t)) = 0 ∧
 dot (velocity (ubar u q) x t) (acceleration (ubar u q) x t - laplacian (ubar u q) x t) = 0) (h_T010 : ∀ t₀ : ℝ, 0 < t₀ → ∀ j : Fin n,
 (∫ x, dot (spatial (ubar u q) j x t₀) (mixed (ubar u q) j x t₀)) =
   -(∫ x, dot (velocity (ubar u q) x t₀) (spatialSecond (ubar u q) j x t₀)) ∧
 Integrable (fun x => dot (spatial (ubar u q) j x t₀) (mixed (ubar u q) j x t₀)) ∧
 Integrable (fun x => dot (velocity (ubar u q) x t₀) (spatialSecond (ubar u q) j x t₀)) ∧
 (∀ k : Fin m,
 Integrable (fun x => velocity (ubar u q) x t₀ k * spatialSecond (ubar u q) j x t₀ k) ∧
 Integrable (fun x => mixed (ubar u q) j x t₀ k * spatial (ubar u q) j x t₀ k) ∧
 Integrable (fun x => velocity (ubar u q) x t₀ k * spatial (ubar u q) j x t₀ k))) : yui_aux_type% "∀ (a b : Value m) (s : Fin n → Value m), dot a (b - ∑ j, s j) = dot a b - ∑ j, dot a (s j)" := by
  intro a b s
  simp only [dot, Pi.sub_apply, Finset.sum_apply, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
  rw [Finset.sum_comm]

theorem yui_aux_0002 (n : ℕ) (m : ℕ) (u : Space n × Set.Ioi (0 : ℝ) → Value m) (q : Value m) (h_T003 : FirstCalculus (ubar u q) ∧ SecondCalculus (ubar u q) ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => density (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => densityRate (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
(∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (fun r => density (ubar u q) x r) (densityRate (ubar u q) x t) t) ∧
(∀ (j : Fin n) (x : Space n) (t : ℝ), 0 < t → ∀ k : Fin m,
 fderiv ℝ (fun y => (ubar u q) (y,t) k) x (Pi.single j 1) = spatial (ubar u q) j x t k ∧
 fderiv ℝ (fun y => velocity (ubar u q) y t k) x (Pi.single j 1) = mixed (ubar u q) j x t k ∧
 fderiv ℝ (fun y => spatial (ubar u q) j y t k) x (Pi.single j 1) = spatialSecond (ubar u q) j x t k) ∧
(∀ (x : Space n) (t : Set.Ioi (0 : ℝ)), (ubar u q) (x,t) = u (x,t)) ∧
(∀ (x : Space n) (t : ℝ), t ≤ 0 → (ubar u q) (x,t) = q)) (h_T005 : (∀ t₀ : ℝ, 0 < t₀ → ∃ C : Set (Space n),
 SlabVanishing (ubar u q) q t₀ C ∧
 ∀ r ∈ Set.Ioo (t₀/2) (3*t₀/2),
 ∀ h ∈ Submodule.span ℝ (sections (ubar u q) r), SupportedSection C h) ∧
(∀ t : ℝ, 0 < t → Integrable (fun x => density (ubar u q) x t))) (h_T007 : ∀ t₀ : ℝ, 0 < t₀ → HasDerivAt (energy (ubar u q)) (∫ x, densityRate (ubar u q) x t₀) t₀) (h_T009 : ∀ (x : Space n) (t : ℝ), 0 < t →
 dot ((ubar u q) (x,t)) (velocity (ubar u q) x t) = 0 ∧
 dot (velocity (ubar u q) x t) ((ubar u q) (x,t)) = 0 ∧
 dot (velocity (ubar u q) x t) (acceleration (ubar u q) x t - laplacian (ubar u q) x t) = 0) (h_T010 : ∀ t₀ : ℝ, 0 < t₀ → ∀ j : Fin n,
 (∫ x, dot (spatial (ubar u q) j x t₀) (mixed (ubar u q) j x t₀)) =
   -(∫ x, dot (velocity (ubar u q) x t₀) (spatialSecond (ubar u q) j x t₀)) ∧
 Integrable (fun x => dot (spatial (ubar u q) j x t₀) (mixed (ubar u q) j x t₀)) ∧
 Integrable (fun x => dot (velocity (ubar u q) x t₀) (spatialSecond (ubar u q) j x t₀)) ∧
 (∀ k : Fin m,
 Integrable (fun x => velocity (ubar u q) x t₀ k * spatialSecond (ubar u q) j x t₀ k) ∧
 Integrable (fun x => mixed (ubar u q) j x t₀ k * spatial (ubar u q) j x t₀ k) ∧
 Integrable (fun x => velocity (ubar u q) x t₀ k * spatial (ubar u q) j x t₀ k))) : yui_aux_type% "∀ t : ℝ, 0 < t → Integrable (fun x => dot (velocity (ubar u q) x t) (acceleration (ubar u q) x t))" := by
  intro t ht
  obtain ⟨C, hC, hsec⟩ := h_T005.1 t ht
  have htmem : t ∈ Set.Ioo (t / 2) (3 * t / 2) := by constructor <;> linarith
  have hmem : (fun x => dot (velocity (ubar u q) x t) (acceleration (ubar u q) x t)) ∈ sections (ubar u q) t := by
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  exact (hsec t htmem _ (Submodule.subset_span hmem)).2.2.2

end Local_T011
open Local_T011 in
theorem T011 (n : ℕ) (m : ℕ) (u : Space n × Set.Ioi (0 : ℝ) → Value m) (q : Value m) (h_T003 : FirstCalculus (ubar u q) ∧ SecondCalculus (ubar u q) ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => density (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => densityRate (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
(∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (fun r => density (ubar u q) x r) (densityRate (ubar u q) x t) t) ∧
(∀ (j : Fin n) (x : Space n) (t : ℝ), 0 < t → ∀ k : Fin m,
 fderiv ℝ (fun y => (ubar u q) (y,t) k) x (Pi.single j 1) = spatial (ubar u q) j x t k ∧
 fderiv ℝ (fun y => velocity (ubar u q) y t k) x (Pi.single j 1) = mixed (ubar u q) j x t k ∧
 fderiv ℝ (fun y => spatial (ubar u q) j y t k) x (Pi.single j 1) = spatialSecond (ubar u q) j x t k) ∧
(∀ (x : Space n) (t : Set.Ioi (0 : ℝ)), (ubar u q) (x,t) = u (x,t)) ∧
(∀ (x : Space n) (t : ℝ), t ≤ 0 → (ubar u q) (x,t) = q)) (h_T005 : (∀ t₀ : ℝ, 0 < t₀ → ∃ C : Set (Space n),
 SlabVanishing (ubar u q) q t₀ C ∧
 ∀ r ∈ Set.Ioo (t₀/2) (3*t₀/2),
 ∀ h ∈ Submodule.span ℝ (sections (ubar u q) r), SupportedSection C h) ∧
(∀ t : ℝ, 0 < t → Integrable (fun x => density (ubar u q) x t))) (h_T007 : ∀ t₀ : ℝ, 0 < t₀ → HasDerivAt (energy (ubar u q)) (∫ x, densityRate (ubar u q) x t₀) t₀) (h_T009 : ∀ (x : Space n) (t : ℝ), 0 < t →
 dot ((ubar u q) (x,t)) (velocity (ubar u q) x t) = 0 ∧
 dot (velocity (ubar u q) x t) ((ubar u q) (x,t)) = 0 ∧
 dot (velocity (ubar u q) x t) (acceleration (ubar u q) x t - laplacian (ubar u q) x t) = 0) (h_T010 : ∀ t₀ : ℝ, 0 < t₀ → ∀ j : Fin n,
 (∫ x, dot (spatial (ubar u q) j x t₀) (mixed (ubar u q) j x t₀)) =
   -(∫ x, dot (velocity (ubar u q) x t₀) (spatialSecond (ubar u q) j x t₀)) ∧
 Integrable (fun x => dot (spatial (ubar u q) j x t₀) (mixed (ubar u q) j x t₀)) ∧
 Integrable (fun x => dot (velocity (ubar u q) x t₀) (spatialSecond (ubar u q) j x t₀)) ∧
 (∀ k : Fin m,
 Integrable (fun x => velocity (ubar u q) x t₀ k * spatialSecond (ubar u q) j x t₀ k) ∧
 Integrable (fun x => mixed (ubar u q) j x t₀ k * spatial (ubar u q) j x t₀ k) ∧
 Integrable (fun x => velocity (ubar u q) x t₀ k * spatial (ubar u q) j x t₀ k))) :
    ∀ t : ℝ, 0 < t → HasDerivAt (energy (ubar u q)) 0 t := by
  classical
  intro t ht
  let v := ubar u q
  let f : Space n → ℝ := fun x => dot (velocity v x t) (acceleration v x t)
  let g : Fin n → Space n → ℝ := fun j x => dot (spatial v j x t) (mixed v j x t)
  let s : Fin n → Space n → ℝ := fun j x => dot (velocity v x t) (spatialSecond v j x t)
  have hf : Integrable f := @yui_aux_0002 n m u q h_T003 h_T005 h_T007 h_T009 h_T010 t ht
  have hg : ∀ j, Integrable (g j) := fun j => (h_T010 t ht j).2.1
  have hs : ∀ j, Integrable (s j) := fun j => (h_T010 t ht j).2.2.1
  have hgsum : Integrable (fun x => ∑ j, g j x) :=
    integrable_finsetSum Finset.univ (fun j _ => hg j)
  have hssum : Integrable (fun x => ∑ j, s j x) :=
    integrable_finsetSum Finset.univ (fun j _ => hs j)
  have hparts : ∀ j, (∫ x, g j x) = -(∫ x, s j x) :=
    fun j => (h_T010 t ht j).1
  have halg : ∀ x, dot (velocity v x t) (acceleration v x t - laplacian v x t) =
      f x - ∑ j, s j x := by
    intro x
    exact @yui_aux_0001 n m u q h_T003 h_T005 h_T007 h_T009 h_T010
      (velocity v x t) (acceleration v x t) (fun j => spatialSecond v j x t)
  have hzero : (∫ x, densityRate v x t) = 0 := by
    calc
      (∫ x, densityRate v x t) =
          2 * (∫ x, f x) + 2 * ∑ j, ∫ x, g j x := by
        change (∫ x, 2 * f x + 2 * ∑ j, g j x) = _
        rw [integral_add (hf.const_mul 2) (hgsum.const_mul 2),
          integral_const_mul, integral_const_mul,
          integral_finsetSum Finset.univ (fun j _ => hg j)]
      _ = 2 * (∫ x, f x) - 2 * ∑ j, ∫ x, s j x := by
        simp_rw [hparts]
        rw [Finset.sum_neg_distrib]
        ring
      _ = 2 * (∫ x, f x - ∑ j, s j x) := by
        rw [integral_sub hf hssum,
          integral_finsetSum Finset.univ (fun j _ => hs j)]
        ring
      _ = 2 * (∫ x, dot (velocity v x t)
          (acceleration v x t - laplacian v x t)) := by
        congr 1
        exact integral_congr_ae (Filter.Eventually.of_forall (fun x => (halg x).symm))
      _ = 0 := by
        have hz : (fun x => dot (velocity v x t)
            (acceleration v x t - laplacian v x t)) = (fun _ : Space n => (0 : ℝ)) :=
          funext (fun x => (h_T009 x t ht).2.2)
        rw [hz]
        simp
  have hd := h_T007 t ht
  rw [hzero] at hd
  exact hd

#check @T011
#print axioms T011

end Translation
