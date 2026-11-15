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

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace Translation
set_option autoImplicit false

theorem T001 (n : ℕ) (m : ℕ) (U : Z n → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m ∧ ‖q‖ = 1 ∧ ContDiffOn ℝ ∞ U (omega n)) (h_E004 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F], ∀ (U : Set E) (f : E → F), IsOpen U → (ContDiffOn ℝ ∞ f U ↔ DifferentiableOn ℝ f U ∧ ContDiffOn ℝ ∞ (fderiv ℝ f) U)) (h_E005 : ∀ (E F G : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G], ∀ (U : Set E) (A : E → F →L[ℝ] G) (b : E → F), ContDiffOn ℝ ∞ A U → ContDiffOn ℝ ∞ b U → ContDiffOn ℝ ∞ (fun z => A z (b z)) U) :
    (∀ ds : List (Z n), ContDiffOn ℝ ∞ (ordered U ds) (omega n)) ∧ (∀ k : ℕ, ContDiffOn ℝ ∞ (iteratedFDeriv ℝ k U) (omega n)) := by
  have ho : IsOpen (omega n) := by
    exact isOpen_lt continuous_const continuous_snd
  have hU : ContDiffOn ℝ ∞ U (omega n) := h_H001.2.2.2
  constructor
  · intro ds
    induction ds with
    | nil => exact hU
    | cons v ds ih =>
      have hd : ContDiffOn ℝ ∞ (fderiv ℝ (ordered U ds)) (omega n) :=
        ((h_E004 (Z n) (V m) (omega n) (ordered U ds) ho).mp ih).2
      exact h_E005 (Z n) (Z n) (V m) (omega n)
        (fderiv ℝ (ordered U ds)) (fun _ => v) hd contDiffOn_const
  · intro k
    induction k with
    | zero =>
      rw [iteratedFDeriv_zero_eq_comp]
      exact (continuousMultilinearCurryFin0 ℝ (Z n) (V m)).symm.contDiff.comp_contDiffOn hU
    | succ k ih =>
      have hd : ContDiffOn ℝ ∞ (fderiv ℝ (iteratedFDeriv ℝ k U)) (omega n) :=
        ((h_E004 (Z n) (ContinuousMultilinearMap ℝ (fun _ : Fin k => Z n) (V m))
          (omega n) (iteratedFDeriv ℝ k U) ho).mp ih).2
      rw [iteratedFDeriv_succ_eq_comp_left]
      exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => Z n)
        (V m)).symm.contDiff.comp_contDiffOn hd

namespace Local_T003
theorem yui_aux_0001 (n : ℕ) (m : ℕ) (U : Z n → V m) (q : V m) (h_E013 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F], ∀ (l : E → F) (L : E →L[ℝ] F) (c : ℝ → E) (v : E) (t : ℝ), HasFDerivAt l L (c t) → HasDerivAt c v t → HasDerivAt (l ∘ c) (L v) t) : yui_aux_type% "∀ (x v : X n), HasDerivAt (fun h : ℝ => x + h • v) v 0" := by
  intro x v
  simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x

end Local_T003
open Local_T003 in
theorem T003 (n : ℕ) (m : ℕ) (U : Z n → V m) (q : V m) (h_E013 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F], ∀ (l : E → F) (L : E →L[ℝ] F) (c : ℝ → E) (v : E) (t : ℝ), HasFDerivAt l L (c t) → HasDerivAt c v t → HasDerivAt (l ∘ c) (L v) t) :
    ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]
 (f : Z n → F), ContDiffOn ℝ ∞ f (omega n) →
 ∀ (x : X n) (t : ℝ), 0 < t →
 HasDerivAt (fun r => f (x, r)) (D (tau n) f (x, t)) t ∧
 (∀ v : X n, fderiv ℝ (fun y : X n => f (y, t)) x v = D (v, 0) f (x, t)) ∧
 (∀ v : X n, HasDerivAt (fun h : ℝ => f (x + h • v, t)) (D (v, 0) f (x, t)) 0) := by
  intro F _ _ f hf x t ht
  have hopen : IsOpen (omega n) := by
    exact isOpen_lt continuous_const continuous_snd
  have hfd : HasFDerivAt f (fderiv ℝ f (x, t)) (x, t) :=
    (hf.differentiableOn (by simp)).hasFDerivAt (hopen.mem_nhds ht)
  have htime : HasDerivAt (fun r : ℝ => (x, r)) (tau n) t := by
    simpa [tau] using (hasDerivAt_const t x).prodMk (hasDerivAt_id t)
  have hsection : DifferentiableAt ℝ (fun y : X n => f (y, t)) x := by
    exact (hfd.comp x (hasFDerivAt_prodMk_left x t)).differentiableAt
  have hcurve : ∀ v : X n,
      HasDerivAt (fun h : ℝ => x + h • v) v 0 :=
    @yui_aux_0001 n m U q h_E013 x
  have hspace : ∀ v : X n,
      HasDerivAt (fun h : ℝ => f (x + h • v, t)) (D (v, 0) f (x, t)) 0 := by
    intro v
    have hc : HasDerivAt (fun h : ℝ => (x + h • v, t)) (v, 0) 0 :=
      (hcurve v).prodMk (hasDerivAt_const (0 : ℝ) t)
    have hd : HasFDerivAt f (fderiv ℝ f (x, t))
        ((fun h : ℝ => (x + h • v, t)) 0) := by
      simpa using hfd
    simpa [Function.comp_def, D] using
      (h_E013 (Z n) F f (fderiv ℝ f (x, t))
        (fun h : ℝ => (x + h • v, t)) (v, 0) 0 hd hc)
  refine ⟨?_, ?_, hspace⟩
  · simpa [Function.comp_def, D] using
      (h_E013 (Z n) F f (fderiv ℝ f (x, t))
        (fun r : ℝ => (x, r)) (tau n) t hfd htime)
  · intro v
    have hs : HasFDerivAt (fun y : X n => f (y, t))
        (fderiv ℝ (fun y : X n => f (y, t)) x)
        ((fun h : ℝ => x + h • v) 0) := by
      simpa using hsection.hasFDerivAt
    have hd := h_E013 (X n) F (fun y : X n => f (y, t))
      (fderiv ℝ (fun y : X n => f (y, t)) x)
      (fun h : ℝ => x + h • v) v 0 hs (hcurve v)
    exact hd.unique (hspace v)

theorem T004 (n : ℕ) (m : ℕ) (U : Z n → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m ∧ ‖q‖ = 1 ∧ ContDiffOn ℝ ∞ U (omega n)) (h_H002 : ∀ x : X n, ∀ t : ℝ, 0 < t → ‖U (x, t)‖ = 1 ∧ ∃ a : ℝ, utt U (x, t) - lap U (x, t) = a • U (x, t)) (h_T001 : (∀ ds : List (Z n), ContDiffOn ℝ ∞ (ordered U ds) (omega n)) ∧ (∀ k : ℕ, ContDiffOn ℝ ∞ (iteratedFDeriv ℝ k U) (omega n))) (h_T003 : ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]
 (f : Z n → F), ContDiffOn ℝ ∞ f (omega n) →
 ∀ (x : X n) (t : ℝ), 0 < t →
 HasDerivAt (fun r => f (x, r)) (D (tau n) f (x, t)) t ∧
 (∀ v : X n, fderiv ℝ (fun y : X n => f (y, t)) x v = D (v, 0) f (x, t)) ∧
 (∀ v : X n, HasDerivAt (fun h : ℝ => f (x + h • v, t)) (D (v, 0) f (x, t)) 0)) (h_E008 : ∀ (E V : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [InnerProductSpace ℝ V], ∀ (f g : E → V) (z v : E), DifferentiableAt ℝ f z → DifferentiableAt ℝ g z → fderiv ℝ (fun y => inner ℝ (f y) (g y)) z v = inner ℝ (f z) (fderiv ℝ g z v) + inner ℝ (fderiv ℝ f z v) (g z)) (h_E010 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F], ∀ (f g : E → F) (z : E), (f =ᶠ[𝓝 z] g) → fderiv ℝ f z = fderiv ℝ g z) :
    ∀ x : X n, ∀ t : ℝ, 0 < t →
 inner ℝ (U (x, t)) (ut U (x, t)) = 0 ∧
 inner ℝ (ut U (x, t)) (utt U (x, t) - lap U (x, t)) = 0 := by
  intro x t ht
  have hopen : IsOpen (omega n) := isOpen_lt continuous_const continuous_snd
  have hnhds : omega n ∈ 𝓝 ((x, t) : Z n) := hopen.mem_nhds ht
  have hdiff : DifferentiableAt ℝ U (x, t) :=
    (h_H001.2.2.2.differentiableOn (by simp)).differentiableAt hnhds
  have heq : (fun z : Z n => inner ℝ (U z) (U z)) =ᶠ[𝓝 (x, t)]
      (fun _ : Z n => (1 : ℝ)) := by
    filter_upwards [hnhds] with z hz
    rw [real_inner_self_eq_norm_sq, (h_H002 z.1 z.2 hz).1]
    norm_num
  have hder : fderiv ℝ (fun z : Z n => inner ℝ (U z) (U z)) (x, t) =
      fderiv ℝ (fun _ : Z n => (1 : ℝ)) (x, t) :=
    h_E010 (Z n) ℝ (fun z => inner ℝ (U z) (U z)) (fun _ => 1) (x, t) heq
  have hzero : fderiv ℝ (fun z : Z n => inner ℝ (U z) (U z)) (x, t)
      (tau n) = 0 := by
    rw [hder]
    simp
  rw [h_E008 (Z n) (V m) U U (x, t) (tau n) hdiff hdiff] at hzero
  change inner ℝ (U (x, t)) (ut U (x, t)) +
    inner ℝ (ut U (x, t)) (U (x, t)) = 0 at hzero
  have hsym : inner ℝ (ut U (x, t)) (U (x, t)) =
      inner ℝ (U (x, t)) (ut U (x, t)) := real_inner_comm _ _
  rw [hsym] at hzero
  have htan : inner ℝ (U (x, t)) (ut U (x, t)) = 0 := by linarith
  refine ⟨htan, ?_⟩
  rcases (h_H002 x t ht).2 with ⟨a, ha⟩
  rw [ha, inner_smul_right, hsym, htan, mul_zero]

namespace Local_T002
theorem yui_aux_0001 (n : ℕ) (m : ℕ) (U : Z n → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m ∧ ‖q‖ = 1 ∧ ContDiffOn ℝ ∞ U (omega n)) (h_T001 : (∀ ds : List (Z n), ContDiffOn ℝ ∞ (ordered U ds) (omega n)) ∧ (∀ k : ℕ, ContDiffOn ℝ ∞ (iteratedFDeriv ℝ k U) (omega n))) (h_E004 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F], ∀ (U : Set E) (f : E → F), IsOpen U → (ContDiffOn ℝ ∞ f U ↔ DifferentiableOn ℝ f U ∧ ContDiffOn ℝ ∞ (fderiv ℝ f) U)) (h_E005 : ∀ (E F G : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G], ∀ (U : Set E) (A : E → F →L[ℝ] G) (b : E → F), ContDiffOn ℝ ∞ A U → ContDiffOn ℝ ∞ b U → ContDiffOn ℝ ∞ (fun z => A z (b z)) U) (h_E006 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F], ∀ (f : E → F) (z : E), ContDiffAt ℝ 2 f z → ∀ v w : E, fderiv ℝ (fderiv ℝ f) z v w = fderiv ℝ (fderiv ℝ f) z w v) (h_E007 : ∀ (E F G : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G], ∀ (A : E → F →L[ℝ] G) (b : E → F) (z : E), DifferentiableAt ℝ A z → DifferentiableAt ℝ b z → fderiv ℝ (fun y => A y (b y)) z = (A z).comp (fderiv ℝ b z) + (fderiv ℝ A z).flip (b z)) (h_E009 : ∀ (E V : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [InnerProductSpace ℝ V], ∀ (U : Set E) (f g : E → V), ContDiffOn ℝ ∞ f U → ContDiffOn ℝ ∞ g U → ContDiffOn ℝ ∞ (fun y => inner ℝ (f y) (g y)) U) (h_E014 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F], ∀ (k : ℕ) (f : Fin k → E → F) (U : Set E), (∀ i, ContDiffOn ℝ ∞ (f i) U) → ContDiffOn ℝ ∞ (fun z => ∑ i, f i z) U) : yui_aux_type% "Regular U" := by
  have hopen : IsOpen (omega n) := isOpen_lt continuous_const continuous_snd
  have hut : ContDiffOn ℝ ∞ (ut U) (omega n) := by
    simpa only [ordered, ut] using h_T001.1 [tau n]
  have huj : ∀ j : Fin n, ContDiffOn ℝ ∞ (uj U j) (omega n) := by
    intro j
    simpa only [ordered, uj] using h_T001.1 [sigma n j]
  have hutt : ContDiffOn ℝ ∞ (utt U) (omega n) := by
    simpa only [ordered, utt, ut] using h_T001.1 [tau n, tau n]
  have hujj : ∀ j : Fin n, ContDiffOn ℝ ∞ (ujj U j) (omega n) := by
    intro j
    simpa only [ordered, ujj, uj] using h_T001.1 [sigma n j, sigma n j]
  have hutj : ∀ j : Fin n, ContDiffOn ℝ ∞ (utj U j) (omega n) := by
    intro j
    simpa only [ordered, utj, ut] using h_T001.1 [sigma n j, tau n]
  have hip : ∀ f g : Z n → V m,
      ContDiffOn ℝ ∞ f (omega n) → ContDiffOn ℝ ∞ g (omega n) →
      ContDiffOn ℝ ∞ (fun z => inner ℝ (f z) (g z)) (omega n) := by
    intro f g hf hg
    exact h_E009 (Z n) (V m) (omega n) f g hf hg
  have hsq : ∀ f : Z n → V m, ContDiffOn ℝ ∞ f (omega n) →
      ContDiffOn ℝ ∞ (fun z => ‖f z‖ ^ 2) (omega n) := by
    intro f hf
    simpa only [real_inner_self_eq_norm_sq] using hip f f hf hf
  have he : ContDiffOn ℝ ∞ (density U) (omega n) := by
    have hsum : ContDiffOn ℝ ∞ (fun z => ∑ j, ‖uj U j z‖ ^ 2) (omega n) :=
      h_E014 (Z n) ℝ n (fun j z => ‖uj U j z‖ ^ 2) (omega n)
        (fun j => hsq (uj U j) (huj j))
    exact (hsq (ut U) hut).add hsum
  have het : ContDiffOn ℝ ∞ (densityTime U) (omega n) := by
    have hde : ContDiffOn ℝ ∞ (fderiv ℝ (density U)) (omega n) :=
      ((h_E004 (Z n) ℝ (omega n) (density U) hopen).mp he).2
    exact h_E005 (Z n) (Z n) ℝ (omega n) (fderiv ℝ (density U))
      (fun _ => tau n) hde contDiffOn_const
  refine ⟨h_T001.1, h_T001.2, ?_⟩
  intro f hf
  rcases hf with rfl | rfl | rfl | ⟨j, rfl | rfl | rfl⟩
  · exact he
  · exact het
  · exact hip (ut U) (utt U) hut hutt
  · exact hip (uj U j) (utj U j) (huj j) (hutj j)
  · exact hip (ut U) (ujj U j) hut (hujj j)
  · exact hip (ut U) (uj U j) hut (huj j)

theorem yui_aux_0002 (n : ℕ) (m : ℕ) (U : Z n → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m ∧ ‖q‖ = 1 ∧ ContDiffOn ℝ ∞ U (omega n)) (h_T001 : (∀ ds : List (Z n), ContDiffOn ℝ ∞ (ordered U ds) (omega n)) ∧ (∀ k : ℕ, ContDiffOn ℝ ∞ (iteratedFDeriv ℝ k U) (omega n))) (h_E004 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F], ∀ (U : Set E) (f : E → F), IsOpen U → (ContDiffOn ℝ ∞ f U ↔ DifferentiableOn ℝ f U ∧ ContDiffOn ℝ ∞ (fderiv ℝ f) U)) (h_E005 : ∀ (E F G : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G], ∀ (U : Set E) (A : E → F →L[ℝ] G) (b : E → F), ContDiffOn ℝ ∞ A U → ContDiffOn ℝ ∞ b U → ContDiffOn ℝ ∞ (fun z => A z (b z)) U) (h_E006 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F], ∀ (f : E → F) (z : E), ContDiffAt ℝ 2 f z → ∀ v w : E, fderiv ℝ (fderiv ℝ f) z v w = fderiv ℝ (fderiv ℝ f) z w v) (h_E007 : ∀ (E F G : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G], ∀ (A : E → F →L[ℝ] G) (b : E → F) (z : E), DifferentiableAt ℝ A z → DifferentiableAt ℝ b z → fderiv ℝ (fun y => A y (b y)) z = (A z).comp (fderiv ℝ b z) + (fderiv ℝ A z).flip (b z)) (h_E009 : ∀ (E V : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [InnerProductSpace ℝ V], ∀ (U : Set E) (f g : E → V), ContDiffOn ℝ ∞ f U → ContDiffOn ℝ ∞ g U → ContDiffOn ℝ ∞ (fun y => inner ℝ (f y) (g y)) U) (h_E014 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F], ∀ (k : ℕ) (f : Fin k → E → F) (U : Set E), (∀ i, ContDiffOn ℝ ∞ (f i) U) → ContDiffOn ℝ ∞ (fun z => ∑ i, f i z) U) : yui_aux_type% "∀ z ∈ omega n, ∀ a b : Z n, D b (D a U) z = fderiv ℝ (fderiv ℝ U) z b a" := by
  have hopen : IsOpen (omega n) := isOpen_lt continuous_const continuous_snd
  have hU : ContDiffOn ℝ ∞ U (omega n) := by
    simpa only [ordered] using h_T001.1 []
  have hdU : ContDiffOn ℝ ∞ (fderiv ℝ U) (omega n) :=
    ((h_E004 (Z n) (V m) (omega n) U hopen).mp hU).2
  have hddU : DifferentiableOn ℝ (fderiv ℝ U) (omega n) :=
    ((h_E004 (Z n) (Z n →L[ℝ] V m) (omega n) (fderiv ℝ U) hopen).mp hdU).1
  intro z hz a b
  have hd : DifferentiableAt ℝ (fderiv ℝ U) z :=
    hddU.differentiableAt (hopen.mem_nhds hz)
  have h := h_E007 (Z n) (Z n) (V m) (fderiv ℝ U) (fun _ => a) z
    hd (differentiableAt_const a)
  have h' := congrArg (fun L : Z n →L[ℝ] V m => L b) h
  change (fderiv ℝ (fun y => fderiv ℝ U y a) z) b = _
  simpa using h'

end Local_T002
open Local_T002 in
theorem T002 (n : ℕ) (m : ℕ) (U : Z n → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m ∧ ‖q‖ = 1 ∧ ContDiffOn ℝ ∞ U (omega n)) (h_T001 : (∀ ds : List (Z n), ContDiffOn ℝ ∞ (ordered U ds) (omega n)) ∧ (∀ k : ℕ, ContDiffOn ℝ ∞ (iteratedFDeriv ℝ k U) (omega n))) (h_E004 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F], ∀ (U : Set E) (f : E → F), IsOpen U → (ContDiffOn ℝ ∞ f U ↔ DifferentiableOn ℝ f U ∧ ContDiffOn ℝ ∞ (fderiv ℝ f) U)) (h_E005 : ∀ (E F G : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G], ∀ (U : Set E) (A : E → F →L[ℝ] G) (b : E → F), ContDiffOn ℝ ∞ A U → ContDiffOn ℝ ∞ b U → ContDiffOn ℝ ∞ (fun z => A z (b z)) U) (h_E006 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F], ∀ (f : E → F) (z : E), ContDiffAt ℝ 2 f z → ∀ v w : E, fderiv ℝ (fderiv ℝ f) z v w = fderiv ℝ (fderiv ℝ f) z w v) (h_E007 : ∀ (E F G : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G], ∀ (A : E → F →L[ℝ] G) (b : E → F) (z : E), DifferentiableAt ℝ A z → DifferentiableAt ℝ b z → fderiv ℝ (fun y => A y (b y)) z = (A z).comp (fderiv ℝ b z) + (fderiv ℝ A z).flip (b z)) (h_E009 : ∀ (E V : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [InnerProductSpace ℝ V], ∀ (U : Set E) (f g : E → V), ContDiffOn ℝ ∞ f U → ContDiffOn ℝ ∞ g U → ContDiffOn ℝ ∞ (fun y => inner ℝ (f y) (g y)) U) (h_E014 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F], ∀ (k : ℕ) (f : Fin k → E → F) (U : Set E), (∀ i, ContDiffOn ℝ ∞ (f i) U) → ContDiffOn ℝ ∞ (fun z => ∑ i, f i z) U) :
    Regular U ∧ (∀ z ∈ omega n, ∀ j : Fin n, D (tau n) (uj U j) z = utj U j z) := by
  refine ⟨@yui_aux_0001 n m U q h_H001 h_T001 h_E004 h_E005 h_E006 h_E007 h_E009 h_E014, ?_⟩
  intro z hz j
  have hopen : IsOpen (omega n) := isOpen_lt continuous_const continuous_snd
  have hU : ContDiffOn ℝ ∞ U (omega n) := by
    simpa only [ordered] using h_T001.1 []
  have htwo : ContDiffAt ℝ 2 U z :=
    (hU.contDiffAt (hopen.mem_nhds hz)).of_le (by simp)
  have heval := @yui_aux_0002 n m U q h_H001 h_T001 h_E004 h_E005 h_E006 h_E007 h_E009 h_E014
  change D (tau n) (D (sigma n j) U) z = D (sigma n j) (D (tau n) U) z
  rw [heval z hz (sigma n j) (tau n), heval z hz (tau n) (sigma n j)]
  exact h_E006 (Z n) (V m) U z htwo (tau n) (sigma n j)

namespace Local_T005
theorem yui_aux_0001 (n : ℕ) (m : ℕ) (U : Z n → V m) (q : V m) (h_H003 : ∀ s t : ℝ, 0 < s → s < t → ∃ C : Set (X n), IsCompact C ∧ ∀ x : X n, x ∉ C → ∀ r ∈ Icc s t, U (x, r) = q) (h_E010 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F], ∀ (f g : E → F) (z : E), (f =ᶠ[𝓝 z] g) → fderiv ℝ f z = fderiv ℝ g z) : yui_aux_type% "∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (f : Z n → F) (c : F) (O : Set (Z n)), IsOpen O → EqOn f (fun _ => c) O → ∀ z ∈ O, fderiv ℝ f z = 0" := by
  intro F _ _ f c O hO hf z hz
  have he : f =ᶠ[𝓝 z] (fun _ => c) := (hO.eventually_mem hz).mono (fun y hy => hf hy)
  rw [h_E010 (Z n) F f (fun _ => c) z he]
  exact fderiv_const_apply c

theorem yui_aux_0002 (n : ℕ) (m : ℕ) (U : Z n → V m) (q : V m) (h_H003 : ∀ s t : ℝ, 0 < s → s < t → ∃ C : Set (X n), IsCompact C ∧ ∀ x : X n, x ∉ C → ∀ r ∈ Icc s t, U (x, r) = q) (h_E010 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F], ∀ (f g : E → F) (z : E), (f =ᶠ[𝓝 z] g) → fderiv ℝ f z = fderiv ℝ g z) : yui_aux_type% "∀ (O : Set (Z n)), IsOpen O → EqOn U (fun _ => q) O → (∀ ds : List (Z n), ds ≠ [] → ∀ z ∈ O, ordered U ds z = 0) ∧ (∀ f : Z n → ℝ, ScalarField U f → ∀ z ∈ O, f z = 0)" := by
  intro O hO hU
  have hord : ∀ ds : List (Z n), ds ≠ [] → ∀ z ∈ O, ordered U ds z = 0 := by
    intro ds
    induction ds with
    | nil => simp
    | cons v vs ih =>
      intro _ z hz
      change fderiv ℝ (ordered U vs) z v = 0
      cases vs with
      | nil =>
        have hd : fderiv ℝ U z = 0 :=
          yui_aux_0001 n m U q h_H003 h_E010 (V m) U q O hO hU z hz
        simpa only [ordered, hd, ContinuousLinearMap.zero_apply]
      | cons w ws =>
        have hf : EqOn (ordered U (w :: ws)) (fun _ => 0) O :=
          fun y hy => ih (by simp) y hy
        rw [yui_aux_0001 n m U q h_H003 h_E010 (V m)
          (ordered U (w :: ws)) 0 O hO hf z hz]
        rfl
  have ht : ∀ z ∈ O, ut U z = 0 := by
    intro z hz
    exact hord [tau n] (by simp) z hz
  have hj : ∀ j z, z ∈ O → uj U j z = 0 := by
    intro j z hz
    exact hord [sigma n j] (by simp) z hz
  have hdensity : ∀ z ∈ O, density U z = 0 := by
    intro z hz
    simp [density, ht z hz, fun j => hj j z hz]
  refine ⟨hord, ?_⟩
  intro f hf z hz
  rcases hf with rfl | rfl | rfl | ⟨j, rfl | rfl | rfl⟩
  · exact hdensity z hz
  · change fderiv ℝ (density U) z (tau n) = 0
    rw [yui_aux_0001 n m U q h_H003 h_E010 ℝ (density U) 0 O hO hdensity z hz]
    rfl
  · simp [timeProd, ht z hz]
  · simp [gradProd, hj j z hz]
  · simp [lapProd, ht z hz]
  · simp [flux, ht z hz]

theorem yui_aux_0003 (n : ℕ) (m : ℕ) (U : Z n → V m) (q : V m) (h_H003 : ∀ s t : ℝ, 0 < s → s < t → ∃ C : Set (X n), IsCompact C ∧ ∀ x : X n, x ∉ C → ∀ r ∈ Icc s t, U (x, r) = q) (h_E010 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F], ∀ (f g : E → F) (z : E), (f =ᶠ[𝓝 z] g) → fderiv ℝ f z = fderiv ℝ g z) : yui_aux_type% "∀ (O : Set (Z n)), IsOpen O → EqOn U (fun _ => q) O → ∀ k : ℕ, 0 < k → ∀ z ∈ O, iteratedFDeriv ℝ k U z = 0" := by
  intro O hO hU
  have heq : ∀ k : ℕ, ∀ z ∈ O,
      iteratedFDeriv ℝ k U z = iteratedFDeriv ℝ k (fun _ : Z n => q) z := by
    intro k
    induction k with
    | zero =>
      intro z hz
      simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, hU hz]
    | succ k ih =>
      intro z hz
      have he : iteratedFDeriv ℝ k U =ᶠ[𝓝 z]
          iteratedFDeriv ℝ k (fun _ : Z n => q) :=
        (hO.eventually_mem hz).mono (fun y hy => ih y hy)
      have hd : fderiv ℝ (iteratedFDeriv ℝ k U) z =
          fderiv ℝ (iteratedFDeriv ℝ k (fun _ : Z n => q)) z :=
        h_E010 (Z n) _ _ _ z he
      simp only [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, hd]
  intro k hk z hz
  rw [heq k z hz, iteratedFDeriv_const_of_ne (Nat.ne_of_gt hk) q]
  rfl

end Local_T005
open Local_T005 in
theorem T005 (n : ℕ) (m : ℕ) (U : Z n → V m) (q : V m) (h_H003 : ∀ s t : ℝ, 0 < s → s < t → ∃ C : Set (X n), IsCompact C ∧ ∀ x : X n, x ∉ C → ∀ r ∈ Icc s t, U (x, r) = q) (h_E010 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F], ∀ (f g : E → F) (z : E), (f =ᶠ[𝓝 z] g) → fderiv ℝ f z = fderiv ℝ g z) :
    ∀ t₀ : ℝ, 0 < t₀ → ∃ C : Set (X n), IsCompact C ∧
 ∀ r ∈ Ioo (t₀ / 2) (3 * t₀ / 2),
 (∀ ds : List (Z n), ds ≠ [] → ∀ x : X n, x ∉ C → ordered U ds (x, r) = 0) ∧
 (∀ k : ℕ, 0 < k → ∀ x : X n, x ∉ C → iteratedFDeriv ℝ k U (x, r) = 0) ∧
 (∀ f : Z n → ℝ, ScalarField U f → ∀ x : X n, x ∉ C → f (x, r) = 0) := by
  intro t₀ ht₀
  have hs : 0 < t₀ / 2 := by linarith
  have hst : t₀ / 2 < 3 * t₀ / 2 := by linarith
  have hCex := h_H003 (t₀ / 2) (3 * t₀ / 2) hs hst
  rcases hCex with ⟨C, hC, hUC⟩
  let O : Set (Z n) := Cᶜ ×ˢ Ioo (t₀ / 2) (3 * t₀ / 2)
  have hO : IsOpen O := hC.isClosed.isOpen_compl.prod isOpen_Ioo
  have hU : EqOn U (fun _ => q) O := by
    intro z hz
    exact hUC z.1 hz.1 z.2 ⟨le_of_lt hz.2.1, le_of_lt hz.2.2⟩
  have hv := yui_aux_0002 n m U q h_H003 h_E010 O hO hU
  have htensor := yui_aux_0003 n m U q h_H003 h_E010 O hO hU
  refine ⟨C, hC, ?_⟩
  intro r hr
  refine ⟨?_, ?_, ?_⟩
  · intro ds hds x hx
    exact hv.1 ds hds (x, r) ⟨hx, hr⟩
  · intro k hk x hx
    exact htensor k hk (x, r) ⟨hx, hr⟩
  · intro f hf x hx
    exact hv.2 f hf (x, r) ⟨hx, hr⟩

theorem T006 (n : ℕ) (m : ℕ) (U : Z n → V m) (q : V m) (h_E003 : ∀ (n : ℕ) (C : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ), IsCompact C → ContinuousOn f C → IntegrableOn f C volume) (h_E012 : ∀ (n : ℕ) (C : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ), MeasurableSet C → IntegrableOn h C volume → Integrable (C.indicator h) volume) :
    ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
 (f : Z n → F) (C : Set (X n)) (r : ℝ),
 IsCompact C → Continuous (fun x : X n => f (x, r)) →
 (∀ x : X n, x ∉ C → f (x, r) = 0) → SectionFacts f C r := by
  intro F _ _ _ f C r hC hc hz
  have hs : Function.support (fun x : X n => f (x, r)) ⊆ C := by
    intro x hx
    by_contra h
    exact hx (hz x h)
  have ht : tsupport (fun x : X n => f (x, r)) ⊆ C :=
    closure_minimal hs hC.isClosed
  have hcompact : HasCompactSupport (fun x : X n => f (x, r)) :=
    HasCompactSupport.intro hC hz
  have hnC : IntegrableOn (fun x : X n => ‖f (x, r)‖) C volume :=
    h_E003 n C (fun x => ‖f (x, r)‖) hC hc.norm.continuousOn
  have hni : Integrable (C.indicator (fun x : X n => ‖f (x, r)‖)) volume :=
    h_E012 n C (fun x => ‖f (x, r)‖) hC.isClosed.measurableSet hnC
  have heq : C.indicator (fun x : X n => ‖f (x, r)‖) =
      (fun x : X n => ‖f (x, r)‖) := by
    funext x
    by_cases hx : x ∈ C
    · simp [hx]
    · simp [hx, hz x hx]
  have hn : Integrable (fun x : X n => ‖f (x, r)‖) volume := by
    rw [heq] at hni
    exact hni
  have hf : Integrable (fun x : X n => f (x, r)) volume :=
    (integrable_norm_iff hc.aestronglyMeasurable).mp hn
  exact ⟨hc, ht, hcompact, hf⟩

namespace Local_T007
theorem yui_aux_0001 (n : ℕ) (m : ℕ) (U : Z n → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m ∧ ‖q‖ = 1 ∧ ContDiffOn ℝ ∞ U (omega n)) (h_H003 : ∀ s t : ℝ, 0 < s → s < t → ∃ C : Set (X n), IsCompact C ∧ ∀ x : X n, x ∉ C → ∀ r ∈ Icc s t, U (x, r) = q) (h_T001 : (∀ ds : List (Z n), ContDiffOn ℝ ∞ (ordered U ds) (omega n)) ∧ (∀ k : ℕ, ContDiffOn ℝ ∞ (iteratedFDeriv ℝ k U) (omega n))) (h_T002 : Regular U ∧ (∀ z ∈ omega n, ∀ j : Fin n, D (tau n) (uj U j) z = utj U j z)) (h_T003 : ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]
 (f : Z n → F), ContDiffOn ℝ ∞ f (omega n) →
 ∀ (x : X n) (t : ℝ), 0 < t →
 HasDerivAt (fun r => f (x, r)) (D (tau n) f (x, t)) t ∧
 (∀ v : X n, fderiv ℝ (fun y : X n => f (y, t)) x v = D (v, 0) f (x, t)) ∧
 (∀ v : X n, HasDerivAt (fun h : ℝ => f (x + h • v, t)) (D (v, 0) f (x, t)) 0)) (h_T005 : ∀ t₀ : ℝ, 0 < t₀ → ∃ C : Set (X n), IsCompact C ∧
 ∀ r ∈ Ioo (t₀ / 2) (3 * t₀ / 2),
 (∀ ds : List (Z n), ds ≠ [] → ∀ x : X n, x ∉ C → ordered U ds (x, r) = 0) ∧
 (∀ k : ℕ, 0 < k → ∀ x : X n, x ∉ C → iteratedFDeriv ℝ k U (x, r) = 0) ∧
 (∀ f : Z n → ℝ, ScalarField U f → ∀ x : X n, x ∉ C → f (x, r) = 0)) (h_T006 : ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
 (f : Z n → F) (C : Set (X n)) (r : ℝ),
 IsCompact C → Continuous (fun x : X n => f (x, r)) →
 (∀ x : X n, x ∉ C → f (x, r) = 0) → SectionFacts f C r) (h_E019 : ∀ (E F G : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G], ∀ (S : Set E) (T : Set F) (f : E → F) (g : F → G), ContDiffOn ℝ ∞ g T → ContDiffOn ℝ ∞ f S → MapsTo f S T → ContDiffOn ℝ ∞ (g ∘ f) S) : yui_aux_type% "∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (f : Z n → F), ContDiffOn ℝ ∞ f (omega n) → ∀ r : ℝ, 0 < r → Continuous (fun x : X n => f (x, r))" := by
  intro F _ _ f hf r hr
  have hi : ContDiff ℝ ∞ (fun x : X n => (x, r)) := contDiff_id.prodMk contDiff_const
  have hc : ContDiffOn ℝ ∞ (fun x : X n => f (x, r)) Set.univ :=
    h_E019 (X n) (Z n) F Set.univ (omega n) (fun x => (x, r)) f hf hi.contDiffOn (by intro x hx; exact hr)
  exact continuousOn_univ.mp hc.continuousOn

theorem yui_aux_0002 (n : ℕ) (m : ℕ) (U : Z n → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m ∧ ‖q‖ = 1 ∧ ContDiffOn ℝ ∞ U (omega n)) (h_H003 : ∀ s t : ℝ, 0 < s → s < t → ∃ C : Set (X n), IsCompact C ∧ ∀ x : X n, x ∉ C → ∀ r ∈ Icc s t, U (x, r) = q) (h_T001 : (∀ ds : List (Z n), ContDiffOn ℝ ∞ (ordered U ds) (omega n)) ∧ (∀ k : ℕ, ContDiffOn ℝ ∞ (iteratedFDeriv ℝ k U) (omega n))) (h_T002 : Regular U ∧ (∀ z ∈ omega n, ∀ j : Fin n, D (tau n) (uj U j) z = utj U j z)) (h_T003 : ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]
 (f : Z n → F), ContDiffOn ℝ ∞ f (omega n) →
 ∀ (x : X n) (t : ℝ), 0 < t →
 HasDerivAt (fun r => f (x, r)) (D (tau n) f (x, t)) t ∧
 (∀ v : X n, fderiv ℝ (fun y : X n => f (y, t)) x v = D (v, 0) f (x, t)) ∧
 (∀ v : X n, HasDerivAt (fun h : ℝ => f (x + h • v, t)) (D (v, 0) f (x, t)) 0)) (h_T005 : ∀ t₀ : ℝ, 0 < t₀ → ∃ C : Set (X n), IsCompact C ∧
 ∀ r ∈ Ioo (t₀ / 2) (3 * t₀ / 2),
 (∀ ds : List (Z n), ds ≠ [] → ∀ x : X n, x ∉ C → ordered U ds (x, r) = 0) ∧
 (∀ k : ℕ, 0 < k → ∀ x : X n, x ∉ C → iteratedFDeriv ℝ k U (x, r) = 0) ∧
 (∀ f : Z n → ℝ, ScalarField U f → ∀ x : X n, x ∉ C → f (x, r) = 0)) (h_T006 : ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
 (f : Z n → F) (C : Set (X n)) (r : ℝ),
 IsCompact C → Continuous (fun x : X n => f (x, r)) →
 (∀ x : X n, x ∉ C → f (x, r) = 0) → SectionFacts f C r) (h_E019 : ∀ (E F G : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G], ∀ (S : Set E) (T : Set F) (f : E → F) (g : F → G), ContDiffOn ℝ ∞ g T → ContDiffOn ℝ ∞ f S → MapsTo f S T → ContDiffOn ℝ ∞ (g ∘ f) S) : yui_aux_type% "∀ k : ℕ, FiniteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin k => Z n) (V m))" := by
  intro k
  let L : ContinuousMultilinearMap ℝ (fun _ : Fin k => Z n) (V m) →ₗ[ℝ] MultilinearMap ℝ (fun _ : Fin k => Z n) (V m) := ContinuousMultilinearMap.toMultilinearMapLinear
  exact FiniteDimensional.of_injective L ContinuousMultilinearMap.toMultilinearMap_injective

end Local_T007
open Local_T007 in
theorem T007 (n : ℕ) (m : ℕ) (U : Z n → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m ∧ ‖q‖ = 1 ∧ ContDiffOn ℝ ∞ U (omega n)) (h_H003 : ∀ s t : ℝ, 0 < s → s < t → ∃ C : Set (X n), IsCompact C ∧ ∀ x : X n, x ∉ C → ∀ r ∈ Icc s t, U (x, r) = q) (h_T001 : (∀ ds : List (Z n), ContDiffOn ℝ ∞ (ordered U ds) (omega n)) ∧ (∀ k : ℕ, ContDiffOn ℝ ∞ (iteratedFDeriv ℝ k U) (omega n))) (h_T002 : Regular U ∧ (∀ z ∈ omega n, ∀ j : Fin n, D (tau n) (uj U j) z = utj U j z)) (h_T003 : ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]
 (f : Z n → F), ContDiffOn ℝ ∞ f (omega n) →
 ∀ (x : X n) (t : ℝ), 0 < t →
 HasDerivAt (fun r => f (x, r)) (D (tau n) f (x, t)) t ∧
 (∀ v : X n, fderiv ℝ (fun y : X n => f (y, t)) x v = D (v, 0) f (x, t)) ∧
 (∀ v : X n, HasDerivAt (fun h : ℝ => f (x + h • v, t)) (D (v, 0) f (x, t)) 0)) (h_T005 : ∀ t₀ : ℝ, 0 < t₀ → ∃ C : Set (X n), IsCompact C ∧
 ∀ r ∈ Ioo (t₀ / 2) (3 * t₀ / 2),
 (∀ ds : List (Z n), ds ≠ [] → ∀ x : X n, x ∉ C → ordered U ds (x, r) = 0) ∧
 (∀ k : ℕ, 0 < k → ∀ x : X n, x ∉ C → iteratedFDeriv ℝ k U (x, r) = 0) ∧
 (∀ f : Z n → ℝ, ScalarField U f → ∀ x : X n, x ∉ C → f (x, r) = 0)) (h_T006 : ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
 (f : Z n → F) (C : Set (X n)) (r : ℝ),
 IsCompact C → Continuous (fun x : X n => f (x, r)) →
 (∀ x : X n, x ∉ C → f (x, r) = 0) → SectionFacts f C r) (h_E019 : ∀ (E F G : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G], ∀ (S : Set E) (T : Set F) (f : E → F) (g : F → G), ContDiffOn ℝ ∞ g T → ContDiffOn ℝ ∞ f S → MapsTo f S T → ContDiffOn ℝ ∞ (g ∘ f) S) :
    Regular U ∧ (∀ z ∈ omega n, ∀ j : Fin n, D (tau n) (uj U j) z = utj U j z) ∧ LocalData U ∧
 (∀ x : X n, ∀ t : ℝ, 0 < t → HasDerivAt (fun r => density U (x, r)) (densityTime U (x, t)) t) ∧
 (∀ x : X n, ∀ t : ℝ, 0 < t → ∀ j : Fin n,
   HasDerivAt (fun r => uj U j (x, r)) (utj U j (x, t)) t) := by
  have hsection := @yui_aux_0001 n m U q h_H001 h_H003 h_T001 h_T002 h_T003 h_T005 h_T006 h_E019
  refine ⟨h_T002.1, h_T002.2, ?_, ?_, ?_⟩
  · intro t₀ ht₀
    obtain ⟨C, hC, hloc⟩ := h_T005 t₀ ht₀
    refine ⟨C, hC, ?_⟩
    intro r hr
    have hrpos : 0 < r := by have := hr.1; linarith
    obtain ⟨hord, hten, hscalar⟩ := hloc r hr
    refine ⟨?_, ?_, ?_⟩
    · intro ds hds
      refine ⟨hord ds hds, ?_⟩
      exact h_T006 (V m) (ordered U ds) C r hC
        (hsection (V m) (ordered U ds) (h_T001.1 ds) r hrpos) (hord ds hds)
    · intro k hk
      letI : FiniteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin k => Z n) (V m)) :=
        @yui_aux_0002 n m U q h_H001 h_H003 h_T001 h_T002 h_T003 h_T005 h_T006 h_E019 k
      refine ⟨hten k hk, ?_⟩
      exact h_T006 _ (iteratedFDeriv ℝ k U) C r hC
        (hsection _ (iteratedFDeriv ℝ k U) (h_T001.2 k) r hrpos) (hten k hk)
    · intro f hf
      refine ⟨hscalar f hf, ?_⟩
      exact h_T006 ℝ f C r hC
        (hsection ℝ f (h_T002.1.2.2 f hf) r hrpos) (hscalar f hf)
  · intro x t ht
    exact (h_T003 ℝ (density U) (h_T002.1.2.2 _ (Or.inl rfl)) x t ht).1
  · intro x t ht j
    have hs : ContDiffOn ℝ ∞ (uj U j) (omega n) := by
      simpa only [ordered, uj] using h_T001.1 [sigma n j]
    have hd := (h_T003 (V m) (uj U j) hs x t ht).1
    rw [h_T002.2 (x, t) ht j] at hd
    exact hd

namespace Local_T008
theorem yui_aux_0001 (n : ℕ) (m : ℕ) (U : Z n → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m ∧ ‖q‖ = 1 ∧ ContDiffOn ℝ ∞ U (omega n)) (h_T007 : Regular U ∧ (∀ z ∈ omega n, ∀ j : Fin n, D (tau n) (uj U j) z = utj U j z) ∧ LocalData U ∧
 (∀ x : X n, ∀ t : ℝ, 0 < t → HasDerivAt (fun r => density U (x, r)) (densityTime U (x, t)) t) ∧
 (∀ x : X n, ∀ t : ℝ, 0 < t → ∀ j : Fin n,
   HasDerivAt (fun r => uj U j (x, r)) (utj U j (x, t)) t)) (h_E004 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F], ∀ (U : Set E) (f : E → F), IsOpen U → (ContDiffOn ℝ ∞ f U ↔ DifferentiableOn ℝ f U ∧ ContDiffOn ℝ ∞ (fderiv ℝ f) U)) (h_E008 : ∀ (E V : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [InnerProductSpace ℝ V], ∀ (f g : E → V) (z v : E), DifferentiableAt ℝ f z → DifferentiableAt ℝ g z → fderiv ℝ (fun y => inner ℝ (f y) (g y)) z v = inner ℝ (f z) (fderiv ℝ g z v) + inner ℝ (fderiv ℝ f z v) (g z)) (h_E013 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F], ∀ (l : E → F) (L : E →L[ℝ] F) (c : ℝ → E) (v : E) (t : ℝ), HasFDerivAt l L (c t) → HasDerivAt c v t → HasDerivAt (l ∘ c) (L v) t) (h_E015 : ∀ (k : ℕ) (A : Fin k → ℝ → ℝ) (a : Fin k → ℝ) (t : ℝ), (∀ i, HasDerivAt (A i) (a i) t) → HasDerivAt (fun r => ∑ i, A i r) (∑ i, a i) t) : yui_aux_type% "∀ (x : X n) (t : ℝ), HasDerivAt (fun r : ℝ => (x, r)) (tau n) t" := by
  intro x t
  simpa only [tau, id_eq] using (hasDerivAt_const t x).prodMk (hasDerivAt_id t)

theorem yui_aux_0002 (n : ℕ) (m : ℕ) (U : Z n → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m ∧ ‖q‖ = 1 ∧ ContDiffOn ℝ ∞ U (omega n)) (h_T007 : Regular U ∧ (∀ z ∈ omega n, ∀ j : Fin n, D (tau n) (uj U j) z = utj U j z) ∧ LocalData U ∧
 (∀ x : X n, ∀ t : ℝ, 0 < t → HasDerivAt (fun r => density U (x, r)) (densityTime U (x, t)) t) ∧
 (∀ x : X n, ∀ t : ℝ, 0 < t → ∀ j : Fin n,
   HasDerivAt (fun r => uj U j (x, r)) (utj U j (x, t)) t)) (h_E004 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F], ∀ (U : Set E) (f : E → F), IsOpen U → (ContDiffOn ℝ ∞ f U ↔ DifferentiableOn ℝ f U ∧ ContDiffOn ℝ ∞ (fderiv ℝ f) U)) (h_E008 : ∀ (E V : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [InnerProductSpace ℝ V], ∀ (f g : E → V) (z v : E), DifferentiableAt ℝ f z → DifferentiableAt ℝ g z → fderiv ℝ (fun y => inner ℝ (f y) (g y)) z v = inner ℝ (f z) (fderiv ℝ g z v) + inner ℝ (fderiv ℝ f z v) (g z)) (h_E013 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F], ∀ (l : E → F) (L : E →L[ℝ] F) (c : ℝ → E) (v : E) (t : ℝ), HasFDerivAt l L (c t) → HasDerivAt c v t → HasDerivAt (l ∘ c) (L v) t) (h_E015 : ∀ (k : ℕ) (A : Fin k → ℝ → ℝ) (a : Fin k → ℝ) (t : ℝ), (∀ i, HasDerivAt (A i) (a i) t) → HasDerivAt (fun r => ∑ i, A i r) (∑ i, a i) t) : yui_aux_type% "∀ (f : Z n → V m) (x : X n) (t : ℝ), DifferentiableAt ℝ f (x, t) → HasDerivAt (fun r => ‖f (x, r)‖ ^ 2) (2 * inner ℝ (f (x, t)) (D (tau n) f (x, t))) t" := by
  intro f x t hf
  have hc := (@yui_aux_0001 n m U q h_H001 h_T007 h_E004 h_E008 h_E013 h_E015) x t
  have hi : DifferentiableAt ℝ (fun y => inner ℝ (f y) (f y)) (x, t) :=
    hf.inner ℝ hf
  have hd := h_E013 (Z n) ℝ (fun y => inner ℝ (f y) (f y))
    (fderiv ℝ (fun y => inner ℝ (f y) (f y)) (x, t))
    (fun r : ℝ => (x, r)) (tau n) t hi.hasFDerivAt hc
  have he := h_E008 (Z n) (V m) f f (x, t) (tau n) hf hf
  rw [he] at hd
  have hs : inner ℝ (f (x,t)) (fderiv ℝ f (x,t) (tau n)) +
      inner ℝ (fderiv ℝ f (x,t) (tau n)) (f (x,t)) =
      2 * inner ℝ (f (x,t)) (D (tau n) f (x,t)) := by
    unfold D
    nlinarith [real_inner_comm (fderiv ℝ f (x,t) (tau n)) (f (x,t))]
  simpa only [Function.comp_def, real_inner_self_eq_norm_sq, hs] using hd

theorem yui_aux_0003 (n : ℕ) (m : ℕ) (U : Z n → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m ∧ ‖q‖ = 1 ∧ ContDiffOn ℝ ∞ U (omega n)) (h_T007 : Regular U ∧ (∀ z ∈ omega n, ∀ j : Fin n, D (tau n) (uj U j) z = utj U j z) ∧ LocalData U ∧
 (∀ x : X n, ∀ t : ℝ, 0 < t → HasDerivAt (fun r => density U (x, r)) (densityTime U (x, t)) t) ∧
 (∀ x : X n, ∀ t : ℝ, 0 < t → ∀ j : Fin n,
   HasDerivAt (fun r => uj U j (x, r)) (utj U j (x, t)) t)) (h_E004 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F], ∀ (U : Set E) (f : E → F), IsOpen U → (ContDiffOn ℝ ∞ f U ↔ DifferentiableOn ℝ f U ∧ ContDiffOn ℝ ∞ (fderiv ℝ f) U)) (h_E008 : ∀ (E V : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [InnerProductSpace ℝ V], ∀ (f g : E → V) (z v : E), DifferentiableAt ℝ f z → DifferentiableAt ℝ g z → fderiv ℝ (fun y => inner ℝ (f y) (g y)) z v = inner ℝ (f z) (fderiv ℝ g z v) + inner ℝ (fderiv ℝ f z v) (g z)) (h_E013 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F], ∀ (l : E → F) (L : E →L[ℝ] F) (c : ℝ → E) (v : E) (t : ℝ), HasFDerivAt l L (c t) → HasDerivAt c v t → HasDerivAt (l ∘ c) (L v) t) (h_E015 : ∀ (k : ℕ) (A : Fin k → ℝ → ℝ) (a : Fin k → ℝ) (t : ℝ), (∀ i, HasDerivAt (A i) (a i) t) → HasDerivAt (fun r => ∑ i, A i r) (∑ i, a i) t) : yui_aux_type% "∀ (f g : ℝ → ℝ) (a b t : ℝ), HasDerivAt f a t → HasDerivAt g b t → HasDerivAt (fun r => f r + g r) (a + b) t" := by
  intro f g a b t hf hg
  simpa only [Pi.add_def] using hf.add hg

end Local_T008
open Local_T008 in
theorem T008 (n : ℕ) (m : ℕ) (U : Z n → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m ∧ ‖q‖ = 1 ∧ ContDiffOn ℝ ∞ U (omega n)) (h_T007 : Regular U ∧ (∀ z ∈ omega n, ∀ j : Fin n, D (tau n) (uj U j) z = utj U j z) ∧ LocalData U ∧
 (∀ x : X n, ∀ t : ℝ, 0 < t → HasDerivAt (fun r => density U (x, r)) (densityTime U (x, t)) t) ∧
 (∀ x : X n, ∀ t : ℝ, 0 < t → ∀ j : Fin n,
   HasDerivAt (fun r => uj U j (x, r)) (utj U j (x, t)) t)) (h_E004 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F], ∀ (U : Set E) (f : E → F), IsOpen U → (ContDiffOn ℝ ∞ f U ↔ DifferentiableOn ℝ f U ∧ ContDiffOn ℝ ∞ (fderiv ℝ f) U)) (h_E008 : ∀ (E V : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [InnerProductSpace ℝ V], ∀ (f g : E → V) (z v : E), DifferentiableAt ℝ f z → DifferentiableAt ℝ g z → fderiv ℝ (fun y => inner ℝ (f y) (g y)) z v = inner ℝ (f z) (fderiv ℝ g z v) + inner ℝ (fderiv ℝ f z v) (g z)) (h_E013 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F], ∀ (l : E → F) (L : E →L[ℝ] F) (c : ℝ → E) (v : E) (t : ℝ), HasFDerivAt l L (c t) → HasDerivAt c v t → HasDerivAt (l ∘ c) (L v) t) (h_E015 : ∀ (k : ℕ) (A : Fin k → ℝ → ℝ) (a : Fin k → ℝ) (t : ℝ), (∀ i, HasDerivAt (A i) (a i) t) → HasDerivAt (fun r => ∑ i, A i r) (∑ i, a i) t) :
    ∀ x : X n, ∀ t : ℝ, 0 < t →
 HasDerivAt (fun r => density U (x, r)) (rate U (x, t)) t ∧
 densityTime U (x, t) = rate U (x, t) := by
  intro x t ht
  have hopen : IsOpen (omega n) := isOpen_lt continuous_const continuous_snd
  have hz : (x,t) ∈ omega n := ht
  have hd (f : Z n → V m) (hf : ContDiffOn ℝ ∞ f (omega n)) :
      DifferentiableAt ℝ f (x,t) :=
    ((h_E004 (Z n) (V m) (omega n) f hopen).mp hf).1.differentiableAt
      (hopen.mem_nhds hz)
  have htu : ContDiffOn ℝ ∞ (ut U) (omega n) := by
    simpa only [ordered, ut] using h_T007.1.1 [tau n]
  have htder : HasDerivAt (fun r => ‖ut U (x,r)‖ ^ 2)
      (2 * timeProd U (x,t)) t := by
    simpa only [timeProd, utt] using
      (@yui_aux_0002 n m U q h_H001 h_T007 h_E004 h_E008 h_E013 h_E015)
        (ut U) x t (hd (ut U) htu)
  have hjder (j : Fin n) : HasDerivAt (fun r => ‖uj U j (x,r)‖ ^ 2)
      (2 * gradProd U j (x,t)) t := by
    have hj : ContDiffOn ℝ ∞ (uj U j) (omega n) := by
      simpa only [ordered, uj] using h_T007.1.1 [sigma n j]
    have hs := (@yui_aux_0002 n m U q h_H001 h_T007 h_E004 h_E008 h_E013 h_E015)
      (uj U j) x t (hd (uj U j) hj)
    rw [h_T007.2.1 (x,t) hz j] at hs
    exact hs
  have hsum := h_E015 n (fun j r => ‖uj U j (x,r)‖ ^ 2)
    (fun j => 2 * gradProd U j (x,t)) t hjder
  have hadd := (@yui_aux_0003 n m U q h_H001 h_T007 h_E004 h_E008 h_E013 h_E015)
    (fun r => ‖ut U (x,r)‖ ^ 2) (fun r => ∑ j, ‖uj U j (x,r)‖ ^ 2)
    (2 * timeProd U (x,t)) (∑ j, 2 * gradProd U j (x,t)) t htder hsum
  have hr : HasDerivAt (fun r => density U (x,r)) (rate U (x,t)) t := by
    simpa only [density, rate, Finset.mul_sum] using hadd
  exact ⟨hr, (h_T007.2.2.2.1 x t ht).unique hr⟩

namespace Local_T009
theorem yui_aux_0001 (n : ℕ) (m : ℕ) (U : Z n → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m ∧ ‖q‖ = 1 ∧ ContDiffOn ℝ ∞ U (omega n)) (h_T007 : Regular U ∧ (∀ z ∈ omega n, ∀ j : Fin n, D (tau n) (uj U j) z = utj U j z) ∧ LocalData U ∧
 (∀ x : X n, ∀ t : ℝ, 0 < t → HasDerivAt (fun r => density U (x, r)) (densityTime U (x, t)) t) ∧
 (∀ x : X n, ∀ t : ℝ, 0 < t → ∀ j : Fin n,
   HasDerivAt (fun r => uj U j (x, r)) (utj U j (x, t)) t)) (h_E003 : ∀ (n : ℕ) (C : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ), IsCompact C → ContinuousOn f C → IntegrableOn f C volume) (h_E011 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F], ∀ (K : Set E) (h : E → F), IsCompact K → ContinuousOn h K → ∃ B : ℝ, ∀ z ∈ K, ‖h z‖ ≤ B) (h_E012 : ∀ (n : ℕ) (C : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ), MeasurableSet C → IntegrableOn h C volume → Integrable (C.indicator h) volume) : yui_aux_type% "ContinuousOn (rate U) (omega n)" := by
  have hT : ContinuousOn (timeProd U) (omega n) := (h_T007.1.2.2 _ (Or.inr (Or.inr (Or.inl rfl)))).continuousOn
  have hA : ∀ j : Fin n, ContinuousOn (gradProd U j) (omega n) := by
    intro j
    exact (h_T007.1.2.2 _ (Or.inr (Or.inr (Or.inr ⟨j, Or.inl rfl⟩)))).continuousOn
  unfold rate
  exact (continuousOn_const.mul hT).add (continuousOn_const.mul (continuousOn_finsetSum Finset.univ (fun j _ => hA j)))

theorem yui_aux_0002 (n : ℕ) (m : ℕ) (U : Z n → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m ∧ ‖q‖ = 1 ∧ ContDiffOn ℝ ∞ U (omega n)) (h_T007 : Regular U ∧ (∀ z ∈ omega n, ∀ j : Fin n, D (tau n) (uj U j) z = utj U j z) ∧ LocalData U ∧
 (∀ x : X n, ∀ t : ℝ, 0 < t → HasDerivAt (fun r => density U (x, r)) (densityTime U (x, t)) t) ∧
 (∀ x : X n, ∀ t : ℝ, 0 < t → ∀ j : Fin n,
   HasDerivAt (fun r => uj U j (x, r)) (utj U j (x, t)) t)) (h_E003 : ∀ (n : ℕ) (C : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ), IsCompact C → ContinuousOn f C → IntegrableOn f C volume) (h_E011 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F], ∀ (K : Set E) (h : E → F), IsCompact K → ContinuousOn h K → ∃ B : ℝ, ∀ z ∈ K, ‖h z‖ ≤ B) (h_E012 : ∀ (n : ℕ) (C : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ), MeasurableSet C → IntegrableOn h C volume → Integrable (C.indicator h) volume) : yui_aux_type% "∀ (C : Set (X n)) (r : ℝ), IsCompact C → Localized U C r → Integrable (fun x : X n => rate U (x, r)) volume" := by
  classical
  intro C r hC hloc
  have hint : ∀ f : Z n → ℝ, ScalarField U f → Integrable (fun x : X n => f (x, r)) volume := by
    intro f hf
    have hsec := hloc.2.2 f hf
    have hon : IntegrableOn (fun x : X n => f (x, r)) C volume :=
      h_E003 n C _ hC hsec.2.1.continuousOn
    have hi := h_E012 n C _ hC.isClosed.measurableSet hon
    have heq : C.indicator (fun x : X n => f (x, r)) = (fun x : X n => f (x, r)) := by
      funext x
      by_cases hx : x ∈ C
      · simp [hx]
      · simp [hx, hsec.1 x hx]
    rw [heq] at hi
    exact hi
  have hT : Integrable (fun x : X n => timeProd U (x, r)) volume :=
    hint _ (Or.inr (Or.inr (Or.inl rfl)))
  have hA : ∀ j : Fin n, Integrable (fun x : X n => gradProd U j (x, r)) volume := by
    intro j
    exact hint _ (Or.inr (Or.inr (Or.inr ⟨j, Or.inl rfl⟩)))
  exact (hT.const_mul 2).add ((integrable_finsetSum Finset.univ (fun j _ => hA j)).const_mul 2)

end Local_T009
open Local_T009 in
theorem T009 (n : ℕ) (m : ℕ) (U : Z n → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m ∧ ‖q‖ = 1 ∧ ContDiffOn ℝ ∞ U (omega n)) (h_T007 : Regular U ∧ (∀ z ∈ omega n, ∀ j : Fin n, D (tau n) (uj U j) z = utj U j z) ∧ LocalData U ∧
 (∀ x : X n, ∀ t : ℝ, 0 < t → HasDerivAt (fun r => density U (x, r)) (densityTime U (x, t)) t) ∧
 (∀ x : X n, ∀ t : ℝ, 0 < t → ∀ j : Fin n,
   HasDerivAt (fun r => uj U j (x, r)) (utj U j (x, t)) t)) (h_E003 : ∀ (n : ℕ) (C : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ), IsCompact C → ContinuousOn f C → IntegrableOn f C volume) (h_E011 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F], ∀ (K : Set E) (h : E → F), IsCompact K → ContinuousOn h K → ∃ B : ℝ, ∀ z ∈ K, ‖h z‖ ≤ B) (h_E012 : ∀ (n : ℕ) (C : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ), MeasurableSet C → IntegrableOn h C volume → Integrable (C.indicator h) volume) :
    ∀ t₀ : ℝ, 0 < t₀ → ∃ C : Set (X n), ∃ B : ℝ,
 IsCompact C ∧ 0 ≤ B ∧
 Ioo (t₀ - t₀ / 4) (t₀ + t₀ / 4) ∈ 𝓝 t₀ ∧
 Integrable (C.indicator (fun _ : X n => B)) volume ∧
 (∀ r ∈ Ioo (t₀ - t₀ / 4) (t₀ + t₀ / 4), 0 < r ∧
  Integrable (fun x : X n => density U (x, r)) volume ∧
  ∀ x : X n, ‖rate U (x, r)‖ ≤ C.indicator (fun _ : X n => B) x) ∧
 Integrable (fun x : X n => rate U (x, t₀)) volume := by
  classical
  intro t₀ ht₀
  have hsupport : ∃ C : Set (X n), IsCompact C ∧
      ∀ r ∈ Ioo (t₀ / 2) (3 * t₀ / 2), Localized U C r :=
    h_T007.2.2.1 t₀ ht₀
  obtain ⟨C, hC, hloc⟩ := hsupport
  have hslab : ∀ r ∈ Icc (t₀ - t₀ / 4) (t₀ + t₀ / 4),
      r ∈ Ioo (t₀ / 2) (3 * t₀ / 2) := by
    intro r hr
    constructor <;> linarith [hr.1, hr.2]
  have hpos : ∀ r ∈ Icc (t₀ - t₀ / 4) (t₀ + t₀ / 4), 0 < r := by
    intro r hr
    linarith [hr.1]
  have hK : IsCompact (C ×ˢ Icc (t₀ - t₀ / 4) (t₀ + t₀ / 4)) :=
    hC.prod isCompact_Icc
  have hKomega : C ×ˢ Icc (t₀ - t₀ / 4) (t₀ + t₀ / 4) ⊆ omega n := by
    intro z hz
    exact hpos z.2 hz.2
  have hcont : ContinuousOn (rate U) (omega n) :=
    @yui_aux_0001 n m U q h_H001 h_T007 h_E003 h_E011 h_E012
  obtain ⟨b, hb⟩ := h_E011 (Z n) ℝ
    (C ×ˢ Icc (t₀ - t₀ / 4) (t₀ + t₀ / 4)) (rate U)
    hK (hcont.mono hKomega)
  let B : ℝ := max b 0
  have hB : 0 ≤ B := le_max_right _ _
  have hbB : b ≤ B := le_max_left _ _
  have hmajor : Integrable (C.indicator (fun _ : X n => B)) volume :=
    h_E012 n C (fun _ : X n => B) hC.isClosed.measurableSet
      (h_E003 n C (fun _ : X n => B) hC continuousOn_const)
  refine ⟨C, B, hC, hB, Ioo_mem_nhds (by linarith) (by linarith), hmajor, ?_, ?_⟩
  · intro r hr
    have hrcc : r ∈ Icc (t₀ - t₀ / 4) (t₀ + t₀ / 4) :=
      ⟨hr.1.le, hr.2.le⟩
    have hL : Localized U C r := hloc r (hslab r hrcc)
    have hdens : Integrable (fun x : X n => density U (x, r)) volume :=
      (hL.2.2 _ (Or.inl rfl)).2.2.2.2
    refine ⟨hpos r hrcc, hdens, ?_⟩
    intro x
    by_cases hx : x ∈ C
    · rw [Set.indicator_of_mem hx]
      exact (hb (x, r) ⟨hx, hrcc⟩).trans hbB
    · have hT : timeProd U (x, r) = 0 :=
        (hL.2.2 _ (Or.inr (Or.inr (Or.inl rfl)))).1 x hx
      have hA : ∀ j : Fin n, gradProd U j (x, r) = 0 := by
        intro j
        exact (hL.2.2 _ (Or.inr (Or.inr (Or.inr ⟨j, Or.inl rfl⟩)))).1 x hx
      simp [rate, hT, hA, Set.indicator_of_notMem hx]
  · have htcc : t₀ ∈ Icc (t₀ - t₀ / 4) (t₀ + t₀ / 4) := by
      constructor <;> linarith
    exact (@yui_aux_0002 n m U q h_H001 h_T007 h_E003 h_E011 h_E012)
      C t₀ hC (hloc t₀ (hslab t₀ htcc))

theorem T010 (n : ℕ) (m : ℕ) (U : Z n → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m ∧ ‖q‖ = 1 ∧ ContDiffOn ℝ ∞ U (omega n)) (h_T007 : Regular U ∧ (∀ z ∈ omega n, ∀ j : Fin n, D (tau n) (uj U j) z = utj U j z) ∧ LocalData U ∧
 (∀ x : X n, ∀ t : ℝ, 0 < t → HasDerivAt (fun r => density U (x, r)) (densityTime U (x, t)) t) ∧
 (∀ x : X n, ∀ t : ℝ, 0 < t → ∀ j : Fin n,
   HasDerivAt (fun r => uj U j (x, r)) (utj U j (x, t)) t)) (h_T008 : ∀ x : X n, ∀ t : ℝ, 0 < t →
 HasDerivAt (fun r => density U (x, r)) (rate U (x, t)) t ∧
 densityTime U (x, t) = rate U (x, t)) (h_T009 : ∀ t₀ : ℝ, 0 < t₀ → ∃ C : Set (X n), ∃ B : ℝ,
 IsCompact C ∧ 0 ≤ B ∧
 Ioo (t₀ - t₀ / 4) (t₀ + t₀ / 4) ∈ 𝓝 t₀ ∧
 Integrable (C.indicator (fun _ : X n => B)) volume ∧
 (∀ r ∈ Ioo (t₀ - t₀ / 4) (t₀ + t₀ / 4), 0 < r ∧
  Integrable (fun x : X n => density U (x, r)) volume ∧
  ∀ x : X n, ‖rate U (x, r)‖ ≤ C.indicator (fun _ : X n => B) x) ∧
 Integrable (fun x : X n => rate U (x, t₀)) volume) (h_E001 : ∀ (n : ℕ) (F G : ℝ → EuclideanSpace ℝ (Fin n) → ℝ) (t₀ : ℝ) (s : Set ℝ) (b : EuclideanSpace ℝ (Fin n) → ℝ),
s ∈ 𝓝 t₀ →
(∀ᶠ t in 𝓝 t₀, AEStronglyMeasurable (F t) volume) →
Integrable (F t₀) volume →
AEStronglyMeasurable (G t₀) volume →
(∀ᵐ x ∂volume, ∀ t ∈ s, ‖G t x‖ ≤ b x) →
Integrable b volume →
(∀ᵐ x ∂volume, ∀ t ∈ s, HasDerivAt (fun r => F r x) (G t x) t) →
Integrable (G t₀) volume ∧ HasDerivAt (fun t => ∫ x, F t x) (∫ x, G t₀ x) t₀) :
    ∀ t : ℝ, 0 < t →
 Integrable (fun x : X n => density U (x, t)) volume ∧
 Integrable (fun x : X n => rate U (x, t)) volume ∧
 Integrable (fun x : X n => 2 * timeProd U (x, t)) volume ∧
 (∀ j : Fin n, Integrable (fun x : X n => 2 * gradProd U j (x, t)) volume) ∧
 HasDerivAt (energy U) (∫ x : X n, rate U (x, t)) t := by
  intro t ht
  rcases h_T009 t ht with ⟨C, B, hC, hB, hs, hb, hslab, hrate⟩
  have hmem : t ∈ Ioo (t - t / 4) (t + t / 4) := by
    constructor <;> linarith
  have hdensity : Integrable (fun x : X n => density U (x, t)) volume :=
    (hslab t hmem).2.1
  have hmeas : ∀ᶠ r in 𝓝 t,
      AEStronglyMeasurable (fun x : X n => density U (x, r)) volume := by
    filter_upwards [hs] with r hr
    exact (hslab r hr).2.1.aestronglyMeasurable
  have hbound : ∀ᵐ x ∂volume, ∀ r ∈ Ioo (t - t / 4) (t + t / 4),
      ‖rate U (x, r)‖ ≤ C.indicator (fun _ : X n => B) x :=
    Filter.Eventually.of_forall (fun x r hr => (hslab r hr).2.2 x)
  have hderivs : ∀ᵐ x ∂volume, ∀ r ∈ Ioo (t - t / 4) (t + t / 4),
      HasDerivAt (fun s => density U (x, s)) (rate U (x, r)) r :=
    Filter.Eventually.of_forall (fun x r hr => (h_T008 x r (hslab r hr).1).1)
  have hdiff := h_E001 n
    (fun r x => density U (x, r)) (fun r x => rate U (x, r))
    t (Ioo (t - t / 4) (t + t / 4)) (C.indicator (fun _ : X n => B))
    hs hmeas hdensity hrate.aestronglyMeasurable hbound hb hderivs
  rcases h_T007.2.2.1 t ht with ⟨K, hK, hlocal⟩
  have htK : t ∈ Ioo (t / 2) (3 * t / 2) := by
    constructor <;> linarith
  have hT : SectionFacts (timeProd U) K t :=
    ((hlocal t htK).2.2 (timeProd U) (Or.inr (Or.inr (Or.inl rfl)))).2
  have hA : ∀ j : Fin n, SectionFacts (gradProd U j) K t := by
    intro j
    exact ((hlocal t htK).2.2 (gradProd U j)
      (Or.inr (Or.inr (Or.inr ⟨j, Or.inl rfl⟩)))).2
  refine ⟨hdensity, hdiff.1, hT.2.2.2.const_mul 2, ?_, ?_⟩
  · intro j
    exact (hA j).2.2.2.const_mul 2
  · exact hdiff.2

theorem T011 (n : ℕ) (m : ℕ) (U : Z n → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m ∧ ‖q‖ = 1 ∧ ContDiffOn ℝ ∞ U (omega n)) (h_T007 : Regular U ∧ (∀ z ∈ omega n, ∀ j : Fin n, D (tau n) (uj U j) z = utj U j z) ∧ LocalData U ∧
 (∀ x : X n, ∀ t : ℝ, 0 < t → HasDerivAt (fun r => density U (x, r)) (densityTime U (x, t)) t) ∧
 (∀ x : X n, ∀ t : ℝ, 0 < t → ∀ j : Fin n,
   HasDerivAt (fun r => uj U j (x, r)) (utj U j (x, t)) t)) (h_T003 : ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]
 (f : Z n → F), ContDiffOn ℝ ∞ f (omega n) →
 ∀ (x : X n) (t : ℝ), 0 < t →
 HasDerivAt (fun r => f (x, r)) (D (tau n) f (x, t)) t ∧
 (∀ v : X n, fderiv ℝ (fun y : X n => f (y, t)) x v = D (v, 0) f (x, t)) ∧
 (∀ v : X n, HasDerivAt (fun h : ℝ => f (x + h • v, t)) (D (v, 0) f (x, t)) 0)) (h_E013 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F], ∀ (l : E → F) (L : E →L[ℝ] F) (c : ℝ → E) (v : E) (t : ℝ), HasFDerivAt l L (c t) → HasDerivAt c v t → HasDerivAt (l ∘ c) (L v) t) (h_E019 : ∀ (E F G : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G], ∀ (S : Set E) (T : Set F) (f : E → F) (g : F → G), ContDiffOn ℝ ∞ g T → ContDiffOn ℝ ∞ f S → MapsTo f S T → ContDiffOn ℝ ∞ (g ∘ f) S) :
    ∀ t : ℝ, 0 < t → ∀ j : Fin n,
 ContDiff ℝ ∞ (fun x : X n => ut U (x, t)) ∧
 ContDiff ℝ ∞ (fun x : X n => uj U j (x, t)) ∧
 (∀ x : X n, fderiv ℝ (fun y : X n => ut U (y, t)) x (basis n j) = utj U j (x, t)) ∧
 (∀ x : X n, fderiv ℝ (fun y : X n => uj U j (y, t)) x (basis n j) = ujj U j (x, t)) := by
  intro t ht j
  have hut : ContDiffOn ℝ ∞ (ut U) (omega n) := by
    simpa only [ordered, ut] using h_T007.1.1 [tau n]
  have huj : ContDiffOn ℝ ∞ (uj U j) (omega n) := by
    simpa only [ordered, uj] using h_T007.1.1 [sigma n j]
  have hi : ContDiff ℝ ∞ (fun x : X n => (x, t)) :=
    contDiff_id.prodMk contDiff_const
  have hmaps : MapsTo (fun x : X n => (x, t)) (univ : Set (X n)) (omega n) := by
    intro x hx
    exact ht
  have hst : ContDiff ℝ ∞ (fun x : X n => ut U (x, t)) := by
    apply contDiffOn_univ.mp
    exact h_E019 (X n) (Z n) (V m) univ (omega n)
      (fun x : X n => (x, t)) (ut U) hut hi.contDiffOn hmaps
  have hsj : ContDiff ℝ ∞ (fun x : X n => uj U j (x, t)) := by
    apply contDiffOn_univ.mp
    exact h_E019 (X n) (Z n) (V m) univ (omega n)
      (fun x : X n => (x, t)) (uj U j) huj hi.contDiffOn hmaps
  refine ⟨hst, hsj, ?_, ?_⟩
  · intro x
    exact (h_T003 (V m) (ut U) hut x t ht).2.1 (basis n j)
  · intro x
    exact (h_T003 (V m) (uj U j) huj x t ht).2.1 (basis n j)

theorem T012 (n : ℕ) (m : ℕ) (U : Z n → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m ∧ ‖q‖ = 1 ∧ ContDiffOn ℝ ∞ U (omega n)) (h_T007 : Regular U ∧ (∀ z ∈ omega n, ∀ j : Fin n, D (tau n) (uj U j) z = utj U j z) ∧ LocalData U ∧
 (∀ x : X n, ∀ t : ℝ, 0 < t → HasDerivAt (fun r => density U (x, r)) (densityTime U (x, t)) t) ∧
 (∀ x : X n, ∀ t : ℝ, 0 < t → ∀ j : Fin n,
   HasDerivAt (fun r => uj U j (x, r)) (utj U j (x, t)) t)) (h_T011 : ∀ t : ℝ, 0 < t → ∀ j : Fin n,
 ContDiff ℝ ∞ (fun x : X n => ut U (x, t)) ∧
 ContDiff ℝ ∞ (fun x : X n => uj U j (x, t)) ∧
 (∀ x : X n, fderiv ℝ (fun y : X n => ut U (y, t)) x (basis n j) = utj U j (x, t)) ∧
 (∀ x : X n, fderiv ℝ (fun y : X n => uj U j (y, t)) x (basis n j) = ujj U j (x, t))) (h_E002 : ∀ (n m : ℕ) (f g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (v : EuclideanSpace ℝ (Fin n)),
Integrable (fun x => inner ℝ (fderiv ℝ f x v) (g x)) volume →
Integrable (fun x => inner ℝ (f x) (fderiv ℝ g x v)) volume →
Integrable (fun x => inner ℝ (f x) (g x)) volume →
(∀ x ∈ tsupport g, DifferentiableAt ℝ f x) →
(∀ x ∈ tsupport f, DifferentiableAt ℝ g x) →
(∫ x, inner ℝ (f x) (fderiv ℝ g x v)) = -(∫ x, inner ℝ (fderiv ℝ f x v) (g x))) :
    ∀ t : ℝ, 0 < t → ∀ j : Fin n,
 Integrable (fun x : X n => gradProd U j (x, t)) volume ∧
 Integrable (fun x : X n => lapProd U j (x, t)) volume ∧
 (∫ x : X n, gradProd U j (x, t)) = -(∫ x : X n, lapProd U j (x, t)) := by
  intro t ht j
  obtain ⟨C, hC, hslab⟩ := h_T007.2.2.1 t ht
  have hmem : t ∈ Ioo (t / 2) (3 * t / 2) := by constructor <;> linarith
  have hloc : Localized U C t := hslab t hmem
  have hint : ∀ f : Z n → ℝ, ScalarField U f →
      Integrable (fun x : X n => f (x, t)) volume := by
    intro f hf
    exact (hloc.2.2 f hf).2.2.2.2
  have hA : Integrable (fun x : X n => gradProd U j (x, t)) volume :=
    hint _ (Or.inr (Or.inr (Or.inr ⟨j, Or.inl rfl⟩)))
  have hB : Integrable (fun x : X n => lapProd U j (x, t)) volume :=
    hint _ (Or.inr (Or.inr (Or.inr ⟨j, Or.inr (Or.inl rfl)⟩)))
  have hH : Integrable (fun x : X n => flux U j (x, t)) volume :=
    hint _ (Or.inr (Or.inr (Or.inr ⟨j, Or.inr (Or.inr rfl)⟩)))
  obtain ⟨hf, hg, hdf, hdg⟩ := h_T011 t ht j
  have hfirst :
      (fun x : X n => inner ℝ
        (fderiv ℝ (fun y : X n => ut U (y, t)) x (basis n j))
        (uj U j (x, t))) =
      (fun x : X n => gradProd U j (x, t)) := by
    funext x
    rw [hdf x]
    exact real_inner_comm _ _
  have hsecond :
      (fun x : X n => inner ℝ (ut U (x, t))
        (fderiv ℝ (fun y : X n => uj U j (y, t)) x (basis n j))) =
      (fun x : X n => lapProd U j (x, t)) := by
    funext x
    rw [hdg x]
    rfl
  have hibp := h_E002 n m (fun x : X n => ut U (x, t))
    (fun x : X n => uj U j (x, t)) (basis n j)
    (by rw [hfirst]; exact hA)
    (by rw [hsecond]; exact hB)
    hH
    (fun x hx => (hf.differentiable (by simp)) x)
    (fun x hx => (hg.differentiable (by simp)) x)
  have hid : (∫ x : X n, lapProd U j (x, t)) =
      -(∫ x : X n, gradProd U j (x, t)) := by
    simpa only [hfirst, hsecond] using hibp
  refine ⟨hA, hB, ?_⟩
  calc
    (∫ x : X n, gradProd U j (x, t)) =
        -(-(∫ x : X n, gradProd U j (x, t))) := (neg_neg _).symm
    _ = -(∫ x : X n, lapProd U j (x, t)) := congrArg Neg.neg hid.symm

namespace Local_T013
theorem yui_aux_0001 (n : ℕ) (m : ℕ) (U : Z n → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m ∧ ‖q‖ = 1 ∧ ContDiffOn ℝ ∞ U (omega n)) (h_T007 : Regular U ∧ (∀ z ∈ omega n, ∀ j : Fin n, D (tau n) (uj U j) z = utj U j z) ∧ LocalData U ∧
 (∀ x : X n, ∀ t : ℝ, 0 < t → HasDerivAt (fun r => density U (x, r)) (densityTime U (x, t)) t) ∧
 (∀ x : X n, ∀ t : ℝ, 0 < t → ∀ j : Fin n,
   HasDerivAt (fun r => uj U j (x, r)) (utj U j (x, t)) t)) (h_T012 : ∀ t : ℝ, 0 < t → ∀ j : Fin n,
 Integrable (fun x : X n => gradProd U j (x, t)) volume ∧
 Integrable (fun x : X n => lapProd U j (x, t)) volume ∧
 (∫ x : X n, gradProd U j (x, t)) = -(∫ x : X n, lapProd U j (x, t))) (h_E016 : ∀ (n k : ℕ) (f : Fin k → EuclideanSpace ℝ (Fin n) → ℝ), (∀ i, Integrable (f i) volume) → (∫ x, ∑ i, f i x) = ∑ i, ∫ x, f i x) (h_E017 : ∀ (n : ℕ) (c : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ), (∫ x, c * f x) = c * ∫ x, f x) (h_E018 : ∀ (n : ℕ) (f g : EuclideanSpace ℝ (Fin n) → ℝ), Integrable f volume → Integrable g volume → (∫ x, f x + g x) = (∫ x, f x) + (∫ x, g x)) : yui_aux_type% "∀ f : Fin n → ℝ, (∑ j : Fin n, -f j) = -(∑ j : Fin n, f j)" := by
  intro f
  exact Finset.sum_neg_distrib (s := Finset.univ) f

end Local_T013
open Local_T013 in
theorem T013 (n : ℕ) (m : ℕ) (U : Z n → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m ∧ ‖q‖ = 1 ∧ ContDiffOn ℝ ∞ U (omega n)) (h_T007 : Regular U ∧ (∀ z ∈ omega n, ∀ j : Fin n, D (tau n) (uj U j) z = utj U j z) ∧ LocalData U ∧
 (∀ x : X n, ∀ t : ℝ, 0 < t → HasDerivAt (fun r => density U (x, r)) (densityTime U (x, t)) t) ∧
 (∀ x : X n, ∀ t : ℝ, 0 < t → ∀ j : Fin n,
   HasDerivAt (fun r => uj U j (x, r)) (utj U j (x, t)) t)) (h_T012 : ∀ t : ℝ, 0 < t → ∀ j : Fin n,
 Integrable (fun x : X n => gradProd U j (x, t)) volume ∧
 Integrable (fun x : X n => lapProd U j (x, t)) volume ∧
 (∫ x : X n, gradProd U j (x, t)) = -(∫ x : X n, lapProd U j (x, t))) (h_E016 : ∀ (n k : ℕ) (f : Fin k → EuclideanSpace ℝ (Fin n) → ℝ), (∀ i, Integrable (f i) volume) → (∫ x, ∑ i, f i x) = ∑ i, ∫ x, f i x) (h_E017 : ∀ (n : ℕ) (c : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ), (∫ x, c * f x) = c * ∫ x, f x) (h_E018 : ∀ (n : ℕ) (f g : EuclideanSpace ℝ (Fin n) → ℝ), Integrable f volume → Integrable g volume → (∫ x, f x + g x) = (∫ x, f x) + (∫ x, g x)) :
    ∀ t : ℝ, 0 < t →
 (∫ x : X n, rate U (x, t)) =
  2 * (∫ x : X n, timeProd U (x, t)) - 2 * ∑ j : Fin n, ∫ x : X n, lapProd U j (x, t) := by
  intro t ht
  obtain ⟨C, hC, hloc⟩ := h_T007.2.2.1 t ht
  have hslab : t ∈ Ioo (t / 2) (3 * t / 2) := by
    constructor <;> linarith
  have hscalar : ScalarField U (timeProd U) := Or.inr (Or.inr (Or.inl rfl))
  have htime : Integrable (fun x : X n => timeProd U (x, t)) volume :=
    ((hloc t hslab).2.2 (timeProd U) hscalar).2.2.2.2
  have hgrad : ∀ j : Fin n, Integrable (fun x : X n => gradProd U j (x, t)) volume :=
    fun j => (h_T012 t ht j).1
  have hsum : Integrable (fun x : X n => ∑ j : Fin n, gradProd U j (x, t)) volume :=
    integrable_finsetSum Finset.univ (fun j _ => hgrad j)
  change (∫ x : X n, 2 * timeProd U (x, t) + 2 * ∑ j : Fin n, gradProd U j (x, t)) = _
  rw [h_E018 n (fun x => 2 * timeProd U (x, t))
    (fun x => 2 * ∑ j : Fin n, gradProd U j (x, t))
    (htime.const_mul 2) (hsum.const_mul 2)]
  rw [h_E017 n 2 (fun x => timeProd U (x, t)),
    h_E017 n 2 (fun x => ∑ j : Fin n, gradProd U j (x, t)),
    h_E016 n n (fun j x => gradProd U j (x, t)) hgrad]
  have hcancel :
      (∑ j : Fin n, ∫ x : X n, gradProd U j (x, t)) =
        -(∑ j : Fin n, ∫ x : X n, lapProd U j (x, t)) := by
    calc
      _ = ∑ j : Fin n, -(∫ x : X n, lapProd U j (x, t)) :=
        Finset.sum_congr rfl (fun j _ => (h_T012 t ht j).2.2)
      _ = _ := (@yui_aux_0001 n m U q h_H001 h_T007 h_T012 h_E016 h_E017 h_E018)
        (fun j => ∫ x : X n, lapProd U j (x, t))
  rw [hcancel]
  ring

theorem T014 (n : ℕ) (m : ℕ) (U : Z n → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m ∧ ‖q‖ = 1 ∧ ContDiffOn ℝ ∞ U (omega n)) (h_T004 : ∀ x : X n, ∀ t : ℝ, 0 < t →
 inner ℝ (U (x, t)) (ut U (x, t)) = 0 ∧
 inner ℝ (ut U (x, t)) (utt U (x, t) - lap U (x, t)) = 0) (h_T007 : Regular U ∧ (∀ z ∈ omega n, ∀ j : Fin n, D (tau n) (uj U j) z = utj U j z) ∧ LocalData U ∧
 (∀ x : X n, ∀ t : ℝ, 0 < t → HasDerivAt (fun r => density U (x, r)) (densityTime U (x, t)) t) ∧
 (∀ x : X n, ∀ t : ℝ, 0 < t → ∀ j : Fin n,
   HasDerivAt (fun r => uj U j (x, r)) (utj U j (x, t)) t)) (h_E016 : ∀ (n k : ℕ) (f : Fin k → EuclideanSpace ℝ (Fin n) → ℝ), (∀ i, Integrable (f i) volume) → (∫ x, ∑ i, f i x) = ∑ i, ∫ x, f i x) :
    ∀ t : ℝ, 0 < t →
 (∫ x : X n, timeProd U (x, t)) = ∑ j : Fin n, ∫ x : X n, lapProd U j (x, t) := by
  intro t ht
  obtain ⟨C, hC, hslab⟩ := h_T007.2.2.1 t ht
  have hmem : t ∈ Ioo (t / 2) (3 * t / 2) := by
    constructor <;> linarith
  have hloc : Localized U C t := hslab t hmem
  have hint : ∀ j : Fin n, Integrable (fun x : X n => lapProd U j (x, t)) volume := by
    intro j
    have hs : ScalarField U (lapProd U j) := by
      right; right; right
      exact ⟨j, Or.inr (Or.inl rfl)⟩
    exact (hloc.2.2 (lapProd U j) hs).2.2.2.2
  have hpoint : ∀ x : X n, timeProd U (x, t) = ∑ j : Fin n, lapProd U j (x, t) := by
    intro x
    have hx := (h_T004 x t ht).2
    rw [inner_sub_right, lap, inner_sum] at hx
    exact sub_eq_zero.mp hx
  calc
    (∫ x : X n, timeProd U (x, t)) =
        ∫ x : X n, ∑ j : Fin n, lapProd U j (x, t) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall hpoint
    _ = ∑ j : Fin n, ∫ x : X n, lapProd U j (x, t) :=
      h_E016 n n (fun j x => lapProd U j (x, t)) hint

theorem T015 (n : ℕ) (m : ℕ) (U : Z n → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m ∧ ‖q‖ = 1 ∧ ContDiffOn ℝ ∞ U (omega n)) (h_H002 : ∀ x : X n, ∀ t : ℝ, 0 < t → ‖U (x, t)‖ = 1 ∧ ∃ a : ℝ, utt U (x, t) - lap U (x, t) = a • U (x, t)) (h_H003 : ∀ s t : ℝ, 0 < s → s < t → ∃ C : Set (X n), IsCompact C ∧ ∀ x : X n, x ∉ C → ∀ r ∈ Icc s t, U (x, r) = q) (h_T004 : ∀ x : X n, ∀ t : ℝ, 0 < t →
 inner ℝ (U (x, t)) (ut U (x, t)) = 0 ∧
 inner ℝ (ut U (x, t)) (utt U (x, t) - lap U (x, t)) = 0) (h_T007 : Regular U ∧ (∀ z ∈ omega n, ∀ j : Fin n, D (tau n) (uj U j) z = utj U j z) ∧ LocalData U ∧
 (∀ x : X n, ∀ t : ℝ, 0 < t → HasDerivAt (fun r => density U (x, r)) (densityTime U (x, t)) t) ∧
 (∀ x : X n, ∀ t : ℝ, 0 < t → ∀ j : Fin n,
   HasDerivAt (fun r => uj U j (x, r)) (utj U j (x, t)) t)) (h_T010 : ∀ t : ℝ, 0 < t →
 Integrable (fun x : X n => density U (x, t)) volume ∧
 Integrable (fun x : X n => rate U (x, t)) volume ∧
 Integrable (fun x : X n => 2 * timeProd U (x, t)) volume ∧
 (∀ j : Fin n, Integrable (fun x : X n => 2 * gradProd U j (x, t)) volume) ∧
 HasDerivAt (energy U) (∫ x : X n, rate U (x, t)) t) (h_T012 : ∀ t : ℝ, 0 < t → ∀ j : Fin n,
 Integrable (fun x : X n => gradProd U j (x, t)) volume ∧
 Integrable (fun x : X n => lapProd U j (x, t)) volume ∧
 (∫ x : X n, gradProd U j (x, t)) = -(∫ x : X n, lapProd U j (x, t))) (h_T013 : ∀ t : ℝ, 0 < t →
 (∫ x : X n, rate U (x, t)) =
  2 * (∫ x : X n, timeProd U (x, t)) - 2 * ∑ j : Fin n, ∫ x : X n, lapProd U j (x, t)) (h_T014 : ∀ t : ℝ, 0 < t →
 (∫ x : X n, timeProd U (x, t)) = ∑ j : Fin n, ∫ x : X n, lapProd U j (x, t)) :
    ∀ t : ℝ, 0 < t → Integrable (fun x : X n => density U (x, t)) volume ∧ DifferentiableAt ℝ (energy U) t ∧ deriv (energy U) t = 0 := by
  intro t ht
  have hzero : (∫ x : X n, rate U (x, t)) = 0 := by
    rw [h_T013 t ht, h_T014 t ht]
    ring
  have hd : HasDerivAt (energy U) 0 t := by
    simpa only [hzero] using (h_T010 t ht).2.2.2.2
  exact ⟨(h_T010 t ht).1, hd.differentiableAt, hd.deriv⟩

set_option Elab.async false in
theorem P (n : ℕ) (m : ℕ) (U : Z n → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m ∧ ‖q‖ = 1 ∧ ContDiffOn ℝ ∞ U (omega n)) (h_H002 : ∀ x : X n, ∀ t : ℝ, 0 < t → ‖U (x, t)‖ = 1 ∧ ∃ a : ℝ, utt U (x, t) - lap U (x, t) = a • U (x, t)) (h_H003 : ∀ s t : ℝ, 0 < s → s < t → ∃ C : Set (X n), IsCompact C ∧ ∀ x : X n, x ∉ C → ∀ r ∈ Icc s t, U (x, r) = q) (h_E001 : ∀ (n : ℕ) (F G : ℝ → EuclideanSpace ℝ (Fin n) → ℝ) (t₀ : ℝ) (s : Set ℝ) (b : EuclideanSpace ℝ (Fin n) → ℝ),
s ∈ 𝓝 t₀ →
(∀ᶠ t in 𝓝 t₀, AEStronglyMeasurable (F t) volume) →
Integrable (F t₀) volume →
AEStronglyMeasurable (G t₀) volume →
(∀ᵐ x ∂volume, ∀ t ∈ s, ‖G t x‖ ≤ b x) →
Integrable b volume →
(∀ᵐ x ∂volume, ∀ t ∈ s, HasDerivAt (fun r => F r x) (G t x) t) →
Integrable (G t₀) volume ∧ HasDerivAt (fun t => ∫ x, F t x) (∫ x, G t₀ x) t₀) (h_E002 : ∀ (n m : ℕ) (f g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (v : EuclideanSpace ℝ (Fin n)),
Integrable (fun x => inner ℝ (fderiv ℝ f x v) (g x)) volume →
Integrable (fun x => inner ℝ (f x) (fderiv ℝ g x v)) volume →
Integrable (fun x => inner ℝ (f x) (g x)) volume →
(∀ x ∈ tsupport g, DifferentiableAt ℝ f x) →
(∀ x ∈ tsupport f, DifferentiableAt ℝ g x) →
(∫ x, inner ℝ (f x) (fderiv ℝ g x v)) = -(∫ x, inner ℝ (fderiv ℝ f x v) (g x))) (h_E003 : ∀ (n : ℕ) (C : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ), IsCompact C → ContinuousOn f C → IntegrableOn f C volume) (h_E004 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F], ∀ (U : Set E) (f : E → F), IsOpen U → (ContDiffOn ℝ ∞ f U ↔ DifferentiableOn ℝ f U ∧ ContDiffOn ℝ ∞ (fderiv ℝ f) U)) (h_E005 : ∀ (E F G : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G], ∀ (U : Set E) (A : E → F →L[ℝ] G) (b : E → F), ContDiffOn ℝ ∞ A U → ContDiffOn ℝ ∞ b U → ContDiffOn ℝ ∞ (fun z => A z (b z)) U) (h_E006 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F], ∀ (f : E → F) (z : E), ContDiffAt ℝ 2 f z → ∀ v w : E, fderiv ℝ (fderiv ℝ f) z v w = fderiv ℝ (fderiv ℝ f) z w v) (h_E007 : ∀ (E F G : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G], ∀ (A : E → F →L[ℝ] G) (b : E → F) (z : E), DifferentiableAt ℝ A z → DifferentiableAt ℝ b z → fderiv ℝ (fun y => A y (b y)) z = (A z).comp (fderiv ℝ b z) + (fderiv ℝ A z).flip (b z)) (h_E008 : ∀ (E V : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [InnerProductSpace ℝ V], ∀ (f g : E → V) (z v : E), DifferentiableAt ℝ f z → DifferentiableAt ℝ g z → fderiv ℝ (fun y => inner ℝ (f y) (g y)) z v = inner ℝ (f z) (fderiv ℝ g z v) + inner ℝ (fderiv ℝ f z v) (g z)) (h_E009 : ∀ (E V : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [InnerProductSpace ℝ V], ∀ (U : Set E) (f g : E → V), ContDiffOn ℝ ∞ f U → ContDiffOn ℝ ∞ g U → ContDiffOn ℝ ∞ (fun y => inner ℝ (f y) (g y)) U) (h_E010 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F], ∀ (f g : E → F) (z : E), (f =ᶠ[𝓝 z] g) → fderiv ℝ f z = fderiv ℝ g z) (h_E011 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F], ∀ (K : Set E) (h : E → F), IsCompact K → ContinuousOn h K → ∃ B : ℝ, ∀ z ∈ K, ‖h z‖ ≤ B) (h_E012 : ∀ (n : ℕ) (C : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ), MeasurableSet C → IntegrableOn h C volume → Integrable (C.indicator h) volume) (h_E013 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F], ∀ (l : E → F) (L : E →L[ℝ] F) (c : ℝ → E) (v : E) (t : ℝ), HasFDerivAt l L (c t) → HasDerivAt c v t → HasDerivAt (l ∘ c) (L v) t) (h_E014 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F], ∀ (k : ℕ) (f : Fin k → E → F) (U : Set E), (∀ i, ContDiffOn ℝ ∞ (f i) U) → ContDiffOn ℝ ∞ (fun z => ∑ i, f i z) U) (h_E015 : ∀ (k : ℕ) (A : Fin k → ℝ → ℝ) (a : Fin k → ℝ) (t : ℝ), (∀ i, HasDerivAt (A i) (a i) t) → HasDerivAt (fun r => ∑ i, A i r) (∑ i, a i) t) (h_E016 : ∀ (n k : ℕ) (f : Fin k → EuclideanSpace ℝ (Fin n) → ℝ), (∀ i, Integrable (f i) volume) → (∫ x, ∑ i, f i x) = ∑ i, ∫ x, f i x) (h_E017 : ∀ (n : ℕ) (c : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ), (∫ x, c * f x) = c * ∫ x, f x) (h_E018 : ∀ (n : ℕ) (f g : EuclideanSpace ℝ (Fin n) → ℝ), Integrable f volume → Integrable g volume → (∫ x, f x + g x) = (∫ x, f x) + (∫ x, g x)) (h_E019 : ∀ (E F G : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G], ∀ (S : Set E) (T : Set F) (f : E → F) (g : F → G), ContDiffOn ℝ ∞ g T → ContDiffOn ℝ ∞ f S → MapsTo f S T → ContDiffOn ℝ ∞ (g ∘ f) S) :
    ∀ t : ℝ, 0 < t → Integrable (fun x : X n => density U (x, t)) volume ∧ DifferentiableAt ℝ (energy U) t ∧ deriv (energy U) t = 0 := by
  have h_T001 : (∀ ds : List (Z n), ContDiffOn ℝ ∞ (ordered U ds) (omega n)) ∧ (∀ k : ℕ, ContDiffOn ℝ ∞ (iteratedFDeriv ℝ k U) (omega n)) := @T001 n m U q h_H001 h_E004 h_E005
  have h_T003 : ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]
 (f : Z n → F), ContDiffOn ℝ ∞ f (omega n) →
 ∀ (x : X n) (t : ℝ), 0 < t →
 HasDerivAt (fun r => f (x, r)) (D (tau n) f (x, t)) t ∧
 (∀ v : X n, fderiv ℝ (fun y : X n => f (y, t)) x v = D (v, 0) f (x, t)) ∧
 (∀ v : X n, HasDerivAt (fun h : ℝ => f (x + h • v, t)) (D (v, 0) f (x, t)) 0) := @T003 n m U q h_E013
  have h_T004 : ∀ x : X n, ∀ t : ℝ, 0 < t →
 inner ℝ (U (x, t)) (ut U (x, t)) = 0 ∧
 inner ℝ (ut U (x, t)) (utt U (x, t) - lap U (x, t)) = 0 := @T004 n m U q h_H001 h_H002 h_T001 h_T003 h_E008 h_E010
  have h_T002 : Regular U ∧ (∀ z ∈ omega n, ∀ j : Fin n, D (tau n) (uj U j) z = utj U j z) := @T002 n m U q h_H001 h_T001 h_E004 h_E005 h_E006 h_E007 h_E009 h_E014
  have h_T005 : ∀ t₀ : ℝ, 0 < t₀ → ∃ C : Set (X n), IsCompact C ∧
 ∀ r ∈ Ioo (t₀ / 2) (3 * t₀ / 2),
 (∀ ds : List (Z n), ds ≠ [] → ∀ x : X n, x ∉ C → ordered U ds (x, r) = 0) ∧
 (∀ k : ℕ, 0 < k → ∀ x : X n, x ∉ C → iteratedFDeriv ℝ k U (x, r) = 0) ∧
 (∀ f : Z n → ℝ, ScalarField U f → ∀ x : X n, x ∉ C → f (x, r) = 0) := @T005 n m U q h_H003 h_E010
  have h_T006 : ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
 (f : Z n → F) (C : Set (X n)) (r : ℝ),
 IsCompact C → Continuous (fun x : X n => f (x, r)) →
 (∀ x : X n, x ∉ C → f (x, r) = 0) → SectionFacts f C r := @T006 n m U q h_E003 h_E012
  have h_T007 : Regular U ∧ (∀ z ∈ omega n, ∀ j : Fin n, D (tau n) (uj U j) z = utj U j z) ∧ LocalData U ∧
 (∀ x : X n, ∀ t : ℝ, 0 < t → HasDerivAt (fun r => density U (x, r)) (densityTime U (x, t)) t) ∧
 (∀ x : X n, ∀ t : ℝ, 0 < t → ∀ j : Fin n,
   HasDerivAt (fun r => uj U j (x, r)) (utj U j (x, t)) t) := @T007 n m U q h_H001 h_H003 h_T001 h_T002 h_T003 h_T005 h_T006 h_E019
  have h_T008 : ∀ x : X n, ∀ t : ℝ, 0 < t →
 HasDerivAt (fun r => density U (x, r)) (rate U (x, t)) t ∧
 densityTime U (x, t) = rate U (x, t) := @T008 n m U q h_H001 h_T007 h_E004 h_E008 h_E013 h_E015
  have h_T009 : ∀ t₀ : ℝ, 0 < t₀ → ∃ C : Set (X n), ∃ B : ℝ,
 IsCompact C ∧ 0 ≤ B ∧
 Ioo (t₀ - t₀ / 4) (t₀ + t₀ / 4) ∈ 𝓝 t₀ ∧
 Integrable (C.indicator (fun _ : X n => B)) volume ∧
 (∀ r ∈ Ioo (t₀ - t₀ / 4) (t₀ + t₀ / 4), 0 < r ∧
  Integrable (fun x : X n => density U (x, r)) volume ∧
  ∀ x : X n, ‖rate U (x, r)‖ ≤ C.indicator (fun _ : X n => B) x) ∧
 Integrable (fun x : X n => rate U (x, t₀)) volume := @T009 n m U q h_H001 h_T007 h_E003 h_E011 h_E012
  have h_T010 : ∀ t : ℝ, 0 < t →
 Integrable (fun x : X n => density U (x, t)) volume ∧
 Integrable (fun x : X n => rate U (x, t)) volume ∧
 Integrable (fun x : X n => 2 * timeProd U (x, t)) volume ∧
 (∀ j : Fin n, Integrable (fun x : X n => 2 * gradProd U j (x, t)) volume) ∧
 HasDerivAt (energy U) (∫ x : X n, rate U (x, t)) t := @T010 n m U q h_H001 h_T007 h_T008 h_T009 h_E001
  have h_T011 : ∀ t : ℝ, 0 < t → ∀ j : Fin n,
 ContDiff ℝ ∞ (fun x : X n => ut U (x, t)) ∧
 ContDiff ℝ ∞ (fun x : X n => uj U j (x, t)) ∧
 (∀ x : X n, fderiv ℝ (fun y : X n => ut U (y, t)) x (basis n j) = utj U j (x, t)) ∧
 (∀ x : X n, fderiv ℝ (fun y : X n => uj U j (y, t)) x (basis n j) = ujj U j (x, t)) := @T011 n m U q h_H001 h_T007 h_T003 h_E013 h_E019
  have h_T012 : ∀ t : ℝ, 0 < t → ∀ j : Fin n,
 Integrable (fun x : X n => gradProd U j (x, t)) volume ∧
 Integrable (fun x : X n => lapProd U j (x, t)) volume ∧
 (∫ x : X n, gradProd U j (x, t)) = -(∫ x : X n, lapProd U j (x, t)) := @T012 n m U q h_H001 h_T007 h_T011 h_E002
  have h_T013 : ∀ t : ℝ, 0 < t →
 (∫ x : X n, rate U (x, t)) =
  2 * (∫ x : X n, timeProd U (x, t)) - 2 * ∑ j : Fin n, ∫ x : X n, lapProd U j (x, t) := @T013 n m U q h_H001 h_T007 h_T012 h_E016 h_E017 h_E018
  have h_T014 : ∀ t : ℝ, 0 < t →
 (∫ x : X n, timeProd U (x, t)) = ∑ j : Fin n, ∫ x : X n, lapProd U j (x, t) := @T014 n m U q h_H001 h_T004 h_T007 h_E016
  have h_T015 : ∀ t : ℝ, 0 < t → Integrable (fun x : X n => density U (x, t)) volume ∧ DifferentiableAt ℝ (energy U) t ∧ deriv (energy U) t = 0 := @T015 n m U q h_H001 h_H002 h_H003 h_T004 h_T007 h_T010 h_T012 h_T013 h_T014
  exact h_T015

#check @P
#print axioms P

end Translation

namespace AuditBExport
set_option autoImplicit false
/- Instantiate only universes that disappear when checked E proofs replace
   premises. Public levels are inferred from the actual arguments/target.
   This elaborator builds an ordinary application, checked by Lean's kernel;
   it adds no theorem, axiom or proof dependency. -/
open Lean Elab Term in
elab "yui_assembly_declared_levels%" : term => do
  return toExpr (← getLevelNames)

-- Capture only the header's explicitly declared levels, before P introduces
-- auto-generated Type* names. Those names can shift after E is removed.
private def yuiAssemblyDeclaredLevels : List Lean.Name := yui_assembly_declared_levels%

open Lean Meta Elab Term in
elab "yui_assembly_export%" "(" args:term,* ")" : term <= expectedType => do
  let info ← getConstInfo `Translation.P
  let used ← forallTelescope info.type fun xs body => do
    let mut retained := #[]
    let omitted : Array String := #[]
    for x in xs do
      let decl ← getFVarLocalDecl x
      if !omitted.contains decl.userName.toString then
        retained := retained.push x
    return (collectLevelParams {} (← mkForallFVars retained body)).params
  let levels ← info.levelParams.mapM fun name =>
    if !used.contains name then pure Level.zero
    -- A named public level retains its name, including max/imax expressions
    -- that cannot be uniquely reconstructed from fresh metavariables. Type*
    -- introduces fresh local levels; infer those from the actual arguments.
    else if yuiAssemblyDeclaredLevels.contains name then pure (Level.param name)
    else mkFreshLevelMVar
  elabAppArgs (mkConst `Translation.P levels) #[] (args.getElems.map Arg.stx)
    expectedType (explicit := true) (ellipsis := false)

set_option Elab.async false in
theorem P (n : ℕ) (m : ℕ) (U : Z n → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m ∧ ‖q‖ = 1 ∧ ContDiffOn ℝ ∞ U (omega n)) (h_H002 : ∀ x : X n, ∀ t : ℝ, 0 < t → ‖U (x, t)‖ = 1 ∧ ∃ a : ℝ, utt U (x, t) - lap U (x, t) = a • U (x, t)) (h_H003 : ∀ s t : ℝ, 0 < s → s < t → ∃ C : Set (X n), IsCompact C ∧ ∀ x : X n, x ∉ C → ∀ r ∈ Icc s t, U (x, r) = q) (h_E001 : ∀ (n : ℕ) (F G : ℝ → EuclideanSpace ℝ (Fin n) → ℝ) (t₀ : ℝ) (s : Set ℝ) (b : EuclideanSpace ℝ (Fin n) → ℝ),
s ∈ 𝓝 t₀ →
(∀ᶠ t in 𝓝 t₀, AEStronglyMeasurable (F t) volume) →
Integrable (F t₀) volume →
AEStronglyMeasurable (G t₀) volume →
(∀ᵐ x ∂volume, ∀ t ∈ s, ‖G t x‖ ≤ b x) →
Integrable b volume →
(∀ᵐ x ∂volume, ∀ t ∈ s, HasDerivAt (fun r => F r x) (G t x) t) →
Integrable (G t₀) volume ∧ HasDerivAt (fun t => ∫ x, F t x) (∫ x, G t₀ x) t₀) (h_E002 : ∀ (n m : ℕ) (f g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (v : EuclideanSpace ℝ (Fin n)),
Integrable (fun x => inner ℝ (fderiv ℝ f x v) (g x)) volume →
Integrable (fun x => inner ℝ (f x) (fderiv ℝ g x v)) volume →
Integrable (fun x => inner ℝ (f x) (g x)) volume →
(∀ x ∈ tsupport g, DifferentiableAt ℝ f x) →
(∀ x ∈ tsupport f, DifferentiableAt ℝ g x) →
(∫ x, inner ℝ (f x) (fderiv ℝ g x v)) = -(∫ x, inner ℝ (fderiv ℝ f x v) (g x))) (h_E003 : ∀ (n : ℕ) (C : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ), IsCompact C → ContinuousOn f C → IntegrableOn f C volume) (h_E004 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F], ∀ (U : Set E) (f : E → F), IsOpen U → (ContDiffOn ℝ ∞ f U ↔ DifferentiableOn ℝ f U ∧ ContDiffOn ℝ ∞ (fderiv ℝ f) U)) (h_E005 : ∀ (E F G : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G], ∀ (U : Set E) (A : E → F →L[ℝ] G) (b : E → F), ContDiffOn ℝ ∞ A U → ContDiffOn ℝ ∞ b U → ContDiffOn ℝ ∞ (fun z => A z (b z)) U) (h_E006 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F], ∀ (f : E → F) (z : E), ContDiffAt ℝ 2 f z → ∀ v w : E, fderiv ℝ (fderiv ℝ f) z v w = fderiv ℝ (fderiv ℝ f) z w v) (h_E007 : ∀ (E F G : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G], ∀ (A : E → F →L[ℝ] G) (b : E → F) (z : E), DifferentiableAt ℝ A z → DifferentiableAt ℝ b z → fderiv ℝ (fun y => A y (b y)) z = (A z).comp (fderiv ℝ b z) + (fderiv ℝ A z).flip (b z)) (h_E008 : ∀ (E V : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [InnerProductSpace ℝ V], ∀ (f g : E → V) (z v : E), DifferentiableAt ℝ f z → DifferentiableAt ℝ g z → fderiv ℝ (fun y => inner ℝ (f y) (g y)) z v = inner ℝ (f z) (fderiv ℝ g z v) + inner ℝ (fderiv ℝ f z v) (g z)) (h_E009 : ∀ (E V : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [InnerProductSpace ℝ V], ∀ (U : Set E) (f g : E → V), ContDiffOn ℝ ∞ f U → ContDiffOn ℝ ∞ g U → ContDiffOn ℝ ∞ (fun y => inner ℝ (f y) (g y)) U) (h_E010 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F], ∀ (f g : E → F) (z : E), (f =ᶠ[𝓝 z] g) → fderiv ℝ f z = fderiv ℝ g z) (h_E011 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F], ∀ (K : Set E) (h : E → F), IsCompact K → ContinuousOn h K → ∃ B : ℝ, ∀ z ∈ K, ‖h z‖ ≤ B) (h_E012 : ∀ (n : ℕ) (C : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ), MeasurableSet C → IntegrableOn h C volume → Integrable (C.indicator h) volume) (h_E013 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F], ∀ (l : E → F) (L : E →L[ℝ] F) (c : ℝ → E) (v : E) (t : ℝ), HasFDerivAt l L (c t) → HasDerivAt c v t → HasDerivAt (l ∘ c) (L v) t) (h_E014 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F], ∀ (k : ℕ) (f : Fin k → E → F) (U : Set E), (∀ i, ContDiffOn ℝ ∞ (f i) U) → ContDiffOn ℝ ∞ (fun z => ∑ i, f i z) U) (h_E015 : ∀ (k : ℕ) (A : Fin k → ℝ → ℝ) (a : Fin k → ℝ) (t : ℝ), (∀ i, HasDerivAt (A i) (a i) t) → HasDerivAt (fun r => ∑ i, A i r) (∑ i, a i) t) (h_E016 : ∀ (n k : ℕ) (f : Fin k → EuclideanSpace ℝ (Fin n) → ℝ), (∀ i, Integrable (f i) volume) → (∫ x, ∑ i, f i x) = ∑ i, ∫ x, f i x) (h_E017 : ∀ (n : ℕ) (c : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ), (∫ x, c * f x) = c * ∫ x, f x) (h_E018 : ∀ (n : ℕ) (f g : EuclideanSpace ℝ (Fin n) → ℝ), Integrable f volume → Integrable g volume → (∫ x, f x + g x) = (∫ x, f x) + (∫ x, g x)) (h_E019 : ∀ (E F G : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G], ∀ (S : Set E) (T : Set F) (f : E → F) (g : F → G), ContDiffOn ℝ ∞ g T → ContDiffOn ℝ ∞ f S → MapsTo f S T → ContDiffOn ℝ ∞ (g ∘ f) S) : ∀ t : ℝ, 0 < t → Integrable (fun x : X n => density U (x, t)) volume ∧ DifferentiableAt ℝ (energy U) t ∧ deriv (energy U) t = 0 := by
  exact yui_assembly_export%(n, m, U, q, h_H001, h_H002, h_H003, h_E001, h_E002, h_E003, h_E004, h_E005, h_E006, h_E007, h_E008, h_E009, h_E010, h_E011, h_E012, h_E013, h_E014, h_E015, h_E016, h_E017, h_E018, h_E019)

end AuditBExport

open Lean Meta Elab Command in
run_cmd do
  let result ← liftTermElabM do
    let info ← getConstInfo `Translation.P
    forallTelescope info.type fun xs body => do
      let mut retained := #[]
      let omitted : Array String := #[]
      for x in xs do
        let decl ← getFVarLocalDecl x
        if !omitted.contains decl.userName.toString then
          retained := retained.push x
      let exported ← mkForallFVars retained body
      let used := (collectLevelParams {} exported).params.toList
      return Json.mkObj [("parameters", toJson (info.levelParams.map Name.toString)),
        ("export_used_parameters", toJson (used.map Name.toString))]
  logInfo m!"YUI_ASSEMBLY_LEVELS_JSON:{result.compress}"


namespace YuiBasis
set_option autoImplicit false
set_option Elab.async false in
theorem B001 : ∀ (n : ℕ) (F G : ℝ → EuclideanSpace ℝ (Fin n) → ℝ) (t₀ : ℝ) (s : Set ℝ) (b : EuclideanSpace ℝ (Fin n) → ℝ),
s ∈ 𝓝 t₀ →
(∀ᶠ t in 𝓝 t₀, AEStronglyMeasurable (F t) volume) →
Integrable (F t₀) volume →
AEStronglyMeasurable (G t₀) volume →
(∀ᵐ x ∂volume, ∀ t ∈ s, ‖G t x‖ ≤ b x) →
Integrable b volume →
(∀ᵐ x ∂volume, ∀ t ∈ s, HasDerivAt (fun r => F r x) (G t x) t) →
Integrable (G t₀) volume ∧ HasDerivAt (fun t => ∫ x, F t x) (∫ x, G t₀ x) t₀ := by
  intro n F G t₀ s b hs hF_meas hF_int hG_meas h_bound hb_int h_diff
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℝ) (μ := volume) (F := F) (F' := G) (x₀ := t₀) (s := s) (bound := b)
    hs hF_meas hF_int hG_meas h_bound hb_int h_diff
set_option Elab.async false in
theorem B002 : ∀ (n m : ℕ) (f g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (v : EuclideanSpace ℝ (Fin n)),
Integrable (fun x => inner ℝ (fderiv ℝ f x v) (g x)) volume →
Integrable (fun x => inner ℝ (f x) (fderiv ℝ g x v)) volume →
Integrable (fun x => inner ℝ (f x) (g x)) volume →
(∀ x ∈ tsupport g, DifferentiableAt ℝ f x) →
(∀ x ∈ tsupport f, DifferentiableAt ℝ g x) →
(∫ x, inner ℝ (f x) (fderiv ℝ g x v)) = -(∫ x, inner ℝ (fderiv ℝ f x v) (g x)) := by
  have yui_nested_41461d4beddbb5390efa_0001  : (∀ (m : ℕ) (a b : EuclideanSpace ℝ (Fin m)), (innerSL ℝ : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) a b = inner ℝ a b) := by
    intro m a b
    rfl
  have yui_nested_41461d4beddbb5390efa_0002  : (∀ (n m : ℕ) (a b : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)), Integrable (fun x => inner ℝ (a x) (b x)) volume → Integrable (fun x => (innerSL ℝ : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) (a x) (b x)) volume) := by
    intro n m a b h
    simpa only [yui_nested_41461d4beddbb5390efa_0001] using h
  have yui_nested_41461d4beddbb5390efa_0003  : (∀ (n m : ℕ) (a b : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)), (∫ x, (innerSL ℝ : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) (a x) (b x)) = ∫ x, inner ℝ (a x) (b x)) := by
    intro n m a b
    exact congrArg (fun h : EuclideanSpace ℝ (Fin n) → ℝ => ∫ x, h x) (funext (fun x => yui_nested_41461d4beddbb5390efa_0001 m (a x) (b x)))
  intro n m f g v hf'g hfg' hfg hf hg
  have H := integral_bilinear_fderiv_right_eq_neg_left_of_integrable
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
      (f := f) (g := g) (v := v)
      (B := (innerSL ℝ : EuclideanSpace ℝ (Fin m) →L[ℝ]
        EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ))
      (yui_nested_41461d4beddbb5390efa_0002 n m (fun x => fderiv ℝ f x v) g hf'g)
      (yui_nested_41461d4beddbb5390efa_0002 n m f (fun x => fderiv ℝ g x v) hfg')
      (yui_nested_41461d4beddbb5390efa_0002 n m f g hfg)
      hf hg
  exact (yui_nested_41461d4beddbb5390efa_0003 n m f (fun x => fderiv ℝ g x v)).symm.trans
    (H.trans (congrArg Neg.neg (yui_nested_41461d4beddbb5390efa_0003 n m (fun x => fderiv ℝ f x v) g)))
set_option Elab.async false in
theorem B003 : ∀ (n : ℕ) (C : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ), IsCompact C → ContinuousOn f C → IntegrableOn f C volume := by
  intro n C f hC hf
  exact ContinuousOn.integrableOn_compact (μ := volume) hC hf
set_option Elab.async false in
theorem B004 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F], ∀ (U : Set E) (f : E → F), IsOpen U → (ContDiffOn ℝ ∞ f U ↔ DifferentiableOn ℝ f U ∧ ContDiffOn ℝ ∞ (fderiv ℝ f) U) := by
  intro E F _ _ _ _ U f hU
  exact contDiffOn_infty_iff_fderiv_of_isOpen (𝕜 := ℝ) (f := f) hU
set_option Elab.async false in
theorem B005 : ∀ (E F G : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G], ∀ (U : Set E) (A : E → F →L[ℝ] G) (b : E → F), ContDiffOn ℝ ∞ A U → ContDiffOn ℝ ∞ b U → ContDiffOn ℝ ∞ (fun z => A z (b z)) U := by
  intro E F G instE instES instF instFS instG instGS U A b hA hb
  exact hA.clm_apply hb
set_option Elab.async false in
theorem B006 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F], ∀ (f : E → F) (z : E), ContDiffAt ℝ 2 f z → ∀ v w : E, fderiv ℝ (fderiv ℝ f) z v w = fderiv ℝ (fderiv ℝ f) z w v := by
  intro E F _ _ _ _ f z hf
  have hs : IsSymmSndFDerivAt ℝ f z :=
    hf.isSymmSndFDerivAt (by simp)
  change ∀ v w : E, fderiv ℝ (fderiv ℝ f) z v w = fderiv ℝ (fderiv ℝ f) z w v at hs
  exact hs
set_option Elab.async false in
theorem B007 : ∀ (E F G : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G], ∀ (A : E → F →L[ℝ] G) (b : E → F) (z : E), DifferentiableAt ℝ A z → DifferentiableAt ℝ b z → fderiv ℝ (fun y => A y (b y)) z = (A z).comp (fderiv ℝ b z) + (fderiv ℝ A z).flip (b z) := by
  intro E F G _ _ _ _ _ _ A b z hA hb
  exact fderiv_clm_apply (𝕜 := ℝ) hA hb
set_option Elab.async false in
theorem B008 : ∀ (E V : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [InnerProductSpace ℝ V], ∀ (f g : E → V) (z v : E), DifferentiableAt ℝ f z → DifferentiableAt ℝ g z → fderiv ℝ (fun y => inner ℝ (f y) (g y)) z v = inner ℝ (f z) (fderiv ℝ g z v) + inner ℝ (fderiv ℝ f z v) (g z) := by
  intro E V _ _ _ _ f g z v hf hg
  exact fderiv_inner_apply ℝ hf hg v
set_option Elab.async false in
theorem B009 : ∀ (E V : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [InnerProductSpace ℝ V], ∀ (U : Set E) (f g : E → V), ContDiffOn ℝ ∞ f U → ContDiffOn ℝ ∞ g U → ContDiffOn ℝ ∞ (fun y => inner ℝ (f y) (g y)) U := by
  intro E V instE instNormE instV instInnerV U f g hf hg
  exact ContDiffOn.inner ℝ hf hg
set_option Elab.async false in
theorem B010 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F], ∀ (f g : E → F) (z : E), (f =ᶠ[𝓝 z] g) → fderiv ℝ f z = fderiv ℝ g z := by
  intro E F _ _ _ _ f g z h
  exact Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) h
set_option Elab.async false in
theorem B011 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F], ∀ (K : Set E) (h : E → F), IsCompact K → ContinuousOn h K → ∃ B : ℝ, ∀ z ∈ K, ‖h z‖ ≤ B := by
  intro E F _ _ _ _ K h hK hh
  exact IsCompact.exists_bound_of_continuousOn hK hh
set_option Elab.async false in
theorem B012 : ∀ (n : ℕ) (C : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ), MeasurableSet C → IntegrableOn h C volume → Integrable (C.indicator h) volume := by
  intro n C h hC hh
  exact hh.integrable_indicator hC
set_option Elab.async false in
theorem B013 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F], ∀ (l : E → F) (L : E →L[ℝ] F) (c : ℝ → E) (v : E) (t : ℝ), HasFDerivAt l L (c t) → HasDerivAt c v t → HasDerivAt (l ∘ c) (L v) t := by
  intro E F _ _ _ _ l L c v t hl hc
  exact hl.comp_hasDerivAt t hc
set_option Elab.async false in
theorem B014 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F], ∀ (k : ℕ) (f : Fin k → E → F) (U : Set E), (∀ i, ContDiffOn ℝ ∞ (f i) U) → ContDiffOn ℝ ∞ (fun z => ∑ i, f i z) U := by
  intro E F _ _ _ _ k f U hf
  exact ContDiffOn.sum (𝕜 := ℝ) (n := ∞) (s := Finset.univ) (fun i _ => hf i)
set_option Elab.async false in
theorem B015 : ∀ (k : ℕ) (A : Fin k → ℝ → ℝ) (a : Fin k → ℝ) (t : ℝ), (∀ i, HasDerivAt (A i) (a i) t) → HasDerivAt (fun r => ∑ i, A i r) (∑ i, a i) t := by
  intro k A a t h
  exact HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => h i)
set_option Elab.async false in
theorem B016 : ∀ (n k : ℕ) (f : Fin k → EuclideanSpace ℝ (Fin n) → ℝ), (∀ i, Integrable (f i) volume) → (∫ x, ∑ i, f i x) = ∑ i, ∫ x, f i x := by
  intro n k f hf
  exact MeasureTheory.integral_finsetSum (μ := volume) (Finset.univ : Finset (Fin k)) (fun i _ => hf i)
set_option Elab.async false in
theorem B017 : ∀ (n : ℕ) (c : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ), (∫ x, c * f x) = c * ∫ x, f x := by
  intro n c f
  exact MeasureTheory.integral_const_mul c f
set_option Elab.async false in
theorem B018 : ∀ (n : ℕ) (f g : EuclideanSpace ℝ (Fin n) → ℝ), Integrable f volume → Integrable g volume → (∫ x, f x + g x) = (∫ x, f x) + (∫ x, g x) := by
  intro n f g hf hg
  exact MeasureTheory.integral_add hf hg
set_option Elab.async false in
theorem B019 : ∀ (E F G : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G], ∀ (S : Set E) (T : Set F) (f : E → F) (g : F → G), ContDiffOn ℝ ∞ g T → ContDiffOn ℝ ∞ f S → MapsTo f S T → ContDiffOn ℝ ∞ (g ∘ f) S := by
  intro E F G _ _ _ _ _ _ S T f g hg hf hmap
  exact ContDiffOn.comp hg hf hmap

end YuiBasis

namespace YuiClosed
set_option autoImplicit false
/- Instantiate only universes that disappear when checked E proofs replace
   premises. Public levels are inferred from the actual arguments/target.
   This elaborator builds an ordinary application, checked by Lean's kernel;
   it adds no theorem, axiom or proof dependency. -/
open Lean Elab Term in
elab "yui_basis_declared_levels%" : term => do
  return toExpr (← getLevelNames)

-- Capture only the header's explicitly declared levels, before P introduces
-- auto-generated Type* names. Those names can shift after E is removed.
private def yuiBasisDeclaredLevels : List Lean.Name := yui_basis_declared_levels%

open Lean Meta Elab Term in
elab "yui_basis_export%" "(" args:term,* ")" : term <= expectedType => do
  let info ← getConstInfo `AuditBExport.P
  let used ← forallTelescope info.type fun xs body => do
    let mut retained := #[]
    let omitted : Array String := #["h_E001", "h_E002", "h_E003", "h_E004", "h_E005", "h_E006", "h_E007", "h_E008", "h_E009", "h_E010", "h_E011", "h_E012", "h_E013", "h_E014", "h_E015", "h_E016", "h_E017", "h_E018", "h_E019"]
    for x in xs do
      let decl ← getFVarLocalDecl x
      if !omitted.contains decl.userName.toString then
        retained := retained.push x
    return (collectLevelParams {} (← mkForallFVars retained body)).params
  let levels ← info.levelParams.mapM fun name =>
    if !used.contains name then pure Level.zero
    -- A named public level retains its name, including max/imax expressions
    -- that cannot be uniquely reconstructed from fresh metavariables. Type*
    -- introduces fresh local levels; infer those from the actual arguments.
    else if yuiBasisDeclaredLevels.contains name then pure (Level.param name)
    else mkFreshLevelMVar
  elabAppArgs (mkConst `AuditBExport.P levels) #[] (args.getElems.map Arg.stx)
    expectedType (explicit := true) (ellipsis := false)

set_option Elab.async false in
theorem P (n : ℕ) (m : ℕ) (U : Z n → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m ∧ ‖q‖ = 1 ∧ ContDiffOn ℝ ∞ U (omega n)) (h_H002 : ∀ x : X n, ∀ t : ℝ, 0 < t → ‖U (x, t)‖ = 1 ∧ ∃ a : ℝ, utt U (x, t) - lap U (x, t) = a • U (x, t)) (h_H003 : ∀ s t : ℝ, 0 < s → s < t → ∃ C : Set (X n), IsCompact C ∧ ∀ x : X n, x ∉ C → ∀ r ∈ Icc s t, U (x, r) = q) : ∀ t : ℝ, 0 < t → Integrable (fun x : X n => density U (x, t)) volume ∧ DifferentiableAt ℝ (energy U) t ∧ deriv (energy U) t = 0 := by
  exact yui_basis_export%(n, m, U, q, h_H001, h_H002, h_H003, (@YuiBasis.B001), (@YuiBasis.B002), (@YuiBasis.B003), (@YuiBasis.B004), (@YuiBasis.B005), (@YuiBasis.B006), (@YuiBasis.B007), (@YuiBasis.B008), (@YuiBasis.B009), (@YuiBasis.B010), (@YuiBasis.B011), (@YuiBasis.B012), (@YuiBasis.B013), (@YuiBasis.B014), (@YuiBasis.B015), (@YuiBasis.B016), (@YuiBasis.B017), (@YuiBasis.B018), (@YuiBasis.B019))

end YuiClosed
