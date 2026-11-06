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

namespace YuiBasis
set_option autoImplicit false
set_option Elab.async false in
theorem B001 : ∀ (n : ℕ) (f : (Fin n → ℝ) → ℝ), Continuous f → HasCompactSupport f → Integrable f := by
  intro n f hf hc
  exact hf.integrable_of_hasCompactSupport hc
set_option Elab.async false in
theorem B002 : ∀ (n : ℕ) (F F' : ℝ → (Fin n → ℝ) → ℝ)
  (b : (Fin n → ℝ) → ℝ) (t₀ : ℝ) (s : Set ℝ),
  s ∈ 𝓝 t₀ →
  (∀ᶠ t in 𝓝 t₀, AEStronglyMeasurable (F t) volume) →
  Integrable (F t₀) →
  AEStronglyMeasurable (F' t₀) volume →
  (∀ᵐ x ∂volume, ∀ t ∈ s, ‖F' t x‖ ≤ b x) →
  Integrable b →
  (∀ᵐ x ∂volume, ∀ t ∈ s, HasDerivAt (fun r => F r x) (F' t x) t) →
  Integrable (F' t₀) ∧
    HasDerivAt (fun t => ∫ x, F t x) (∫ x, F' t₀ x) t₀ := by
  intro n F F' b t₀ s hs hm hi hm' hb hbi hd
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hm hi hm' hb hbi hd
set_option Elab.async false in
theorem B003 : ∀ (n : ℕ) (f g : (Fin n → ℝ) → ℝ) (v : Fin n → ℝ),
  Integrable (fun x => fderiv ℝ f x v * g x) →
  Integrable (fun x => f x * fderiv ℝ g x v) →
  Integrable (fun x => f x * g x) →
  (∀ x ∈ tsupport g, DifferentiableAt ℝ f x) →
  (∀ x ∈ tsupport f, DifferentiableAt ℝ g x) →
  (∫ x, f x * fderiv ℝ g x v) = -(∫ x, fderiv ℝ f x v * g x) := by
  intro n f g v h1 h2 h3 hf hg
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h1 h2 h3 hf hg
set_option Elab.async false in
theorem B004 : ∀ (f g : ℝ → ℝ) (f' g' t : ℝ), HasDerivAt f f' t → HasDerivAt g g' t →
  HasDerivAt (fun r => f r * g r) (f' * g t + f t * g') t := by
  intro f g f' g' t hf hg
  exact hf.mul hg
set_option Elab.async false in
theorem B005 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (x : E),
  ContDiffAt ℝ 2 f x →
  ∀ v w : E, fderiv ℝ (fderiv ℝ f) x v w = fderiv ℝ (fderiv ℝ f) x w v := by
  intro E F _ _ _ _ f x hf v w
  exact hf.isSymmSndFDerivAt (by simp) v w
set_option Elab.async false in
theorem B006 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (U : Set E),
  IsOpen U → ContDiffOn ℝ ∞ f U → ContDiffOn ℝ ∞ (fderiv ℝ f) U := by
  intro E F _ _ _ _ f U hU hf
  exact hf.fderiv_of_isOpen hU (by simp)
set_option Elab.async false in
theorem B007 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (c : F) (x : E),
  (f =ᶠ[𝓝 x] fun _ => c) → fderiv ℝ f x = 0 := by
  intro E F _ _ _ _ f c x h
  rw [h.fderiv_eq]
  simp
set_option Elab.async false in
theorem B008 : ∀ (n : ℕ) (K : Set ((Fin n → ℝ) × ℝ)) (f : ((Fin n → ℝ) × ℝ) → ℝ),
  IsCompact K → ContinuousOn f K → ∃ B : ℝ, ∀ p ∈ K, ‖f p‖ ≤ B := by
  intro n K f hK hf
  exact hK.exists_bound_of_continuousOn hf
set_option Elab.async false in
theorem B009 : ∀ (n : ℕ) (K : Set (Fin n → ℝ)) (B : ℝ),
  IsCompact K → Integrable (K.indicator (fun _ => B)) := by
  intro n K B hK
  rw [integrable_indicator_iff hK.measurableSet]
  exact integrableOn_const hK.measure_ne_top

end YuiBasis
