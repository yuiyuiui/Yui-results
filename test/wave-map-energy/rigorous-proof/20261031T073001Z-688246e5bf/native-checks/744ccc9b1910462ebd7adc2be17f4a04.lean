import Mathlib
open scoped BigOperators
open MeasureTheory Set Filter Topology

abbrev WM.Space (n : ℕ) := Fin n → ℝ
abbrev WM.Target (m : ℕ) := EuclideanSpace ℝ (Fin m)
abbrev WM.Domain (n : ℕ) := WM.Space n × ℝ

def WM.smoothOrder : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)
def WM.positive (n : ℕ) : Set (WM.Domain n) := {p | 0 < p.2}
def WM.box (n : ℕ) (R : ℝ) : Set (WM.Space n) := Set.pi Set.univ (fun _ => Set.Icc (-R) R)
def WM.openBox (n : ℕ) (R : ℝ) : Set (WM.Space n) := Set.pi Set.univ (fun _ => Set.Ioo (-R) R)
def WM.timeBand (t : ℝ) : Set ℝ := Set.Icc (t / 2) (3 * t / 2)

noncomputable def WM.dt {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : WM.Domain n → F) (p : WM.Domain n) : F :=
  fderiv ℝ f p (0, 1)
noncomputable def WM.dx {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : WM.Domain n → F) (j : Fin n) (p : WM.Domain n) : F :=
  fderiv ℝ f p (Pi.single j 1, 0)
noncomputable def WM.dtt {n m : ℕ} (u : WM.Domain n → WM.Target m) := WM.dt (WM.dt u)
noncomputable def WM.dxx {n m : ℕ} (u : WM.Domain n → WM.Target m) (j : Fin n) := WM.dx (WM.dx u j) j
noncomputable def WM.lap {n m : ℕ} (u : WM.Domain n → WM.Target m) (p : WM.Domain n) := ∑ j, WM.dxx u j p
noncomputable def WM.gradSq {n m : ℕ} (u : WM.Domain n → WM.Target m) (p : WM.Domain n) : ℝ :=
  ∑ j, ‖WM.dx u j p‖ ^ 2
noncomputable def WM.density {n m : ℕ} (u : WM.Domain n → WM.Target m) (p : WM.Domain n) : ℝ :=
  ‖WM.dt u p‖ ^ 2 + WM.gradSq u p
noncomputable def WM.densityT {n m : ℕ} (u : WM.Domain n → WM.Target m) := WM.dt (WM.density u)
noncomputable def WM.energy {n m : ℕ} (u : WM.Domain n → WM.Target m) (t : ℝ) : ℝ :=
  ∫ x : WM.Space n, WM.density u (x, t)
noncomputable def WM.accelProduct {n m : ℕ} (u : WM.Domain n → WM.Target m) (p : WM.Domain n) : ℝ :=
  inner ℝ (WM.dt u p) (WM.dtt u p)
noncomputable def WM.gradProduct {n m : ℕ} (u : WM.Domain n → WM.Target m) (j : Fin n) (p : WM.Domain n) : ℝ :=
  inner ℝ (WM.dx u j p) (WM.dx (WM.dt u) j p)
noncomputable def WM.lapProduct {n m : ℕ} (u : WM.Domain n → WM.Target m) (j : Fin n) (p : WM.Domain n) : ℝ :=
  inner ℝ (WM.dt u p) (WM.dxx u j p)
noncomputable def WM.flux {n m : ℕ} (u : WM.Domain n → WM.Target m) (j : Fin n) (p : WM.Domain n) : ℝ :=
  inner ℝ (WM.dt u p) (WM.dx u j p)

def WM.fields {n m : ℕ} (u : WM.Domain n → WM.Target m) : Set (WM.Domain n → ℝ) :=
  {f | f = WM.density u ∨ f = WM.densityT u ∨ f = WM.accelProduct u ∨
    ∃ j : Fin n, f = WM.gradProduct u j ∨ f = WM.lapProduct u j ∨
      f = WM.flux u j ∨ f = WM.dx (WM.flux u j) j}

def WM.sectionGood {n : ℕ} (f : WM.Domain n → ℝ) (C Q : Set (WM.Space n)) (t : ℝ) : Prop :=
  Continuous (fun x => f (x, t)) ∧ Function.support (fun x => f (x, t)) ⊆ C ∧
  (∃ b : ℝ, ∀ x ∈ Q, |f (x, t)| ≤ b) ∧
  Measurable (fun x => f (x, t)) ∧ Integrable (fun x => f (x, t))

def WM.commonSupport {n m : ℕ} (u : WM.Domain n → WM.Target m) (q : WM.Target m)
    (t : ℝ) (C : Set (WM.Space n)) (R η B : ℝ) : Prop :=
  IsCompact C ∧ 0 < R ∧ 0 < η ∧ 0 ≤ B ∧ C ⊆ WM.openBox n R ∧
  volume (WM.box n R) = ENNReal.ofReal ((2 * R) ^ n) ∧
  volume (WM.box n R) < ⊤ ∧
  Set.Icc (t - η) (t + η) ⊆ interior (WM.timeBand t) ∧
  (∀ x r, x ∉ C → r ∈ WM.timeBand t → u (x, r) = q) ∧
  (∀ x r, x ∉ C → r ∈ interior (WM.timeBand t) →
    ∀ k : ℕ, 1 ≤ k → iteratedFDeriv ℝ k u (x, r) = 0) ∧
  (∀ r ∈ interior (WM.timeBand t), ∀ f ∈ WM.fields u, WM.sectionGood f C (WM.box n R) r) ∧
  (∀ x ∈ WM.box n R, ∀ r ∈ Set.Icc (t - η) (t + η), |WM.densityT u (x, r)| ≤ B)

def WM.supportFacts {n m : ℕ} (u : WM.Domain n → WM.Target m) (q : WM.Target m) : Prop :=
  (∀ t : ℝ, 0 < t → Integrable (fun x => WM.density u (x, t))) ∧
  ContDiffOn ℝ WM.smoothOrder (WM.density u) (WM.positive n) ∧
  ContDiffOn ℝ WM.smoothOrder (WM.densityT u) (WM.positive n) ∧
  (∀ t : ℝ, 0 < t → ∃ C : Set (WM.Space n), ∃ R η B : ℝ, WM.commonSupport u q t C R η B)

def WM.tangency {n m : ℕ} (u : WM.Domain n → WM.Target m) : Prop :=
  ∀ x t, 0 < t →
    inner ℝ (u (x,t)) (WM.dt u (x,t)) = 0 ∧
    inner ℝ (WM.dt u (x,t)) (WM.dtt u (x,t) - WM.lap u (x,t)) = 0 ∧
    inner ℝ (u (x,t)) (WM.dtt u (x,t)) = -(‖WM.dt u (x,t)‖ ^ 2) ∧
    (∀ j : Fin n, inner ℝ (u (x,t)) (WM.dxx u j (x,t)) = -(‖WM.dx u j (x,t)‖ ^ 2)) ∧
    (∀ a : ℝ, WM.dtt u (x,t) - WM.lap u (x,t) = a • u (x,t) →
      a = WM.gradSq u (x,t) - ‖WM.dt u (x,t)‖ ^ 2) ∧
    WM.dtt u (x,t) - WM.lap u (x,t) =
      (WM.gradSq u (x,t) - ‖WM.dt u (x,t)‖ ^ 2) • u (x,t)

def WM.energyDerivative {n m : ℕ} (u : WM.Domain n → WM.Target m) : Prop :=
  (∀ t : ℝ, 0 < t →
    HasDerivAt (WM.energy u) (∫ x : WM.Space n, WM.densityT u (x,t)) t) ∧
  (∀ x t, 0 < t → WM.densityT u (x,t) =
    2 * WM.accelProduct u (x,t) + 2 * ∑ j, WM.gradProduct u j (x,t)) ∧
  (∀ t : ℝ, 0 < t →
    Integrable (fun x => WM.densityT u (x,t)) ∧
    Integrable (fun x => WM.accelProduct u (x,t)) ∧
    ∀ j : Fin n, Integrable (fun x => WM.gradProduct u j (x,t)))

def WM.integrationByParts {n m : ℕ} (u : WM.Domain n → WM.Target m) : Prop :=
  ∀ t : ℝ, 0 < t → ∀ j : Fin n,
    Integrable (fun x => WM.gradProduct u j (x,t)) ∧
    Integrable (fun x => WM.lapProduct u j (x,t)) ∧
    (∫ x : WM.Space n, WM.gradProduct u j (x,t)) =
      -(∫ x : WM.Space n, WM.lapProduct u j (x,t))

def WM.conservation {n m : ℕ} (u : WM.Domain n → WM.Target m) : Prop :=
  (∀ t : ℝ, 0 < t → Integrable (fun x => WM.density u (x,t))) ∧
  (∀ t : ℝ, 0 < t → HasDerivAt (WM.energy u) 0 t) ∧
  (∀ s t : ℝ, 0 < s → 0 < t → WM.energy u s = WM.energy u t)

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem checked (n : ℕ) (m : ℕ) (u : WM.Domain n → WM.Target m) (q : WM.Target m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ WM.smoothOrder u (WM.positive n)) (h_H006 : ∀ s t : ℝ, 0 < s → s < t → ∃ C : Set (WM.Space n), IsCompact C ∧ ∀ x : WM.Space n, ∀ r : ℝ, x ∉ C → r ∈ Set.Icc s t → u (x,r) = q) : yui_aux_type% "∀ (p : WM.Domain n), u =ᶠ[𝓝 p] (fun _ => q) → ∀ f ∈ WM.fields u, f p = 0" := by
  have evdir : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
      {f : WM.Domain n → F} {p : WM.Domain n} {c : F},
      f =ᶠ[𝓝 p] (fun _ => c) → ∀ v : WM.Domain n,
      (fun z => fderiv ℝ f z v) =ᶠ[𝓝 p] (fun _ => 0) := by
    intro F _ _ f p c h v
    filter_upwards [h.fderiv (𝕜 := ℝ)] with z hz
    simp [hz, fderiv_const_apply]
  have evfields : ∀ {p : WM.Domain n},
      u =ᶠ[𝓝 p] (fun _ => q) →
      ∀ f ∈ WM.fields u, f =ᶠ[𝓝 p] (fun _ => 0) := by
    intro p hu
    have h0 : WM.dt u =ᶠ[𝓝 p] (fun _ => 0) := evdir hu (0, 1)
    have hx0 : ∀ j, WM.dx u j =ᶠ[𝓝 p] (fun _ => 0) :=
      fun j => evdir hu (Pi.single j 1, 0)
    have he0 : WM.density u =ᶠ[𝓝 p] (fun _ => 0) := by
      filter_upwards [h0, eventually_all.mpr hx0] with z hz hzx
      simp [WM.density, WM.gradSq, hz, hzx]
    have hflux0 : ∀ j, WM.flux u j =ᶠ[𝓝 p] (fun _ => 0) := by
      intro j
      filter_upwards [h0] with z hz
      simp [WM.flux, hz]
    intro f hf
    rcases hf with rfl | rfl | rfl | ⟨j, rfl | rfl | rfl | rfl⟩
    · exact he0
    · exact evdir he0 (0, 1)
    · filter_upwards [h0] with z hz
      simp [WM.accelProduct, hz]
    · filter_upwards [hx0 j] with z hz
      simp [WM.gradProduct, hz]
    · filter_upwards [h0] with z hz
      simp [WM.lapProduct, hz]
    · exact hflux0 j
    · exact evdir (hflux0 j) (Pi.single j 1, 0)
  intro p hp f hf
  exact (evfields hp f hf).self_of_nhds
#check @checked
#print axioms checked
end YuiAuxiliary
