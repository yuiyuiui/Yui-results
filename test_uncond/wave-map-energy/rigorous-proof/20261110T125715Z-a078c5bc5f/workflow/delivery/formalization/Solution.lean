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

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace Translation
set_option autoImplicit false

theorem T001 (n : ℕ) (m : ℕ) (u : WMZ n → WMX m) (q : WMX m) (h_H001 : 1 ≤ n ∧ 1 ≤ m ∧ ContDiffOn ℝ ∞ u (WMOmega n)) (h_M008 : ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] (f : X → Y) (s : Set X), IsOpen s → ContDiffOn ℝ ∞ f s → ContDiffOn ℝ ∞ (fderiv ℝ f) s) :
    ContDiffOn ℝ ∞ (WMV u) (WMOmega n) ∧ (∀ j : Fin n, ContDiffOn ℝ ∞ (WMW u j) (WMOmega n)) ∧ ContDiffOn ℝ ∞ (WMA u) (WMOmega n) ∧ (∀ j : Fin n, ContDiffOn ℝ ∞ (WMB u j) (WMOmega n)) ∧ (∀ j : Fin n, ContDiffOn ℝ ∞ (WMMixed u j) (WMOmega n)) := by
  have hΩ : IsOpen (WMOmega n) := by
    exact isOpen_lt continuous_const continuous_snd
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ u) (WMOmega n) :=
    h_M008 u (WMOmega n) hΩ h_H001.2.2
  have hV : ContDiffOn ℝ ∞ (WMV u) (WMOmega n) := by
    exact hD.clm_apply contDiffOn_const
  have hW : ∀ j : Fin n, ContDiffOn ℝ ∞ (WMW u j) (WMOmega n) := by
    intro j
    exact hD.clm_apply contDiffOn_const
  have hDV : ContDiffOn ℝ ∞ (fderiv ℝ (WMV u)) (WMOmega n) :=
    h_M008 (WMV u) (WMOmega n) hΩ hV
  have hA : ContDiffOn ℝ ∞ (WMA u) (WMOmega n) := by
    exact hDV.clm_apply contDiffOn_const
  have hB : ∀ j : Fin n, ContDiffOn ℝ ∞ (WMB u j) (WMOmega n) := by
    intro j
    have hDW : ContDiffOn ℝ ∞ (fderiv ℝ (WMW u j)) (WMOmega n) :=
      h_M008 (WMW u j) (WMOmega n) hΩ (hW j)
    exact hDW.clm_apply contDiffOn_const
  have hMixed : ∀ j : Fin n, ContDiffOn ℝ ∞ (WMMixed u j) (WMOmega n) := by
    intro j
    exact hDV.clm_apply contDiffOn_const
  exact ⟨hV, hW, hA, hB, hMixed⟩

theorem T002 (n : ℕ) (m : ℕ) (u : WMZ n → WMX m) (q : WMX m) (h_T001 : ContDiffOn ℝ ∞ (WMV u) (WMOmega n) ∧ (∀ j : Fin n, ContDiffOn ℝ ∞ (WMW u j) (WMOmega n)) ∧ ContDiffOn ℝ ∞ (WMA u) (WMOmega n) ∧ (∀ j : Fin n, ContDiffOn ℝ ∞ (WMB u j) (WMOmega n)) ∧ (∀ j : Fin n, ContDiffOn ℝ ∞ (WMMixed u j) (WMOmega n))) (h_M008 : ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] (f : X → Y) (s : Set X), IsOpen s → ContDiffOn ℝ ∞ f s → ContDiffOn ℝ ∞ (fderiv ℝ f) s) :
    ∀ k : WMTerm n, ContDiffOn ℝ ∞ (WMField u k) (WMOmega n) := by
  rcases h_T001 with ⟨hV, hW, hA, hB, hMixed⟩
  have hopen : IsOpen (WMOmega n) := by
    exact isOpen_lt continuous_const continuous_snd
  have hsum : ContDiffOn ℝ ∞
      (fun z : WMZ n => ∑ j : Fin n, ‖WMW u j z‖ ^ 2) (WMOmega n) := by
    exact ContDiffOn.sum (fun j _ => (hW j).norm_sq ℝ)
  have hE : ContDiffOn ℝ ∞ (WME u) (WMOmega n) := by
    apply ((hV.norm_sq ℝ).add hsum).congr
    intro z hz
    simp only [WME, show 0 < z.2 from hz, if_pos]
  have hG : ∀ j : Fin n, ContDiffOn ℝ ∞ (WMG u j) (WMOmega n) := by
    intro j
    apply (hV.inner ℝ (hW j)).congr
    intro z hz
    simp only [WMG, show 0 < z.2 from hz, if_pos]
  intro k
  cases k with
  | density => exact hE
  | densityTime =>
      exact (h_M008 (WME u) (WMOmega n) hopen hE).clm_apply contDiffOn_const
  | kineticPair => exact hV.inner ℝ hA
  | flux j => exact hG j
  | fluxSpace j =>
      exact (h_M008 (WMG u j) (WMOmega n) hopen (hG j)).clm_apply contDiffOn_const
  | mixedPair j => exact (hW j).inner ℝ (hMixed j)
  | laplacePair j => exact hV.inner ℝ (hB j)

namespace Local_T003
theorem yui_aux_0001 (n : ℕ) (m : ℕ) (u : WMZ n → WMX m) (q : WMX m) (h_H005 : ∀ s t : ℝ, 0 < s → s < t → ∃ C : Set (WMX n), IsCompact C ∧ ∀ (x : WMX n) (r : ℝ), x ∉ C → r ∈ Icc s t → u (x, r) = q) (h_M009 : ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] (f g : X → Y) (x : X), Filter.EventuallyEq (𝓝 x) f g → fderiv ℝ f x = fderiv ℝ g x) : yui_aux_type% "∀ {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (f : WMZ n → Y) (c : Y) (O : Set (WMZ n)), IsOpen O → (∀ z ∈ O, f z = c) → ∀ z ∈ O, fderiv ℝ f z = 0" := by
  intro Y _ _ f c O hO hf z hz
  have heq : Filter.EventuallyEq (𝓝 z) f (fun _ => c) :=
    (hO.eventually_mem hz).mono (fun y hy => hf y hy)
  calc
    fderiv ℝ f z = fderiv ℝ (fun _ : WMZ n => c) z := h_M009 f (fun _ => c) z heq
    _ = 0 := fderiv_const_apply c

theorem yui_aux_0002 (n : ℕ) (m : ℕ) (u : WMZ n → WMX m) (q : WMX m) (h_H005 : ∀ s t : ℝ, 0 < s → s < t → ∃ C : Set (WMX n), IsCompact C ∧ ∀ (x : WMX n) (r : ℝ), x ∉ C → r ∈ Icc s t → u (x, r) = q) (h_M009 : ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] (f g : X → Y) (x : X), Filter.EventuallyEq (𝓝 x) f g → fderiv ℝ f x = fderiv ℝ g x) : yui_aux_type% "∀ O : Set (WMZ n), IsOpen O → (∀ z ∈ O, u z = q) → ∀ z ∈ O, ∀ k : WMTerm n, WMField u k z = 0" := by
  intro O hO hu
  have hD : ∀ z ∈ O, fderiv ℝ u z = 0 :=
    yui_aux_0001 n m u q h_H005 h_M009 u q O hO hu
  have hDD : ∀ z ∈ O, fderiv ℝ (fderiv ℝ u) z = 0 :=
    yui_aux_0001 n m u q h_H005 h_M009 (fderiv ℝ u) 0 O hO hD
  have hV : ∀ z ∈ O, WMV u z = 0 := by
    intro z hz
    simp [WMV, hD z hz]
  have hW : ∀ j : Fin n, ∀ z ∈ O, WMW u j z = 0 := by
    intro j z hz
    simp [WMW, hD z hz]
  have hDV : ∀ z ∈ O, fderiv ℝ (WMV u) z = 0 :=
    yui_aux_0001 n m u q h_H005 h_M009 (WMV u) 0 O hO hV
  have hDW : ∀ j : Fin n, ∀ z ∈ O, fderiv ℝ (WMW u j) z = 0 := by
    intro j
    exact yui_aux_0001 n m u q h_H005 h_M009 (WMW u j) 0 O hO (hW j)
  have hE : ∀ z ∈ O, WME u z = 0 := by
    intro z hz
    simp [WME, hV z hz, fun j => hW j z hz]
  have hG : ∀ j : Fin n, ∀ z ∈ O, WMG u j z = 0 := by
    intro j z hz
    simp [WMG, hV z hz]
  have hDE : ∀ z ∈ O, fderiv ℝ (WME u) z = 0 :=
    yui_aux_0001 n m u q h_H005 h_M009 (WME u) 0 O hO hE
  have hDG : ∀ j : Fin n, ∀ z ∈ O, fderiv ℝ (WMG u j) z = 0 := by
    intro j
    exact yui_aux_0001 n m u q h_H005 h_M009 (WMG u j) 0 O hO (hG j)
  intro z hz k
  cases k with
  | density => exact hE z hz
  | densityTime => simp [WMField, WMET, hDE z hz]
  | kineticPair => simp [WMField, hV z hz, WMA, hDV z hz]
  | flux j => exact hG j z hz
  | fluxSpace j => simp [WMField, WMGX, hDG j z hz]
  | mixedPair j => simp [WMField, hW j z hz, WMMixed, hDV z hz]
  | laplacePair j => simp [WMField, hV z hz, WMB, hDW j z hz]

end Local_T003
open Local_T003 in
theorem T003 (n : ℕ) (m : ℕ) (u : WMZ n → WMX m) (q : WMX m) (h_H005 : ∀ s t : ℝ, 0 < s → s < t → ∃ C : Set (WMX n), IsCompact C ∧ ∀ (x : WMX n) (r : ℝ), x ∉ C → r ∈ Icc s t → u (x, r) = q) (h_M009 : ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] (f g : X → Y) (x : X), Filter.EventuallyEq (𝓝 x) f g → fderiv ℝ f x = fderiv ℝ g x) :
    ∀ t0 : ℝ, 0 < t0 → ∃ C : Set (WMX n), IsCompact C ∧ ∀ r ∈ Ioo (t0 / 2) (3 * t0 / 2), ∀ k : WMTerm n, (∀ x : WMX n, x ∉ C → WMField u k (x, r) = 0) ∧ tsupport (fun x : WMX n => WMField u k (x, r)) ⊆ C := by
  intro t0 ht0
  obtain ⟨C, hC, hu⟩ := h_H005 (t0 / 2) (3 * t0 / 2) (by linarith) (by linarith)
  let O : Set (WMZ n) := Cᶜ ×ˢ Ioo (t0 / 2) (3 * t0 / 2)
  have hO : IsOpen O := hC.isClosed.isOpen_compl.prod isOpen_Ioo
  have huO : ∀ z ∈ O, u z = q := by
    intro z hz
    exact hu z.1 z.2 hz.1 ⟨le_of_lt hz.2.1, le_of_lt hz.2.2⟩
  have hzero : ∀ z ∈ O, ∀ k : WMTerm n, WMField u k z = 0 :=
    yui_aux_0002 n m u q h_H005 h_M009 O hO huO
  refine ⟨C, hC, ?_⟩
  intro r hr k
  have hv : ∀ x : WMX n, x ∉ C → WMField u k (x, r) = 0 := by
    intro x hx
    exact hzero (x, r) ⟨hx, hr⟩ k
  refine ⟨hv, ?_⟩
  change closure (Function.support (fun x : WMX n => WMField u k (x, r))) ⊆ C
  apply closure_minimal _ hC.isClosed
  intro x hx
  by_contra hxc
  exact hx (hv x hxc)

theorem T004 (n : ℕ) (m : ℕ) (u : WMZ n → WMX m) (q : WMX m) (h_T002 : ∀ k : WMTerm n, ContDiffOn ℝ ∞ (WMField u k) (WMOmega n)) (h_T003 : ∀ t0 : ℝ, 0 < t0 → ∃ C : Set (WMX n), IsCompact C ∧ ∀ r ∈ Ioo (t0 / 2) (3 * t0 / 2), ∀ k : WMTerm n, (∀ x : WMX n, x ∉ C → WMField u k (x, r) = 0) ∧ tsupport (fun x : WMX n => WMField u k (x, r)) ⊆ C) :
    (∀ k : WMTerm n, ContDiffOn ℝ ∞ (WMField u k) (WMOmega n)) ∧ (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (WMX n), IsCompact C ∧ ∀ r ∈ Ioo (t0 / 2) (3 * t0 / 2), ∀ k : WMTerm n, (∀ x : WMX n, x ∉ C → WMField u k (x, r) = 0) ∧ tsupport (fun x : WMX n => WMField u k (x, r)) ⊆ C) := by
  exact ⟨h_T002, h_T003⟩

theorem T009 (n : ℕ) (m : ℕ) (u : WMZ n → WMX m) (q : WMX m) (h_T004 : (∀ k : WMTerm n, ContDiffOn ℝ ∞ (WMField u k) (WMOmega n)) ∧ (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (WMX n), IsCompact C ∧ ∀ r ∈ Ioo (t0 / 2) (3 * t0 / 2), ∀ k : WMTerm n, (∀ x : WMX n, x ∉ C → WMField u k (x, r) = 0) ∧ tsupport (fun x : WMX n => WMField u k (x, r)) ⊆ C)) (h_M001 : ∀ (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ), Continuous f → HasCompactSupport f → Integrable f) :
    ∀ t : ℝ, 0 < t → ∀ k : WMTerm n, Integrable (fun x : WMX n => WMField u k (x, t)) := by
  intro t ht k
  obtain ⟨C, hC, hwin⟩ := h_T004.2 t ht
  have htw : t ∈ Ioo (t / 2) (3 * t / 2) := by
    constructor <;> linarith
  have hsupport : HasCompactSupport (fun x : WMX n => WMField u k (x, t)) := by
    exact hC.of_isClosed_subset (isClosed_tsupport _) (hwin t htw k).2
  have hsection : Continuous (fun x : WMX n => (x, t)) :=
    continuous_id.prodMk continuous_const
  have hcont : Continuous (fun x : WMX n => WMField u k (x, t)) :=
    (h_T004.1 k).continuousOn.comp_continuous hsection (fun x => ht)
  exact h_M001 n (fun x : WMX n => WMField u k (x, t)) hcont hsupport

namespace Local_T010
theorem yui_aux_0001 (n : ℕ) (m : ℕ) (u : WMZ n → WMX m) (q : WMX m) (h_T004 : (∀ k : WMTerm n, ContDiffOn ℝ ∞ (WMField u k) (WMOmega n)) ∧ (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (WMX n), IsCompact C ∧ ∀ r ∈ Ioo (t0 / 2) (3 * t0 / 2), ∀ k : WMTerm n, (∀ x : WMX n, x ∉ C → WMField u k (x, r) = 0) ∧ tsupport (fun x : WMX n => WMField u k (x, r)) ⊆ C)) : yui_aux_type% "∀ C : Set (WMX n), IsCompact C → ∃ ρ : ℝ, 0 < ρ ∧ ∃ Q : Set (WMX n), Q = (EuclideanSpace.equiv (Fin n) ℝ).symm '' (Set.pi Set.univ (fun _ : Fin n => Icc (-ρ) ρ)) ∧ IsCompact Q ∧ C ⊆ Q" := by
  intro C hC
  let e := EuclideanSpace.equiv (Fin n) ℝ
  obtain ⟨R, hR⟩ := (hC.image e.continuous).isBounded.exists_norm_le
  let ρ := max R 0 + 1
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  let Q : Set (WMX n) := e.symm '' (Set.pi Set.univ (fun _ : Fin n => Icc (-ρ) ρ))
  refine ⟨ρ, hρ, Q, rfl, ?_, ?_⟩
  · exact (isCompact_univ_pi (fun _ : Fin n => isCompact_Icc)).image e.symm.continuous
  · intro x hx
    refine ⟨e x, ?_, e.symm_apply_apply x⟩
    intro j hj
    have hb : ‖e x‖ ≤ R := hR (e x) (mem_image_of_mem e hx)
    have hjb : |e x j| ≤ R := (norm_le_pi_norm (e x) j).trans hb
    have hRρ : R ≤ ρ := by dsimp [ρ]; linarith [le_max_left R 0]
    exact ⟨by have := (abs_le.mp hjb).1; linarith, by have := (abs_le.mp hjb).2; linarith⟩

end Local_T010
open Local_T010 in
theorem T010 (n : ℕ) (m : ℕ) (u : WMZ n → WMX m) (q : WMX m) (h_T004 : (∀ k : WMTerm n, ContDiffOn ℝ ∞ (WMField u k) (WMOmega n)) ∧ (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (WMX n), IsCompact C ∧ ∀ r ∈ Ioo (t0 / 2) (3 * t0 / 2), ∀ k : WMTerm n, (∀ x : WMX n, x ∉ C → WMField u k (x, r) = 0) ∧ tsupport (fun x : WMX n => WMField u k (x, r)) ⊆ C)) :
    ∀ t0 : ℝ, 0 < t0 → ∃ b : WMX n → ℝ, Integrable b ∧ ∀ (x : WMX n) (r : ℝ), r ∈ Ioo (3 * t0 / 4) (5 * t0 / 4) → ‖WMET u (x, r)‖ ≤ b x := by
  classical
  intro t0 ht0
  obtain ⟨C, hC, hvan⟩ := h_T004.2 t0 ht0
  obtain ⟨ρ, hρ, Q, hQdef, hQ, hCQ⟩ := yui_aux_0001 n m u q h_T004 C hC
  let L : Set ℝ := Icc (3 * t0 / 4) (5 * t0 / 4)
  have hK : IsCompact (Q ×ˢ L) := hQ.prod isCompact_Icc
  have hsub : Q ×ˢ L ⊆ WMOmega n := by
    intro z hz
    change 0 < z.2
    have hzlow := hz.2.1
    linarith
  have hcont : ContinuousOn (WMET u) (Q ×ˢ L) :=
    (h_T004.1 WMTerm.densityTime).continuousOn.mono hsub
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hcont
  let β : ℝ := max B 0
  have hβ : 0 ≤ β := le_max_right _ _
  refine ⟨Q.indicator (fun _ => β), ?_, ?_⟩
  · apply IntegrableOn.integrable_indicator _ hQ.measurableSet
    exact integrableOn_const (μ := volume) hQ.measure_lt_top.ne
  · intro x r hr
    by_cases hx : x ∈ Q
    · rw [Set.indicator_of_mem hx]
      exact (hB (x, r) ⟨hx, le_of_lt hr.1, le_of_lt hr.2⟩).trans (le_max_left _ _)
    · rw [Set.indicator_of_notMem hx]
      have hxC : x ∉ C := fun h => hx (hCQ h)
      have hrU : r ∈ Ioo (t0 / 2) (3 * t0 / 2) := by
        constructor <;> linarith [hr.1, hr.2]
      have hz : WMET u (x, r) = 0 := (hvan r hrU WMTerm.densityTime).1 x hxC
      simp [hz]

namespace Local_T011
theorem yui_aux_0001 (n : ℕ) (m : ℕ) (u : WMZ n → WMX m) (q : WMX m) (h_T004 : (∀ k : WMTerm n, ContDiffOn ℝ ∞ (WMField u k) (WMOmega n)) ∧ (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (WMX n), IsCompact C ∧ ∀ r ∈ Ioo (t0 / 2) (3 * t0 / 2), ∀ k : WMTerm n, (∀ x : WMX n, x ∉ C → WMField u k (x, r) = 0) ∧ tsupport (fun x : WMX n => WMField u k (x, r)) ⊆ C)) (h_T009 : ∀ t : ℝ, 0 < t → ∀ k : WMTerm n, Integrable (fun x : WMX n => WMField u k (x, t))) (h_T010 : ∀ t0 : ℝ, 0 < t0 → ∃ b : WMX n → ℝ, Integrable b ∧ ∀ (x : WMX n) (r : ℝ), r ∈ Ioo (3 * t0 / 4) (5 * t0 / 4) → ‖WMET u (x, r)‖ ≤ b x) (h_M002 : ∀ (n : ℕ) (F D : ℝ → EuclideanSpace ℝ (Fin n) → ℝ) (t0 : ℝ) (s : Set ℝ) (b : EuclideanSpace ℝ (Fin n) → ℝ), s ∈ 𝓝 t0 → (∀ᶠ t in 𝓝 t0, AEStronglyMeasurable (F t) volume) → Integrable (F t0) → AEStronglyMeasurable (D t0) volume → (∀ᵐ x ∂volume, ∀ t ∈ s, ‖D t x‖ ≤ b x) → Integrable b → (∀ᵐ x ∂volume, ∀ t ∈ s, HasDerivAt (fun r => F r x) (D t x) t) → Integrable (D t0) ∧ HasDerivAt (fun t => ∫ x, F t x) (∫ x, D t0 x) t0) : yui_aux_type% "∀ (x : WMX n) (r : ℝ), 0 < r → HasDerivAt (fun s : ℝ => WME u (x, s)) (WMET u (x, r)) r" := by
  intro x r hr
  have ho : IsOpen (WMOmega n) := isOpen_lt continuous_const continuous_snd
  have hd : DifferentiableAt ℝ (WME u) (x, r) :=
    ((h_T004.1 WMTerm.density).differentiableOn (by simp)).differentiableAt (ho.mem_nhds hr)
  have hi : HasDerivAt (fun s : ℝ => (x, s)) (WMT n) r := by
    simpa [WMT] using (hasDerivAt_const r x).prodMk (hasDerivAt_id r)
  simpa only [Function.comp_def, WMET] using hd.hasFDerivAt.comp_hasDerivAt r hi

end Local_T011
open Local_T011 in
theorem T011 (n : ℕ) (m : ℕ) (u : WMZ n → WMX m) (q : WMX m) (h_T004 : (∀ k : WMTerm n, ContDiffOn ℝ ∞ (WMField u k) (WMOmega n)) ∧ (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (WMX n), IsCompact C ∧ ∀ r ∈ Ioo (t0 / 2) (3 * t0 / 2), ∀ k : WMTerm n, (∀ x : WMX n, x ∉ C → WMField u k (x, r) = 0) ∧ tsupport (fun x : WMX n => WMField u k (x, r)) ⊆ C)) (h_T009 : ∀ t : ℝ, 0 < t → ∀ k : WMTerm n, Integrable (fun x : WMX n => WMField u k (x, t))) (h_T010 : ∀ t0 : ℝ, 0 < t0 → ∃ b : WMX n → ℝ, Integrable b ∧ ∀ (x : WMX n) (r : ℝ), r ∈ Ioo (3 * t0 / 4) (5 * t0 / 4) → ‖WMET u (x, r)‖ ≤ b x) (h_M002 : ∀ (n : ℕ) (F D : ℝ → EuclideanSpace ℝ (Fin n) → ℝ) (t0 : ℝ) (s : Set ℝ) (b : EuclideanSpace ℝ (Fin n) → ℝ), s ∈ 𝓝 t0 → (∀ᶠ t in 𝓝 t0, AEStronglyMeasurable (F t) volume) → Integrable (F t0) → AEStronglyMeasurable (D t0) volume → (∀ᵐ x ∂volume, ∀ t ∈ s, ‖D t x‖ ≤ b x) → Integrable b → (∀ᵐ x ∂volume, ∀ t ∈ s, HasDerivAt (fun r => F r x) (D t x) t) → Integrable (D t0) ∧ HasDerivAt (fun t => ∫ x, F t x) (∫ x, D t0 x) t0) :
    ∀ t : ℝ, 0 < t → HasDerivAt (WMEnergy u) (∫ x : WMX n, WMET u (x, t)) t := by
  intro t ht
  obtain ⟨b, hb, hbound⟩ := h_T010 t ht
  have hs : Ioo (3 * t / 4) (5 * t / 4) ∈ 𝓝 t :=
    Ioo_mem_nhds (by linarith) (by linarith)
  have hpos : ∀ r ∈ Ioo (3 * t / 4) (5 * t / 4), 0 < r := by
    intro r hr
    have := hr.1
    linarith
  have hmeas : ∀ᶠ r in 𝓝 t, AEStronglyMeasurable (fun x : WMX n => WME u (x, r)) volume := by
    filter_upwards [hs] with r hr
    exact (h_T009 r (hpos r hr) WMTerm.density).aestronglyMeasurable
  have hbase : Integrable (fun x : WMX n => WME u (x, t)) :=
    h_T009 t ht WMTerm.density
  have hdmeas : AEStronglyMeasurable (fun x : WMX n => WMET u (x, t)) volume :=
    (h_T009 t ht WMTerm.densityTime).aestronglyMeasurable
  have hboundae : ∀ᵐ x : WMX n ∂volume, ∀ r ∈ Ioo (3 * t / 4) (5 * t / 4), ‖WMET u (x, r)‖ ≤ b x :=
    Filter.Eventually.of_forall hbound
  have hderiv : ∀ᵐ x : WMX n ∂volume, ∀ r ∈ Ioo (3 * t / 4) (5 * t / 4),
      HasDerivAt (fun s : ℝ => WME u (x, s)) (WMET u (x, r)) r := by
    exact Filter.Eventually.of_forall (fun x r hr =>
      (@yui_aux_0001 n m u q h_T004 h_T009 h_T010 h_M002) x r (hpos r hr))
  exact (h_M002 n (fun r x => WME u (x, r)) (fun r x => WMET u (x, r))
    t (Ioo (3 * t / 4) (5 * t / 4)) b hs hmeas hbase hdmeas hboundae hb hderiv).2

namespace Local_T005
theorem yui_aux_0001 (n : ℕ) (m : ℕ) (u : WMZ n → WMX m) (q : WMX m) (h_H001 : 1 ≤ n ∧ 1 ≤ m ∧ ContDiffOn ℝ ∞ u (WMOmega n)) (h_H003 : ∀ (x : WMX n) (t : ℝ), 0 < t → ‖u (x, t)‖ = 1) (h_H004 : ∀ (x : WMX n) (t : ℝ), 0 < t → ∃ a : ℝ, WMA u (x, t) - (∑ j : Fin n, WMB u j (x, t)) = a • u (x, t)) (h_M005 : ∀ {Y : Type} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] (f : ℝ → Y) (f' : Y) (t : ℝ), HasDerivAt f f' t → HasDerivAt (fun r => ‖f r‖ ^ 2) (2 * inner ℝ (f t) f') t) (h_M009 : ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] (f g : X → Y) (x : X), Filter.EventuallyEq (𝓝 x) f g → fderiv ℝ f x = fderiv ℝ g x) : yui_aux_type% "∀ (x : WMX n) (t : ℝ), HasDerivAt (fun r : ℝ => (x, r)) (WMT n) t" := by
  intro x t
  have hc : HasDerivAt (fun _ : ℝ => x) (0 : WMX n) t := hasDerivAt_const t x
  have hi : HasDerivAt (fun r : ℝ => r) (1 : ℝ) t := hasDerivAt_id' t
  exact hc.prodMk hi

theorem yui_aux_0002 (n : ℕ) (m : ℕ) (u : WMZ n → WMX m) (q : WMX m) (h_H001 : 1 ≤ n ∧ 1 ≤ m ∧ ContDiffOn ℝ ∞ u (WMOmega n)) (h_H003 : ∀ (x : WMX n) (t : ℝ), 0 < t → ‖u (x, t)‖ = 1) (h_H004 : ∀ (x : WMX n) (t : ℝ), 0 < t → ∃ a : ℝ, WMA u (x, t) - (∑ j : Fin n, WMB u j (x, t)) = a • u (x, t)) (h_M005 : ∀ {Y : Type} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] (f : ℝ → Y) (f' : Y) (t : ℝ), HasDerivAt f f' t → HasDerivAt (fun r => ‖f r‖ ^ 2) (2 * inner ℝ (f t) f') t) (h_M009 : ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] (f g : X → Y) (x : X), Filter.EventuallyEq (𝓝 x) f g → fderiv ℝ f x = fderiv ℝ g x) : yui_aux_type% "∀ (x : WMX n) (t : ℝ), 0 < t → HasDerivAt (fun r : ℝ => u (x, r)) (WMV u (x, t)) t" := by
  intro x t ht
  have hopen : IsOpen (WMOmega n) := isOpen_lt continuous_const continuous_snd
  have hdiff : DifferentiableAt ℝ u (x, t) :=
    (h_H001.2.2.differentiableOn (by simp)).differentiableAt (hopen.mem_nhds ht)
  have hcurve : HasDerivAt (fun r : ℝ => (x, r)) (WMT n) t :=
    (@yui_aux_0001 n m u q h_H001 h_H003 h_H004 h_M005 h_M009) x t
  simpa only [Function.comp_def, WMV] using hdiff.hasFDerivAt.comp_hasDerivAt t hcurve

theorem yui_aux_0003 (n : ℕ) (m : ℕ) (u : WMZ n → WMX m) (q : WMX m) (h_H001 : 1 ≤ n ∧ 1 ≤ m ∧ ContDiffOn ℝ ∞ u (WMOmega n)) (h_H003 : ∀ (x : WMX n) (t : ℝ), 0 < t → ‖u (x, t)‖ = 1) (h_H004 : ∀ (x : WMX n) (t : ℝ), 0 < t → ∃ a : ℝ, WMA u (x, t) - (∑ j : Fin n, WMB u j (x, t)) = a • u (x, t)) (h_M005 : ∀ {Y : Type} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] (f : ℝ → Y) (f' : Y) (t : ℝ), HasDerivAt f f' t → HasDerivAt (fun r => ‖f r‖ ^ 2) (2 * inner ℝ (f t) f') t) (h_M009 : ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] (f g : X → Y) (x : X), Filter.EventuallyEq (𝓝 x) f g → fderiv ℝ f x = fderiv ℝ g x) : yui_aux_type% "∀ (g : ℝ → ℝ) (c t : ℝ), HasDerivAt g c t → fderiv ℝ g t 1 = c" := by
  intro g c t hg
  have heq := hg.hasFDerivAt.fderiv
  simpa using congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) heq

end Local_T005
open Local_T005 in
theorem T005 (n : ℕ) (m : ℕ) (u : WMZ n → WMX m) (q : WMX m) (h_H001 : 1 ≤ n ∧ 1 ≤ m ∧ ContDiffOn ℝ ∞ u (WMOmega n)) (h_H003 : ∀ (x : WMX n) (t : ℝ), 0 < t → ‖u (x, t)‖ = 1) (h_H004 : ∀ (x : WMX n) (t : ℝ), 0 < t → ∃ a : ℝ, WMA u (x, t) - (∑ j : Fin n, WMB u j (x, t)) = a • u (x, t)) (h_M005 : ∀ {Y : Type} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] (f : ℝ → Y) (f' : Y) (t : ℝ), HasDerivAt f f' t → HasDerivAt (fun r => ‖f r‖ ^ 2) (2 * inner ℝ (f t) f') t) (h_M009 : ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] (f g : X → Y) (x : X), Filter.EventuallyEq (𝓝 x) f g → fderiv ℝ f x = fderiv ℝ g x) :
    ∀ (x : WMX n) (t : ℝ), 0 < t → inner ℝ (u (x, t)) (WMV u (x, t)) = 0 ∧ inner ℝ (WMV u (x, t)) (WMA u (x, t) - ∑ j : Fin n, WMB u j (x, t)) = 0 := by
  intro x t ht
  have hcurve : HasDerivAt (fun r : ℝ => u (x, r)) (WMV u (x, t)) t :=
    (@yui_aux_0002 n m u q h_H001 h_H003 h_H004 h_M005 h_M009) x t ht
  have hsq : HasDerivAt (fun r : ℝ => ‖u (x, r)‖ ^ 2)
      (2 * inner ℝ (u (x, t)) (WMV u (x, t))) t :=
    h_M005 (fun r : ℝ => u (x, r)) (WMV u (x, t)) t hcurve
  have hevent : Filter.EventuallyEq (𝓝 t)
      (fun r : ℝ => ‖u (x, r)‖ ^ 2) (fun _ : ℝ => (1 : ℝ)) := by
    filter_upwards [Ioi_mem_nhds ht] with r hr
    simp only [h_H003 x r hr, one_pow]
  have hfd : fderiv ℝ (fun r : ℝ => ‖u (x, r)‖ ^ 2) t = 0 := by
    rw [h_M009 (fun r : ℝ => ‖u (x, r)‖ ^ 2) (fun _ : ℝ => (1 : ℝ)) t hevent]
    exact fderiv_const_apply 1
  have hval : fderiv ℝ (fun r : ℝ => ‖u (x, r)‖ ^ 2) t 1 =
      2 * inner ℝ (u (x, t)) (WMV u (x, t)) :=
    (@yui_aux_0003 n m u q h_H001 h_H003 h_H004 h_M005 h_M009)
      (fun r : ℝ => ‖u (x, r)‖ ^ 2)
      (2 * inner ℝ (u (x, t)) (WMV u (x, t))) t hsq
  have htangent : inner ℝ (u (x, t)) (WMV u (x, t)) = 0 := by
    rw [hfd] at hval
    simp only [ContinuousLinearMap.zero_apply] at hval
    linarith
  refine ⟨htangent, ?_⟩
  obtain ⟨a, ha⟩ := h_H004 x t ht
  rw [ha, inner_smul_right, real_inner_comm (u (x, t)) (WMV u (x, t)), htangent, mul_zero]

namespace Local_T006
theorem yui_aux_0001 (n : ℕ) (m : ℕ) (u : WMZ n → WMX m) (q : WMX m) (h_H001 : 1 ≤ n ∧ 1 ≤ m ∧ ContDiffOn ℝ ∞ u (WMOmega n)) (h_T001 : ContDiffOn ℝ ∞ (WMV u) (WMOmega n) ∧ (∀ j : Fin n, ContDiffOn ℝ ∞ (WMW u j) (WMOmega n)) ∧ ContDiffOn ℝ ∞ (WMA u) (WMOmega n) ∧ (∀ j : Fin n, ContDiffOn ℝ ∞ (WMB u j) (WMOmega n)) ∧ (∀ j : Fin n, ContDiffOn ℝ ∞ (WMMixed u j) (WMOmega n))) (h_M007 : ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] (f : X → Y) (x : X), ContDiffAt ℝ 2 f x → ∀ v w : X, fderiv ℝ (fderiv ℝ f) x v w = fderiv ℝ (fderiv ℝ f) x w v) : yui_aux_type% "(2 : ℕ∞ω) ≤ ∞" := by
  change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
  exact WithTop.coe_le_coe.mpr le_top

end Local_T006
open Local_T006 in
theorem T006 (n : ℕ) (m : ℕ) (u : WMZ n → WMX m) (q : WMX m) (h_H001 : 1 ≤ n ∧ 1 ≤ m ∧ ContDiffOn ℝ ∞ u (WMOmega n)) (h_T001 : ContDiffOn ℝ ∞ (WMV u) (WMOmega n) ∧ (∀ j : Fin n, ContDiffOn ℝ ∞ (WMW u j) (WMOmega n)) ∧ ContDiffOn ℝ ∞ (WMA u) (WMOmega n) ∧ (∀ j : Fin n, ContDiffOn ℝ ∞ (WMB u j) (WMOmega n)) ∧ (∀ j : Fin n, ContDiffOn ℝ ∞ (WMMixed u j) (WMOmega n))) (h_M007 : ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] (f : X → Y) (x : X), ContDiffAt ℝ 2 f x → ∀ v w : X, fderiv ℝ (fderiv ℝ f) x v w = fderiv ℝ (fderiv ℝ f) x w v) :
    ∀ (x : WMX n) (t : ℝ), 0 < t → ∀ j : Fin n, fderiv ℝ (WMW u j) (x, t) (WMT n) = WMMixed u j (x, t) := by
  intro x t ht j
  have hopen : IsOpen (WMOmega n) := by
    exact isOpen_lt continuous_const continuous_snd
  have hmem : (x, t) ∈ WMOmega n := ht
  have hf : ContDiffAt ℝ ∞ u (x, t) :=
    h_H001.2.2.contDiffAt (hopen.mem_nhds hmem)
  have hf2 : ContDiffAt ℝ 2 u (x, t) :=
    hf.of_le (@yui_aux_0001 n m u q h_H001 h_T001 h_M007)
  have hdf : ContDiffAt ℝ 1 (fderiv ℝ u) (x, t) :=
    hf2.fderiv_right (by norm_num)
  have heval : ∀ v w : WMZ n,
      fderiv ℝ (fun z : WMZ n => fderiv ℝ u z v) (x, t) w =
        fderiv ℝ (fderiv ℝ u) (x, t) w v := by
    intro v w
    have h := fderiv_clm_apply hdf.differentiableAt_one
      (differentiableAt_const v : DifferentiableAt ℝ (fun _ : WMZ n => v) (x, t))
    simpa using congrArg (fun L : WMZ n →L[ℝ] WMX m => L w) h
  change fderiv ℝ (fun z : WMZ n => fderiv ℝ u z (WMS n j)) (x, t) (WMT n) =
    fderiv ℝ (fun z : WMZ n => fderiv ℝ u z (WMT n)) (x, t) (WMS n j)
  calc
    _ = fderiv ℝ (fderiv ℝ u) (x, t) (WMT n) (WMS n j) := heval _ _
    _ = fderiv ℝ (fderiv ℝ u) (x, t) (WMS n j) (WMT n) :=
      h_M007 u (x, t) hf2 (WMT n) (WMS n j)
    _ = _ := (heval _ _).symm

namespace Local_T007
theorem yui_aux_0001 (n : ℕ) (m : ℕ) (u : WMZ n → WMX m) (q : WMX m) (h_T001 : ContDiffOn ℝ ∞ (WMV u) (WMOmega n) ∧ (∀ j : Fin n, ContDiffOn ℝ ∞ (WMW u j) (WMOmega n)) ∧ ContDiffOn ℝ ∞ (WMA u) (WMOmega n) ∧ (∀ j : Fin n, ContDiffOn ℝ ∞ (WMB u j) (WMOmega n)) ∧ (∀ j : Fin n, ContDiffOn ℝ ∞ (WMMixed u j) (WMOmega n))) (h_T002 : ∀ k : WMTerm n, ContDiffOn ℝ ∞ (WMField u k) (WMOmega n)) (h_T006 : ∀ (x : WMX n) (t : ℝ), 0 < t → ∀ j : Fin n, fderiv ℝ (WMW u j) (x, t) (WMT n) = WMMixed u j (x, t)) (h_M005 : ∀ {Y : Type} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] (f : ℝ → Y) (f' : Y) (t : ℝ), HasDerivAt f f' t → HasDerivAt (fun r => ‖f r‖ ^ 2) (2 * inner ℝ (f t) f') t) (h_M006 : ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] (f g : X → Y) (x v : X), DifferentiableAt ℝ f x → DifferentiableAt ℝ g x → fderiv ℝ (fun y => inner ℝ (f y) (g y)) x v = inner ℝ (f x) (fderiv ℝ g x v) + inner ℝ (fderiv ℝ f x v) (g x)) : yui_aux_type% "∀ (x : WMX n) (t : ℝ), HasDerivAt (fun r : ℝ => (x, r)) (WMT n) t" := by
  intro x t
  convert (hasDerivAt_const t x).prodMk (hasDerivAt_id t) using 1 <;> rfl

theorem yui_aux_0002 (n : ℕ) (m : ℕ) (u : WMZ n → WMX m) (q : WMX m) (h_T001 : ContDiffOn ℝ ∞ (WMV u) (WMOmega n) ∧ (∀ j : Fin n, ContDiffOn ℝ ∞ (WMW u j) (WMOmega n)) ∧ ContDiffOn ℝ ∞ (WMA u) (WMOmega n) ∧ (∀ j : Fin n, ContDiffOn ℝ ∞ (WMB u j) (WMOmega n)) ∧ (∀ j : Fin n, ContDiffOn ℝ ∞ (WMMixed u j) (WMOmega n))) (h_T002 : ∀ k : WMTerm n, ContDiffOn ℝ ∞ (WMField u k) (WMOmega n)) (h_T006 : ∀ (x : WMX n) (t : ℝ), 0 < t → ∀ j : Fin n, fderiv ℝ (WMW u j) (x, t) (WMT n) = WMMixed u j (x, t)) (h_M005 : ∀ {Y : Type} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] (f : ℝ → Y) (f' : Y) (t : ℝ), HasDerivAt f f' t → HasDerivAt (fun r => ‖f r‖ ^ 2) (2 * inner ℝ (f t) f') t) (h_M006 : ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] (f g : X → Y) (x v : X), DifferentiableAt ℝ f x → DifferentiableAt ℝ g x → fderiv ℝ (fun y => inner ℝ (f y) (g y)) x v = inner ℝ (f x) (fderiv ℝ g x v) + inner ℝ (fderiv ℝ f x v) (g x)) : yui_aux_type% "∀ {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]\n(f : WMZ n → Y) (x : WMX n) (t : ℝ), DifferentiableAt ℝ f (x,t) →\nHasDerivAt (fun r : ℝ => f (x,r)) (fderiv ℝ f (x,t) (WMT n)) t" := by
  intro Y _ _ f x t hf
  have hc : HasDerivAt (fun r : ℝ => (x,r)) (WMT n) t :=
    @yui_aux_0001 n m u q h_T001 h_T002 h_T006 h_M005 h_M006 x t
  convert hf.hasFDerivAt.comp_hasDerivAt t hc using 1 <;> rfl

theorem yui_aux_0003 (n : ℕ) (m : ℕ) (u : WMZ n → WMX m) (q : WMX m) (h_T001 : ContDiffOn ℝ ∞ (WMV u) (WMOmega n) ∧ (∀ j : Fin n, ContDiffOn ℝ ∞ (WMW u j) (WMOmega n)) ∧ ContDiffOn ℝ ∞ (WMA u) (WMOmega n) ∧ (∀ j : Fin n, ContDiffOn ℝ ∞ (WMB u j) (WMOmega n)) ∧ (∀ j : Fin n, ContDiffOn ℝ ∞ (WMMixed u j) (WMOmega n))) (h_T002 : ∀ k : WMTerm n, ContDiffOn ℝ ∞ (WMField u k) (WMOmega n)) (h_T006 : ∀ (x : WMX n) (t : ℝ), 0 < t → ∀ j : Fin n, fderiv ℝ (WMW u j) (x, t) (WMT n) = WMMixed u j (x, t)) (h_M005 : ∀ {Y : Type} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] (f : ℝ → Y) (f' : Y) (t : ℝ), HasDerivAt f f' t → HasDerivAt (fun r => ‖f r‖ ^ 2) (2 * inner ℝ (f t) f') t) (h_M006 : ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] (f g : X → Y) (x v : X), DifferentiableAt ℝ f x → DifferentiableAt ℝ g x → fderiv ℝ (fun y => inner ℝ (f y) (g y)) x v = inner ℝ (f x) (fderiv ℝ g x v) + inner ℝ (fderiv ℝ f x v) (g x)) : yui_aux_type% "∀ (x : WMX n) (t : ℝ), 0 < t → HasDerivAt\n(fun r : ℝ => ‖WMV u (x,r)‖ ^ 2 + ∑ j : Fin n, ‖WMW u j (x,r)‖ ^ 2)\n(2 * inner ℝ (WMV u (x,t)) (WMA u (x,t)) +\n2 * ∑ j : Fin n, inner ℝ (WMW u j (x,t)) (WMMixed u j (x,t))) t" := by
  intro x t ht
  have hopen : IsOpen (WMOmega n) := isOpen_lt continuous_const continuous_snd
  have hmem : WMOmega n ∈ 𝓝 (x,t) := hopen.mem_nhds ht
  have hV : DifferentiableAt ℝ (WMV u) (x,t) :=
    (h_T001.1.differentiableOn (by simp)).differentiableAt hmem
  have hW : ∀ j : Fin n, DifferentiableAt ℝ (WMW u j) (x,t) :=
    fun j => ((h_T001.2.1 j).differentiableOn (by simp)).differentiableAt hmem
  have hv : HasDerivAt (fun r : ℝ => WMV u (x,r)) (WMA u (x,t)) t :=
    @yui_aux_0002 n m u q h_T001 h_T002 h_T006 h_M005 h_M006
      (WMX m) _ _ (WMV u) x t hV
  have hw : ∀ j : Fin n, HasDerivAt (fun r : ℝ => WMW u j (x,r))
      (WMMixed u j (x,t)) t := by
    intro j
    rw [← h_T006 x t ht j]
    exact @yui_aux_0002 n m u q h_T001 h_T002 h_T006 h_M005 h_M006
      (WMX m) _ _ (WMW u j) x t (hW j)
  have hvnorm := h_M005 (fun r : ℝ => WMV u (x,r)) (WMA u (x,t)) t hv
  have hwnorm : ∀ j : Fin n, HasDerivAt (fun r : ℝ => ‖WMW u j (x,r)‖ ^ 2)
      (2 * inner ℝ (WMW u j (x,t)) (WMMixed u j (x,t))) t :=
    fun j => h_M005 (fun r : ℝ => WMW u j (x,r)) (WMMixed u j (x,t)) t (hw j)
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => hwnorm j)
  convert hvnorm.add hsum using 1 <;> first | rfl | simp only [Finset.mul_sum]

end Local_T007
open Local_T007 in
theorem T007 (n : ℕ) (m : ℕ) (u : WMZ n → WMX m) (q : WMX m) (h_T001 : ContDiffOn ℝ ∞ (WMV u) (WMOmega n) ∧ (∀ j : Fin n, ContDiffOn ℝ ∞ (WMW u j) (WMOmega n)) ∧ ContDiffOn ℝ ∞ (WMA u) (WMOmega n) ∧ (∀ j : Fin n, ContDiffOn ℝ ∞ (WMB u j) (WMOmega n)) ∧ (∀ j : Fin n, ContDiffOn ℝ ∞ (WMMixed u j) (WMOmega n))) (h_T002 : ∀ k : WMTerm n, ContDiffOn ℝ ∞ (WMField u k) (WMOmega n)) (h_T006 : ∀ (x : WMX n) (t : ℝ), 0 < t → ∀ j : Fin n, fderiv ℝ (WMW u j) (x, t) (WMT n) = WMMixed u j (x, t)) (h_M005 : ∀ {Y : Type} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] (f : ℝ → Y) (f' : Y) (t : ℝ), HasDerivAt f f' t → HasDerivAt (fun r => ‖f r‖ ^ 2) (2 * inner ℝ (f t) f') t) (h_M006 : ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] (f g : X → Y) (x v : X), DifferentiableAt ℝ f x → DifferentiableAt ℝ g x → fderiv ℝ (fun y => inner ℝ (f y) (g y)) x v = inner ℝ (f x) (fderiv ℝ g x v) + inner ℝ (fderiv ℝ f x v) (g x)) :
    ∀ (x : WMX n) (t : ℝ), 0 < t → (WMET u (x, t) = 2 * inner ℝ (WMV u (x, t)) (WMA u (x, t)) + 2 * ∑ j : Fin n, inner ℝ (WMW u j (x, t)) (WMMixed u j (x, t))) ∧ (∀ j : Fin n, WMGX u j (x, t) = inner ℝ (WMV u (x, t)) (WMB u j (x, t)) + inner ℝ (WMMixed u j (x, t)) (WMW u j (x, t))) := by
  intro x t ht
  have hopen : IsOpen (WMOmega n) := isOpen_lt continuous_const continuous_snd
  have hmem : WMOmega n ∈ 𝓝 (x, t) := hopen.mem_nhds ht
  constructor
  · have hformula := @yui_aux_0003 n m u q h_T001 h_T002 h_T006 h_M005 h_M006 x t ht
    have hdensity : HasDerivAt (fun r : ℝ => WME u (x, r))
        (2 * inner ℝ (WMV u (x, t)) (WMA u (x, t)) +
          2 * ∑ j : Fin n, inner ℝ (WMW u j (x, t)) (WMMixed u j (x, t))) t := by
      apply hformula.congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds ht] with r hr
      change 0 < r at hr
      exact if_pos hr
    have he : DifferentiableAt ℝ (WME u) (x, t) :=
      ((h_T002 WMTerm.density).differentiableOn (by simp)).differentiableAt hmem
    have hactual : HasDerivAt (fun r : ℝ => WME u (x, r)) (WMET u (x, t)) t :=
      @yui_aux_0002 n m u q h_T001 h_T002 h_T006 h_M005 h_M006
        ℝ _ _ (WME u) x t he
    exact hactual.unique hdensity
  · intro j
    have hV : DifferentiableAt ℝ (WMV u) (x, t) :=
      (h_T001.1.differentiableOn (by simp)).differentiableAt hmem
    have hW : DifferentiableAt ℝ (WMW u j) (x, t) :=
      ((h_T001.2.1 j).differentiableOn (by simp)).differentiableAt hmem
    have heq : WMG u j =ᶠ[𝓝 (x, t)] (fun z => inner ℝ (WMV u z) (WMW u j z)) := by
      filter_upwards [hmem] with z hz
      exact if_pos hz
    change fderiv ℝ (WMG u j) (x, t) (WMS n j) = _
    rw [heq.fderiv_eq]
    exact h_M006 (WMV u) (WMW u j) (x, t) (WMS n j) hV hW

theorem T008 (n : ℕ) (m : ℕ) (u : WMZ n → WMX m) (q : WMX m) (h_T005 : ∀ (x : WMX n) (t : ℝ), 0 < t → inner ℝ (u (x, t)) (WMV u (x, t)) = 0 ∧ inner ℝ (WMV u (x, t)) (WMA u (x, t) - ∑ j : Fin n, WMB u j (x, t)) = 0) (h_T007 : ∀ (x : WMX n) (t : ℝ), 0 < t → (WMET u (x, t) = 2 * inner ℝ (WMV u (x, t)) (WMA u (x, t)) + 2 * ∑ j : Fin n, inner ℝ (WMW u j (x, t)) (WMMixed u j (x, t))) ∧ (∀ j : Fin n, WMGX u j (x, t) = inner ℝ (WMV u (x, t)) (WMB u j (x, t)) + inner ℝ (WMMixed u j (x, t)) (WMW u j (x, t)))) :
    ∀ (x : WMX n) (t : ℝ), 0 < t → WMET u (x, t) = 2 * ∑ j : Fin n, WMGX u j (x, t) := by
  intro x t ht
  have hnormal := (h_T005 x t ht).2
  have he := (h_T007 x t ht).1
  have hg := (h_T007 x t ht).2
  rw [inner_sub_right, inner_sum] at hnormal
  rw [he]
  simp_rw [hg, real_inner_comm (WMW u _ (x, t)) (WMMixed u _ (x, t))]
  rw [Finset.sum_add_distrib]
  linarith

namespace Local_T012
theorem yui_aux_0001 (n : ℕ) (m : ℕ) (u : WMZ n → WMX m) (q : WMX m) (h_T004 : (∀ k : WMTerm n, ContDiffOn ℝ ∞ (WMField u k) (WMOmega n)) ∧ (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (WMX n), IsCompact C ∧ ∀ r ∈ Ioo (t0 / 2) (3 * t0 / 2), ∀ k : WMTerm n, (∀ x : WMX n, x ∉ C → WMField u k (x, r) = 0) ∧ tsupport (fun x : WMX n => WMField u k (x, r)) ⊆ C)) : yui_aux_type% "∀ (t : ℝ), 0 < t → ∀ (j : Fin n) (x : WMX n),\nHasFDerivAt (fun y : WMX n => WMG u j (y, t))\n ((fderiv ℝ (WMG u j) (x, t)).comp (ContinuousLinearMap.inl ℝ (WMX n) ℝ)) x" := by
  intro t ht j x
  have hopen : IsOpen (WMOmega n) := isOpen_lt continuous_const continuous_snd
  have hflux : ContDiffOn ℝ 1 (WMG u j) (WMOmega n) :=
    (h_T004.1 (WMTerm.flux j)).of_le (by simp)
  have hdiff : DifferentiableAt ℝ (WMG u j) (x, t) :=
    (hflux.contDiffAt (hopen.mem_nhds ht)).differentiableAt_one
  have hi : HasFDerivAt (fun y : WMX n => (y, t))
      (ContinuousLinearMap.inl ℝ (WMX n) ℝ) x :=
    hasFDerivAt_prodMk_left (𝕜 := ℝ) x t
  exact HasFDerivAt.comp (𝕜 := ℝ) (f := fun y : WMX n => (y, t))
    (g := WMG u j) x hdiff.hasFDerivAt hi

end Local_T012
open Local_T012 in
theorem T012 (n : ℕ) (m : ℕ) (u : WMZ n → WMX m) (q : WMX m) (h_T004 : (∀ k : WMTerm n, ContDiffOn ℝ ∞ (WMField u k) (WMOmega n)) ∧ (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (WMX n), IsCompact C ∧ ∀ r ∈ Ioo (t0 / 2) (3 * t0 / 2), ∀ k : WMTerm n, (∀ x : WMX n, x ∉ C → WMField u k (x, r) = 0) ∧ tsupport (fun x : WMX n => WMField u k (x, r)) ⊆ C)) :
    ∀ t : ℝ, 0 < t → ∀ j : Fin n, ContDiff ℝ 1 (fun x : WMX n => WMG u j (x, t)) ∧ HasCompactSupport (fun x : WMX n => WMG u j (x, t)) ∧ (∀ x : WMX n, fderiv ℝ (fun y : WMX n => WMG u j (y, t)) x (WMBasis n j) = WMGX u j (x, t)) := by
  intro t ht j
  have hflux : ContDiffOn ℝ 1 (WMG u j) (WMOmega n) :=
    (h_T004.1 (WMTerm.flux j)).of_le (by simp)
  have hinc : ContDiff ℝ 1 (fun x : WMX n => (x, t)) :=
    contDiff_id.prodMk contDiff_const
  have hsection : ContDiff ℝ 1 (fun x : WMX n => WMG u j (x, t)) :=
    hflux.comp_contDiff hinc (fun x => ht)
  refine ⟨hsection, ?_, ?_⟩
  · obtain ⟨C, hC, hsupport⟩ := h_T004.2 t ht
    have htime : t ∈ Ioo (t / 2) (3 * t / 2) := by
      constructor <;> linarith
    exact hC.of_isClosed_subset (isClosed_tsupport _) (hsupport t htime (WMTerm.flux j)).2
  · intro x
    have hchain := @yui_aux_0001 n m u q h_T004 t ht j x
    rw [hchain.fderiv]
    rfl

theorem T013 (n : ℕ) (m : ℕ) (u : WMZ n → WMX m) (q : WMX m) (h_T012 : ∀ t : ℝ, 0 < t → ∀ j : Fin n, ContDiff ℝ 1 (fun x : WMX n => WMG u j (x, t)) ∧ HasCompactSupport (fun x : WMX n => WMG u j (x, t)) ∧ (∀ x : WMX n, fderiv ℝ (fun y : WMX n => WMG u j (y, t)) x (WMBasis n j) = WMGX u j (x, t))) (h_E004 : ∀ (n : ℕ) (g : EuclideanSpace ℝ (Fin n) → ℝ) (v : EuclideanSpace ℝ (Fin n)), ContDiff ℝ 1 g → HasCompactSupport g → Integrable (fun x => fderiv ℝ g x v) ∧ (∫ x, fderiv ℝ g x v) = 0) :
    ∀ t : ℝ, 0 < t → ∀ j : Fin n, (∫ x : WMX n, WMGX u j (x, t)) = 0 := by
  intro t ht j
  obtain ⟨hC, hK, hD⟩ := h_T012 t ht j
  have hzero := (h_E004 n (fun x : WMX n => WMG u j (x, t)) (WMBasis n j) hC hK).2
  simpa only [hD] using hzero

theorem T014 (n : ℕ) (m : ℕ) (u : WMZ n → WMX m) (q : WMX m) (h_T008 : ∀ (x : WMX n) (t : ℝ), 0 < t → WMET u (x, t) = 2 * ∑ j : Fin n, WMGX u j (x, t)) (h_T009 : ∀ t : ℝ, 0 < t → ∀ k : WMTerm n, Integrable (fun x : WMX n => WMField u k (x, t))) (h_T013 : ∀ t : ℝ, 0 < t → ∀ j : Fin n, (∫ x : WMX n, WMGX u j (x, t)) = 0) :
    ∀ t : ℝ, 0 < t → (∫ x : WMX n, WMET u (x, t)) = 0 := by
  intro t ht
  have hi (j : Fin n) : Integrable (fun x : WMX n => WMGX u j (x, t)) := by
    simpa only [WMField] using h_T009 t ht (WMTerm.fluxSpace j)
  calc
    (∫ x : WMX n, WMET u (x, t)) =
        ∫ x : WMX n, 2 * ∑ j : Fin n, WMGX u j (x, t) := by
      congr 1
      funext x
      exact h_T008 x t ht
    _ = 2 * (∫ x : WMX n, ∑ j : Fin n, WMGX u j (x, t)) :=
      integral_const_mul 2 _
    _ = 2 * ∑ j : Fin n, (∫ x : WMX n, WMGX u j (x, t)) := by
      rw [integral_finsetSum Finset.univ (fun j _ => hi j)]
    _ = 0 := by simp [h_T013 t ht]

theorem T015 (n : ℕ) (m : ℕ) (u : WMZ n → WMX m) (q : WMX m) (h_T009 : ∀ t : ℝ, 0 < t → ∀ k : WMTerm n, Integrable (fun x : WMX n => WMField u k (x, t))) (h_T011 : ∀ t : ℝ, 0 < t → HasDerivAt (WMEnergy u) (∫ x : WMX n, WMET u (x, t)) t) (h_T014 : ∀ t : ℝ, 0 < t → (∫ x : WMX n, WMET u (x, t)) = 0) :
    ∀ t : ℝ, 0 < t → Integrable (fun x : WMX n => WME u (x, t)) ∧ HasDerivAt (WMEnergy u) 0 t := by
  intro t ht
  constructor
  · simpa only [WMField] using h_T009 t ht (WMTerm.density)
  · rw [← h_T014 t ht]
    exact h_T011 t ht

set_option Elab.async false in
theorem P (n : ℕ) (m : ℕ) (u : WMZ n → WMX m) (q : WMX m) (h_H001 : 1 ≤ n ∧ 1 ≤ m ∧ ContDiffOn ℝ ∞ u (WMOmega n)) (h_H002 : ‖q‖ = 1) (h_H003 : ∀ (x : WMX n) (t : ℝ), 0 < t → ‖u (x, t)‖ = 1) (h_H004 : ∀ (x : WMX n) (t : ℝ), 0 < t → ∃ a : ℝ, WMA u (x, t) - (∑ j : Fin n, WMB u j (x, t)) = a • u (x, t)) (h_H005 : ∀ s t : ℝ, 0 < s → s < t → ∃ C : Set (WMX n), IsCompact C ∧ ∀ (x : WMX n) (r : ℝ), x ∉ C → r ∈ Icc s t → u (x, r) = q) (h_M001 : ∀ (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ), Continuous f → HasCompactSupport f → Integrable f) (h_M002 : ∀ (n : ℕ) (F D : ℝ → EuclideanSpace ℝ (Fin n) → ℝ) (t0 : ℝ) (s : Set ℝ) (b : EuclideanSpace ℝ (Fin n) → ℝ), s ∈ 𝓝 t0 → (∀ᶠ t in 𝓝 t0, AEStronglyMeasurable (F t) volume) → Integrable (F t0) → AEStronglyMeasurable (D t0) volume → (∀ᵐ x ∂volume, ∀ t ∈ s, ‖D t x‖ ≤ b x) → Integrable b → (∀ᵐ x ∂volume, ∀ t ∈ s, HasDerivAt (fun r => F r x) (D t x) t) → Integrable (D t0) ∧ HasDerivAt (fun t => ∫ x, F t x) (∫ x, D t0 x) t0) (h_E004 : ∀ (n : ℕ) (g : EuclideanSpace ℝ (Fin n) → ℝ) (v : EuclideanSpace ℝ (Fin n)), ContDiff ℝ 1 g → HasCompactSupport g → Integrable (fun x => fderiv ℝ g x v) ∧ (∫ x, fderiv ℝ g x v) = 0) (h_M005 : ∀ {Y : Type} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] (f : ℝ → Y) (f' : Y) (t : ℝ), HasDerivAt f f' t → HasDerivAt (fun r => ‖f r‖ ^ 2) (2 * inner ℝ (f t) f') t) (h_M006 : ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] (f g : X → Y) (x v : X), DifferentiableAt ℝ f x → DifferentiableAt ℝ g x → fderiv ℝ (fun y => inner ℝ (f y) (g y)) x v = inner ℝ (f x) (fderiv ℝ g x v) + inner ℝ (fderiv ℝ f x v) (g x)) (h_M007 : ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] (f : X → Y) (x : X), ContDiffAt ℝ 2 f x → ∀ v w : X, fderiv ℝ (fderiv ℝ f) x v w = fderiv ℝ (fderiv ℝ f) x w v) (h_M008 : ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] (f : X → Y) (s : Set X), IsOpen s → ContDiffOn ℝ ∞ f s → ContDiffOn ℝ ∞ (fderiv ℝ f) s) (h_M009 : ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] (f g : X → Y) (x : X), Filter.EventuallyEq (𝓝 x) f g → fderiv ℝ f x = fderiv ℝ g x) :
    ∀ t : ℝ, 0 < t → Integrable (fun x : WMX n => WME u (x, t)) ∧ HasDerivAt (WMEnergy u) 0 t := by
  have h_T001 : ContDiffOn ℝ ∞ (WMV u) (WMOmega n) ∧ (∀ j : Fin n, ContDiffOn ℝ ∞ (WMW u j) (WMOmega n)) ∧ ContDiffOn ℝ ∞ (WMA u) (WMOmega n) ∧ (∀ j : Fin n, ContDiffOn ℝ ∞ (WMB u j) (WMOmega n)) ∧ (∀ j : Fin n, ContDiffOn ℝ ∞ (WMMixed u j) (WMOmega n)) := @T001 n m u q h_H001 h_M008
  have h_T002 : ∀ k : WMTerm n, ContDiffOn ℝ ∞ (WMField u k) (WMOmega n) := @T002 n m u q h_T001 h_M008
  have h_T003 : ∀ t0 : ℝ, 0 < t0 → ∃ C : Set (WMX n), IsCompact C ∧ ∀ r ∈ Ioo (t0 / 2) (3 * t0 / 2), ∀ k : WMTerm n, (∀ x : WMX n, x ∉ C → WMField u k (x, r) = 0) ∧ tsupport (fun x : WMX n => WMField u k (x, r)) ⊆ C := @T003 n m u q h_H005 h_M009
  have h_T004 : (∀ k : WMTerm n, ContDiffOn ℝ ∞ (WMField u k) (WMOmega n)) ∧ (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (WMX n), IsCompact C ∧ ∀ r ∈ Ioo (t0 / 2) (3 * t0 / 2), ∀ k : WMTerm n, (∀ x : WMX n, x ∉ C → WMField u k (x, r) = 0) ∧ tsupport (fun x : WMX n => WMField u k (x, r)) ⊆ C) := @T004 n m u q h_T002 h_T003
  have h_T009 : ∀ t : ℝ, 0 < t → ∀ k : WMTerm n, Integrable (fun x : WMX n => WMField u k (x, t)) := @T009 n m u q h_T004 h_M001
  have h_T010 : ∀ t0 : ℝ, 0 < t0 → ∃ b : WMX n → ℝ, Integrable b ∧ ∀ (x : WMX n) (r : ℝ), r ∈ Ioo (3 * t0 / 4) (5 * t0 / 4) → ‖WMET u (x, r)‖ ≤ b x := @T010 n m u q h_T004
  have h_T011 : ∀ t : ℝ, 0 < t → HasDerivAt (WMEnergy u) (∫ x : WMX n, WMET u (x, t)) t := @T011 n m u q h_T004 h_T009 h_T010 h_M002
  have h_T005 : ∀ (x : WMX n) (t : ℝ), 0 < t → inner ℝ (u (x, t)) (WMV u (x, t)) = 0 ∧ inner ℝ (WMV u (x, t)) (WMA u (x, t) - ∑ j : Fin n, WMB u j (x, t)) = 0 := @T005 n m u q h_H001 h_H003 h_H004 h_M005 h_M009
  have h_T006 : ∀ (x : WMX n) (t : ℝ), 0 < t → ∀ j : Fin n, fderiv ℝ (WMW u j) (x, t) (WMT n) = WMMixed u j (x, t) := @T006 n m u q h_H001 h_T001 h_M007
  have h_T007 : ∀ (x : WMX n) (t : ℝ), 0 < t → (WMET u (x, t) = 2 * inner ℝ (WMV u (x, t)) (WMA u (x, t)) + 2 * ∑ j : Fin n, inner ℝ (WMW u j (x, t)) (WMMixed u j (x, t))) ∧ (∀ j : Fin n, WMGX u j (x, t) = inner ℝ (WMV u (x, t)) (WMB u j (x, t)) + inner ℝ (WMMixed u j (x, t)) (WMW u j (x, t))) := @T007 n m u q h_T001 h_T002 h_T006 h_M005 h_M006
  have h_T008 : ∀ (x : WMX n) (t : ℝ), 0 < t → WMET u (x, t) = 2 * ∑ j : Fin n, WMGX u j (x, t) := @T008 n m u q h_T005 h_T007
  have h_T012 : ∀ t : ℝ, 0 < t → ∀ j : Fin n, ContDiff ℝ 1 (fun x : WMX n => WMG u j (x, t)) ∧ HasCompactSupport (fun x : WMX n => WMG u j (x, t)) ∧ (∀ x : WMX n, fderiv ℝ (fun y : WMX n => WMG u j (y, t)) x (WMBasis n j) = WMGX u j (x, t)) := @T012 n m u q h_T004
  have h_T013 : ∀ t : ℝ, 0 < t → ∀ j : Fin n, (∫ x : WMX n, WMGX u j (x, t)) = 0 := @T013 n m u q h_T012 h_E004
  have h_T014 : ∀ t : ℝ, 0 < t → (∫ x : WMX n, WMET u (x, t)) = 0 := @T014 n m u q h_T008 h_T009 h_T013
  have h_T015 : ∀ t : ℝ, 0 < t → Integrable (fun x : WMX n => WME u (x, t)) ∧ HasDerivAt (WMEnergy u) 0 t := @T015 n m u q h_T009 h_T011 h_T014
  exact h_T015

#check @P
#print axioms P

end Translation

namespace AuditBExport
set_option autoImplicit false
theorem resolved_M001 (n : ℕ) (m : ℕ) (u : WMZ n → WMX m) (q : WMX m) (h_H001 : 1 ≤ n ∧ 1 ≤ m ∧ ContDiffOn ℝ ∞ u (WMOmega n)) (h_H002 : ‖q‖ = 1) (h_H003 : ∀ (x : WMX n) (t : ℝ), 0 < t → ‖u (x, t)‖ = 1) (h_H004 : ∀ (x : WMX n) (t : ℝ), 0 < t → ∃ a : ℝ, WMA u (x, t) - (∑ j : Fin n, WMB u j (x, t)) = a • u (x, t)) (h_H005 : ∀ s t : ℝ, 0 < s → s < t → ∃ C : Set (WMX n), IsCompact C ∧ ∀ (x : WMX n) (r : ℝ), x ∉ C → r ∈ Icc s t → u (x, r) = q) (h_E004 : ∀ (n : ℕ) (g : EuclideanSpace ℝ (Fin n) → ℝ) (v : EuclideanSpace ℝ (Fin n)), ContDiff ℝ 1 g → HasCompactSupport g → Integrable (fun x => fderiv ℝ g x v) ∧ (∫ x, fderiv ℝ g x v) = 0) : ∀ (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ), Continuous f → HasCompactSupport f → Integrable f := by
  intro n f hf hc
  exact hf.integrable_of_hasCompactSupport hc

theorem resolved_M002 (n : ℕ) (m : ℕ) (u : WMZ n → WMX m) (q : WMX m) (h_H001 : 1 ≤ n ∧ 1 ≤ m ∧ ContDiffOn ℝ ∞ u (WMOmega n)) (h_H002 : ‖q‖ = 1) (h_H003 : ∀ (x : WMX n) (t : ℝ), 0 < t → ‖u (x, t)‖ = 1) (h_H004 : ∀ (x : WMX n) (t : ℝ), 0 < t → ∃ a : ℝ, WMA u (x, t) - (∑ j : Fin n, WMB u j (x, t)) = a • u (x, t)) (h_H005 : ∀ s t : ℝ, 0 < s → s < t → ∃ C : Set (WMX n), IsCompact C ∧ ∀ (x : WMX n) (r : ℝ), x ∉ C → r ∈ Icc s t → u (x, r) = q) (h_E004 : ∀ (n : ℕ) (g : EuclideanSpace ℝ (Fin n) → ℝ) (v : EuclideanSpace ℝ (Fin n)), ContDiff ℝ 1 g → HasCompactSupport g → Integrable (fun x => fderiv ℝ g x v) ∧ (∫ x, fderiv ℝ g x v) = 0) : ∀ (n : ℕ) (F D : ℝ → EuclideanSpace ℝ (Fin n) → ℝ) (t0 : ℝ) (s : Set ℝ) (b : EuclideanSpace ℝ (Fin n) → ℝ), s ∈ 𝓝 t0 → (∀ᶠ t in 𝓝 t0, AEStronglyMeasurable (F t) volume) → Integrable (F t0) → AEStronglyMeasurable (D t0) volume → (∀ᵐ x ∂volume, ∀ t ∈ s, ‖D t x‖ ≤ b x) → Integrable b → (∀ᵐ x ∂volume, ∀ t ∈ s, HasDerivAt (fun r => F r x) (D t x) t) → Integrable (D t0) ∧ HasDerivAt (fun t => ∫ x, F t x) (∫ x, D t0 x) t0 := by
  intro n F D t0 s b hs hm hi hd hb hbi hder
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hm hi hd hb hbi hder

theorem resolved_M005 (n : ℕ) (m : ℕ) (u : WMZ n → WMX m) (q : WMX m) (h_H001 : 1 ≤ n ∧ 1 ≤ m ∧ ContDiffOn ℝ ∞ u (WMOmega n)) (h_H002 : ‖q‖ = 1) (h_H003 : ∀ (x : WMX n) (t : ℝ), 0 < t → ‖u (x, t)‖ = 1) (h_H004 : ∀ (x : WMX n) (t : ℝ), 0 < t → ∃ a : ℝ, WMA u (x, t) - (∑ j : Fin n, WMB u j (x, t)) = a • u (x, t)) (h_H005 : ∀ s t : ℝ, 0 < s → s < t → ∃ C : Set (WMX n), IsCompact C ∧ ∀ (x : WMX n) (r : ℝ), x ∉ C → r ∈ Icc s t → u (x, r) = q) (h_E004 : ∀ (n : ℕ) (g : EuclideanSpace ℝ (Fin n) → ℝ) (v : EuclideanSpace ℝ (Fin n)), ContDiff ℝ 1 g → HasCompactSupport g → Integrable (fun x => fderiv ℝ g x v) ∧ (∫ x, fderiv ℝ g x v) = 0) : ∀ {Y : Type} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] (f : ℝ → Y) (f' : Y) (t : ℝ), HasDerivAt f f' t → HasDerivAt (fun r => ‖f r‖ ^ 2) (2 * inner ℝ (f t) f') t := by
  intro Y _ _ f f' t hf
  exact hf.norm_sq

theorem resolved_M006 (n : ℕ) (m : ℕ) (u : WMZ n → WMX m) (q : WMX m) (h_H001 : 1 ≤ n ∧ 1 ≤ m ∧ ContDiffOn ℝ ∞ u (WMOmega n)) (h_H002 : ‖q‖ = 1) (h_H003 : ∀ (x : WMX n) (t : ℝ), 0 < t → ‖u (x, t)‖ = 1) (h_H004 : ∀ (x : WMX n) (t : ℝ), 0 < t → ∃ a : ℝ, WMA u (x, t) - (∑ j : Fin n, WMB u j (x, t)) = a • u (x, t)) (h_H005 : ∀ s t : ℝ, 0 < s → s < t → ∃ C : Set (WMX n), IsCompact C ∧ ∀ (x : WMX n) (r : ℝ), x ∉ C → r ∈ Icc s t → u (x, r) = q) (h_E004 : ∀ (n : ℕ) (g : EuclideanSpace ℝ (Fin n) → ℝ) (v : EuclideanSpace ℝ (Fin n)), ContDiff ℝ 1 g → HasCompactSupport g → Integrable (fun x => fderiv ℝ g x v) ∧ (∫ x, fderiv ℝ g x v) = 0) : ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] (f g : X → Y) (x v : X), DifferentiableAt ℝ f x → DifferentiableAt ℝ g x → fderiv ℝ (fun y => inner ℝ (f y) (g y)) x v = inner ℝ (f x) (fderiv ℝ g x v) + inner ℝ (fderiv ℝ f x v) (g x) := by
  intro X Y _ _ _ _ f g x v hf hg
  exact fderiv_inner_apply ℝ hf hg v

theorem resolved_M007 (n : ℕ) (m : ℕ) (u : WMZ n → WMX m) (q : WMX m) (h_H001 : 1 ≤ n ∧ 1 ≤ m ∧ ContDiffOn ℝ ∞ u (WMOmega n)) (h_H002 : ‖q‖ = 1) (h_H003 : ∀ (x : WMX n) (t : ℝ), 0 < t → ‖u (x, t)‖ = 1) (h_H004 : ∀ (x : WMX n) (t : ℝ), 0 < t → ∃ a : ℝ, WMA u (x, t) - (∑ j : Fin n, WMB u j (x, t)) = a • u (x, t)) (h_H005 : ∀ s t : ℝ, 0 < s → s < t → ∃ C : Set (WMX n), IsCompact C ∧ ∀ (x : WMX n) (r : ℝ), x ∉ C → r ∈ Icc s t → u (x, r) = q) (h_E004 : ∀ (n : ℕ) (g : EuclideanSpace ℝ (Fin n) → ℝ) (v : EuclideanSpace ℝ (Fin n)), ContDiff ℝ 1 g → HasCompactSupport g → Integrable (fun x => fderiv ℝ g x v) ∧ (∫ x, fderiv ℝ g x v) = 0) : ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] (f : X → Y) (x : X), ContDiffAt ℝ 2 f x → ∀ v w : X, fderiv ℝ (fderiv ℝ f) x v w = fderiv ℝ (fderiv ℝ f) x w v := by
  intro X Y _ _ _ _ f x hf
  exact hf.isSymmSndFDerivAt (by simp)

theorem resolved_M008 (n : ℕ) (m : ℕ) (u : WMZ n → WMX m) (q : WMX m) (h_H001 : 1 ≤ n ∧ 1 ≤ m ∧ ContDiffOn ℝ ∞ u (WMOmega n)) (h_H002 : ‖q‖ = 1) (h_H003 : ∀ (x : WMX n) (t : ℝ), 0 < t → ‖u (x, t)‖ = 1) (h_H004 : ∀ (x : WMX n) (t : ℝ), 0 < t → ∃ a : ℝ, WMA u (x, t) - (∑ j : Fin n, WMB u j (x, t)) = a • u (x, t)) (h_H005 : ∀ s t : ℝ, 0 < s → s < t → ∃ C : Set (WMX n), IsCompact C ∧ ∀ (x : WMX n) (r : ℝ), x ∉ C → r ∈ Icc s t → u (x, r) = q) (h_E004 : ∀ (n : ℕ) (g : EuclideanSpace ℝ (Fin n) → ℝ) (v : EuclideanSpace ℝ (Fin n)), ContDiff ℝ 1 g → HasCompactSupport g → Integrable (fun x => fderiv ℝ g x v) ∧ (∫ x, fderiv ℝ g x v) = 0) : ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] (f : X → Y) (s : Set X), IsOpen s → ContDiffOn ℝ ∞ f s → ContDiffOn ℝ ∞ (fderiv ℝ f) s := by
  intro X Y _ _ _ _ f s hs hf
  exact ((contDiffOn_infty_iff_fderiv_of_isOpen hs).mp hf).2

theorem resolved_M009 (n : ℕ) (m : ℕ) (u : WMZ n → WMX m) (q : WMX m) (h_H001 : 1 ≤ n ∧ 1 ≤ m ∧ ContDiffOn ℝ ∞ u (WMOmega n)) (h_H002 : ‖q‖ = 1) (h_H003 : ∀ (x : WMX n) (t : ℝ), 0 < t → ‖u (x, t)‖ = 1) (h_H004 : ∀ (x : WMX n) (t : ℝ), 0 < t → ∃ a : ℝ, WMA u (x, t) - (∑ j : Fin n, WMB u j (x, t)) = a • u (x, t)) (h_H005 : ∀ s t : ℝ, 0 < s → s < t → ∃ C : Set (WMX n), IsCompact C ∧ ∀ (x : WMX n) (r : ℝ), x ∉ C → r ∈ Icc s t → u (x, r) = q) (h_E004 : ∀ (n : ℕ) (g : EuclideanSpace ℝ (Fin n) → ℝ) (v : EuclideanSpace ℝ (Fin n)), ContDiff ℝ 1 g → HasCompactSupport g → Integrable (fun x => fderiv ℝ g x v) ∧ (∫ x, fderiv ℝ g x v) = 0) : ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] (f g : X → Y) (x : X), Filter.EventuallyEq (𝓝 x) f g → fderiv ℝ f x = fderiv ℝ g x := by
  intro X Y _ _ _ _ f g x hfg
  exact hfg.fderiv_eq

set_option Elab.async false in
theorem P (n : ℕ) (m : ℕ) (u : WMZ n → WMX m) (q : WMX m) (h_H001 : 1 ≤ n ∧ 1 ≤ m ∧ ContDiffOn ℝ ∞ u (WMOmega n)) (h_H002 : ‖q‖ = 1) (h_H003 : ∀ (x : WMX n) (t : ℝ), 0 < t → ‖u (x, t)‖ = 1) (h_H004 : ∀ (x : WMX n) (t : ℝ), 0 < t → ∃ a : ℝ, WMA u (x, t) - (∑ j : Fin n, WMB u j (x, t)) = a • u (x, t)) (h_H005 : ∀ s t : ℝ, 0 < s → s < t → ∃ C : Set (WMX n), IsCompact C ∧ ∀ (x : WMX n) (r : ℝ), x ∉ C → r ∈ Icc s t → u (x, r) = q) (h_E004 : ∀ (n : ℕ) (g : EuclideanSpace ℝ (Fin n) → ℝ) (v : EuclideanSpace ℝ (Fin n)), ContDiff ℝ 1 g → HasCompactSupport g → Integrable (fun x => fderiv ℝ g x v) ∧ (∫ x, fderiv ℝ g x v) = 0) : ∀ t : ℝ, 0 < t → Integrable (fun x : WMX n => WME u (x, t)) ∧ HasDerivAt (WMEnergy u) 0 t := by
  exact @Translation.P n m u q h_H001 h_H002 h_H003 h_H004 h_H005 (@resolved_M001 n m u q h_H001 h_H002 h_H003 h_H004 h_H005 h_E004) (@resolved_M002 n m u q h_H001 h_H002 h_H003 h_H004 h_H005 h_E004) h_E004 (@resolved_M005 n m u q h_H001 h_H002 h_H003 h_H004 h_H005 h_E004) (@resolved_M006 n m u q h_H001 h_H002 h_H003 h_H004 h_H005 h_E004) (@resolved_M007 n m u q h_H001 h_H002 h_H003 h_H004 h_H005 h_E004) (@resolved_M008 n m u q h_H001 h_H002 h_H003 h_H004 h_H005 h_E004) (@resolved_M009 n m u q h_H001 h_H002 h_H003 h_H004 h_H005 h_E004)

#check @P
#print axioms P
end AuditBExport


namespace YuiBasis
set_option autoImplicit false
set_option Elab.async false in
theorem B001 : ∀ (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ), Continuous f → HasCompactSupport f → Integrable f := by
  intro n f hf hc
  exact hf.integrable_of_hasCompactSupport hc
set_option Elab.async false in
theorem B002 : ∀ (n : ℕ) (F D : ℝ → EuclideanSpace ℝ (Fin n) → ℝ) (t0 : ℝ) (s : Set ℝ) (b : EuclideanSpace ℝ (Fin n) → ℝ), s ∈ 𝓝 t0 → (∀ᶠ t in 𝓝 t0, AEStronglyMeasurable (F t) volume) → Integrable (F t0) → AEStronglyMeasurable (D t0) volume → (∀ᵐ x ∂volume, ∀ t ∈ s, ‖D t x‖ ≤ b x) → Integrable b → (∀ᵐ x ∂volume, ∀ t ∈ s, HasDerivAt (fun r => F r x) (D t x) t) → Integrable (D t0) ∧ HasDerivAt (fun t => ∫ x, F t x) (∫ x, D t0 x) t0 := by
  intro n F D t0 s b hs hF_meas hF_int hD_meas h_bound hb h_diff
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (F := F) (F' := D) (x₀ := t0) (s := s) (bound := b)
    hs hF_meas hF_int hD_meas h_bound hb h_diff
set_option Elab.async false in
theorem B003 : ∀ (n : ℕ) (f g : EuclideanSpace ℝ (Fin n) → ℝ) (v : EuclideanSpace ℝ (Fin n)), Integrable (fun x => fderiv ℝ f x v * g x) → Integrable (fun x => f x * fderiv ℝ g x v) → Integrable (fun x => f x * g x) → (∀ x ∈ tsupport g, DifferentiableAt ℝ f x) → (∀ x ∈ tsupport f, DifferentiableAt ℝ g x) → (∫ x, f x * fderiv ℝ g x v) = -(∫ x, fderiv ℝ f x v * g x) := by
  intro n f g v hf'g hfg' hfg hf hg
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) (f := f) (g := g) (v := v) hf'g hfg' hfg hf hg
set_option Elab.async false in
theorem B004 : ∀ (n : ℕ) (g : EuclideanSpace ℝ (Fin n) → ℝ) (v : EuclideanSpace ℝ (Fin n)), ContDiff ℝ 1 g → HasCompactSupport g → Integrable (fun x => fderiv ℝ g x v) ∧ (∫ x, fderiv ℝ g x v) = 0 := by
  have h_H001 : ∀ (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ), Continuous f → HasCompactSupport f → Integrable f := @YuiBasis.B001
  have h_H002 : ∀ (n : ℕ) (f g : EuclideanSpace ℝ (Fin n) → ℝ) (v : EuclideanSpace ℝ (Fin n)), Integrable (fun x => fderiv ℝ f x v * g x) → Integrable (fun x => f x * fderiv ℝ g x v) → Integrable (fun x => f x * g x) → (∀ x ∈ tsupport g, DifferentiableAt ℝ f x) → (∀ x ∈ tsupport f, DifferentiableAt ℝ g x) → (∫ x, f x * fderiv ℝ g x v) = -(∫ x, fderiv ℝ f x v * g x) := @YuiBasis.B003
  intro n g v hg hgc
  rcases contDiff_one_iff_fderiv.mp hg with ⟨hgd, hgderiv⟩
  have hcont : Continuous (fun x => fderiv ℝ g x v) :=
    hgderiv.clm_apply continuous_const
  have hsupport : HasCompactSupport (fun x => fderiv ℝ g x v) :=
    hgc.fderiv_apply ℝ v
  have hint : Integrable (fun x => fderiv ℝ g x v) :=
    h_H001 n _ hcont hsupport
  have hgint : Integrable g := h_H001 n g hg.continuous hgc
  refine ⟨hint, ?_⟩
  have hzero : Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      fderiv ℝ (fun _ : EuclideanSpace ℝ (Fin n) => (1 : ℝ)) x v * g x) := by
    simpa using (integrable_zero : Integrable (fun _ : EuclideanSpace ℝ (Fin n) => (0 : ℝ)))
  have hparts := h_H002 n (fun _ => (1 : ℝ)) g v hzero
    (by simpa using hint) (by simpa using hgint)
    (by intro x hx; exact differentiableAt_const (1 : ℝ))
    (by intro x hx; exact hgd x)
  simpa using hparts
set_option Elab.async false in
theorem B005 : ∀ {Y : Type} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] (f : ℝ → Y) (f' : Y) (t : ℝ), HasDerivAt f f' t → HasDerivAt (fun r => ‖f r‖ ^ 2) (2 * inner ℝ (f t) f') t := by
  intro Y _ _ f f' t hf
  exact hf.norm_sq
set_option Elab.async false in
theorem B006 : ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] (f g : X → Y) (x v : X), DifferentiableAt ℝ f x → DifferentiableAt ℝ g x → fderiv ℝ (fun y => inner ℝ (f y) (g y)) x v = inner ℝ (f x) (fderiv ℝ g x v) + inner ℝ (fderiv ℝ f x v) (g x) := by
  intro X Y _ _ _ _ f g x v hf hg
  exact fderiv_inner_apply ℝ hf hg v
set_option Elab.async false in
theorem B007 : ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] (f : X → Y) (x : X), ContDiffAt ℝ 2 f x → ∀ v w : X, fderiv ℝ (fderiv ℝ f) x v w = fderiv ℝ (fderiv ℝ f) x w v := by
  intro X Y _ _ _ _ f x hf
  exact hf.isSymmSndFDerivAt (by simp)
set_option Elab.async false in
theorem B008 : ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] (f : X → Y) (s : Set X), IsOpen s → ContDiffOn ℝ ∞ f s → ContDiffOn ℝ ∞ (fderiv ℝ f) s := by
  intro X Y _ _ _ _ f s hs hf
  exact (contDiffOn_infty_iff_fderiv_of_isOpen hs).mp hf |>.2
set_option Elab.async false in
theorem B009 : ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] (f g : X → Y) (x : X), Filter.EventuallyEq (𝓝 x) f g → fderiv ℝ f x = fderiv ℝ g x := by
  intro X Y _ _ _ _ f g x h
  exact Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) h

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
    let omitted : Array String := #["h_E004"]
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
theorem P (n : ℕ) (m : ℕ) (u : WMZ n → WMX m) (q : WMX m) (h_H001 : 1 ≤ n ∧ 1 ≤ m ∧ ContDiffOn ℝ ∞ u (WMOmega n)) (h_H002 : ‖q‖ = 1) (h_H003 : ∀ (x : WMX n) (t : ℝ), 0 < t → ‖u (x, t)‖ = 1) (h_H004 : ∀ (x : WMX n) (t : ℝ), 0 < t → ∃ a : ℝ, WMA u (x, t) - (∑ j : Fin n, WMB u j (x, t)) = a • u (x, t)) (h_H005 : ∀ s t : ℝ, 0 < s → s < t → ∃ C : Set (WMX n), IsCompact C ∧ ∀ (x : WMX n) (r : ℝ), x ∉ C → r ∈ Icc s t → u (x, r) = q) : ∀ t : ℝ, 0 < t → Integrable (fun x : WMX n => WME u (x, t)) ∧ HasDerivAt (WMEnergy u) 0 t := by
  exact yui_basis_export%(n, m, u, q, h_H001, h_H002, h_H003, h_H004, h_H005, (@YuiBasis.B004))

end YuiClosed
