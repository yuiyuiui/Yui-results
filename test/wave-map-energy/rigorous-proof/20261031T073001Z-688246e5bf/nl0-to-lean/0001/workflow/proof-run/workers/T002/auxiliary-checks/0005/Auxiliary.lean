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
theorem checked (n : ℕ) (m : ℕ) (u : WM.Domain n → WM.Target m) (q : WM.Target m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ WM.smoothOrder u (WM.positive n)) (h_H006 : ∀ s t : ℝ, 0 < s → s < t → ∃ C : Set (WM.Space n), IsCompact C ∧ ∀ x : WM.Space n, ∀ r : ℝ, x ∉ C → r ∈ Set.Icc s t → u (x,r) = q) : yui_aux_type% "∀ t : ℝ, 0 < t → ∃ C : Set (WM.Space n), ∃ R η B : ℝ, WM.commonSupport u q t C R η B" := by
  classical
  have hopen : IsOpen (WM.positive n) := isOpen_lt continuous_const continuous_snd
  have hdir : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
      {f : WM.Domain n → F}, ContDiffOn ℝ WM.smoothOrder f (WM.positive n) →
      ∀ v : WM.Domain n, ContDiffOn ℝ WM.smoothOrder
        (fun p => fderiv ℝ f p v) (WM.positive n) := by
    intro F _ _ f hf v
    exact (hf.fderiv_of_isOpen hopen (by simp [WM.smoothOrder])).clm_apply contDiffOn_const
  have hdt := hdir h_H002 (0, 1)
  have hdx : ∀ j, ContDiffOn ℝ WM.smoothOrder (WM.dx u j) (WM.positive n) :=
    fun j => hdir h_H002 (Pi.single j 1, 0)
  have hdtt : ContDiffOn ℝ WM.smoothOrder (WM.dtt u) (WM.positive n) :=
    hdir hdt (0, 1)
  have hdxx : ∀ j, ContDiffOn ℝ WM.smoothOrder (WM.dxx u j) (WM.positive n) :=
    fun j => hdir (hdx j) (Pi.single j 1, 0)
  have hdxdt : ∀ j, ContDiffOn ℝ WM.smoothOrder (WM.dx (WM.dt u) j) (WM.positive n) :=
    fun j => hdir hdt (Pi.single j 1, 0)
  have he : ContDiffOn ℝ WM.smoothOrder (WM.density u) (WM.positive n) := by
    exact (hdt.norm_sq ℝ).add (ContDiffOn.sum fun j _ => ((hdx j).norm_sq ℝ))
  have het : ContDiffOn ℝ WM.smoothOrder (WM.densityT u) (WM.positive n) :=
    hdir he (0, 1)
  have hfSmooth : ∀ f ∈ WM.fields u, ContDiffOn ℝ WM.smoothOrder f (WM.positive n) := by
    intro f hf
    rcases hf with rfl | rfl | rfl | ⟨j, rfl | rfl | rfl | rfl⟩
    · exact he
    · exact het
    · exact hdt.inner ℝ hdtt
    · exact (hdx j).inner ℝ (hdxdt j)
    · exact hdt.inner ℝ (hdxx j)
    · exact hdt.inner ℝ (hdx j)
    · exact hdir (hdt.inner ℝ (hdx j)) (Pi.single j 1, 0)
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
  have common : ∀ t : ℝ, 0 < t →
      ∃ C : Set (WM.Space n), ∃ R η B : ℝ, WM.commonSupport u q t C R η B := by
    intro t ht
    obtain ⟨C, hC, hu⟩ := h_H006 (t / 2) (3 * t / 2) (by linarith) (by linarith)
    obtain ⟨R, hR, hCR⟩ := hC.isBounded.exists_pos_norm_lt
    have hCo : C ⊆ WM.openBox n R := by
      intro x hx j hj
      have hj' : |x j| < R := (norm_le_pi_norm x j).trans_lt (hCR x hx)
      exact abs_lt.mp hj'
    have hCQ : C ⊆ WM.box n R := by
      intro x hx j hj
      exact ⟨(hCo hx j hj).1.le, (hCo hx j hj).2.le⟩
    have hQ : IsCompact (WM.box n R) := isCompact_univ_pi fun _ => isCompact_Icc
    have hvol : volume (WM.box n R) = ENNReal.ofReal ((2 * R) ^ n) := by
      rw [WM.box, pi_univ_Icc, Real.volume_Icc_pi]
      simp only [sub_neg_eq_add, ← two_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact (ENNReal.ofReal_pow (by positivity) n).symm
    have hfin : volume (WM.box n R) < ⊤ := by
      rw [hvol]
      exact ENNReal.ofReal_lt_top
    have hJpos : ∀ r ∈ interior (WM.timeBand t), 0 < r := by
      intro r hr
      have hr' := interior_subset hr
      change r ∈ Icc (t / 2) (3 * t / 2) at hr'
      linarith [hr'.1]
    have hwindow : Icc (t - t / 4) (t + t / 4) ⊆ interior (WM.timeBand t) := by
      rw [WM.timeBand, interior_Icc]
      intro r hr
      exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
    have huEv : ∀ x r, x ∉ C → r ∈ interior (WM.timeBand t) →
        u =ᶠ[𝓝 (x, r)] (fun _ => q) := by
      intro x r hx hr
      have hO : IsOpen (Cᶜ ×ˢ interior (WM.timeBand t)) :=
        hC.isClosed.isOpen_compl.prod isOpen_interior
      filter_upwards [hO.mem_nhds ⟨hx, hr⟩] with p hp
      exact hu p.1 p.2 hp.1 (interior_subset hp.2)
    have hiter : ∀ x r, x ∉ C → r ∈ interior (WM.timeBand t) →
        ∀ k : ℕ, 1 ≤ k → iteratedFDeriv ℝ k u (x, r) = 0 := by
      intro x r hx hr k hk
      have heq := ((huEv x r hx hr).iteratedFDeriv ℝ k).self_of_nhds
      rw [heq, iteratedFDeriv_const_of_ne (by omega)]
      rfl
    have hsection : ∀ r ∈ interior (WM.timeBand t), ∀ f ∈ WM.fields u,
        WM.sectionGood f C (WM.box n R) r := by
      intro r hr f hf
      have hcont : Continuous (fun x => f (x, r)) :=
        (hfSmooth f hf).continuousOn.comp_continuous
          (continuous_id.prodMk continuous_const) (fun _ => hJpos r hr)
      have hz : ∀ x, x ∉ C → f (x, r) = 0 := by
        intro x hx
        exact (evfields (huEv x r hx hr) f hf).self_of_nhds
      have hsupp : Function.support (fun x => f (x, r)) ⊆ C := by
        intro x hx
        by_contra h
        exact hx (hz x h)
      obtain ⟨b, hb⟩ := hQ.exists_bound_of_continuousOn hcont.continuousOn
      have hbound : ∀ x ∈ WM.box n R, |f (x, r)| ≤ b := by
        simpa only [Real.norm_eq_abs] using hb
      have hind : Integrable ((WM.box n R).indicator (fun _ => b)) :=
        (integrableOn_const hfin.ne).integrable_indicator hQ.measurableSet
      have hint : Integrable (fun x => f (x, r)) := by
        refine hind.mono' hcont.aestronglyMeasurable (ae_of_all _ fun x => ?_)
        by_cases hx : x ∈ WM.box n R
        · simpa only [Set.indicator_of_mem hx, Real.norm_eq_abs] using hbound x hx
        · have hxc : x ∉ C := fun hc => hx (hCQ hc)
          simp [Set.indicator_of_notMem hx, hz x hxc]
      exact ⟨hcont, hsupp, ⟨b, hbound⟩, hcont.measurable, hint⟩
    have hK : IsCompact (WM.box n R ×ˢ Icc (t - t / 4) (t + t / 4)) :=
      hQ.prod isCompact_Icc
    have hKpos : WM.box n R ×ˢ Icc (t - t / 4) (t + t / 4) ⊆ WM.positive n := by
      intro p hp
      exact hJpos p.2 (hwindow hp.2)
    obtain ⟨b, hb⟩ := hK.exists_bound_of_continuousOn (het.continuousOn.mono hKpos)
    refine ⟨C, R, t / 4, max b 0, hC, hR, by positivity, le_max_right _ _,
      hCo, hvol, hfin, hwindow, hu, hiter, hsection, ?_⟩
    intro x hx r hr
    exact (hb (x, r) ⟨hx, hr⟩).trans (le_max_left _ _)
  exact common
#check @checked
#print axioms checked
end YuiAuxiliary
