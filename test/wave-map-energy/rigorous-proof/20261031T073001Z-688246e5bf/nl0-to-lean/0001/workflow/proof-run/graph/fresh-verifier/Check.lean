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

namespace Translation
set_option autoImplicit false

theorem T002 (n : ℕ) (m : ℕ) (u : WM.Domain n → WM.Target m) (q : WM.Target m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ WM.smoothOrder u (WM.positive n)) (h_H006 : ∀ s t : ℝ, 0 < s → s < t → ∃ C : Set (WM.Space n), IsCompact C ∧ ∀ x : WM.Space n, ∀ r : ℝ, x ∉ C → r ∈ Set.Icc s t → u (x,r) = q) :
    WM.supportFacts u q := by
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
  refine ⟨?_, he, het, common⟩
  intro t ht
  obtain ⟨C, R, η, B, hc⟩ := common t ht
  rcases hc with ⟨hC, hR, hη, hB, hCo, hvol, hfin, hwin, hu, hiter, hsec, hbound⟩
  have hmem : t ∈ interior (WM.timeBand t) :=
    hwin ⟨by linarith, by linarith⟩
  exact (hsec t hmem (WM.density u) (Or.inl rfl)).2.2.2.2

theorem T001 (n : ℕ) (m : ℕ) (u : WM.Domain n → WM.Target m) (q : WM.Target m) (h_H002 : ContDiffOn ℝ WM.smoothOrder u (WM.positive n)) (h_H004 : ∀ x : WM.Space n, ∀ t : ℝ, 0 < t → ‖u (x,t)‖ = 1) (h_H005 : ∀ x : WM.Space n, ∀ t : ℝ, 0 < t → ∃ a : ℝ, WM.dtt u (x,t) - WM.lap u (x,t) = a • u (x,t)) :
    WM.tangency u := by
  have hopen : IsOpen (WM.positive n) := isOpen_lt continuous_const continuous_snd
  have hdu : ContDiffOn ℝ 1 (fderiv ℝ u) (WM.positive n) :=
    h_H002.fderiv_of_isOpen hopen (by
      change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)
  have hdiff : ∀ p ∈ WM.positive n, DifferentiableAt ℝ u p := by
    intro p hp
    exact (h_H002.contDiffAt (hopen.mem_nhds hp)).differentiableAt (by simp [WM.smoothOrder])
  have hdiffv : ∀ (p : WM.Domain n), p ∈ WM.positive n →
      ∀ v : WM.Domain n, DifferentiableAt ℝ (fun z => fderiv ℝ u z v) p := by
    intro p hp v
    exact ((hdu.clm_apply contDiffOn_const).contDiffAt (hopen.mem_nhds hp)).differentiableAt one_ne_zero
  have horth : ∀ p ∈ WM.positive n, ∀ v : WM.Domain n,
      inner ℝ (u p) (fderiv ℝ u p v) = 0 := by
    intro p hp v
    have heq : (fun z => inner ℝ (u z) (u z)) =ᶠ[𝓝 p] (fun _ => (1 : ℝ)) := by
      filter_upwards [hopen.mem_nhds hp] with z hz
      rw [real_inner_self_eq_norm_sq, h_H004 z.1 z.2 hz]
      norm_num
    have hzero : fderiv ℝ (fun z => inner ℝ (u z) (u z)) p v = 0 := by
      rw [heq.fderiv_eq, fderiv_const_apply]
      rfl
    rw [fderiv_inner_apply ℝ (hdiff p hp) (hdiff p hp) v] at hzero
    have hs := real_inner_comm (u p) (fderiv ℝ u p v)
    linarith only [hzero, hs]
  have hsecond : ∀ p ∈ WM.positive n, ∀ v : WM.Domain n,
      inner ℝ (u p) (fderiv ℝ (fun z => fderiv ℝ u z v) p v) =
        -(‖fderiv ℝ u p v‖ ^ 2) := by
    intro p hp v
    have heq : (fun z => inner ℝ (u z) (fderiv ℝ u z v)) =ᶠ[𝓝 p] (fun _ => (0 : ℝ)) := by
      filter_upwards [hopen.mem_nhds hp] with z hz
      exact horth z hz v
    have hzero : fderiv ℝ (fun z => inner ℝ (u z) (fderiv ℝ u z v)) p v = 0 := by
      rw [heq.fderiv_eq, fderiv_const_apply]
      rfl
    rw [fderiv_inner_apply ℝ (hdiff p hp) (hdiffv p hp v) v,
      real_inner_self_eq_norm_sq] at hzero
    linarith
  intro x t ht
  have hp : (x,t) ∈ WM.positive n := ht
  have htorth : inner ℝ (u (x,t)) (WM.dt u (x,t)) = 0 :=
    horth (x,t) hp (0,1)
  have htt : inner ℝ (u (x,t)) (WM.dtt u (x,t)) = -(‖WM.dt u (x,t)‖ ^ 2) :=
    hsecond (x,t) hp (0,1)
  have hxx : ∀ j : Fin n, inner ℝ (u (x,t)) (WM.dxx u j (x,t)) =
      -(‖WM.dx u j (x,t)‖ ^ 2) := by
    intro j
    exact hsecond (x,t) hp (Pi.single j 1,0)
  obtain ⟨a, ha⟩ := h_H005 x t ht
  have hnormal : inner ℝ (WM.dt u (x,t)) (WM.dtt u (x,t) - WM.lap u (x,t)) = 0 := by
    rw [ha, inner_smul_right, real_inner_comm (u (x,t)) (WM.dt u (x,t)), htorth, mul_zero]
  have hscalar : ∀ a : ℝ, WM.dtt u (x,t) - WM.lap u (x,t) = a • u (x,t) →
      a = WM.gradSq u (x,t) - ‖WM.dt u (x,t)‖ ^ 2 := by
    intro b hb
    have heq := congrArg (fun z => inner ℝ (u (x,t)) z) hb
    have hunit : inner ℝ (u (x,t)) (u (x,t)) = 1 := by
      rw [real_inner_self_eq_norm_sq, h_H004 x t ht]
      norm_num
    rw [inner_sub_right, inner_smul_right, hunit, mul_one, htt] at heq
    have hlap : inner ℝ (u (x,t)) (WM.lap u (x,t)) = -WM.gradSq u (x,t) := by
      simp only [WM.lap, inner_sum, hxx, WM.gradSq, Finset.sum_neg_distrib]
    rw [hlap] at heq
    linarith only [heq]
  refine ⟨htorth, hnormal, htt, hxx, hscalar, ?_⟩
  rw [ha, hscalar a ha]

theorem T003 (n : ℕ) (m : ℕ) (u : WM.Domain n → WM.Target m) (q : WM.Target m) (h_H002 : ContDiffOn ℝ WM.smoothOrder u (WM.positive n)) :
    (∀ x : WM.Space n, ∀ t : ℝ, 0 < t → HasDerivAt (fun r : ℝ => WM.density u (x,r)) (WM.densityT u (x,t)) t ∧ WM.densityT u (x,t) = 2 * WM.accelProduct u (x,t) + 2 * ∑ j : Fin n, WM.gradProduct u j (x,t)) ∧ (∀ x : WM.Space n, ∀ t : ℝ, 0 < t → ∀ j : Fin n, WM.dt (WM.dx u j) (x,t) = WM.dx (WM.dt u) j (x,t) ∧ WM.dx (WM.flux u j) j (x,t) = WM.gradProduct u j (x,t) + WM.lapProduct u j (x,t)) := by
  classical
  have hlocal : ∀ (x : WM.Space n) (t : ℝ), 0 < t →
      DifferentiableAt ℝ (WM.dt u) (x,t) ∧
      (∀ j, DifferentiableAt ℝ (WM.dx u j) (x,t)) ∧
      (∀ j, WM.dt (WM.dx u j) (x,t) = WM.dx (WM.dt u) j (x,t)) := by
    intro x t ht
    have hopen : IsOpen (WM.positive n) := isOpen_lt continuous_const continuous_snd
    have hc : ContDiffAt ℝ WM.smoothOrder u (x,t) :=
      h_H002.contDiffAt (hopen.mem_nhds ht)
    have hc2 : ContDiffAt ℝ 2 u (x,t) := hc.of_le (by
      change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)
    have hd : DifferentiableAt ℝ (fderiv ℝ u) (x,t) :=
      (hc2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have hdir : ∀ v w : WM.Domain n,
        DifferentiableAt ℝ (fun y => fderiv ℝ u y v) (x,t) ∧
        fderiv ℝ (fun y => fderiv ℝ u y v) (x,t) w =
          fderiv ℝ (fderiv ℝ u) (x,t) w v := by
      intro v w
      have hconst : HasFDerivAt (fun _ : WM.Domain n => v)
          (0 : WM.Domain n →L[ℝ] WM.Domain n) (x,t) := hasFDerivAt_const v (x,t)
      have h := hd.hasFDerivAt.clm_apply hconst
      exact ⟨h.differentiableAt, by rw [h.fderiv]; simp⟩
    refine ⟨(hdir (0,1) (0,1)).1, ?_, ?_⟩
    · intro j
      exact (hdir (Pi.single j 1,0) (0,1)).1
    · intro j
      change fderiv ℝ (fun y => fderiv ℝ u y (Pi.single j 1,0)) (x,t) (0,1) =
        fderiv ℝ (fun y => fderiv ℝ u y (0,1)) (x,t) (Pi.single j 1,0)
      rw [(hdir _ _).2, (hdir _ _).2]
      exact (hc2.isSymmSndFDerivAt (by simp)).eq _ _

  constructor
  · intro x t ht
    obtain ⟨hdt, hdx, hmix⟩ := hlocal x t ht
    have hsum := HasFDerivAt.fun_sum (u := Finset.univ)
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => (hdx j).hasFDerivAt.norm_sq)
    have hden := hdt.hasFDerivAt.norm_sq.add hsum
    change HasFDerivAt (WM.density u) _ (x,t) at hden
    have hval : WM.densityT u (x,t) =
        2 * WM.accelProduct u (x,t) +
        ∑ j : Fin n, 2 * inner ℝ (WM.dx u j (x,t)) (WM.dt (WM.dx u j) (x,t)) := by
      have heval := congrArg (fun L : WM.Domain n →L[ℝ] ℝ => L (0,1)) hden.fderiv
      simpa [WM.densityT, WM.dt, WM.accelProduct, WM.dtt] using heval
    have hformula : WM.densityT u (x,t) =
        2 * WM.accelProduct u (x,t) + 2 * ∑ j : Fin n, WM.gradProduct u j (x,t) := by
      rw [hval]
      simp_rw [hmix]
      simp only [WM.gradProduct, Finset.mul_sum]
    refine ⟨?_, hformula⟩
    have hline : HasDerivAt (fun r : ℝ => (x,r)) (0,1) t :=
      (hasDerivAt_const t x).prodMk (hasDerivAt_id t)
    exact hden.differentiableAt.hasFDerivAt.comp_hasDerivAt t hline
  · intro x t ht j
    obtain ⟨hdt, hdx, hmix⟩ := hlocal x t ht
    refine ⟨hmix j, ?_⟩
    have hp := hdt.hasFDerivAt.inner ℝ (hdx j).hasFDerivAt
    change HasFDerivAt (WM.flux u j) _ (x,t) at hp
    have heval := congrArg (fun L : WM.Domain n →L[ℝ] ℝ => L (Pi.single j 1,0)) hp.fderiv
    simpa [WM.dx, WM.gradProduct, WM.lapProduct, WM.dxx,
      ContinuousLinearMap.comp_apply, fderivInnerCLM_apply, real_inner_comm, add_comm] using heval

theorem T005 (n : ℕ) (m : ℕ) (u : WM.Domain n → WM.Target m) (q : WM.Target m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ WM.smoothOrder u (WM.positive n)) (h_T002 : WM.supportFacts u q) (h_T003 : (∀ x : WM.Space n, ∀ t : ℝ, 0 < t → HasDerivAt (fun r : ℝ => WM.density u (x,r)) (WM.densityT u (x,t)) t ∧ WM.densityT u (x,t) = 2 * WM.accelProduct u (x,t) + 2 * ∑ j : Fin n, WM.gradProduct u j (x,t)) ∧ (∀ x : WM.Space n, ∀ t : ℝ, 0 < t → ∀ j : Fin n, WM.dt (WM.dx u j) (x,t) = WM.dx (WM.dt u) j (x,t) ∧ WM.dx (WM.flux u j) j (x,t) = WM.gradProduct u j (x,t) + WM.lapProduct u j (x,t))) :
    WM.integrationByParts u := by
  classical
  have hcoord : ∀ (k : ℕ) (j : Fin (k+1)) (R : ℝ), 0 < R →
    ∀ (g d : (Fin (k+1) → ℝ) → ℝ),
    Continuous d → Integrable d →
    Function.support d ⊆ WM.box (k+1) R →
    (∀ y : Fin k → ℝ, g (j.insertNth R y) = 0 ∧ g (j.insertNth (-R) y) = 0) →
    (∀ (y : Fin k → ℝ) (r : ℝ),
      HasDerivAt (fun s => g (j.insertNth s y)) (d (j.insertNth r y)) r) →
    (∫ x, d x) = 0 := by
    intro k j R hR g d hc hi hs hend hder
    let e : (ℝ × (Fin k → ℝ)) ≃ᵐ (Fin (k+1) → ℝ) :=
      (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) j).symm
    have he : ∀ z, e z = j.insertNth z.1 z.2 := by intro z; rfl
    have hm : MeasurePreserving e :=
      (volume_preserving_piFinSuccAbove (fun _ : Fin (k+1) => ℝ) j).symm _
    have hb : e ⁻¹' WM.box (k+1) R = Icc (-R) R ×ˢ WM.box k R := by
      ext z
      simp only [mem_preimage, he, WM.box, Set.mem_pi, mem_univ, true_implies,
        mem_prod, mem_Icc]
      rw [j.forall_iff_succAbove]
      simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
    have hrest : IsCompact (WM.box k R) := isCompact_univ_pi (fun _ => isCompact_Icc)
    letI : IsFiniteMeasure (volume.restrict (WM.box k R)) :=
      isFiniteMeasure_restrict.mpr hrest.measure_ne_top
    have hp : Integrable (fun z : ℝ × (Fin k → ℝ) => d (e z))
        ((volume.restrict (Icc (-R) R)).prod (volume.restrict (WM.box k R))) := by
      rw [Measure.prod_restrict]
      have hh := (hm.integrableOn_comp_preimage e.measurableEmbedding).mpr
        (hi.integrableOn (s := WM.box (k+1) R))
      simpa only [hb, Measure.volume_eq_prod, Function.comp_def, IntegrableOn] using hh
    have hslice : ∀ y : Fin k → ℝ, (∫ r in Icc (-R) R, d (j.insertNth r y)) = 0 := by
      intro y
      have hin : Continuous (fun r : ℝ => (j.insertNth r y : Fin (k+1) → ℝ)) := by
        apply continuous_pi
        intro i
        rcases j.eq_self_or_eq_succAbove i with rfl | ⟨a, rfl⟩
        · simp only [Fin.insertNth_apply_same]
          exact continuous_id
        · simpa only [Fin.insertNth_apply_succAbove] using (continuous_const : Continuous (fun _ : ℝ => y a))
      have hint : IntervalIntegrable (fun r => d (j.insertNth r y)) volume (-R) R :=
        (hc.comp hin).intervalIntegrable _ _
      have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hder y r) hint
      rw [(hend y).1, (hend y).2, sub_self] at hf
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : -R ≤ R)]
      exact hf
    calc
      (∫ x, d x) = ∫ x in WM.box (k+1) R, d x := by
        symm
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro x hx
        by_contra hn
        exact hx (hs hn)
      _ = ∫ z in Icc (-R) R ×ˢ WM.box k R, d (e z) := by
        rw [← hb]
        exact (hm.setIntegral_preimage_emb e.measurableEmbedding d _).symm
      _ = ∫ y in WM.box k R, ∫ r in Icc (-R) R, d (e (r,y)) := by
        rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
        exact integral_prod_symm _ hp
      _ = 0 := by simp only [he, hslice, integral_zero]
  have hinsert : ∀ (k : ℕ) (j : Fin (k+1)) (y : Fin k → ℝ) (t r : ℝ),
      HasDerivAt (fun s : ℝ => ((j.insertNth s y : Fin (k+1) → ℝ), t))
        (Pi.single j 1, 0) r := by
    intro k j y t r
    apply HasDerivAt.prodMk _ (hasDerivAt_const r t)
    apply hasDerivAt_pi.mpr
    intro i
    rcases j.eq_self_or_eq_succAbove i with rfl | ⟨a, rfl⟩
    · simp only [Fin.insertNth_apply_same, Pi.single_eq_same]
      exact hasDerivAt_id' r
    · simpa [Pi.single_apply, Fin.succAbove_ne] using hasDerivAt_const r (y a)
  have hflux : ∀ (j : Fin n) (p : WM.Domain n), 0 < p.2 →
      DifferentiableAt ℝ (WM.flux u j) p := by
    intro j p hp
    have ho : IsOpen (WM.positive n) := isOpen_lt continuous_const continuous_snd
    have hf : ContDiffOn ℝ (1 : WithTop ℕ∞) (fderiv ℝ u) (WM.positive n) :=
      h_H002.fderiv_of_isOpen ho (by change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞); exact WithTop.coe_le_coe.mpr le_top)
    have ht : ContDiffOn ℝ (1 : WithTop ℕ∞) (WM.dt u) (WM.positive n) :=
      hf.clm_apply contDiffOn_const
    have hx : ContDiffOn ℝ (1 : WithTop ℕ∞) (WM.dx u j) (WM.positive n) :=
      hf.clm_apply contDiffOn_const
    have hg : ContDiffOn ℝ (1 : WithTop ℕ∞) (WM.flux u j) (WM.positive n) := ht.inner ℝ hx
    exact (hg.differentiableOn one_ne_zero p hp).differentiableAt (ho.mem_nhds hp)
  cases n with
  | zero => omega
  | succ k =>
    intro t ht j
    obtain ⟨C, R, η, B, hcs⟩ := h_T002.2.2.2 t ht
    rcases hcs with ⟨hcompact, hR, hη, hB, hC, hvol, hfinite, hband,
      hconst, hjet, hgood, hbound⟩
    have htint : t ∈ interior (WM.timeBand t) :=
      hband ⟨by linarith, by linarith⟩
    have ha : WM.sectionGood (WM.gradProduct u j) C (WM.box (k+1) R) t := by
      apply hgood t htint
      exact Or.inr (Or.inr (Or.inr ⟨j, Or.inl rfl⟩))
    have hb : WM.sectionGood (WM.lapProduct u j) C (WM.box (k+1) R) t := by
      apply hgood t htint
      exact Or.inr (Or.inr (Or.inr ⟨j, Or.inr (Or.inl rfl)⟩))
    have hg : WM.sectionGood (WM.flux u j) C (WM.box (k+1) R) t := by
      apply hgood t htint
      exact Or.inr (Or.inr (Or.inr ⟨j, Or.inr (Or.inr (Or.inl rfl))⟩))
    have hd : WM.sectionGood (WM.dx (WM.flux u j) j) C (WM.box (k+1) R) t := by
      apply hgood t htint
      exact Or.inr (Or.inr (Or.inr ⟨j, Or.inr (Or.inr (Or.inr rfl))⟩))
    have hCQ : C ⊆ WM.box (k+1) R := by
      intro x hx i hi
      have hh := hC hx i hi
      exact ⟨hh.1.le, hh.2.le⟩
    have hend : ∀ y : Fin k → ℝ,
        WM.flux u j (j.insertNth R y,t) = 0 ∧
        WM.flux u j (j.insertNth (-R) y,t) = 0 := by
      intro y
      constructor
      · by_contra hn
        have hh := hC (hg.2.1 hn) j (mem_univ j)
        simp only [Fin.insertNth_apply_same] at hh
        exact (lt_irrefl R) hh.2
      · by_contra hn
        have hh := hC (hg.2.1 hn) j (mem_univ j)
        simp only [Fin.insertNth_apply_same] at hh
        exact (lt_irrefl (-R)) hh.1
    have hder : ∀ (y : Fin k → ℝ) (r : ℝ),
        HasDerivAt (fun s => WM.flux u j (j.insertNth s y,t))
          (WM.dx (WM.flux u j) j (j.insertNth r y,t)) r := by
      intro y r
      exact (hflux j (j.insertNth r y,t) ht).hasFDerivAt.comp_hasDerivAt r
        (hinsert k j y t r)
    have hz : (∫ x : WM.Space (k+1), WM.dx (WM.flux u j) j (x,t)) = 0 :=
      hcoord k j R hR (fun x => WM.flux u j (x,t))
        (fun x => WM.dx (WM.flux u j) j (x,t))
        hd.1 hd.2.2.2.2 (hd.2.1.trans hCQ) hend hder
    have hid : (fun x : WM.Space (k+1) => WM.dx (WM.flux u j) j (x,t)) =
        (fun x => WM.gradProduct u j (x,t) + WM.lapProduct u j (x,t)) :=
      funext (fun x => (h_T003.2 x t ht j).2)
    rw [hid, integral_add ha.2.2.2.2 hb.2.2.2.2] at hz
    exact ⟨ha.2.2.2.2, hb.2.2.2.2, by linarith⟩

theorem T004 (n : ℕ) (m : ℕ) (u : WM.Domain n → WM.Target m) (q : WM.Target m) (h_T002 : WM.supportFacts u q) (h_T003 : (∀ x : WM.Space n, ∀ t : ℝ, 0 < t → HasDerivAt (fun r : ℝ => WM.density u (x,r)) (WM.densityT u (x,t)) t ∧ WM.densityT u (x,t) = 2 * WM.accelProduct u (x,t) + 2 * ∑ j : Fin n, WM.gradProduct u j (x,t)) ∧ (∀ x : WM.Space n, ∀ t : ℝ, 0 < t → ∀ j : Fin n, WM.dt (WM.dx u j) (x,t) = WM.dx (WM.dt u) j (x,t) ∧ WM.dx (WM.flux u j) j (x,t) = WM.gradProduct u j (x,t) + WM.lapProduct u j (x,t))) :
    ∀ t : ℝ, 0 < t → ∃ η : ℝ, 0 < η ∧ ∃ w : WM.Space n → ℝ, Integrable w ∧ ∀ h : ℝ, 0 < |h| → |h| < η → 0 < t + h ∧ ∀ x : WM.Space n, |(WM.density u (x,t+h) - WM.density u (x,t)) / h| ≤ w x := by
  intro t ht
  rcases h_T002.2.2.2 t ht with ⟨C, R, η, B, hc⟩
  rcases hc with ⟨hcompact, hR, hη, hB, hC, hvol, hfinite, hwindow,
    hconstant, hvanish, hsections, hbound⟩
  have hQ : MeasurableSet (WM.box n R) := by
    exact MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  have hCQ : C ⊆ WM.box n R := by
    intro x hx
    have hx' := hC hx
    change ∀ j ∈ (Set.univ : Set (Fin n)), x j ∈ Set.Icc (-R) R
    intro j hj
    have hj' : x j ∈ Set.Ioo (-R) R := hx' j hj
    exact ⟨hj'.1.le, hj'.2.le⟩
  have hpos : ∀ r ∈ Set.Icc (t - η) (t + η), 0 < r := by
    intro r hr
    have hr' := interior_subset (hwindow hr)
    change t / 2 ≤ r ∧ r ≤ 3 * t / 2 at hr'
    linarith [hr'.1]
  have hzero : ∀ x, x ∉ WM.box n R →
      ∀ r ∈ Set.Icc (t - η) (t + η), WM.density u (x, r) = 0 := by
    intro x hx r hr
    have hs := (hsections r (hwindow hr) (WM.density u) (Or.inl rfl)).2.1
    have hn : x ∉ C := fun hxc => hx (hCQ hxc)
    have hns : x ∉ Function.support (fun y => WM.density u (y, r)) :=
      fun hxs => hn (hs hxs)
    by_contra hz
    exact hns hz
  refine ⟨η, hη, (WM.box n R).indicator (fun _ => B), ?_, ?_⟩
  · exact (integrableOn_const (C := B) hfinite.ne).integrable_indicator hQ
  · intro h hh hhη
    have hhabs := (abs_lt.mp hhη)
    have htmem : t ∈ Set.Icc (t - η) (t + η) := by
      constructor <;> linarith
    have hthmem : t + h ∈ Set.Icc (t - η) (t + η) := by
      constructor <;> linarith [hhabs.1, hhabs.2]
    refine ⟨hpos (t + h) hthmem, ?_⟩
    intro x
    by_cases hx : x ∈ WM.box n R
    · rw [Set.indicator_of_mem hx]
      let a : ℝ := min t (t + h)
      let b : ℝ := max t (t + h)
      have hn : h ≠ 0 := by
        intro hz
        simpa [hz] using hh
      have hab : a < b := by
        dsimp [a, b]
        rcases lt_or_gt_of_ne hn with hneg | hpos
        · rw [min_eq_right (by linarith), max_eq_left (by linarith)]
          linarith
        · rw [min_eq_left (by linarith), max_eq_right (by linarith)]
          linarith
      have hsub : Set.Icc a b ⊆ Set.Icc (t - η) (t + η) := by
        intro r hr
        have ha : t - η ≤ a := by
          dsimp [a]
          exact le_min htmem.1 hthmem.1
        have hb : b ≤ t + η := by
          dsimp [b]
          exact max_le htmem.2 hthmem.2
        exact ⟨le_trans ha hr.1, le_trans hr.2 hb⟩
      have hd : ∀ r ∈ Set.Icc a b,
          HasDerivAt (fun r => WM.density u (x, r)) (WM.densityT u (x, r)) r := by
        intro r hr
        exact (h_T003.1 x r (hpos r (hsub hr))).1
      obtain ⟨c, hc, heq⟩ := exists_hasDerivAt_eq_slope
        (fun r => WM.density u (x, r)) (fun r => WM.densityT u (x, r)) hab
        (fun r hr => (hd r hr).continuousAt.continuousWithinAt)
        (fun r hr => hd r ⟨hr.1.le, hr.2.le⟩)
      have hcbound : |WM.densityT u (x, c)| ≤ B :=
        hbound x hx c (hsub ⟨hc.1.le, hc.2.le⟩)
      have hslope : (WM.density u (x, b) - WM.density u (x, a)) / (b - a) =
          (WM.density u (x, t + h) - WM.density u (x, t)) / h := by
        rcases lt_or_gt_of_ne hn with hneg | hpos
        · have ha : a = t + h := min_eq_right (by linarith)
          have hb : b = t := max_eq_left (by linarith)
          rw [ha, hb]
          have he : t - (t + h) = -h := by ring
          rw [he, div_neg, ← neg_div, neg_sub]
        · have ha : a = t := min_eq_left (by linarith)
          have hb : b = t + h := max_eq_right (by linarith)
          rw [ha, hb]
          congr 1
          ring
      rw [heq, hslope] at hcbound
      exact hcbound
    · rw [Set.indicator_of_notMem hx, hzero x hx (t + h) hthmem,
        hzero x hx t htmem]
      simp

theorem T006 (n : ℕ) (m : ℕ) (u : WM.Domain n → WM.Target m) (q : WM.Target m) (h_T002 : WM.supportFacts u q) (h_T003 : (∀ x : WM.Space n, ∀ t : ℝ, 0 < t → HasDerivAt (fun r : ℝ => WM.density u (x,r)) (WM.densityT u (x,t)) t ∧ WM.densityT u (x,t) = 2 * WM.accelProduct u (x,t) + 2 * ∑ j : Fin n, WM.gradProduct u j (x,t)) ∧ (∀ x : WM.Space n, ∀ t : ℝ, 0 < t → ∀ j : Fin n, WM.dt (WM.dx u j) (x,t) = WM.dx (WM.dt u) j (x,t) ∧ WM.dx (WM.flux u j) j (x,t) = WM.gradProduct u j (x,t) + WM.lapProduct u j (x,t))) (h_T004 : ∀ t : ℝ, 0 < t → ∃ η : ℝ, 0 < η ∧ ∃ w : WM.Space n → ℝ, Integrable w ∧ ∀ h : ℝ, 0 < |h| → |h| < η → 0 < t + h ∧ ∀ x : WM.Space n, |(WM.density u (x,t+h) - WM.density u (x,t)) / h| ≤ w x) :
    WM.energyDerivative u := by
  have hsection : ∀ t : ℝ, 0 < t → ∀ f ∈ WM.fields u,
      Continuous (fun x => f (x,t)) ∧ Integrable (fun x => f (x,t)) := by
    intro t ht f hf
    rcases h_T002.2.2.2 t ht with ⟨C, R, η, B, hC⟩
    rcases hC with ⟨hc, hR, hη, hB, hCQ, hvol, hfin, hband, hout, hder, hsec, hbound⟩
    have hmem : t ∈ interior (WM.timeBand t) := hband (by constructor <;> linarith)
    exact ⟨(hsec t hmem f hf).1, (hsec t hmem f hf).2.2.2.2⟩
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    rcases h_T004 t ht with ⟨η, hη, w, hw, hwindow⟩
    apply hasDerivAt_iff_tendsto_slope_zero.2
    apply Filter.tendsto_iff_seq_tendsto.2
    intro a ha
    have ha0 : Tendsto a atTop (𝓝 (0 : ℝ)) := ha.mono_right nhdsWithin_le_nhds
    have habs : ∀ᶠ k in atTop, |a k| < η :=
      ha0.abs.eventually (gt_mem_nhds (by simpa only [abs_zero] using hη))
    have hne : ∀ᶠ k in atTop, a k ≠ 0 := by
      simpa using ha.eventually self_mem_nhdsWithin
    rcases eventually_atTop.1 (hne.and habs) with ⟨N, hN⟩
    have hgood (k : ℕ) : 0 < |a (k + N)| ∧ |a (k + N)| < η :=
      ⟨abs_pos.mpr (hN (k+N) (Nat.le_add_left N k)).1,
        (hN (k+N) (Nat.le_add_left N k)).2⟩
    let b : ℕ → ℝ := fun k => a (k + N)
    have hb : Tendsto b atTop (𝓝[≠] (0 : ℝ)) := ha.comp (tendsto_add_atTop_nat N)
    have hpos (k : ℕ) : 0 < t + b k := (hwindow (b k) (hgood k).1 (hgood k).2).1
    let V : ℕ → WM.Space n → ℝ := fun k x =>
      (WM.density u (x,t+b k) - WM.density u (x,t)) / b k
    have hmeas (k : ℕ) : AEStronglyMeasurable (V k) (volume : Measure (WM.Space n)) := by
      have hc1 := (hsection (t + b k) (hpos k) (WM.density u) (by simp [WM.fields])).1
      have hc0 := (hsection t ht (WM.density u) (by simp [WM.fields])).1
      exact ((hc1.sub hc0).div_const (b k)).aestronglyMeasurable
    have hbound (k : ℕ) : ∀ᵐ x ∂(volume : Measure (WM.Space n)), ‖V k x‖ ≤ w x := by
      filter_upwards [] with x
      exact (hwindow (b k) (hgood k).1 (hgood k).2).2 x
    have hlim : ∀ᵐ x ∂(volume : Measure (WM.Space n)),
        Tendsto (fun k => V k x) atTop (𝓝 (WM.densityT u (x,t))) := by
      filter_upwards [] with x
      have hh := ((h_T003.1 x t ht).1.tendsto_slope_zero).comp hb
      simpa only [V, Function.comp_def, smul_eq_mul, div_eq_mul_inv, mul_comm] using hh
    have hDCT : Tendsto (fun k => ∫ x : WM.Space n, V k x) atTop
        (𝓝 (∫ x : WM.Space n, WM.densityT u (x,t))) :=
      MeasureTheory.tendsto_integral_of_dominated_convergence w hmeas hw hbound hlim
    have hquot (k : ℕ) : (∫ x : WM.Space n, V k x) =
        (WM.energy u (t + b k) - WM.energy u t) / b k := by
      dsimp only [V]
      rw [MeasureTheory.integral_div,
        MeasureTheory.integral_sub (h_T002.1 (t+b k) (hpos k)) (h_T002.1 t ht)]
      rfl
    have hshift : Tendsto (fun k =>
        (WM.energy u (t + a (k+N)) - WM.energy u t) / a (k+N)) atTop
        (𝓝 (∫ x : WM.Space n, WM.densityT u (x,t))) := by
      simpa only [hquot, b] using hDCT
    have hfull := (tendsto_add_atTop_iff_nat
      (f := fun k => (WM.energy u (t + a k) - WM.energy u t) / a k) N).1 hshift
    simpa only [Function.comp_def, smul_eq_mul, div_eq_mul_inv, mul_comm] using hfull
  · intro x t ht
    exact (h_T003.1 x t ht).2
  · intro t ht
    refine ⟨(hsection t ht (WM.densityT u) (by simp [WM.fields])).2,
      (hsection t ht (WM.accelProduct u) (by simp [WM.fields])).2, ?_⟩
    intro j
    exact (hsection t ht (WM.gradProduct u j)
      (Or.inr (Or.inr (Or.inr ⟨j, Or.inl rfl⟩)))).2

theorem T007 (n : ℕ) (m : ℕ) (u : WM.Domain n → WM.Target m) (q : WM.Target m) (h_H002 : ContDiffOn ℝ WM.smoothOrder u (WM.positive n)) (h_T001 : WM.tangency u) (h_T002 : WM.supportFacts u q) (h_T005 : WM.integrationByParts u) (h_T006 : WM.energyDerivative u) :
    ∀ t : ℝ, 0 < t → HasDerivAt (WM.energy u) 0 t := by
  intro t ht
  have hA : Integrable (fun x : WM.Space n => WM.accelProduct u (x, t)) :=
    (h_T006.2.2 t ht).2.1
  have hG (j : Fin n) :
      Integrable (fun x : WM.Space n => WM.gradProduct u j (x, t)) :=
    (h_T006.2.2 t ht).2.2 j
  have hL (j : Fin n) :
      Integrable (fun x : WM.Space n => WM.lapProduct u j (x, t)) :=
    (h_T005 t ht j).2.1
  have hGS : Integrable (fun x : WM.Space n => ∑ j, WM.gradProduct u j (x, t)) :=
    integrable_finsetSum Finset.univ (fun j _ => hG j)
  have hLS : Integrable (fun x : WM.Space n => ∑ j, WM.lapProduct u j (x, t)) :=
    integrable_finsetSum Finset.univ (fun j _ => hL j)
  have hpoint (x : WM.Space n) :
      WM.accelProduct u (x, t) - ∑ j, WM.lapProduct u j (x, t) = 0 := by
    have hz := (h_T001 x t ht).2.1
    simpa only [inner_sub_right, WM.lap, inner_sum, WM.accelProduct,
      WM.lapProduct] using hz
  have hzero :
      (∫ x : WM.Space n, WM.accelProduct u (x, t)) -
        ∑ j, (∫ x : WM.Space n, WM.lapProduct u j (x, t)) = 0 := by
    rw [← integral_finsetSum Finset.univ (fun j _ => hL j),
      ← integral_sub hA hLS]
    simp only [hpoint, integral_zero]
  have hparts :
      (∑ j, (∫ x : WM.Space n, WM.gradProduct u j (x, t))) =
        -(∑ j, (∫ x : WM.Space n, WM.lapProduct u j (x, t))) := by
    calc
      _ = ∑ j, -(∫ x : WM.Space n, WM.lapProduct u j (x, t)) :=
        Finset.sum_congr rfl (fun j _ => (h_T005 t ht j).2.2)
      _ = _ := Finset.sum_neg_distrib (fun j : Fin n => ∫ x : WM.Space n, WM.lapProduct u j (x, t))
  have hval : (∫ x : WM.Space n, WM.densityT u (x, t)) = 0 := by
    calc
      _ = ∫ x : WM.Space n,
          2 * WM.accelProduct u (x, t) +
            2 * ∑ j, WM.gradProduct u j (x, t) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => h_T006.2.1 x t ht)
      _ = 2 * (∫ x : WM.Space n, WM.accelProduct u (x, t)) +
          2 * ∑ j, (∫ x : WM.Space n, WM.gradProduct u j (x, t)) := by
        rw [integral_add (hA.const_mul 2) (hGS.const_mul 2),
          integral_const_mul, integral_const_mul,
          integral_finsetSum Finset.univ (fun j _ => hG j)]
      _ = 0 := by rw [hparts]; linarith [hzero]
  simpa only [hval] using h_T006.1 t ht

theorem T008 (n : ℕ) (m : ℕ) (u : WM.Domain n → WM.Target m) (q : WM.Target m) (h_T002 : WM.supportFacts u q) (h_T007 : ∀ t : ℝ, 0 < t → HasDerivAt (WM.energy u) 0 t) :
    WM.conservation u := by
  refine ⟨h_T002.1, h_T007, ?_⟩
  let f : ℝ → ℝ := fun r => if 0 < r then WM.energy u r else 0
  have hf : ∀ r : ℝ, 0 < r → HasDerivAt f 0 r := by
    intro r hr
    apply (h_T007 r hr).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioi.mem_nhds hr] with z hz
    exact if_pos hz
  have hordered : ∀ s t : ℝ, 0 < s → s < t → WM.energy u s = WM.energy u t := by
    intro s t hs hst
    have ht : 0 < t := lt_trans hs hst
    have hcont : ContinuousOn f (Set.Icc s t) := by
      intro r hr
      exact (hf r (lt_of_lt_of_le hs hr.1)).continuousAt.continuousWithinAt
    have hderiv : ∀ r ∈ Set.Ioo s t, HasDerivAt f ((fun _ : ℝ => (0 : ℝ)) r) r := by
      intro r hr
      exact hf r (lt_trans hs hr.1)
    obtain ⟨c, hc_mem, hc⟩ := exists_hasDerivAt_eq_slope f (fun _ : ℝ => (0 : ℝ)) hst hcont hderiv
    have hz : 0 * (t - s) = f t - f s :=
      (eq_div_iff (ne_of_gt (sub_pos.mpr hst))).mp hc
    have heq : f s = f t := by linarith
    simpa only [f, if_pos hs, if_pos ht] using heq
  intro s t hs ht
  rcases lt_trichotomy s t with hst | hst | hts
  · exact hordered s t hs hst
  · exact congrArg (WM.energy u) hst
  · exact (hordered t s ht hts).symm

set_option Elab.async false in
theorem P (n : ℕ) (m : ℕ) (u : WM.Domain n → WM.Target m) (q : WM.Target m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ WM.smoothOrder u (WM.positive n)) (h_H003 : ‖q‖ = 1) (h_H004 : ∀ x : WM.Space n, ∀ t : ℝ, 0 < t → ‖u (x,t)‖ = 1) (h_H005 : ∀ x : WM.Space n, ∀ t : ℝ, 0 < t → ∃ a : ℝ, WM.dtt u (x,t) - WM.lap u (x,t) = a • u (x,t)) (h_H006 : ∀ s t : ℝ, 0 < s → s < t → ∃ C : Set (WM.Space n), IsCompact C ∧ ∀ x : WM.Space n, ∀ r : ℝ, x ∉ C → r ∈ Set.Icc s t → u (x,r) = q) :
    WM.conservation u := by
  have h_T002 : WM.supportFacts u q := @T002 n m u q h_H001 h_H002 h_H006
  have h_T001 : WM.tangency u := @T001 n m u q h_H002 h_H004 h_H005
  have h_T003 : (∀ x : WM.Space n, ∀ t : ℝ, 0 < t → HasDerivAt (fun r : ℝ => WM.density u (x,r)) (WM.densityT u (x,t)) t ∧ WM.densityT u (x,t) = 2 * WM.accelProduct u (x,t) + 2 * ∑ j : Fin n, WM.gradProduct u j (x,t)) ∧ (∀ x : WM.Space n, ∀ t : ℝ, 0 < t → ∀ j : Fin n, WM.dt (WM.dx u j) (x,t) = WM.dx (WM.dt u) j (x,t) ∧ WM.dx (WM.flux u j) j (x,t) = WM.gradProduct u j (x,t) + WM.lapProduct u j (x,t)) := @T003 n m u q h_H002
  have h_T005 : WM.integrationByParts u := @T005 n m u q h_H001 h_H002 h_T002 h_T003
  have h_T004 : ∀ t : ℝ, 0 < t → ∃ η : ℝ, 0 < η ∧ ∃ w : WM.Space n → ℝ, Integrable w ∧ ∀ h : ℝ, 0 < |h| → |h| < η → 0 < t + h ∧ ∀ x : WM.Space n, |(WM.density u (x,t+h) - WM.density u (x,t)) / h| ≤ w x := @T004 n m u q h_T002 h_T003
  have h_T006 : WM.energyDerivative u := @T006 n m u q h_T002 h_T003 h_T004
  have h_T007 : ∀ t : ℝ, 0 < t → HasDerivAt (WM.energy u) 0 t := @T007 n m u q h_H002 h_T001 h_T002 h_T005 h_T006
  have h_T008 : WM.conservation u := @T008 n m u q h_T002 h_T007
  exact h_T008

#check @P
#print axioms P

end Translation
