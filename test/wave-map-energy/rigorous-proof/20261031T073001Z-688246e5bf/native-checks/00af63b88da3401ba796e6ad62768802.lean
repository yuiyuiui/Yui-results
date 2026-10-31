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

#check @T001
#print axioms T001

end Translation
