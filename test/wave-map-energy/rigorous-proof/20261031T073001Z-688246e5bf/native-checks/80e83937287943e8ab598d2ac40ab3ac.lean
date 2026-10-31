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
    exact hden.comp_hasDerivAt t hline
  · intro x t ht j
    obtain ⟨hdt, hdx, hmix⟩ := hlocal x t ht
    refine ⟨hmix j, ?_⟩
    have hp := hdt.hasFDerivAt.inner ℝ (hdx j).hasFDerivAt
    have heval := congrArg (fun L : WM.Domain n →L[ℝ] ℝ => L (Pi.single j 1,0)) hp.fderiv
    simpa [WM.flux, WM.dx, WM.gradProduct, WM.lapProduct, WM.dxx,
      ContinuousLinearMap.comp_apply, fderivInnerCLM_apply, real_inner_comm, add_comm] using heval

#check @T003
#print axioms T003

end Translation
