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

#check @T004
#print axioms T004

end Translation
