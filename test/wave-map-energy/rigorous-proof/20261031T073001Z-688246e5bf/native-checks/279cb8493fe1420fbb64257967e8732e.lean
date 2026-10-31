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
      exact (hflux j (j.insertNth r y,t) ht).hasFDerivAt.comp_hasDerivAt
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

#check @T005
#print axioms T005

end Translation
