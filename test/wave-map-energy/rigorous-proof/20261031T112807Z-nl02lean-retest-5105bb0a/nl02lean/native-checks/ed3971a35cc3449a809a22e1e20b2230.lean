import Mathlib
open MeasureTheory Set Filter
open scoped BigOperators ContDiff
noncomputable section
namespace WaveMap
abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)
def positive (n : ℕ) : Set (Space n × ℝ) := {p | 0 < p.2}
def box (n : ℕ) (R : ℝ) : Set (Space n) := {x | ∀ j, x j ∈ Icc (-R) R}
def openBox (n : ℕ) (R : ℝ) : Set (Space n) := {x | ∀ j, x j ∈ Ioo (-R) R}
def timeInterval (t : ℝ) : Set ℝ := Icc (t / 2) (3 * t / 2)
def timeInterior (t : ℝ) : Set ℝ := Ioo (t / 2) (3 * t / 2)
def spatial {n : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Space n → F) (j : Fin n) (x : Space n) : F :=
  fderiv ℝ f x (PiLp.single 2 j 1)
def ut {n m : ℕ} (u : Space n × ℝ → Space m) (x : Space n) (t : ℝ) : Space m :=
  deriv (fun r => u (x, r)) t
def utt {n m : ℕ} (u : Space n × ℝ → Space m) (x : Space n) (t : ℝ) : Space m :=
  deriv (ut u x) t
def ux {n m : ℕ} (u : Space n × ℝ → Space m) (j : Fin n) (x : Space n) (t : ℝ) : Space m :=
  spatial (fun y => u (y, t)) j x
def uxx {n m : ℕ} (u : Space n × ℝ → Space m) (j : Fin n) (x : Space n) (t : ℝ) : Space m :=
  spatial (fun y => ux u j y t) j x
def utx {n m : ℕ} (u : Space n × ℝ → Space m) (j : Fin n) (x : Space n) (t : ℝ) : Space m :=
  spatial (fun y => ut u y t) j x
def laplace {n m : ℕ} (u : Space n × ℝ → Space m) (x : Space n) (t : ℝ) : Space m :=
  ∑ j, uxx u j x t
def density {n m : ℕ} (u : Space n × ℝ → Space m) (x : Space n) (t : ℝ) : ℝ :=
  ‖ut u x t‖ ^ 2 + ∑ j, ‖ux u j x t‖ ^ 2
def densityTime {n m : ℕ} (u : Space n × ℝ → Space m) (x : Space n) (t : ℝ) : ℝ :=
  deriv (density u x) t
def energy {n m : ℕ} (u : Space n × ℝ → Space m) (t : ℝ) : ℝ :=
  ∫ x, density u x t
def kineticProduct {n m : ℕ} (u : Space n × ℝ → Space m) (t : ℝ) (x : Space n) : ℝ :=
  inner ℝ (ut u x t) (utt u x t)
def gradientProduct {n m : ℕ} (u : Space n × ℝ → Space m) (j : Fin n) (t : ℝ) (x : Space n) : ℝ :=
  inner ℝ (ux u j x t) (utx u j x t)
def laplaceProduct {n m : ℕ} (u : Space n × ℝ → Space m) (j : Fin n) (t : ℝ) (x : Space n) : ℝ :=
  inner ℝ (ut u x t) (uxx u j x t)
def flux {n m : ℕ} (u : Space n × ℝ → Space m) (j : Fin n) (t : ℝ) (x : Space n) : ℝ :=
  inner ℝ (ut u x t) (ux u j x t)
def terms {n m : ℕ} (u : Space n × ℝ → Space m) (t : ℝ) (j : Fin n) : List (Space n → ℝ) :=
  [fun x => density u x t, fun x => densityTime u x t, kineticProduct u t,
   gradientProduct u j t, laplaceProduct u j t, flux u j t, spatial (flux u j t) j]
def quotient {n m : ℕ} (u : Space n × ℝ → Space m) (t h : ℝ) (x : Space n) : ℝ :=
  (density u x (t + h) - density u x t) / h
def bound (n : ℕ) (R B : ℝ) : Space n → ℝ :=
  (box n R).indicator (fun _ => B)
end WaveMap

namespace Translation
set_option autoImplicit false

theorem T006 (n : ℕ) (m : ℕ) (u : WaveMap.Space n × ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H002 : ContDiffOn ℝ (∞ : ℕ∞ω) u (WaveMap.positive n)) (h_T003 : (∀ t : ℝ, 0 < t → Integrable (fun x => WaveMap.density u x t)) ∧
  ContDiffOn ℝ (∞ : ℕ∞ω) (fun p => WaveMap.density u p.1 p.2) (WaveMap.positive n) ∧
  ContDiffOn ℝ (∞ : ℕ∞ω) (fun p => WaveMap.densityTime u p.1 p.2) (WaveMap.positive n) ∧
  ∀ t0 : ℝ, 0 < t0 → ∃ (C : Set (WaveMap.Space n)) (R η B : ℝ),
    IsCompact C ∧ 0 < R ∧ 0 < η ∧ 0 ≤ B ∧
    C ⊆ WaveMap.openBox n R ∧ IsCompact (WaveMap.box n R) ∧
    volume (WaveMap.box n R) = ENNReal.ofReal ((2 * R) ^ n) ∧
    volume (WaveMap.box n R) ≠ ⊤ ∧
    Icc (t0 - η) (t0 + η) ⊆ WaveMap.timeInterior t0 ∧
    (∀ x : WaveMap.Space n, x ∉ C → ∀ r ∈ WaveMap.timeInterval t0, u (x,r) = q) ∧
    (∀ (k : ℕ) (x : WaveMap.Space n) (r : ℝ), 0 < k → x ∉ C →
      r ∈ WaveMap.timeInterior t0 → iteratedFDeriv ℝ k u (x,r) = 0) ∧
    (∀ r ∈ WaveMap.timeInterior t0, ∀ (j : Fin n) (f : WaveMap.Space n → ℝ),
      f ∈ WaveMap.terms u r j →
      Continuous f ∧ Function.support f ⊆ C ∧
      (∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ WaveMap.box n R, |f x| ≤ K) ∧
      Measurable f ∧ Integrable f) ∧
    (∀ x ∈ WaveMap.box n R, ∀ r ∈ Icc (t0 - η) (t0 + η), |WaveMap.densityTime u x r| ≤ B)) (h_T004 : ∀ (x : WaveMap.Space n) (t : ℝ), 0 < t →
  HasDerivAt (WaveMap.density u x) (WaveMap.densityTime u x t) t ∧
  WaveMap.densityTime u x t = 2 * WaveMap.kineticProduct u t x +
    2 * ∑ j, WaveMap.gradientProduct u j t x) (h_T005 : ∀ t0 : ℝ, 0 < t0 → ∃ R η B : ℝ,
  0 < R ∧ 0 < η ∧ 0 ≤ B ∧ Icc (t0 - η) (t0 + η) ⊆ Ioi (0 : ℝ) ∧
  Integrable (WaveMap.bound n R B) ∧
  ∀ h : ℝ, 0 < |h| → |h| < η → ∀ x : WaveMap.Space n,
    |WaveMap.quotient u t0 h x| ≤ WaveMap.bound n R B x) :
    ∀ t : ℝ, 0 < t →
  HasDerivAt (WaveMap.energy u) (∫ x, WaveMap.densityTime u x t) t ∧
  (∀ x : WaveMap.Space n, WaveMap.densityTime u x t =
    2 * WaveMap.kineticProduct u t x + 2 * ∑ j, WaveMap.gradientProduct u j t x) ∧
  Integrable (fun x => WaveMap.densityTime u x t) ∧
  Integrable (WaveMap.kineticProduct u t) ∧
  (∀ j : Fin n, Integrable (WaveMap.gradientProduct u j t)) := by
  intro t ht
  have hcontD : Continuous (fun x : WaveMap.Space n => WaveMap.densityTime u x t) := by
    have hc : ContinuousOn (fun p : WaveMap.Space n × ℝ => WaveMap.densityTime u p.1 p.2) (WaveMap.positive n) := h_T003.2.2.1.continuousOn
    have hp : Continuous (fun x : WaveMap.Space n => (x,t)) := continuous_id.prodMk continuous_const
    exact ContinuousOn.comp_continuous (g := fun p : WaveMap.Space n × ℝ => WaveMap.densityTime u p.1 p.2) (f := fun x : WaveMap.Space n => (x,t)) hc hp (fun x => ht)
  have hpoint : ∀ x : WaveMap.Space n, Tendsto (fun h : ℝ => WaveMap.quotient u t h x)
      (nhdsWithin 0 ({0}ᶜ)) (nhds (WaveMap.densityTime u x t)) := by
    intro x
    simpa only [WaveMap.quotient, smul_eq_mul, div_eq_mul_inv, mul_comm] using
      (h_T004 x t ht).1.tendsto_slope_zero
  obtain ⟨R, η, B, hR, hη, hB, hpos, hboundint, hbound⟩ := h_T005 t ht
  have hwindow : ∀ᶠ h : ℝ in nhdsWithin 0 ({0}ᶜ), 0 < |h| ∧ |h| < η := by
    have ha : ∀ᶠ h : ℝ in nhds (0 : ℝ), |h| < η :=
      (continuous_abs.tendsto 0).eventually (gt_mem_nhds (by simpa using hη))
    filter_upwards [ha.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with h hh hn
    exact ⟨abs_pos.mpr hn, hh⟩
  have hDint : Integrable (fun x => WaveMap.densityTime u x t) := by
    apply hboundint.mono' hcontD.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    apply le_of_tendsto (hpoint x).norm
    filter_upwards [hwindow] with h hh
    simpa only [Real.norm_eq_abs] using hbound h hh.1 hh.2 x
  have htime : ∀ h : ℝ, |h| < η → 0 < t + h := by
    intro h hh
    apply hpos
    have hab := abs_lt.mp hh
    constructor <;> linarith
  have hquotint : ∀ h : ℝ, |h| < η → Integrable (WaveMap.quotient u t h) := by
    intro h hh
    exact ((h_T003.1 (t+h) (htime h hh)).sub (h_T003.1 t ht)).div_const h
  have hintegral : ∀ h : ℝ, |h| < η →
      (∫ x, WaveMap.quotient u t h x) = (WaveMap.energy u (t+h) - WaveMap.energy u t) / h := by
    intro h hh
    unfold WaveMap.quotient WaveMap.energy
    rw [integral_div, integral_sub (h_T003.1 (t+h) (htime h hh)) (h_T003.1 t ht)]
  have hseq : ∀ s : ℕ → ℝ, (∀ k, 0 < |s k| ∧ |s k| < η) →
      Tendsto s atTop (nhdsWithin 0 ({0}ᶜ)) →
      Tendsto (fun k => (WaveMap.energy u (t+s k) - WaveMap.energy u t) / s k)
        atTop (nhds (∫ x, WaveMap.densityTime u x t)) := by
    intro s hs hslim
    have hdct : Tendsto (fun k => ∫ x, WaveMap.quotient u t (s k) x)
        atTop (nhds (∫ x, WaveMap.densityTime u x t)) := by
      apply tendsto_integral_of_dominated_convergence (WaveMap.bound n R B)
      · intro k
        exact (hquotint (s k) (hs k).2).aestronglyMeasurable
      · exact hboundint
      · intro k
        exact Filter.Eventually.of_forall (fun x => by
          simpa only [Real.norm_eq_abs] using hbound (s k) (hs k).1 (hs k).2 x)
      · exact Filter.Eventually.of_forall (fun x => (hpoint x).comp hslim)
    simpa only [hintegral _ (hs _).2] using hdct
  have hlim : Tendsto (fun h : ℝ => (WaveMap.energy u (t+h) - WaveMap.energy u t) / h)
      (nhdsWithin 0 ({0}ᶜ)) (nhds (∫ x, WaveMap.densityTime u x t)) := by
    apply Filter.tendsto_of_seq_tendsto
    intro s hs
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hs.eventually hwindow)
    have hh := hseq (fun k => s (k+N)) (fun k => hN (k+N) (Nat.le_add_left N k))
      (hs.comp (tendsto_add_atTop_nat N))
    exact (tendsto_add_atTop_iff_nat N).mp hh
  have hderiv : HasDerivAt (WaveMap.energy u) (∫ x, WaveMap.densityTime u x t) t := by
    apply hasDerivAt_iff_tendsto_slope_zero.mpr
    simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using hlim
  obtain ⟨C, R', η', B', hc, hR', hη', hB', hsub, hbox, hvol, hfin, hwin, hu, hiter, hterms, hbd⟩ :=
    h_T003.2.2.2 t ht
  have htinterior : t ∈ WaveMap.timeInterior t := by
    change t/2 < t ∧ t < 3*t/2
    constructor <;> linarith
  have hGint : ∀ j : Fin n, Integrable (WaveMap.gradientProduct u j t) := by
    intro j
    exact (hterms t htinterior j (WaveMap.gradientProduct u j t) (by simp [WaveMap.terms])).2.2.2.2
  have hsumint : Integrable (fun x => ∑ j, WaveMap.gradientProduct u j t x) :=
    integrable_finsetSum Finset.univ (fun j _ => hGint j)
  have hKint : Integrable (WaveMap.kineticProduct u t) := by
    have hi := (hDint.sub (hsumint.const_mul 2)).div_const 2
    apply hi.congr
    apply Filter.Eventually.of_forall
    intro x
    dsimp
    rw [(h_T004 x t ht).2]
    ring
  exact ⟨hderiv, (fun x => (h_T004 x t ht).2), hDint, hKint, hGint⟩

#check @T006
#print axioms T006

end Translation
