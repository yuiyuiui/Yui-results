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

theorem T007 (n : ℕ) (m : ℕ) (u : WaveMap.Space n × ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H002 : ContDiffOn ℝ (∞ : ℕ∞ω) u (WaveMap.positive n)) (h_T003 : (∀ t : ℝ, 0 < t → Integrable (fun x => WaveMap.density u x t)) ∧
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
    (∀ x ∈ WaveMap.box n R, ∀ r ∈ Icc (t0 - η) (t0 + η), |WaveMap.densityTime u x r| ≤ B)) :
    ∀ (t : ℝ), 0 < t → ∀ j : Fin n,
  ContDiff ℝ (∞ : ℕ∞ω) (WaveMap.flux u j t) ∧ HasCompactSupport (WaveMap.flux u j t) ∧
  (∀ x : WaveMap.Space n, WaveMap.spatial (WaveMap.flux u j t) j x =
    WaveMap.gradientProduct u j t x + WaveMap.laplaceProduct u j t x) ∧
  Integrable (WaveMap.spatial (WaveMap.flux u j t) j) ∧
  Integrable (WaveMap.gradientProduct u j t) ∧ Integrable (WaveMap.laplaceProduct u j t) := by
  intro t ht j
  have hop : IsOpen (WaveMap.positive n) :=
    isOpen_lt continuous_const continuous_snd
  have hut : ContDiff ℝ (∞ : ℕ∞ω) (fun x => WaveMap.ut u x t) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    have hu : ContDiffAt ℝ (∞ : ℕ∞ω) u (x,t) :=
      h_H002.contDiffAt (hop.mem_nhds ht)
    have hd : ContDiffAt ℝ (∞ : ℕ∞ω)
        (fun y : WaveMap.Space n => fderiv ℝ (fun r : ℝ => u (y,r)) t) x :=
      hu.fderiv (f := fun y r => u (y,r)) contDiffAt_const (by simp)
    simpa only [WaveMap.ut, deriv] using
      hd.clm_apply (contDiffAt_const (c := (1 : ℝ)))
  have hs : ContDiff ℝ (∞ : ℕ∞ω) (fun x : WaveMap.Space n => u (x,t)) :=
    h_H002.comp_contDiff (contDiff_id.prodMk contDiff_const) (fun x => ht)
  have hux : ContDiff ℝ (∞ : ℕ∞ω) (fun x => WaveMap.ux u j x t) :=
    (hs.fderiv_right (m := (∞ : ℕ∞ω)) (by simp)).clm_apply contDiff_const
  have hflux : ContDiff ℝ (∞ : ℕ∞ω) (WaveMap.flux u j t) :=
    hut.inner ℝ hux
  rcases h_T003.2.2.2 t ht with
    ⟨C, R, η, B, hC, hR, hη, hB, hsub, hbox, hvol, hfin,
      htime, hconst, hiter, hterms, hbound⟩
  have htI : t ∈ WaveMap.timeInterior t := by
    change t / 2 < t ∧ t < 3 * t / 2
    constructor <;> linarith
  have hfdata := hterms t htI j (WaveMap.flux u j t) (by simp [WaveMap.terms])
  have hddata := hterms t htI j (WaveMap.spatial (WaveMap.flux u j t) j)
    (by simp [WaveMap.terms])
  have hgdata := hterms t htI j (WaveMap.gradientProduct u j t)
    (by simp [WaveMap.terms])
  have hldata := hterms t htI j (WaveMap.laplaceProduct u j t)
    (by simp [WaveMap.terms])
  refine ⟨hflux, HasCompactSupport.of_support_subset_isCompact hC hfdata.2.1,
    ?_, hddata.2.2.2.2, hgdata.2.2.2.2, hldata.2.2.2.2⟩
  intro x
  change fderiv ℝ (fun y => inner ℝ (WaveMap.ut u y t) (WaveMap.ux u j y t))
      x (PiLp.single 2 j 1) =
    inner ℝ (WaveMap.ux u j x t) (WaveMap.utx u j x t) +
      inner ℝ (WaveMap.ut u x t) (WaveMap.uxx u j x t)
  calc
    _ = inner ℝ (WaveMap.ut u x t) (WaveMap.uxx u j x t) +
        inner ℝ (WaveMap.utx u j x t) (WaveMap.ux u j x t) :=
      fderiv_inner_apply ℝ (hut.differentiable (by simp) x)
        (hux.differentiable (by simp) x) (PiLp.single 2 j 1)
    _ = _ := by
      rw [real_inner_comm (WaveMap.utx u j x t) (WaveMap.ux u j x t)]
      exact add_comm _ _

#check @T007
#print axioms T007

end Translation
