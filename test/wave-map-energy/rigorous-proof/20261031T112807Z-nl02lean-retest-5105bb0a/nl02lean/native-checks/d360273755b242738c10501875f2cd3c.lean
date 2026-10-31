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

theorem T009 (n : ℕ) (m : ℕ) (u : WaveMap.Space n × ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H002 : ContDiffOn ℝ (∞ : ℕ∞ω) u (WaveMap.positive n)) (h_T001 : ∀ (x : WaveMap.Space n) (t : ℝ), 0 < t →
  inner ℝ (u (x,t)) (WaveMap.ut u x t) = 0 ∧
  inner ℝ (WaveMap.ut u x t) (WaveMap.utt u x t - WaveMap.laplace u x t) = 0 ∧
  inner ℝ (u (x,t)) (WaveMap.utt u x t) = -(‖WaveMap.ut u x t‖ ^ 2) ∧
  (∀ j : Fin n, inner ℝ (u (x,t)) (WaveMap.uxx u j x t) = -(‖WaveMap.ux u j x t‖ ^ 2)) ∧
  (∀ a : ℝ, WaveMap.utt u x t - WaveMap.laplace u x t = a • u (x,t) →
    a = (∑ j, ‖WaveMap.ux u j x t‖ ^ 2) - ‖WaveMap.ut u x t‖ ^ 2) ∧
  WaveMap.utt u x t - WaveMap.laplace u x t =
    ((∑ j, ‖WaveMap.ux u j x t‖ ^ 2) - ‖WaveMap.ut u x t‖ ^ 2) • u (x,t)) (h_T003 : (∀ t : ℝ, 0 < t → Integrable (fun x => WaveMap.density u x t)) ∧
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
    (∀ x ∈ WaveMap.box n R, ∀ r ∈ Icc (t0 - η) (t0 + η), |WaveMap.densityTime u x r| ≤ B)) (h_T006 : ∀ t : ℝ, 0 < t →
  HasDerivAt (WaveMap.energy u) (∫ x, WaveMap.densityTime u x t) t ∧
  (∀ x : WaveMap.Space n, WaveMap.densityTime u x t =
    2 * WaveMap.kineticProduct u t x + 2 * ∑ j, WaveMap.gradientProduct u j t x) ∧
  Integrable (fun x => WaveMap.densityTime u x t) ∧
  Integrable (WaveMap.kineticProduct u t) ∧
  (∀ j : Fin n, Integrable (WaveMap.gradientProduct u j t))) (h_T008 : ∀ (t : ℝ), 0 < t → ∀ j : Fin n,
  (∫ x, WaveMap.gradientProduct u j t x) = -(∫ x, WaveMap.laplaceProduct u j t x) ∧
  Integrable (WaveMap.gradientProduct u j t) ∧ Integrable (WaveMap.laplaceProduct u j t)) :
    ∀ t : ℝ, 0 < t → HasDerivAt (WaveMap.energy u) 0 t := by
  intro t ht
  rcases h_T006 t ht with ⟨hd, hformula, hD, hK, hG⟩
  have hL : ∀ j : Fin n, Integrable (WaveMap.laplaceProduct u j t) :=
    fun j => (h_T008 t ht j).2.2
  have hGsum : Integrable (fun x => ∑ j : Fin n, WaveMap.gradientProduct u j t x) :=
    integrable_finsetSum Finset.univ (fun j _ => hG j)
  have hLsum : Integrable (fun x => ∑ j : Fin n, WaveMap.laplaceProduct u j t x) :=
    integrable_finsetSum Finset.univ (fun j _ => hL j)
  have hIBP : ∀ j : Fin n,
      (∫ x, WaveMap.gradientProduct u j t x) =
        -(∫ x, WaveMap.laplaceProduct u j t x) :=
    fun j => (h_T008 t ht j).1
  have hdiff :
      (fun x => inner ℝ (WaveMap.ut u x t)
        (WaveMap.utt u x t - WaveMap.laplace u x t)) =
      (fun x => WaveMap.kineticProduct u t x -
        ∑ j : Fin n, WaveMap.laplaceProduct u j t x) := by
    funext x
    simp only [WaveMap.kineticProduct, WaveMap.laplaceProduct,
      WaveMap.laplace, inner_sub_right, inner_sum]
  have hz : (∫ x, WaveMap.densityTime u x t) = 0 := by
    calc
      (∫ x, WaveMap.densityTime u x t) =
          ∫ x, (2 * WaveMap.kineticProduct u t x +
            2 * ∑ j : Fin n, WaveMap.gradientProduct u j t x) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hformula
      _ = 2 * (∫ x, WaveMap.kineticProduct u t x) +
          2 * ∑ j : Fin n, (∫ x, WaveMap.gradientProduct u j t x) := by
        rw [integral_add (hK.const_mul 2) (hGsum.const_mul 2),
          integral_const_mul, integral_const_mul,
          integral_finsetSum Finset.univ (fun j _ => hG j)]
      _ = 2 * (∫ x, WaveMap.kineticProduct u t x) -
          2 * ∑ j : Fin n, (∫ x, WaveMap.laplaceProduct u j t x) := by
        simp_rw [hIBP]
        rw [Finset.sum_neg_distrib]
        ring
      _ = 2 * (∫ x, inner ℝ (WaveMap.ut u x t)
          (WaveMap.utt u x t - WaveMap.laplace u x t)) := by
        rw [hdiff, integral_sub hK hLsum,
          integral_finsetSum Finset.univ (fun j _ => hL j)]
        ring
      _ = 0 := by
        have hzero :
            (fun x => inner ℝ (WaveMap.ut u x t)
              (WaveMap.utt u x t - WaveMap.laplace u x t)) =
            (fun _ : WaveMap.Space n => (0 : ℝ)) := by
          funext x
          exact (h_T001 x t ht).2.1
        rw [hzero]
        simp
  simpa only [hz] using hd

#check @T009
#print axioms T009

end Translation
