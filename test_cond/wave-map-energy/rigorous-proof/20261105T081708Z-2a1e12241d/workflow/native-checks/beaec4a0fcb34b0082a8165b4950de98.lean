import Mathlib
open scoped BigOperators ContDiff Topology
open MeasureTheory
namespace WaveMap
abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)
def timeDomain (n : ℕ) : Set (Space n × ℝ) := {p | 0 < p.2}
noncomputable def dt {n m : ℕ} (u : Space n → ℝ → Space m) (x : Space n) (t : ℝ) : Space m :=
  deriv (u x) t
noncomputable def dtt {n m : ℕ} (u : Space n → ℝ → Space m) (x : Space n) (t : ℝ) : Space m :=
  deriv (fun r => dt u x r) t
noncomputable def dx {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Space n → F) (j : Fin n) (x : Space n) : F :=
  fderiv ℝ f x (EuclideanSpace.single j 1)
noncomputable def du {n m : ℕ} (u : Space n → ℝ → Space m) (j : Fin n) (x : Space n) (t : ℝ) : Space m :=
  dx (fun y => u y t) j x
noncomputable def duu {n m : ℕ} (u : Space n → ℝ → Space m) (j : Fin n) (x : Space n) (t : ℝ) : Space m :=
  dx (fun y => du u j y t) j x
noncomputable def dut {n m : ℕ} (u : Space n → ℝ → Space m) (j : Fin n) (x : Space n) (t : ℝ) : Space m :=
  dx (fun y => dt u y t) j x
noncomputable def lap {n m : ℕ} (u : Space n → ℝ → Space m) (x : Space n) (t : ℝ) : Space m :=
  ∑ j, duu u j x t
noncomputable def density {n m : ℕ} (u : Space n → ℝ → Space m) (x : Space n) (t : ℝ) : ℝ :=
  ‖dt u x t‖ ^ 2 + ∑ j, ‖du u j x t‖ ^ 2
noncomputable def densityT {n m : ℕ} (u : Space n → ℝ → Space m) (x : Space n) (t : ℝ) : ℝ :=
  deriv (density u x) t
noncomputable def energy {n m : ℕ} (u : Space n → ℝ → Space m) (t : ℝ) : ℝ :=
  ∫ x, density u x t
noncomputable def flux {n m : ℕ} (u : Space n → ℝ → Space m) (j : Fin n) (t : ℝ) (x : Space n) : ℝ :=
  inner ℝ (dt u x t) (du u j x t)
def box {n : ℕ} (R : ℝ) : Set (Space n) := {x | ∀ j, x j ∈ Set.Icc (-R) R}
def openBox {n : ℕ} (R : ℝ) : Set (Space n) := {x | ∀ j, x j ∈ Set.Ioo (-R) R}
def sectionGood {n : ℕ} (f : Space n → ℝ) (C : Set (Space n)) (R : ℝ) : Prop :=
  Continuous f ∧ (∃ B : ℝ, ∀ x ∈ box (n := n) R, |f x| ≤ B) ∧
  (∀ x ∉ C, f x = 0) ∧ Integrable f
end WaveMap

open WaveMap

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace Translation
set_option autoImplicit false

namespace Local_T005
theorem yui_aux_0001 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_T003 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (Space n), ∃ R : ℝ, IsCompact C ∧ 0 < R ∧ C ⊆ openBox (n := n) R ∧ (∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc (t0 / 2) (3 * t0 / 2) → u x r = q) ∧ volume (box (n := n) R) = ENNReal.ofReal ((2 * R) ^ n) ∧ volume (box (n := n) R) < ⊤ ∧ (∀ (k : ℕ) (x : Space n) (r : ℝ), 0 < k → x ∉ C → r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2) → iteratedFDeriv ℝ k (Function.uncurry u) (x, r) = 0) ∧ (∀ r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2), sectionGood (fun x => density u x r) C R ∧ sectionGood (fun x => densityT u x r) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (dtt u x r)) C R ∧ (∀ j : Fin n, sectionGood (flux u j r) C R ∧ sectionGood (fun x => inner ℝ (dut u j x r) (du u j x r)) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (duu u j x r)) C R ∧ sectionGood (fun x => dx (flux u j r) j x) C R))) ∧ (∀ t : ℝ, 0 < t → Integrable (fun x => density u x t))) (h_T004 : (∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (density u x) (2 * inner ℝ (dt u x t) (dtt u x t) + 2 * ∑ j : Fin n, inner ℝ (du u j x t) (dut u j x t)) t ∧ densityT u x t = 2 * inner ℝ (dt u x t) (dtt u x t) + 2 * ∑ j : Fin n, inner ℝ (du u j x t) (dut u j x t)) ∧ ContinuousOn (Function.uncurry (densityT u)) (timeDomain n)) : yui_aux_type% "∀ R : ℝ, IsCompact (box (n := n) R)" := by
  intro R
  have hc : IsCompact (Set.pi Set.univ (fun _ : Fin n => Set.Icc (-R) R)) := isCompact_univ_pi (fun _ => isCompact_Icc)
  have he : box (n := n) R = (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)) ⁻¹' (Set.pi Set.univ (fun _ : Fin n => Set.Icc (-R) R)) := by
    ext x
    simp [box, PiLp.homeomorph, Pi.le_def, forall_and]
  rw [he]
  exact (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).isCompact_preimage.mpr hc

theorem yui_aux_0002 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_T003 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (Space n), ∃ R : ℝ, IsCompact C ∧ 0 < R ∧ C ⊆ openBox (n := n) R ∧ (∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc (t0 / 2) (3 * t0 / 2) → u x r = q) ∧ volume (box (n := n) R) = ENNReal.ofReal ((2 * R) ^ n) ∧ volume (box (n := n) R) < ⊤ ∧ (∀ (k : ℕ) (x : Space n) (r : ℝ), 0 < k → x ∉ C → r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2) → iteratedFDeriv ℝ k (Function.uncurry u) (x, r) = 0) ∧ (∀ r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2), sectionGood (fun x => density u x r) C R ∧ sectionGood (fun x => densityT u x r) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (dtt u x r)) C R ∧ (∀ j : Fin n, sectionGood (flux u j r) C R ∧ sectionGood (fun x => inner ℝ (dut u j x r) (du u j x r)) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (duu u j x r)) C R ∧ sectionGood (fun x => dx (flux u j r) j x) C R))) ∧ (∀ t : ℝ, 0 < t → Integrable (fun x => density u x t))) (h_T004 : (∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (density u x) (2 * inner ℝ (dt u x t) (dtt u x t) + 2 * ∑ j : Fin n, inner ℝ (du u j x t) (dut u j x t)) t ∧ densityT u x t = 2 * inner ℝ (dt u x t) (dtt u x t) + 2 * ∑ j : Fin n, inner ℝ (du u j x t) (dut u j x t)) ∧ ContinuousOn (Function.uncurry (densityT u)) (timeDomain n)) : yui_aux_type% "∀ (t : ℝ), 0 < t → ∀ R : ℝ, ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ box (n := n) R, ∀ r ∈ Set.Icc (t - t / 4) (t + t / 4), ‖densityT u x r‖ ≤ B" := by
  intro t ht R
  have hc : IsCompact ((box (n := n) R) ×ˢ Set.Icc (t-t/4) (t+t/4)) :=
    (@yui_aux_0001 n m u q h_H002 h_T003 h_T004 R).prod isCompact_Icc
  have hsub : (box (n := n) R) ×ˢ Set.Icc (t-t/4) (t+t/4) ⊆ timeDomain n := by
    intro p hp
    change 0 < p.2
    have := hp.2.1
    linarith
  obtain ⟨B, hB⟩ := hc.exists_bound_of_continuousOn (h_T004.2.mono hsub)
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro x hx r hr
  exact (hB (x,r) ⟨hx,hr⟩).trans (le_max_left _ _)

theorem yui_aux_0003 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_T003 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (Space n), ∃ R : ℝ, IsCompact C ∧ 0 < R ∧ C ⊆ openBox (n := n) R ∧ (∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc (t0 / 2) (3 * t0 / 2) → u x r = q) ∧ volume (box (n := n) R) = ENNReal.ofReal ((2 * R) ^ n) ∧ volume (box (n := n) R) < ⊤ ∧ (∀ (k : ℕ) (x : Space n) (r : ℝ), 0 < k → x ∉ C → r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2) → iteratedFDeriv ℝ k (Function.uncurry u) (x, r) = 0) ∧ (∀ r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2), sectionGood (fun x => density u x r) C R ∧ sectionGood (fun x => densityT u x r) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (dtt u x r)) C R ∧ (∀ j : Fin n, sectionGood (flux u j r) C R ∧ sectionGood (fun x => inner ℝ (dut u j x r) (du u j x r)) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (duu u j x r)) C R ∧ sectionGood (fun x => dx (flux u j r) j x) C R))) ∧ (∀ t : ℝ, 0 < t → Integrable (fun x => density u x t))) (h_T004 : (∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (density u x) (2 * inner ℝ (dt u x t) (dtt u x t) + 2 * ∑ j : Fin n, inner ℝ (du u j x t) (dut u j x t)) t ∧ densityT u x t = 2 * inner ℝ (dt u x t) (dtt u x t) + 2 * ∑ j : Fin n, inner ℝ (du u j x t) (dut u j x t)) ∧ ContinuousOn (Function.uncurry (densityT u)) (timeDomain n)) : yui_aux_type% "∀ (t R B : ℝ), 0 < t → (∀ x ∈ box (n := n) R, ∀ r ∈ Set.Icc (t-t/4) (t+t/4), ‖densityT u x r‖ ≤ B) → ∀ (h : ℝ), h ≠ 0 → |h| < t/4 → ∀ x ∈ box (n := n) R, ‖(density u x (t+h) - density u x t) / h‖ ≤ B" := by
  intro t R B ht hB h hn hh x hx
  have hd : ∀ r ∈ Set.Icc (t-t/4) (t+t/4), HasDerivWithinAt (density u x) (densityT u x r) (Set.Icc (t-t/4) (t+t/4)) r := by
    intro r hr
    have hr0 : 0 < r := by linarith [hr.1]
    rw [(h_T004.1 x r hr0).2]
    exact (h_T004.1 x r hr0).1.hasDerivWithinAt
  have htmem : t ∈ Set.Icc (t-t/4) (t+t/4) := by constructor <;> linarith
  have hhmem : t+h ∈ Set.Icc (t-t/4) (t+t/4) := by
    rw [abs_lt] at hh
    constructor <;> linarith [hh.1, hh.2]
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd (hB x hx) (convex_Icc _ _) htmem hhmem
  have hnabs : 0 < |h| := abs_pos.mpr hn
  rw [norm_div, Real.norm_eq_abs h, div_le_iff₀ hnabs]
  simpa only [add_sub_cancel_left, Real.norm_eq_abs] using hm

theorem yui_aux_0004 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_T003 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (Space n), ∃ R : ℝ, IsCompact C ∧ 0 < R ∧ C ⊆ openBox (n := n) R ∧ (∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc (t0 / 2) (3 * t0 / 2) → u x r = q) ∧ volume (box (n := n) R) = ENNReal.ofReal ((2 * R) ^ n) ∧ volume (box (n := n) R) < ⊤ ∧ (∀ (k : ℕ) (x : Space n) (r : ℝ), 0 < k → x ∉ C → r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2) → iteratedFDeriv ℝ k (Function.uncurry u) (x, r) = 0) ∧ (∀ r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2), sectionGood (fun x => density u x r) C R ∧ sectionGood (fun x => densityT u x r) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (dtt u x r)) C R ∧ (∀ j : Fin n, sectionGood (flux u j r) C R ∧ sectionGood (fun x => inner ℝ (dut u j x r) (du u j x r)) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (duu u j x r)) C R ∧ sectionGood (fun x => dx (flux u j r) j x) C R))) ∧ (∀ t : ℝ, 0 < t → Integrable (fun x => density u x t))) (h_T004 : (∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (density u x) (2 * inner ℝ (dt u x t) (dtt u x t) + 2 * ∑ j : Fin n, inner ℝ (du u j x t) (dut u j x t)) t ∧ densityT u x t = 2 * inner ℝ (dt u x t) (dtt u x t) + 2 * ∑ j : Fin n, inner ℝ (du u j x t) (dut u j x t)) ∧ ContinuousOn (Function.uncurry (densityT u)) (timeDomain n)) : yui_aux_type% "∀ (t h : ℝ), 0 < t → 0 < t+h → AEStronglyMeasurable (fun x => (density u x (t+h) - density u x t) / h) volume" := by
  intro t h ht hh
  exact ((h_T003.2 (t+h) hh).sub (h_T003.2 t ht)).div_const h |>.aestronglyMeasurable

theorem yui_aux_0005 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_T003 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (Space n), ∃ R : ℝ, IsCompact C ∧ 0 < R ∧ C ⊆ openBox (n := n) R ∧ (∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc (t0 / 2) (3 * t0 / 2) → u x r = q) ∧ volume (box (n := n) R) = ENNReal.ofReal ((2 * R) ^ n) ∧ volume (box (n := n) R) < ⊤ ∧ (∀ (k : ℕ) (x : Space n) (r : ℝ), 0 < k → x ∉ C → r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2) → iteratedFDeriv ℝ k (Function.uncurry u) (x, r) = 0) ∧ (∀ r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2), sectionGood (fun x => density u x r) C R ∧ sectionGood (fun x => densityT u x r) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (dtt u x r)) C R ∧ (∀ j : Fin n, sectionGood (flux u j r) C R ∧ sectionGood (fun x => inner ℝ (dut u j x r) (du u j x r)) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (duu u j x r)) C R ∧ sectionGood (fun x => dx (flux u j r) j x) C R))) ∧ (∀ t : ℝ, 0 < t → Integrable (fun x => density u x t))) (h_T004 : (∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (density u x) (2 * inner ℝ (dt u x t) (dtt u x t) + 2 * ∑ j : Fin n, inner ℝ (du u j x t) (dut u j x t)) t ∧ densityT u x t = 2 * inner ℝ (dt u x t) (dtt u x t) + 2 * ∑ j : Fin n, inner ℝ (du u j x t) (dut u j x t)) ∧ ContinuousOn (Function.uncurry (densityT u)) (timeDomain n)) : yui_aux_type% "∀ t : ℝ, 0 < t → HasDerivAt (energy u) (∫ x, densityT u x t) t" := by
  intro t ht
  classical
  obtain ⟨C, R, hC, hR, hCQ, hconst, hvol, hfin, hvan, hg⟩ := h_T003.1 t ht
  have htJ : t ∈ Set.Ioo (t/2) (3*t/2) := by constructor <;> linarith
  have hsmall : ∀ h : ℝ, |h| < t/4 → t+h ∈ Set.Ioo (t/2) (3*t/2) := by
    intro h hh
    rw [abs_lt] at hh
    constructor <;> linarith [hh.1, hh.2]
  have hCQ' : C ⊆ box (n := n) R := by
    intro x hx j
    exact ⟨(hCQ hx j).1.le, (hCQ hx j).2.le⟩
  obtain ⟨B, hB0, hB⟩ := @yui_aux_0002 n m u q h_H002 h_T003 h_T004 t ht R
  let bnd : Space n → ℝ := (box (n := n) R).indicator (fun _ => B)
  have hQmeas : MeasurableSet (box (n := n) R) :=
    (@yui_aux_0001 n m u q h_H002 h_T003 h_T004 R).measurableSet
  have hbnd : Integrable bnd := by
    exact (integrableOn_const hfin.ne).integrable_indicator hQmeas
  let v : ℝ → Space n → ℝ := fun h x =>
    if h ≠ 0 ∧ |h| < t/4 then (density u x (t+h) - density u x t) / h else 0
  have hevent : ∀ᶠ h : ℝ in 𝓝[≠] 0, h ≠ 0 ∧ |h| < t/4 := by
    have hs : ∀ᶠ h : ℝ in 𝓝 (0 : ℝ), |h| < t/4 := by
      have hb := Metric.ball_mem_nhds (0 : ℝ) (by linarith : 0 < t/4)
      filter_upwards [hb] with h hh
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hh
    filter_upwards [self_mem_nhdsWithin, hs.filter_mono nhdsWithin_le_nhds] with h hn hh
    exact ⟨hn, hh⟩
  have hmeas : ∀ᶠ h : ℝ in 𝓝[≠] 0, AEStronglyMeasurable (v h) volume := by
    filter_upwards [hevent] with h hh
    have hc := ((hg (t+h) (hsmall h hh.2)).1.1.sub (hg t htJ).1.1).div_const h
    have hp : 0 < t+h := by linarith [(hsmall h hh.2).1]
    simpa only [v, if_pos hh] using
      (@yui_aux_0004 n m u q h_H002 h_T003 h_T004 t h ht hp)
  have hdom : ∀ᶠ h : ℝ in 𝓝[≠] 0, ∀ᵐ x ∂volume, ‖v h x‖ ≤ bnd x := by
    filter_upwards [hevent] with h hh
    apply Filter.Eventually.of_forall
    intro x
    by_cases hx : x ∈ box (n := n) R
    · simpa only [v, if_pos hh, bnd, Set.indicator_of_mem hx] using
        (@yui_aux_0003 n m u q h_H002 h_T003 h_T004 t R B ht hB h hh.1 hh.2 x hx)
    · have hxc : x ∉ C := fun hc => hx (hCQ' hc)
      have hz1 := (hg (t+h) (hsmall h hh.2)).1.2.2.1 x hxc
      have hz0 := (hg t htJ).1.2.2.1 x hxc
      simp [v, hh, bnd, hx, hz1, hz0]
  have hlim : ∀ᵐ x ∂volume, Filter.Tendsto (fun h => v h x) (𝓝[≠] 0) (𝓝 (densityT u x t)) := by
    apply Filter.Eventually.of_forall
    intro x
    have hd : HasDerivAt (density u x) (densityT u x t) t := by
      rw [(h_T004.1 x t ht).2]
      exact (h_T004.1 x t ht).1
    apply hd.tendsto_slope_zero.congr'
    filter_upwards [hevent] with h hh
    dsimp only [v]
    rw [if_pos hh]
    simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hDCT := tendsto_integral_filter_of_dominated_convergence bnd hmeas hdom hbnd hlim
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  apply hDCT.congr'
  filter_upwards [hevent] with h hh
  have hp : 0 < t+h := by linarith [(hsmall h hh.2).1]
  dsimp only [v]
  simp only [if_pos hh]
  rw [integral_div, integral_sub (h_T003.2 (t+h) hp) (h_T003.2 t ht)]
  simp only [energy, smul_eq_mul, div_eq_mul_inv, mul_comm]

end Local_T005
open Local_T005 in
theorem T005 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_T003 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (Space n), ∃ R : ℝ, IsCompact C ∧ 0 < R ∧ C ⊆ openBox (n := n) R ∧ (∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc (t0 / 2) (3 * t0 / 2) → u x r = q) ∧ volume (box (n := n) R) = ENNReal.ofReal ((2 * R) ^ n) ∧ volume (box (n := n) R) < ⊤ ∧ (∀ (k : ℕ) (x : Space n) (r : ℝ), 0 < k → x ∉ C → r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2) → iteratedFDeriv ℝ k (Function.uncurry u) (x, r) = 0) ∧ (∀ r ∈ Set.Ioo (t0 / 2) (3 * t0 / 2), sectionGood (fun x => density u x r) C R ∧ sectionGood (fun x => densityT u x r) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (dtt u x r)) C R ∧ (∀ j : Fin n, sectionGood (flux u j r) C R ∧ sectionGood (fun x => inner ℝ (dut u j x r) (du u j x r)) C R ∧ sectionGood (fun x => inner ℝ (dt u x r) (duu u j x r)) C R ∧ sectionGood (fun x => dx (flux u j r) j x) C R))) ∧ (∀ t : ℝ, 0 < t → Integrable (fun x => density u x t))) (h_T004 : (∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (density u x) (2 * inner ℝ (dt u x t) (dtt u x t) + 2 * ∑ j : Fin n, inner ℝ (du u j x t) (dut u j x t)) t ∧ densityT u x t = 2 * inner ℝ (dt u x t) (dtt u x t) + 2 * ∑ j : Fin n, inner ℝ (du u j x t) (dut u j x t)) ∧ ContinuousOn (Function.uncurry (densityT u)) (timeDomain n)) :
    ∀ t : ℝ, 0 < t → (∀ x : Space n, densityT u x t = 2 * inner ℝ (dt u x t) (dtt u x t) + 2 * ∑ j : Fin n, inner ℝ (du u j x t) (dut u j x t)) ∧ Integrable (fun x => densityT u x t) ∧ Integrable (fun x => inner ℝ (dt u x t) (dtt u x t)) ∧ (∀ j : Fin n, Integrable (fun x => inner ℝ (du u j x t) (dut u j x t))) ∧ HasDerivAt (energy u) (∫ x, densityT u x t) t ∧ deriv (energy u) t = (∫ x, densityT u x t) ∧ deriv (energy u) t = 2 * (∫ x, inner ℝ (dt u x t) (dtt u x t)) + 2 * ∑ j : Fin n, (∫ x, inner ℝ (du u j x t) (dut u j x t)) := by
  intro t ht
  classical
  obtain ⟨C, R, hC, hR, hCQ, hconst, hvol, hfin, hvan, hg⟩ := h_T003.1 t ht
  have htJ : t ∈ Set.Ioo (t/2) (3*t/2) := by constructor <;> linarith
  rcases hg t htJ with ⟨he, het, ha, hj⟩
  have hA : Integrable (fun x => inner ℝ (dt u x t) (dtt u x t)) := ha.2.2.2
  have hJ : ∀ j : Fin n, Integrable (fun x => inner ℝ (du u j x t) (dut u j x t)) := by
    intro j
    exact ((hj j).2.1.2.2.2).congr (Filter.Eventually.of_forall (fun x => real_inner_comm _ _))
  have hD := @yui_aux_0005 n m u q h_H002 h_T003 h_T004 t ht
  refine ⟨(fun x => (h_T004.1 x t ht).2), het.2.2.2, hA, hJ, hD, hD.deriv, ?_⟩
  rw [hD.deriv]
  have hS : Integrable (fun x => ∑ j : Fin n, inner ℝ (du u j x t) (dut u j x t)) :=
    integrable_finsetSum Finset.univ (fun j _ => hJ j)
  calc
    (∫ x, densityT u x t) =
        ∫ x, 2 * inner ℝ (dt u x t) (dtt u x t) +
          2 * ∑ j : Fin n, inner ℝ (du u j x t) (dut u j x t) := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall (fun x => (h_T004.1 x t ht).2)
    _ = 2 * (∫ x, inner ℝ (dt u x t) (dtt u x t)) +
        2 * ∑ j : Fin n, (∫ x, inner ℝ (du u j x t) (dut u j x t)) := by
          rw [integral_add (hA.const_mul 2) (hS.const_mul 2)]
          simp only [integral_const_mul]
          rw [integral_finsetSum Finset.univ (fun j _ => hJ j)]

#check @T005
#print axioms T005

end Translation
