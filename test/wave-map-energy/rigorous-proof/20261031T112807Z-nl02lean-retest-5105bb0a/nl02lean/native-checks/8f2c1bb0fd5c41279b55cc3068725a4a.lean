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

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem checked (n : ℕ) (m : ℕ) (u : WaveMap.Space n × ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_T003 : (∀ t : ℝ, 0 < t → Integrable (fun x => WaveMap.density u x t)) ∧
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
    (∀ x ∈ WaveMap.box n R, ∀ r ∈ Icc (t0 - η) (t0 + η), |WaveMap.densityTime u x r| ≤ B)) (h_T007 : ∀ (t : ℝ), 0 < t → ∀ j : Fin n,
  ContDiff ℝ (∞ : ℕ∞ω) (WaveMap.flux u j t) ∧ HasCompactSupport (WaveMap.flux u j t) ∧
  (∀ x : WaveMap.Space n, WaveMap.spatial (WaveMap.flux u j t) j x =
    WaveMap.gradientProduct u j t x + WaveMap.laplaceProduct u j t x) ∧
  Integrable (WaveMap.spatial (WaveMap.flux u j t) j) ∧
  Integrable (WaveMap.gradientProduct u j t) ∧ Integrable (WaveMap.laplaceProduct u j t)) : yui_aux_type% "∀ (k : ℕ) (j : Fin (k+1)) (g : WaveMap.Space (k+1) → ℝ) (R : ℝ),\nContDiff ℝ (∞ : ℕ∞ω) g → 0 < R → IsCompact (WaveMap.box (k+1) R) →\nFunction.support g ⊆ WaveMap.openBox (k+1) R →\nFunction.support (WaveMap.spatial g j) ⊆ WaveMap.box (k+1) R →\n(∫ x, WaveMap.spatial g j x) = 0" := by
  classical
  have hline : ∀ (k : ℕ) (j : Fin (k + 1)) (g : WaveMap.Space (k+1) → ℝ), ContDiff ℝ (∞ : ℕ∞ω) g → ∀ (y : Fin k → ℝ) (r : ℝ), HasDerivAt (fun s => g (WithLp.toLp 2 (j.insertNth s y))) (WaveMap.spatial g j (WithLp.toLp 2 (j.insertNth r y))) r := by
    intro k j g hg y r
    have heq : (fun s : ℝ => (WithLp.toLp 2 (j.insertNth s y) : WaveMap.Space (k+1))) =
        (fun s => (WithLp.toLp 2 (j.insertNth 0 y) : WaveMap.Space (k+1)) +
          s • (PiLp.single 2 j 1 : WaveMap.Space (k+1))) := by
      funext s
      apply PiLp.ext
      intro i
      rcases j.eq_self_or_eq_succAbove i with hi | ⟨a, ha⟩
      · subst i
        simp
      · subst i
        simp [Fin.succAbove_ne]
    have hi : HasDerivAt
        (fun s : ℝ => (WithLp.toLp 2 (j.insertNth s y) : WaveMap.Space (k+1)))
        (PiLp.single 2 j 1) r := by
      rw [heq]
      simpa using ((hasDerivAt_id r).smul_const
        (PiLp.single 2 j 1 : WaveMap.Space (k+1))).const_add
        (WithLp.toLp 2 (j.insertNth 0 y))
    exact (hg.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt r hi
  have htransport : ∀ (k : ℕ) (j : Fin (k+1)) (R : ℝ), IsCompact (WaveMap.box (k+1) R) → let e : (ℝ × (Fin k → ℝ)) ≃ᵐ WaveMap.Space (k+1) :=   (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k+1) => ℝ) j).symm.trans     (MeasurableEquiv.toLp 2 (Fin (k+1) → ℝ)) MeasurePreserving e   ((volume.restrict (Icc (-R) R)).prod     (Measure.pi (fun _ : Fin k => (volume : Measure ℝ).restrict (Icc (-R) R))))   (volume.restrict (WaveMap.box (k+1) R)) := by
    have hpre : ∀ (k : ℕ) (j : Fin (k+1)) (R : ℝ),
    let e : (ℝ × (Fin k → ℝ)) ≃ᵐ WaveMap.Space (k+1) :=
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k+1) => ℝ) j).symm.trans
        (MeasurableEquiv.toLp 2 (Fin (k+1) → ℝ))
    e ⁻¹' WaveMap.box (k+1) R = Icc (-R) R ×ˢ (Set.univ.pi (fun _ : Fin k => Icc (-R) R)) := by
      intro k j R e
      ext p
      rcases p with ⟨r,y⟩
      simp only [Set.mem_prod, Set.mem_pi, Set.mem_univ, forall_const]
      change (∀ i, Fin.insertNth (α := fun _ => ℝ) j r y i ∈ Icc (-R) R) ↔
        (r ∈ Icc (-R) R ∧ ∀ a, y a ∈ Icc (-R) R)
      simp only [j.forall_iff_succAbove, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
    intro k j R hQ e
    have hfull : MeasurePreserving e (volume : Measure (ℝ × (Fin k → ℝ))) volume :=
      (PiLp.volume_preserving_toLp (Fin (k+1))).comp
        (volume_preserving_piFinSuccAbove (fun _ : Fin (k+1) => ℝ) j).symm
    have hres := hfull.restrict_preimage hQ.measurableSet
    rw [hpre k j R] at hres
    change MeasurePreserving e
      (((volume : Measure ℝ).prod (volume : Measure (Fin k → ℝ))).restrict
        (Icc (-R) R ×ˢ Set.univ.pi (fun _ : Fin k => Icc (-R) R)))
      (volume.restrict (WaveMap.box (k+1) R)) at hres
    rw [← Measure.prod_restrict, volume_pi, Measure.restrict_pi_pi] at hres
    exact hres
  intro k j g R hg hR hQ hs hd
  let e : (ℝ × (Fin k → ℝ)) ≃ᵐ WaveMap.Space (k+1) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k+1) => ℝ) j).symm.trans
      (MeasurableEquiv.toLp 2 (Fin (k+1) → ℝ))
  let μ : Measure ℝ := volume.restrict (Icc (-R) R)
  let ν : Measure (Fin k → ℝ) := Measure.pi (fun _ : Fin k => μ)
  have hμ : IsFiniteMeasure μ := by dsimp [μ]; infer_instance
  have hν : IsFiniteMeasure ν := by dsimp [ν]; infer_instance
  letI := hμ
  letI := hν
  have hmp : MeasurePreserving e (μ.prod ν)
      (volume.restrict (WaveMap.box (k+1) R)) := htransport k j R hQ
  have hc : Continuous (WaveMap.spatial g j) := by
    exact (hg.fderiv_right (m := 0) (by simp)).continuous.clm_apply continuous_const
  have hinner : ∀ y : Fin k → ℝ, ∫ r in Icc (-R) R,
      WaveMap.spatial g j (e (r,y)) = 0 := by
    intro y
    have hi : Continuous (fun r : ℝ => (e (r,y) : WaveMap.Space (k+1))) := by
      exact (PiLp.continuous_toLp 2 (fun _ : Fin (k+1) => ℝ)).comp
        (continuous_id.finInsertNth j continuous_const)
    have hp : g (e (R,y)) = 0 := by
      apply Function.notMem_support.mp
      intro hx
      have hb := (hs hx) j
      have : R < R := by simpa [e] using hb.2
      exact lt_irrefl R this
    have hm : g (e (-R,y)) = 0 := by
      apply Function.notMem_support.mp
      intro hx
      have hb := (hs hx) j
      have : -R < -R := by simpa [e] using hb.1
      exact lt_irrefl (-R) this
    have hftc : (∫ r in (-R)..R, WaveMap.spatial g j (e (r,y))) =
        g (e (R,y)) - g (e (-R,y)) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun r _ => hline k j g hg y r)
        ((hc.comp hi).intervalIntegrable (-R) R)
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (show -R ≤ R by linarith), hftc, hp, hm, sub_self]
  have hboxint : Integrable (WaveMap.spatial g j)
      (volume.restrict (WaveMap.box (k+1) R)) :=
    hc.continuousOn.integrableOn_compact hQ
  have hprodint : Integrable (fun p => WaveMap.spatial g j (e p)) (μ.prod ν) :=
    hmp.integrable_comp_of_integrable hboxint
  have hboxzero : (∫ x in WaveMap.box (k+1) R, WaveMap.spatial g j x) = 0 := by
    rw [← hmp.integral_comp' (WaveMap.spatial g j),
      integral_prod_symm _ hprodint]
    change (∫ y, (∫ r in Icc (-R) R, WaveMap.spatial g j (e (r,y))) ∂ν) = 0
    simp only [hinner, integral_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := WaveMap.box (k+1) R) (fun x hx => Function.notMem_support.mp
      (fun h => hx (hd h)))]
  exact hboxzero
#check @checked
#print axioms checked
end YuiAuxiliary
