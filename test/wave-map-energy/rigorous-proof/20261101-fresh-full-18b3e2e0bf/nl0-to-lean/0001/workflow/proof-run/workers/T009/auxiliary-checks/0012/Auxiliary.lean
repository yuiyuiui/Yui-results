import Mathlib

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace WaveMap

abbrev X (n : ℕ) := Fin n → ℝ
abbrev V (m : ℕ) := EuclideanSpace ℝ (Fin m)

def domain (n : ℕ) : Set (X n × ℝ) := {p | 0 < p.2}
def box (n : ℕ) (R : ℝ) : Set (X n) :=
  Set.pi Set.univ (fun _ => Set.Icc (-R) R)
def openBox (n : ℕ) (R : ℝ) : Set (X n) :=
  Set.pi Set.univ (fun _ => Set.Ioo (-R) R)
def slab (t : ℝ) : Set ℝ := Set.Icc (t / 2) (3 * t / 2)

noncomputable def dt {n m : ℕ} (u : X n × ℝ → V m) : X n × ℝ → V m :=
  fun p => deriv (fun r : ℝ => u (p.1, r)) p.2
noncomputable def dx {n m : ℕ} (u : X n × ℝ → V m) (j : Fin n) :
    X n × ℝ → V m :=
  fun p => fderiv ℝ (fun x : X n => u (x, p.2)) p.1 (Pi.single j 1)
noncomputable def lap {n m : ℕ} (u : X n × ℝ → V m) : X n × ℝ → V m :=
  fun p => ∑ j : Fin n, dx (dx u j) j p
noncomputable def density {n m : ℕ} (u : X n × ℝ → V m) :
    X n × ℝ → ℝ :=
  fun p => ‖dt u p‖ ^ 2 + ∑ j : Fin n, ‖dx u j p‖ ^ 2
noncomputable def densityT {n m : ℕ} (u : X n × ℝ → V m) :
    X n × ℝ → ℝ :=
  fun p => deriv (fun r : ℝ => density u (p.1, r)) p.2
noncomputable def energy {n m : ℕ} (u : X n × ℝ → V m) (t : ℝ) : ℝ :=
  ∫ x : X n, density u (x, t)
noncomputable def timeProduct {n m : ℕ} (u : X n × ℝ → V m) :
    X n × ℝ → ℝ :=
  fun p => inner ℝ (dt u p) (dt (dt u) p)
noncomputable def mixedProduct {n m : ℕ} (u : X n × ℝ → V m) (j : Fin n) :
    X n × ℝ → ℝ :=
  fun p => inner ℝ (dx u j p) (dx (dt u) j p)
noncomputable def lapProduct {n m : ℕ} (u : X n × ℝ → V m) (j : Fin n) :
    X n × ℝ → ℝ :=
  fun p => inner ℝ (dt u p) (dx (dx u j) j p)
noncomputable def flux {n m : ℕ} (u : X n × ℝ → V m) (j : Fin n) :
    X n × ℝ → ℝ :=
  fun p => inner ℝ (dt u p) (dx u j p)
noncomputable def fluxDx {n m : ℕ} (u : X n × ℝ → V m) (j : Fin n) :
    X n × ℝ → ℝ :=
  fun p => fderiv ℝ (fun x : X n => flux u j (x, p.2)) p.1 (Pi.single j 1)

def sectionGood {n : ℕ} (C : Set (X n)) (R : ℝ) (f : X n → ℝ) : Prop :=
  Continuous f ∧ (∀ x, x ∉ C → f x = 0) ∧
  (∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ box n R, |f x| ≤ B) ∧ Integrable f

def supportGeometry {n m : ℕ} (u : X n × ℝ → V m) (q : V m)
    (t : ℝ) (C : Set (X n)) (R : ℝ) : Prop :=
  IsCompact C ∧ 0 < R ∧ C ⊆ openBox n R ∧
  (∀ x, x ∉ C → ∀ r ∈ slab t, u (x, r) = q) ∧
  volume (box n R) = ENNReal.ofReal ((2 * R) ^ n) ∧
  volume (box n R) < ⊤ ∧
  (∀ k : ℕ, ∀ x, x ∉ C → ∀ r ∈ interior (slab t),
    iteratedFDeriv ℝ (k + 1) u (x, r) = 0)

def supportSections {n m : ℕ} (u : X n × ℝ → V m)
    (t : ℝ) (C : Set (X n)) (R : ℝ) : Prop :=
  ∀ r ∈ interior (slab t),
    sectionGood C R (fun x => density u (x, r)) ∧
    sectionGood C R (fun x => densityT u (x, r)) ∧
    sectionGood C R (fun x => timeProduct u (x, r)) ∧
    (∀ j : Fin n,
      sectionGood C R (fun x => mixedProduct u j (x, r)) ∧
      sectionGood C R (fun x => lapProduct u j (x, r)) ∧
      sectionGood C R (fun x => fluxDx u j (x, r)))

noncomputable def quotient {n m : ℕ} (u : X n × ℝ → V m)
    (t h : ℝ) (x : X n) : ℝ :=
  (density u (x, t + h) - density u (x, t)) / h

abbrev Other {n : ℕ} (j : Fin n) := {i : Fin n // i ≠ j}
def insertCoord {n : ℕ} (j : Fin n) (y : Other j → ℝ) (z : ℝ) : X n :=
  fun i => if h : i = j then z else y ⟨i, h⟩
def otherBox {n : ℕ} (j : Fin n) (R : ℝ) : Set (Other j → ℝ) :=
  Set.pi Set.univ (fun _ => Set.Icc (-R) R)

end WaveMap

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem yui_aux_0001 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_T004 : (∀ t : ℝ, 0 < t → ∃ C : Set (WaveMap.X n), ∃ R : ℝ,
    WaveMap.supportGeometry u q t C R ∧ WaveMap.supportSections u t C R) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : WaveMap.X n => WaveMap.density u (x, t))) ∧
  ContinuousOn (WaveMap.density u) (WaveMap.domain n) ∧
  ContinuousOn (WaveMap.densityT u) (WaveMap.domain n)) (h_T008 : ∀ (j : Fin n) (R : ℝ), 0 < R → ∀ f : WaveMap.X n → ℝ,
  IntegrableOn f (WaveMap.box n R) →
  (∫ x in WaveMap.box n R, f x) =
    ∫ y in WaveMap.otherBox j R, ∫ z in Set.Icc (-R) R, f (WaveMap.insertCoord j y z)) : yui_aux_type% "∀ t : ℝ, 0 < t → ContDiff ℝ (⊤ : ℕ∞) (fun x : WaveMap.X n => WaveMap.dt u (x,t)) ∧ ∀ j : Fin n, ContDiff ℝ (⊤ : ℕ∞) (fun x : WaveMap.X n => WaveMap.dx u j (x,t))" := by
  intro t ht
  have hopen : IsOpen (WaveMap.domain n) := isOpen_lt continuous_const continuous_snd
  have hu (x : WaveMap.X n) : ContDiffAt ℝ (⊤ : ℕ∞) u (x,t) :=
    h_H002.contDiffAt (hopen.mem_nhds ht)
  constructor
  · apply contDiff_iff_contDiffAt.mpr
    intro x
    have hf : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun x : WaveMap.X n => fderiv ℝ (fun r : ℝ => u (x,r)) t) x :=
      (hu x).fderiv contDiffAt_const (by simp)
    exact hf.clm_apply contDiffAt_const
  · intro j
    have hs : ContDiff ℝ (⊤ : ℕ∞) (fun x : WaveMap.X n => u (x,t)) :=
      contDiff_iff_contDiffAt.mpr (fun x => (hu x).comp x (contDiffAt_id.prodMk contDiffAt_const))
    exact (hs.fderiv_right (by simp)).clm_apply contDiff_const

theorem yui_aux_0002 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_T004 : (∀ t : ℝ, 0 < t → ∃ C : Set (WaveMap.X n), ∃ R : ℝ,
    WaveMap.supportGeometry u q t C R ∧ WaveMap.supportSections u t C R) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : WaveMap.X n => WaveMap.density u (x, t))) ∧
  ContinuousOn (WaveMap.density u) (WaveMap.domain n) ∧
  ContinuousOn (WaveMap.densityT u) (WaveMap.domain n)) (h_T008 : ∀ (j : Fin n) (R : ℝ), 0 < R → ∀ f : WaveMap.X n → ℝ,
  IntegrableOn f (WaveMap.box n R) →
  (∫ x in WaveMap.box n R, f x) =
    ∫ y in WaveMap.otherBox j R, ∫ z in Set.Icc (-R) R, f (WaveMap.insertCoord j y z)) : yui_aux_type% "∀ t : ℝ, 0 < t → t ∈ interior (WaveMap.slab t) ∧\n  ∀ (C : Set (WaveMap.X n)) (R : ℝ), WaveMap.supportGeometry u q t C R →\n  ∀ j : Fin n, ∀ x : WaveMap.X n, x ∉ C → WaveMap.flux u j (x,t) = 0" := by
  intro t ht
  have hti : t ∈ interior (WaveMap.slab t) := by
    simp only [WaveMap.slab, interior_Icc, mem_Ioo]
    constructor <;> linarith
  refine ⟨hti, ?_⟩
  intro C R hg j x hx
  have heq : (fun r : ℝ => u (x,r)) =ᶠ[𝓝 t] (fun _ => q) := by
    filter_upwards [mem_interior_iff_mem_nhds.mp hti] with r hr
    exact hg.2.2.2.1 x hx r hr
  have hz : WaveMap.dt u (x,t) = 0 := by
    exact heq.deriv_eq.trans (deriv_const t q)
  simp [WaveMap.flux, hz]

theorem yui_aux_0003 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_T004 : (∀ t : ℝ, 0 < t → ∃ C : Set (WaveMap.X n), ∃ R : ℝ,
    WaveMap.supportGeometry u q t C R ∧ WaveMap.supportSections u t C R) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : WaveMap.X n => WaveMap.density u (x, t))) ∧
  ContinuousOn (WaveMap.density u) (WaveMap.domain n) ∧
  ContinuousOn (WaveMap.densityT u) (WaveMap.domain n)) (h_T008 : ∀ (j : Fin n) (R : ℝ), 0 < R → ∀ f : WaveMap.X n → ℝ,
  IntegrableOn f (WaveMap.box n R) →
  (∫ x in WaveMap.box n R, f x) =
    ∫ y in WaveMap.otherBox j R, ∫ z in Set.Icc (-R) R, f (WaveMap.insertCoord j y z)) : yui_aux_type% "∀ t : ℝ, 0 < t → ∀ j : Fin n, ∀ x : WaveMap.X n,\n  fderiv ℝ (fun y : WaveMap.X n => inner ℝ (WaveMap.dt u (y,t)) (WaveMap.dx u j (y,t))) x (Pi.single j 1) =\n  inner ℝ (WaveMap.dt u (x,t)) (WaveMap.dx (WaveMap.dx u j) j (x,t)) +\n  inner ℝ (WaveMap.dx (WaveMap.dt u) j (x,t)) (WaveMap.dx u j (x,t))" := by
  intro t ht j x
  obtain ⟨ha,hb⟩ := yui_aux_0001 n m u q h_H001 h_H002 h_T004 h_T008 t ht
  exact fderiv_inner_apply ℝ (ha.differentiable (by simp)).differentiableAt
    ((hb j).differentiable (by simp)).differentiableAt (Pi.single j 1)

theorem yui_aux_0004 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_T004 : (∀ t : ℝ, 0 < t → ∃ C : Set (WaveMap.X n), ∃ R : ℝ,
    WaveMap.supportGeometry u q t C R ∧ WaveMap.supportSections u t C R) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : WaveMap.X n => WaveMap.density u (x, t))) ∧
  ContinuousOn (WaveMap.density u) (WaveMap.domain n) ∧
  ContinuousOn (WaveMap.densityT u) (WaveMap.domain n)) (h_T008 : ∀ (j : Fin n) (R : ℝ), 0 < R → ∀ f : WaveMap.X n → ℝ,
  IntegrableOn f (WaveMap.box n R) →
  (∫ x in WaveMap.box n R, f x) =
    ∫ y in WaveMap.otherBox j R, ∫ z in Set.Icc (-R) R, f (WaveMap.insertCoord j y z)) : yui_aux_type% "∀ j : Fin n, ∀ (y : WaveMap.Other j → ℝ) (z : ℝ),\n  HasDerivAt (WaveMap.insertCoord j y) (Pi.single j 1) z" := by
  intro j y z
  apply hasDerivAt_pi.mpr
  intro i
  by_cases h : i = j
  · subst i
    convert! (hasDerivAt_id' z) using 1 <;> simp [WaveMap.insertCoord]
  · simpa [WaveMap.insertCoord, h, Pi.single_eq_of_ne h] using
      (hasDerivAt_const z (y ⟨i,h⟩))

theorem yui_aux_0005 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_T004 : (∀ t : ℝ, 0 < t → ∃ C : Set (WaveMap.X n), ∃ R : ℝ,
    WaveMap.supportGeometry u q t C R ∧ WaveMap.supportSections u t C R) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : WaveMap.X n => WaveMap.density u (x, t))) ∧
  ContinuousOn (WaveMap.density u) (WaveMap.domain n) ∧
  ContinuousOn (WaveMap.densityT u) (WaveMap.domain n)) (h_T008 : ∀ (j : Fin n) (R : ℝ), 0 < R → ∀ f : WaveMap.X n → ℝ,
  IntegrableOn f (WaveMap.box n R) →
  (∫ x in WaveMap.box n R, f x) =
    ∫ y in WaveMap.otherBox j R, ∫ z in Set.Icc (-R) R, f (WaveMap.insertCoord j y z)) : yui_aux_type% "∀ t : ℝ, 0 < t → ∀ j : Fin n,\n  ContDiff ℝ (⊤ : ℕ∞) (fun x : WaveMap.X n => WaveMap.flux u j (x,t)) ∧\n  (∀ (y : WaveMap.Other j → ℝ) (z : ℝ),\n    HasDerivAt (fun r : ℝ => WaveMap.flux u j (WaveMap.insertCoord j y r,t))\n      (WaveMap.fluxDx u j (WaveMap.insertCoord j y z,t)) z)" := by
  intro t ht j
  obtain ⟨ha,hb⟩ := yui_aux_0001 n m u q h_H001 h_H002 h_T004 h_T008 t ht
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun x : WaveMap.X n => WaveMap.flux u j (x,t)) :=
    ha.inner ℝ (hb j)
  refine ⟨hg, ?_⟩
  intro y z
  exact (hg.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt z
    (yui_aux_0004 n m u q h_H001 h_H002 h_T004 h_T008 j y z)

theorem yui_aux_0006 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_T004 : (∀ t : ℝ, 0 < t → ∃ C : Set (WaveMap.X n), ∃ R : ℝ,
    WaveMap.supportGeometry u q t C R ∧ WaveMap.supportSections u t C R) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : WaveMap.X n => WaveMap.density u (x, t))) ∧
  ContinuousOn (WaveMap.density u) (WaveMap.domain n) ∧
  ContinuousOn (WaveMap.densityT u) (WaveMap.domain n)) (h_T008 : ∀ (j : Fin n) (R : ℝ), 0 < R → ∀ f : WaveMap.X n → ℝ,
  IntegrableOn f (WaveMap.box n R) →
  (∫ x in WaveMap.box n R, f x) =
    ∫ y in WaveMap.otherBox j R, ∫ z in Set.Icc (-R) R, f (WaveMap.insertCoord j y z)) : yui_aux_type% "∀ t : ℝ, 0 < t → ∀ (C : Set (WaveMap.X n)) (R : ℝ),\n  WaveMap.supportGeometry u q t C R → WaveMap.supportSections u t C R →\n  ∀ (j : Fin n) (y : WaveMap.Other j → ℝ),\n    (∫ z in Set.Icc (-R) R, WaveMap.fluxDx u j (WaveMap.insertCoord j y z,t)) = 0" := by
  intro t ht C R hg hs j y
  obtain ⟨hti,hzero⟩ := yui_aux_0002 n m u q h_H001 h_H002 h_T004 h_T008 t ht
  have hd := (hs t hti).2.2.2 j
  have hc : Continuous (fun x : WaveMap.X n => WaveMap.fluxDx u j (x,t)) := hd.2.2.1
  have hi : Continuous (WaveMap.insertCoord j y) :=
    continuous_iff_continuousAt.mpr (fun z =>
      (yui_aux_0004 n m u q h_H001 h_H002 h_T004 h_T008 j y z).continuousAt)
  obtain ⟨hgf,hder⟩ := yui_aux_0005 n m u q h_H001 h_H002 h_T004 h_T008 t ht j
  have hend (z : ℝ) (hz : z = R ∨ z = -R) :
      WaveMap.flux u j (WaveMap.insertCoord j y z,t) = 0 := by
    apply hzero C R hg j
    intro hx
    have ho := hg.2.2.1 hx
    have hj := ho j (mem_univ j)
    have hh : -R < z ∧ z < R := by simpa [WaveMap.insertCoord] using hj
    rcases hz with rfl | rfl <;> linarith
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (show -R ≤ R by linarith [hg.2.1])
    (hgf.continuous.comp hi).continuousOn
    (fun z _ => hder y z)
    ((hc.comp hi).intervalIntegrable (-R) R)
  rw [intervalIntegral.integral_of_le (show -R ≤ R by linarith [hg.2.1]),
    ← integral_Icc_eq_integral_Ioc] at he
  simpa [hend R (Or.inl rfl), hend (-R) (Or.inr rfl)] using he

theorem checked (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_T004 : (∀ t : ℝ, 0 < t → ∃ C : Set (WaveMap.X n), ∃ R : ℝ,
    WaveMap.supportGeometry u q t C R ∧ WaveMap.supportSections u t C R) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : WaveMap.X n => WaveMap.density u (x, t))) ∧
  ContinuousOn (WaveMap.density u) (WaveMap.domain n) ∧
  ContinuousOn (WaveMap.densityT u) (WaveMap.domain n)) (h_T008 : ∀ (j : Fin n) (R : ℝ), 0 < R → ∀ f : WaveMap.X n → ℝ,
  IntegrableOn f (WaveMap.box n R) →
  (∫ x in WaveMap.box n R, f x) =
    ∫ y in WaveMap.otherBox j R, ∫ z in Set.Icc (-R) R, f (WaveMap.insertCoord j y z)) : yui_aux_type% "∀ j : Fin n, Continuous (fun p : (WaveMap.Other j → ℝ) × ℝ =>\n    WaveMap.insertCoord j p.1 p.2)" := by
  intro j
  apply continuous_pi
  intro i
  by_cases h : i = j
  · simpa [WaveMap.insertCoord, h] using
      (continuous_snd : Continuous (fun p : (WaveMap.Other j → ℝ) × ℝ => p.2))
  · simpa [WaveMap.insertCoord, h, Function.comp_def] using
      (continuous_apply ⟨i,h⟩).comp
        (continuous_fst : Continuous (fun p : (WaveMap.Other j → ℝ) × ℝ => p.1))
#check @checked
#print axioms checked
end YuiAuxiliary
