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

namespace Translation
set_option autoImplicit false

namespace Local_T001
theorem yui_aux_0001 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_H004 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t → ‖u (x, t)‖ = 1) (h_H005 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t → ∃ a : ℝ, WaveMap.dt (WaveMap.dt u) (x, t) - WaveMap.lap u (x, t) = a • u (x, t)) : yui_aux_type% "∀ x : WaveMap.X n, ∀ t : ℝ, DifferentiableAt ℝ (fun r : ℝ => (x, r)) t" := by
  intro x t
  have hc : DifferentiableAt ℝ (fun _ : ℝ => x) t := differentiableAt_const x
  exact hc.prodMk (differentiableAt_id)

theorem yui_aux_0002 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_H004 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t → ‖u (x, t)‖ = 1) (h_H005 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t → ∃ a : ℝ, WaveMap.dt (WaveMap.dt u) (x, t) - WaveMap.lap u (x, t) = a • u (x, t)) : yui_aux_type% "∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t → HasDerivAt (fun r : ℝ => u (x, r)) (WaveMap.dt u (x, t)) t" := by
  intro x t ht
  have hopen : IsOpen (WaveMap.domain n) := isOpen_lt continuous_const continuous_snd
  have hd : DifferentiableAt ℝ u (x, t) :=
    (h_H002.differentiableOn (by simp)).differentiableAt (hopen.mem_nhds ht)
  exact (hd.comp t (@yui_aux_0001 n m u q h_H001 h_H002 h_H004 h_H005 x t)).hasDerivAt

theorem yui_aux_0003 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_H004 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t → ‖u (x, t)‖ = 1) (h_H005 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t → ∃ a : ℝ, WaveMap.dt (WaveMap.dt u) (x, t) - WaveMap.lap u (x, t) = a • u (x, t)) : yui_aux_type% "∀ x : WaveMap.X n, ∀ t : ℝ, inner ℝ (WaveMap.dt u (x, t)) (u (x, t)) = inner ℝ (u (x, t)) (WaveMap.dt u (x, t))" := by
  intro x t
  exact real_inner_comm (u (x, t)) (WaveMap.dt u (x, t))

end Local_T001
open Local_T001 in
theorem T001 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_H004 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t → ‖u (x, t)‖ = 1) (h_H005 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t → ∃ a : ℝ, WaveMap.dt (WaveMap.dt u) (x, t) - WaveMap.lap u (x, t) = a • u (x, t)) :
    ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t → inner ℝ (u (x, t)) (WaveMap.dt u (x, t)) = 0 ∧ inner ℝ (WaveMap.dt u (x, t)) (WaveMap.dt (WaveMap.dt u) (x, t) - WaveMap.lap u (x, t)) = 0 := by
  intro x t ht
  have hu : HasDerivAt (fun r : ℝ => u (x, r)) (WaveMap.dt u (x, t)) t :=
    @yui_aux_0002 n m u q h_H001 h_H002 h_H004 h_H005 x t ht
  have hprod : HasDerivAt (fun r : ℝ => inner ℝ (u (x, r)) (u (x, r)))
      (inner ℝ (u (x, t)) (WaveMap.dt u (x, t)) +
        inner ℝ (WaveMap.dt u (x, t)) (u (x, t))) t := hu.inner ℝ hu
  have heq : (fun r : ℝ => inner ℝ (u (x, r)) (u (x, r))) =ᶠ[𝓝 t]
      (fun _ : ℝ => (1 : ℝ)) := by
    filter_upwards [eventually_gt_nhds ht] with r hr
    rw [real_inner_self_eq_norm_sq, h_H004 x r hr]
    norm_num
  have hconst : HasDerivAt (fun r : ℝ => inner ℝ (u (x, r)) (u (x, r))) 0 t :=
    (hasDerivAt_const t (1 : ℝ)).congr_of_eventuallyEq heq
  have hsym := @yui_aux_0003 n m u q h_H001 h_H002 h_H004 h_H005 x t
  have hsum := hprod.unique hconst
  have horth : inner ℝ (u (x, t)) (WaveMap.dt u (x, t)) = 0 := by
    rw [hsym] at hsum
    linarith
  refine ⟨horth, ?_⟩
  obtain ⟨a, ha⟩ := h_H005 x t ht
  rw [ha, inner_smul_right, hsym, horth, mul_zero]

namespace Local_T002
theorem yui_aux_0001 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_H004 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t → ‖u (x, t)‖ = 1) (h_H005 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t → ∃ a : ℝ, WaveMap.dt (WaveMap.dt u) (x, t) - WaveMap.lap u (x, t) = a • u (x, t)) (h_T001 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t → inner ℝ (u (x, t)) (WaveMap.dt u (x, t)) = 0 ∧ inner ℝ (WaveMap.dt u (x, t)) (WaveMap.dt (WaveMap.dt u) (x, t) - WaveMap.lap u (x, t)) = 0) : yui_aux_type% "∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (x v : E) (c : ℝ), (fderiv ℝ (fun _ : E => c) x) v = 0" := by
  intro E _ _ x v c
  simp

theorem yui_aux_0002 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_H004 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t → ‖u (x, t)‖ = 1) (h_H005 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t → ∃ a : ℝ, WaveMap.dt (WaveMap.dt u) (x, t) - WaveMap.lap u (x, t) = a • u (x, t)) (h_T001 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t → inner ℝ (u (x, t)) (WaveMap.dt u (x, t)) = 0 ∧ inner ℝ (WaveMap.dt u (x, t)) (WaveMap.dt (WaveMap.dt u) (x, t) - WaveMap.lap u (x, t)) = 0) : yui_aux_type% "∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → WaveMap.V m) (s : Set E), IsOpen s → ContDiffOn ℝ 2 f s → (∀ y ∈ s, ‖f y‖ = 1) → ∀ x ∈ s, ∀ v : E, inner ℝ (f x) (fderiv ℝ (fun y => fderiv ℝ f y v) x v) = - ‖fderiv ℝ f x v‖ ^ 2" := by
  intro E _ _ f s hs hf hn
  have hd (y : E) (hy : y ∈ s) : DifferentiableAt ℝ f y :=
    (hf.contDiffAt (hs.mem_nhds hy)).differentiableAt (by norm_num)
  have hfirst (y : E) (hy : y ∈ s) (v : E) :
      inner ℝ (f y) (fderiv ℝ f y v) = 0 := by
    have he : (fun z => inner ℝ (f z) (f z)) =ᶠ[𝓝 y] (fun _ => (1 : ℝ)) := by
      filter_upwards [hs.mem_nhds hy] with z hz
      rw [real_inner_self_eq_norm_sq, hn z hz]
      norm_num
    have hh := congrArg (fun L : E →L[ℝ] ℝ => L v) (he.fderiv_eq (𝕜 := ℝ))
    rw [fderiv_inner_apply ℝ (hd y hy) (hd y hy),
      yui_aux_0001 n m u q h_H001 h_H002 h_H004 h_H005 h_T001 E y v 1] at hh
    have hc : inner ℝ (f y) (fderiv ℝ f y v) = inner ℝ (fderiv ℝ f y v) (f y) := real_inner_comm _ _
    linarith
  intro x hx v
  have hg : ContDiffOn ℝ 1 (fun y => fderiv ℝ f y v) s :=
    (hf.fderiv_of_isOpen hs (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply contDiffOn_const
  have he : (fun y => inner ℝ (f y) (fderiv ℝ f y v)) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [hs.mem_nhds hx] with y hy using hfirst y hy v
  have hh := congrArg (fun L : E →L[ℝ] ℝ => L v) (he.fderiv_eq (𝕜 := ℝ))
  rw [fderiv_inner_apply ℝ (hd x hx) ((hg.contDiffAt (hs.mem_nhds hx)).differentiableAt (by norm_num)),
    yui_aux_0001 n m u q h_H001 h_H002 h_H004 h_H005 h_T001 E x v 0,
    real_inner_self_eq_norm_sq] at hh
  linarith

theorem yui_aux_0003 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_H004 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t → ‖u (x, t)‖ = 1) (h_H005 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t → ∃ a : ℝ, WaveMap.dt (WaveMap.dt u) (x, t) - WaveMap.lap u (x, t) = a • u (x, t)) (h_T001 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t → inner ℝ (u (x, t)) (WaveMap.dt u (x, t)) = 0 ∧ inner ℝ (WaveMap.dt u (x, t)) (WaveMap.dt (WaveMap.dt u) (x, t) - WaveMap.lap u (x, t)) = 0) : yui_aux_type% "(2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)" := by
  change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
  exact WithTop.coe_le_coe.mpr le_top

theorem yui_aux_0004 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_H004 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t → ‖u (x, t)‖ = 1) (h_H005 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t → ∃ a : ℝ, WaveMap.dt (WaveMap.dt u) (x, t) - WaveMap.lap u (x, t) = a • u (x, t)) (h_T001 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t → inner ℝ (u (x, t)) (WaveMap.dt u (x, t)) = 0 ∧ inner ℝ (WaveMap.dt u (x, t)) (WaveMap.dt (WaveMap.dt u) (x, t) - WaveMap.lap u (x, t)) = 0) : yui_aux_type% "∀ (x : WaveMap.X n) (t : ℝ), 0 < t → (inner ℝ (u (x,t)) (WaveMap.dt (WaveMap.dt u) (x,t)) = - ‖WaveMap.dt u (x,t)‖ ^ 2) ∧ (∀ j : Fin n, inner ℝ (u (x,t)) (WaveMap.dx (WaveMap.dx u j) j (x,t)) = - ‖WaveMap.dx u j (x,t)‖ ^ 2)" := by
  intro x t ht
  have hu : ContDiffOn ℝ 2 u (WaveMap.domain n) :=
    h_H002.of_le (yui_aux_0003 n m u q h_H001 h_H002 h_H004 h_H005 h_T001)
  have htime : ContDiffOn ℝ 2 (fun r : ℝ => u (x,r)) (Ioi 0) :=
    hu.comp (contDiff_const.prodMk contDiff_id).contDiffOn (by intro r hr; exact hr)
  have hspace : ContDiffOn ℝ 2 (fun y : WaveMap.X n => u (y,t)) univ :=
    hu.comp (contDiff_id.prodMk contDiff_const).contDiffOn (by intro y hy; exact ht)
  constructor
  · have h := yui_aux_0002 n m u q h_H001 h_H002 h_H004 h_H005 h_T001
      ℝ (fun r : ℝ => u (x,r)) (Ioi 0) isOpen_Ioi htime
      (by intro r hr; exact h_H004 x r hr) t ht 1
    simpa only [fderiv_apply_one_eq_deriv, WaveMap.dt] using h
  · intro j
    have h := yui_aux_0002 n m u q h_H001 h_H002 h_H004 h_H005 h_T001
      (WaveMap.X n) (fun y : WaveMap.X n => u (y,t)) univ isOpen_univ hspace
      (by intro y hy; exact h_H004 y t ht) x (mem_univ x) (Pi.single j 1)
    simpa only [WaveMap.dx] using h

end Local_T002
open Local_T002 in
theorem T002 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_H004 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t → ‖u (x, t)‖ = 1) (h_H005 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t → ∃ a : ℝ, WaveMap.dt (WaveMap.dt u) (x, t) - WaveMap.lap u (x, t) = a • u (x, t)) (h_T001 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t → inner ℝ (u (x, t)) (WaveMap.dt u (x, t)) = 0 ∧ inner ℝ (WaveMap.dt u (x, t)) (WaveMap.dt (WaveMap.dt u) (x, t) - WaveMap.lap u (x, t)) = 0) :
    ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t →
  (inner ℝ (u (x, t)) (WaveMap.dt u (x, t)) = 0 ∧
   inner ℝ (WaveMap.dt u (x, t)) (WaveMap.dt (WaveMap.dt u) (x, t) - WaveMap.lap u (x, t)) = 0) ∧
  (∀ a : ℝ, WaveMap.dt (WaveMap.dt u) (x, t) - WaveMap.lap u (x, t) = a • u (x, t) →
    a = (∑ j : Fin n, ‖WaveMap.dx u j (x, t)‖ ^ 2) - ‖WaveMap.dt u (x, t)‖ ^ 2) ∧
  WaveMap.dt (WaveMap.dt u) (x, t) - WaveMap.lap u (x, t) =
    ((∑ j : Fin n, ‖WaveMap.dx u j (x, t)‖ ^ 2) - ‖WaveMap.dt u (x, t)‖ ^ 2) • u (x, t) := by
  intro x t ht
  refine ⟨h_T001 x t ht, ?_⟩
  have hd := yui_aux_0004 n m u q h_H001 h_H002 h_H004 h_H005 h_T001 x t ht
  have hcoeff : ∀ a : ℝ,
      WaveMap.dt (WaveMap.dt u) (x,t) - WaveMap.lap u (x,t) = a • u (x,t) →
      a = (∑ j : Fin n, ‖WaveMap.dx u j (x,t)‖ ^ 2) - ‖WaveMap.dt u (x,t)‖ ^ 2 := by
    intro a ha
    have hh := congrArg (fun v : WaveMap.V m => inner ℝ (u (x,t)) v) ha
    simp only [inner_sub_right, WaveMap.lap, inner_sum, hd.1, hd.2,
      Finset.sum_neg_distrib, inner_smul_right, real_inner_self_eq_norm_sq,
      h_H004 x t ht, one_pow, mul_one] at hh
    linarith
  refine ⟨hcoeff, ?_⟩
  obtain ⟨a, ha⟩ := h_H005 x t ht
  rw [← hcoeff a ha]
  exact ha

namespace Local_T003
theorem yui_aux_0001 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_H006 : ∀ s t : ℝ, 0 < s → s < t → ∃ C : Set (WaveMap.X n), IsCompact C ∧ ∀ x : WaveMap.X n, x ∉ C → ∀ r ∈ Set.Icc s t, u (x, r) = q) : yui_aux_type% "∀ R : ℝ, 0 < R → volume (WaveMap.box n R) = ENNReal.ofReal ((2 * R) ^ n)" := by
  intro R hR
  have hp : ENNReal.ofReal ((2 * R) ^ n) = (ENNReal.ofReal (2 * R)) ^ n :=
    ENNReal.ofReal_pow (by positivity) n
  unfold WaveMap.box
  rw [volume_pi_pi]
  simp only [Real.volume_Icc, sub_neg_eq_add, ← two_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact hp.symm

end Local_T003
open Local_T003 in
theorem T003 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_H006 : ∀ s t : ℝ, 0 < s → s < t → ∃ C : Set (WaveMap.X n), IsCompact C ∧ ∀ x : WaveMap.X n, x ∉ C → ∀ r ∈ Set.Icc s t, u (x, r) = q) :
    ∀ t : ℝ, 0 < t → ∃ C : Set (WaveMap.X n), ∃ R : ℝ, WaveMap.supportGeometry u q t C R := by
  intro t ht
  obtain ⟨C, hC, hu⟩ := h_H006 (t / 2) (3 * t / 2) (by linarith) (by linarith)
  obtain ⟨R, hR, hbound⟩ := hC.isBounded.exists_pos_norm_lt
  have hbox : C ⊆ WaveMap.openBox n R := by
    intro x hx
    change ∀ j ∈ (Set.univ : Set (Fin n)), x j ∈ Set.Ioo (-R) R
    intro j hj
    have hjbound : |x j| < R := by
      simpa only [Real.norm_eq_abs] using (norm_le_pi_norm x j).trans_lt (hbound x hx)
    exact abs_lt.mp hjbound
  have hvol : volume (WaveMap.box n R) = ENNReal.ofReal ((2 * R) ^ n) :=
    yui_aux_0001 n m u q h_H001 h_H002 h_H006 R hR
  refine ⟨C, R, hC, hR, hbox, ?_, hvol, ?_, ?_⟩
  · intro x hx r hr
    exact hu x hx r hr
  · rw [hvol]
    exact ENNReal.ofReal_lt_top
  · intro k x hx r hr
    have hU : IsOpen ((Cᶜ) ×ˢ interior (WaveMap.slab t)) :=
      hC.isClosed.isOpen_compl.prod isOpen_interior
    have hmem : (x, r) ∈ (Cᶜ) ×ˢ interior (WaveMap.slab t) := ⟨hx, hr⟩
    have heq : u =ᶠ[𝓝 (x, r)] (fun _ => q) := by
      filter_upwards [hU.mem_nhds hmem] with p hp
      exact hu p.1 hp.1 p.2 (interior_subset hp.2)
    have hder := (heq.iteratedFDeriv ℝ (k + 1)).self_of_nhds
    rw [hder, iteratedFDeriv_succ_const]
    rfl

namespace Local_T004
theorem yui_aux_0001 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_T003 : ∀ t : ℝ, 0 < t → ∃ C : Set (WaveMap.X n), ∃ R : ℝ, WaveMap.supportGeometry u q t C R) : yui_aux_type% "∀ (F : Type) (inst : NormedAddCommGroup F) (inst' : NormedSpace ℝ F) (f : WaveMap.X n × ℝ → F), ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (WaveMap.domain n) → (ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : WaveMap.X n × ℝ => deriv (fun r : ℝ => f (p.1, r)) p.2) (WaveMap.domain n)) ∧ (∀ j : Fin n, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : WaveMap.X n × ℝ => fderiv ℝ (fun x : WaveMap.X n => f (x, p.2)) p.1 (Pi.single j 1)) (WaveMap.domain n))" := by
  intro F inst inst' f hf
  have ho : IsOpen (WaveMap.domain n) := isOpen_lt continuous_const continuous_snd
  have hd := (contDiffOn_infty_iff_fderiv_of_isOpen ho).mp hf
  have hD (v : WaveMap.X n × ℝ) : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p => fderiv ℝ f p v) (WaveMap.domain n) :=
    hd.2.clm_apply contDiffOn_const
  constructor
  · refine (hD (0, 1)).congr ?_
    intro p hp
    have hfp := (hd.1 p hp).differentiableAt (ho.mem_nhds hp)
    have hi : HasDerivAt (fun r : ℝ => (p.1, r)) (0, 1) p.2 :=
      (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
    exact (hfp.hasFDerivAt.comp_hasDerivAt p.2 hi).deriv
  · intro j
    refine (hD (Pi.single j 1, 0)).congr ?_
    intro p hp
    have hfp := (hd.1 p hp).differentiableAt (ho.mem_nhds hp)
    have hi : HasFDerivAt (fun x : WaveMap.X n => (x, p.2))
        ((ContinuousLinearMap.id ℝ (WaveMap.X n)).prod 0) p.1 :=
      (hasFDerivAt_id p.1).prodMk (hasFDerivAt_const p.2 p.1)
    have he := (hfp.hasFDerivAt.comp p.1 hi).fderiv
    change fderiv ℝ (fun x : WaveMap.X n => f (x, p.2)) p.1 (Pi.single j 1) = _
    exact congrArg (fun L : WaveMap.X n →L[ℝ] F => L (Pi.single j 1)) he

theorem yui_aux_0002 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_T003 : ∀ t : ℝ, 0 < t → ∃ C : Set (WaveMap.X n), ∃ R : ℝ, WaveMap.supportGeometry u q t C R) : yui_aux_type% "ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p => ‖u p‖ ^ 2) (WaveMap.domain n)" := by
  exact h_H002.norm_sq ℝ

theorem yui_aux_0003 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_T003 : ∀ t : ℝ, 0 < t → ∃ C : Set (WaveMap.X n), ∃ R : ℝ, WaveMap.supportGeometry u q t C R) : yui_aux_type% "ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (WaveMap.density u) (WaveMap.domain n) ∧\nContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (WaveMap.densityT u) (WaveMap.domain n) ∧\nContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (WaveMap.timeProduct u) (WaveMap.domain n) ∧\n∀ j : Fin n, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (WaveMap.mixedProduct u j) (WaveMap.domain n) ∧\nContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (WaveMap.lapProduct u j) (WaveMap.domain n) ∧\nContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (WaveMap.fluxDx u j) (WaveMap.domain n)" := by
  have parts := @yui_aux_0001 n m u q h_H001 h_H002 h_T003
  have ht : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (WaveMap.dt u) (WaveMap.domain n) :=
    (parts (WaveMap.V m) inferInstance inferInstance u h_H002).1
  have hx (j : Fin n) : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (WaveMap.dx u j) (WaveMap.domain n) :=
    (parts (WaveMap.V m) inferInstance inferInstance u h_H002).2 j
  have htt : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (WaveMap.dt (WaveMap.dt u)) (WaveMap.domain n) :=
    (parts (WaveMap.V m) inferInstance inferInstance _ ht).1
  have hxt (j : Fin n) : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (WaveMap.dx (WaveMap.dt u) j) (WaveMap.domain n) :=
    (parts (WaveMap.V m) inferInstance inferInstance _ ht).2 j
  have hxx (j : Fin n) : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (WaveMap.dx (WaveMap.dx u j) j) (WaveMap.domain n) :=
    (parts (WaveMap.V m) inferInstance inferInstance _ (hx j)).2 j
  have he : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (WaveMap.density u) (WaveMap.domain n) :=
    (ht.norm_sq ℝ).add (ContDiffOn.sum (fun j _ => (hx j).norm_sq ℝ))
  refine ⟨he, (parts ℝ inferInstance inferInstance _ he).1, ht.inner ℝ htt, ?_⟩
  intro j
  exact ⟨(hx j).inner ℝ (hxt j), ht.inner ℝ (hxx j),
    (parts ℝ inferInstance inferInstance (WaveMap.flux u j) (ht.inner ℝ (hx j))).2 j⟩

theorem yui_aux_0004 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_T003 : ∀ t : ℝ, 0 < t → ∃ C : Set (WaveMap.X n), ∃ R : ℝ, WaveMap.supportGeometry u q t C R) : yui_aux_type% "∀ (F : Type) (inst : NormedAddCommGroup F) (inst' : NormedSpace ℝ F)\n(f : WaveMap.X n × ℝ → F) (A : Set (WaveMap.X n)) (I : Set ℝ) (c : F),\nIsOpen A → IsOpen I → (∀ x ∈ A, ∀ r ∈ I, f (x,r) = c) →\n∀ x ∈ A, ∀ r ∈ I,\nderiv (fun s : ℝ => f (x,s)) r = 0 ∧\n∀ j : Fin n, fderiv ℝ (fun y : WaveMap.X n => f (y,r)) x (Pi.single j 1) = 0" := by
  intro F inst inst' f A I c hA hI hf x hx r hr
  constructor
  · have he : (fun s : ℝ => f (x,s)) =ᶠ[𝓝 r] (fun _ => c) :=
      Filter.eventually_of_mem (hI.mem_nhds hr) (fun s hs => hf x hx s hs)
    rw [he.deriv_eq, deriv_const]
  · have he : (fun y : WaveMap.X n => f (y,r)) =ᶠ[𝓝 x] (fun _ => c) :=
      Filter.eventually_of_mem (hA.mem_nhds hx) (fun y hy => hf y hy r hr)
    intro j
    rw [he.fderiv_eq]
    simp

theorem yui_aux_0005 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_T003 : ∀ t : ℝ, 0 < t → ∃ C : Set (WaveMap.X n), ∃ R : ℝ, WaveMap.supportGeometry u q t C R) : yui_aux_type% "∀ (t : ℝ) (C : Set (WaveMap.X n)) (R : ℝ),\nWaveMap.supportGeometry u q t C R →\n∀ r ∈ interior (WaveMap.slab t), ∀ x, x ∉ C →\nWaveMap.density u (x,r) = 0 ∧\nWaveMap.densityT u (x,r) = 0 ∧\nWaveMap.timeProduct u (x,r) = 0 ∧\n∀ j : Fin n, WaveMap.mixedProduct u j (x,r) = 0 ∧\nWaveMap.lapProduct u j (x,r) = 0 ∧\nWaveMap.fluxDx u j (x,r) = 0" := by
  intro t C R hg
  have ho : IsOpen Cᶜ := hg.1.isClosed.isOpen_compl
  have hz := @yui_aux_0004 n m u q h_H001 h_H002 h_T003
  have hu : ∀ x ∈ Cᶜ, ∀ r ∈ interior (WaveMap.slab t), u (x,r) = q :=
    fun x hx r hr => hg.2.2.2.1 x hx r (interior_subset hr)
  have ht (x) (hx : x ∉ C) (r) (hr : r ∈ interior (WaveMap.slab t)) :
      WaveMap.dt u (x,r) = 0 :=
    (hz (WaveMap.V m) inferInstance inferInstance u Cᶜ _ q ho isOpen_interior hu x hx r hr).1
  have hx (x) (hx : x ∉ C) (r) (hr : r ∈ interior (WaveMap.slab t)) (j : Fin n) :
      WaveMap.dx u j (x,r) = 0 :=
    (hz (WaveMap.V m) inferInstance inferInstance u Cᶜ _ q ho isOpen_interior hu x hx r hr).2 j
  have he : ∀ x ∈ Cᶜ, ∀ r ∈ interior (WaveMap.slab t), WaveMap.density u (x,r) = 0 := by
    intro x hxc r hr
    simp [WaveMap.density, ht x hxc r hr, hx x hxc r hr]
  have hf (j : Fin n) : ∀ x ∈ Cᶜ, ∀ r ∈ interior (WaveMap.slab t),
      WaveMap.flux u j (x,r) = 0 := by
    intro x hxc r hr
    simp [WaveMap.flux, ht x hxc r hr]
  intro r hr x hxc
  refine ⟨he x hxc r hr, ?_, ?_, ?_⟩
  · exact (hz ℝ inferInstance inferInstance (WaveMap.density u) Cᶜ _ 0 ho isOpen_interior he x hxc r hr).1
  · simp [WaveMap.timeProduct, ht x hxc r hr]
  · intro j
    refine ⟨?_, ?_, ?_⟩
    · simp [WaveMap.mixedProduct, hx x hxc r hr]
    · simp [WaveMap.lapProduct, ht x hxc r hr]
    · exact (hz ℝ inferInstance inferInstance (WaveMap.flux u j) Cᶜ _ 0 ho isOpen_interior (hf j) x hxc r hr).2 j

theorem yui_aux_0006 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_T003 : ∀ t : ℝ, 0 < t → ∃ C : Set (WaveMap.X n), ∃ R : ℝ, WaveMap.supportGeometry u q t C R) : yui_aux_type% "∀ (C : Set (WaveMap.X n)) (R : ℝ) (f : WaveMap.X n → ℝ),\nC ⊆ WaveMap.box n R → volume (WaveMap.box n R) < ⊤ →\nContinuous f → (∀ x, x ∉ C → f x = 0) → WaveMap.sectionGood C R f" := by
  intro C R f hC hvol hf hz
  have hQ : IsCompact (WaveMap.box n R) := isCompact_univ_pi (fun _ => isCompact_Icc)
  obtain ⟨B, hB⟩ := hQ.exists_bound_of_continuousOn hf.continuousOn
  have hb : ∀ x ∈ WaveMap.box n R, |f x| ≤ max B 0 := by
    intro x hx
    have hbx : |f x| ≤ B := by simpa only [Real.norm_eq_abs] using hB x hx
    exact hbx.trans (le_max_left B 0)
  refine ⟨hf, hz, ⟨max B 0, le_max_right B 0, hb⟩, ?_⟩
  have hi : Integrable ((WaveMap.box n R).indicator (fun _ : WaveMap.X n => max B 0)) := by
    apply IntegrableOn.integrable_indicator _ hQ.measurableSet
    exact integrableOn_const hvol.ne
  apply hi.mono' hf.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  by_cases hx : x ∈ WaveMap.box n R
  · simpa only [Set.indicator_of_mem hx, Real.norm_eq_abs] using hb x hx
  · have hxc : x ∉ C := fun hc => hx (hC hc)
    simp [Set.indicator_of_notMem hx, hz x hxc]

theorem yui_aux_0007 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_T003 : ∀ t : ℝ, 0 < t → ∃ C : Set (WaveMap.X n), ∃ R : ℝ, WaveMap.supportGeometry u q t C R) : yui_aux_type% "∀ t : ℝ, 0 < t → ∀ (C : Set (WaveMap.X n)) (R : ℝ), WaveMap.supportGeometry u q t C R → WaveMap.supportSections u t C R" := by
  intro t ht C R hg r hr
  have hs := @yui_aux_0003 n m u q h_H001 h_H002 h_T003
  have hz := @yui_aux_0005 n m u q h_H001 h_H002 h_T003 t C R hg r hr
  have hC : C ⊆ WaveMap.box n R := by
    intro x hx
    have hxo := hg.2.2.1 hx
    intro j hj
    exact ⟨(hxo j hj).1.le, (hxo j hj).2.le⟩
  have hp : 0 < r := by
    have hh := (interior_subset hr).1
    linarith
  have hcont (f : WaveMap.X n × ℝ → ℝ) (hc : ContinuousOn f (WaveMap.domain n)) :
      Continuous (fun x : WaveMap.X n => f (x,r)) :=
    hc.comp_continuous (continuous_id.prodMk continuous_const) (fun _ => hp)
  have good (f : WaveMap.X n × ℝ → ℝ) (hc : ContinuousOn f (WaveMap.domain n))
      (hf : ∀ x, x ∉ C → f (x,r) = 0) :
      WaveMap.sectionGood C R (fun x => f (x,r)) :=
    @yui_aux_0006 n m u q h_H001 h_H002 h_T003 C R _ hC hg.2.2.2.2.2.1 (hcont f hc) hf
  refine ⟨good _ hs.1.continuousOn (fun x hx => (hz x hx).1),
    good _ hs.2.1.continuousOn (fun x hx => (hz x hx).2.1),
    good _ hs.2.2.1.continuousOn (fun x hx => (hz x hx).2.2.1), ?_⟩
  intro j
  exact ⟨good _ (hs.2.2.2 j).1.continuousOn (fun x hx => ((hz x hx).2.2.2 j).1),
    good _ (hs.2.2.2 j).2.1.continuousOn (fun x hx => ((hz x hx).2.2.2 j).2.1),
    good _ (hs.2.2.2 j).2.2.continuousOn (fun x hx => ((hz x hx).2.2.2 j).2.2)⟩

end Local_T004
open Local_T004 in
theorem T004 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_T003 : ∀ t : ℝ, 0 < t → ∃ C : Set (WaveMap.X n), ∃ R : ℝ, WaveMap.supportGeometry u q t C R) :
    (∀ t : ℝ, 0 < t → ∃ C : Set (WaveMap.X n), ∃ R : ℝ,
    WaveMap.supportGeometry u q t C R ∧ WaveMap.supportSections u t C R) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : WaveMap.X n => WaveMap.density u (x, t))) ∧
  ContinuousOn (WaveMap.density u) (WaveMap.domain n) ∧
  ContinuousOn (WaveMap.densityT u) (WaveMap.domain n) := by
  have hs := @yui_aux_0003 n m u q h_H001 h_H002 h_T003
  have hall : ∀ t : ℝ, 0 < t → ∃ C : Set (WaveMap.X n), ∃ R : ℝ,
      WaveMap.supportGeometry u q t C R ∧ WaveMap.supportSections u t C R := by
    intro t ht
    obtain ⟨C, R, hg⟩ := h_T003 t ht
    exact ⟨C, R, hg, @yui_aux_0007 n m u q h_H001 h_H002 h_T003 t ht C R hg⟩
  refine ⟨hall, ?_, hs.1.continuousOn, hs.2.1.continuousOn⟩
  intro t ht
  obtain ⟨C, R, hg, hsec⟩ := hall t ht
  have hti : t ∈ interior (WaveMap.slab t) := by
    rw [WaveMap.slab, interior_Icc]
    constructor <;> linarith
  exact (hsec t hti).1.2.2.2

namespace Local_T005
theorem yui_aux_0001 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) : yui_aux_type% "∀ (f : WaveMap.X n × ℝ → WaveMap.V m) (p : WaveMap.X n × ℝ), DifferentiableAt ℝ f p → WaveMap.dt f p = fderiv ℝ f p (0, 1) ∧ ∀ j : Fin n, WaveMap.dx f j p = fderiv ℝ f p (Pi.single j 1, 0)" := by
  intro f p hf
  have ht : HasFDerivAt (fun r : ℝ => (p.1, r)) ((0 : ℝ →L[ℝ] WaveMap.X n).prod (ContinuousLinearMap.id ℝ ℝ)) p.2 := (hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2)
  have hx : HasFDerivAt (fun x : WaveMap.X n => (x, p.2)) ((ContinuousLinearMap.id ℝ (WaveMap.X n)).prod (0 : WaveMap.X n →L[ℝ] ℝ)) p.1 := (hasFDerivAt_id p.1).prodMk (hasFDerivAt_const p.2 p.1)
  constructor
  · have h := hf.hasFDerivAt.comp p.2 ht
    simpa [WaveMap.dt, Function.comp_def] using h.hasDerivAt.deriv
  · intro j
    have h := hf.hasFDerivAt.comp p.1 hx
    simpa [WaveMap.dx, Function.comp_def] using congrArg (fun L : WaveMap.X n →L[ℝ] WaveMap.V m => L (Pi.single j 1)) h.fderiv

theorem yui_aux_0002 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) : yui_aux_type% "∀ p : WaveMap.X n × ℝ, 0 < p.2 → ContDiffAt ℝ 2 u p" := by
  intro p hp
  have ho : IsOpen (WaveMap.domain n) := isOpen_lt continuous_const continuous_snd
  exact (h_H002.contDiffAt (ho.mem_nhds hp)).of_le (show (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from WithTop.coe_le_coe.mpr le_top)

theorem yui_aux_0003 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) : yui_aux_type% "∀ p : WaveMap.X n × ℝ, 0 < p.2 → HasFDerivAt (WaveMap.dt u) ((fderiv ℝ (fderiv ℝ u) p).flip (0, 1)) p ∧ ∀ j : Fin n, HasFDerivAt (WaveMap.dx u j) ((fderiv ℝ (fderiv ℝ u) p).flip (Pi.single j 1, 0)) p" := by
  intro p hp
  have hs := @yui_aux_0002 n m u q h_H001 h_H002 p hp
  have hd : HasFDerivAt (fderiv ℝ u) (fderiv ℝ (fderiv ℝ u) p) p := ((hs.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
  have hv (v : WaveMap.X n × ℝ) : HasFDerivAt (fun z => fderiv ℝ u z v) ((fderiv ℝ (fderiv ℝ u) p).flip v) p := by
    simpa using hd.clm_apply (hasFDerivAt_const v p)
  have ho : IsOpen (WaveMap.domain n) := isOpen_lt continuous_const continuous_snd
  have he : ∀ᶠ z in 𝓝 p, WaveMap.dt u z = fderiv ℝ u z (0, 1) ∧ ∀ j : Fin n, WaveMap.dx u j z = fderiv ℝ u z (Pi.single j 1, 0) := by
    filter_upwards [ho.mem_nhds hp] with z hz
    exact @yui_aux_0001 n m u q h_H001 h_H002 u z ((@yui_aux_0002 n m u q h_H001 h_H002 z hz).differentiableAt two_ne_zero)
  constructor
  · exact (hv (0, 1)).congr_of_eventuallyEq (he.mono fun z hz => hz.1)
  · intro j
    exact (hv (Pi.single j 1, 0)).congr_of_eventuallyEq (he.mono fun z hz => hz.2 j)

theorem yui_aux_0004 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) : yui_aux_type% "∀ (x : WaveMap.X n) (t : ℝ), 0 < t → HasDerivAt (fun r => WaveMap.dt u (x, r)) (WaveMap.dt (WaveMap.dt u) (x, t)) t ∧ ∀ j : Fin n, HasDerivAt (fun r => WaveMap.dx u j (x, r)) (WaveMap.dx (WaveMap.dt u) j (x, t)) t" := by
  intro x t ht
  have hd := @yui_aux_0003 n m u q h_H001 h_H002 (x, t) ht
  have hi : HasFDerivAt (fun r : ℝ => (x, r)) ((0 : ℝ →L[ℝ] WaveMap.X n).prod (ContinuousLinearMap.id ℝ ℝ)) t := (hasFDerivAt_const x t).prodMk (hasFDerivAt_id t)
  constructor
  · have h : DifferentiableAt ℝ (fun r => WaveMap.dt u (x, r)) t := by
      simpa [Function.comp_def] using (hd.1.comp t hi).differentiableAt
    exact h.hasDerivAt
  · intro j
    have he := (@yui_aux_0001 n m u q h_H001 h_H002 (WaveMap.dt u) (x, t) hd.1.differentiableAt).2 j
    rw [hd.1.fderiv] at he
    have hs := (@yui_aux_0002 n m u q h_H001 h_H002 (x, t) ht).isSymmSndFDerivAt (by simp)
    have he' : WaveMap.dx (WaveMap.dt u) j (x, t) = fderiv ℝ (fderiv ℝ u) (x, t) (0, 1) (Pi.single j 1, 0) := by
      simpa using he.trans (hs (Pi.single j 1, 0) (0, 1))
    rw [he']
    simpa [Function.comp_def] using (hd.2 j |>.comp t hi).hasDerivAt

theorem yui_aux_0005 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) : yui_aux_type% "∀ (x : WaveMap.X n) (t : ℝ), 0 < t → HasDerivAt (fun r : ℝ => WaveMap.density u (x, r)) (2 * WaveMap.timeProduct u (x, t) + 2 * ∑ j : Fin n, WaveMap.mixedProduct u j (x, t)) t" := by
  intro x t ht
  have hd := @yui_aux_0004 n m u q h_H001 h_H002 x t ht
  convert! hd.1.norm_sq.add (HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => (hd.2 j).norm_sq)) using 1 <;>
    simp [WaveMap.density, WaveMap.timeProduct, WaveMap.mixedProduct, Finset.mul_sum]

end Local_T005
open Local_T005 in
theorem T005 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) :
    ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t →
  HasDerivAt (fun r : ℝ => WaveMap.density u (x, r)) (WaveMap.densityT u (x, t)) t ∧
  WaveMap.densityT u (x, t) =
    2 * WaveMap.timeProduct u (x, t) + 2 * ∑ j : Fin n, WaveMap.mixedProduct u j (x, t) := by
  intro x t ht
  have h := @yui_aux_0005 n m u q h_H001 h_H002 x t ht
  have he : WaveMap.densityT u (x, t) =
      2 * WaveMap.timeProduct u (x, t) + 2 * ∑ j : Fin n, WaveMap.mixedProduct u j (x, t) := h.deriv
  constructor
  · rw [he]
    exact h
  · exact he

namespace Local_T006
theorem yui_aux_0001 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_T004 : (∀ t : ℝ, 0 < t → ∃ C : Set (WaveMap.X n), ∃ R : ℝ,
    WaveMap.supportGeometry u q t C R ∧ WaveMap.supportSections u t C R) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : WaveMap.X n => WaveMap.density u (x, t))) ∧
  ContinuousOn (WaveMap.density u) (WaveMap.domain n) ∧
  ContinuousOn (WaveMap.densityT u) (WaveMap.domain n)) (h_T005 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t →
  HasDerivAt (fun r : ℝ => WaveMap.density u (x, r)) (WaveMap.densityT u (x, t)) t ∧
  WaveMap.densityT u (x, t) =
    2 * WaveMap.timeProduct u (x, t) + 2 * ∑ j : Fin n, WaveMap.mixedProduct u j (x, t)) : yui_aux_type% "∀ (t h : ℝ), 0 < t → 0 < |h| → |h| < t / 4 → ∀ x : WaveMap.X n, ∃ c ∈ Set.Icc (t - t / 4) (t + t / 4), WaveMap.quotient u t h x = WaveMap.densityT u (x, c)" := by
  intro t h ht hh hsmall x
  have habs := abs_lt.mp hsmall
  have hder : ∀ r ∈ Set.Icc (t - t / 4) (t + t / 4),
      HasDerivAt (fun s : ℝ => WaveMap.density u (x, s))
        (WaveMap.densityT u (x, r)) r := by
    intro r hr
    exact (h_T005 x r (by linarith [hr.1])).1
  have hcont : ContinuousOn (fun r : ℝ => WaveMap.density u (x, r))
      (Set.Icc (t - t / 4) (t + t / 4)) := by
    intro r hr
    exact (hder r hr).continuousAt.continuousWithinAt
  have hn : h ≠ 0 := by
    intro heq
    simpa [heq] using hh
  rcases lt_or_gt_of_ne hn with hneg | hpos
  · have hsub : Set.Icc (t + h) t ⊆ Set.Icc (t - t / 4) (t + t / 4) := by
      intro r hr
      exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
    obtain ⟨c, hc, heq⟩ := exists_hasDerivAt_eq_slope
      (fun r : ℝ => WaveMap.density u (x, r))
      (fun r : ℝ => WaveMap.densityT u (x, r))
      (show t + h < t by linarith)
      (hcont.mono hsub)
      (fun r hr => hder r (hsub ⟨le_of_lt hr.1, le_of_lt hr.2⟩))
    refine ⟨c, hsub ⟨le_of_lt hc.1, le_of_lt hc.2⟩, ?_⟩
    rw [heq]
    unfold WaveMap.quotient
    have hden : t - (t + h) = -h := by ring
    rw [hden]
    rw [div_neg, ← neg_div, neg_sub]
  · have hsub : Set.Icc t (t + h) ⊆ Set.Icc (t - t / 4) (t + t / 4) := by
      intro r hr
      exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
    obtain ⟨c, hc, heq⟩ := exists_hasDerivAt_eq_slope
      (fun r : ℝ => WaveMap.density u (x, r))
      (fun r : ℝ => WaveMap.densityT u (x, r))
      (show t < t + h by linarith)
      (hcont.mono hsub)
      (fun r hr => hder r (hsub ⟨le_of_lt hr.1, le_of_lt hr.2⟩))
    refine ⟨c, hsub ⟨le_of_lt hc.1, le_of_lt hc.2⟩, ?_⟩
    simpa [WaveMap.quotient] using heq.symm

end Local_T006
open Local_T006 in
theorem T006 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_T004 : (∀ t : ℝ, 0 < t → ∃ C : Set (WaveMap.X n), ∃ R : ℝ,
    WaveMap.supportGeometry u q t C R ∧ WaveMap.supportSections u t C R) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : WaveMap.X n => WaveMap.density u (x, t))) ∧
  ContinuousOn (WaveMap.density u) (WaveMap.domain n) ∧
  ContinuousOn (WaveMap.densityT u) (WaveMap.domain n)) (h_T005 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t →
  HasDerivAt (fun r : ℝ => WaveMap.density u (x, r)) (WaveMap.densityT u (x, t)) t ∧
  WaveMap.densityT u (x, t) =
    2 * WaveMap.timeProduct u (x, t) + 2 * ∑ j : Fin n, WaveMap.mixedProduct u j (x, t)) :
    ∀ t : ℝ, 0 < t → ∃ η B R : ℝ,
  0 < η ∧ 0 ≤ B ∧ 0 < R ∧ η < t ∧
  Integrable ((WaveMap.box n R).indicator (fun _ => B)) ∧
  ∀ h : ℝ, 0 < |h| → |h| < η → ∀ x : WaveMap.X n,
    |WaveMap.quotient u t h x| ≤ (WaveMap.box n R).indicator (fun _ => B) x := by
  classical
  intro t ht
  obtain ⟨C, R, hgeo, hsections⟩ := h_T004.1 t ht
  rcases hgeo with ⟨hC, hR, hCR, hu, hvol, hfinite, hvan⟩
  have hbox : IsCompact (WaveMap.box n R) := by
    exact isCompact_univ_pi (fun _ => isCompact_Icc)
  have hcompact : IsCompact ((WaveMap.box n R) ×ˢ Set.Icc (t - t / 4) (t + t / 4)) :=
    hbox.prod isCompact_Icc
  have hpositive : ∀ r ∈ Set.Icc (t - t / 4) (t + t / 4), 0 < r := by
    intro r hr
    linarith [hr.1]
  have hslab : ∀ r ∈ Set.Icc (t - t / 4) (t + t / 4),
      r ∈ interior (WaveMap.slab t) := by
    intro r hr
    simp only [WaveMap.slab, interior_Icc, Set.mem_Ioo]
    constructor <;> linarith [hr.1, hr.2]
  have hcontinuous : ContinuousOn (WaveMap.densityT u)
      ((WaveMap.box n R) ×ˢ Set.Icc (t - t / 4) (t + t / 4)) := by
    apply h_T004.2.2.2.mono
    intro p hp
    exact hpositive p.2 hp.2
  obtain ⟨B₀, hB₀⟩ := hcompact.exists_bound_of_continuousOn hcontinuous
  let B : ℝ := max B₀ 0
  have hB : 0 ≤ B := le_max_right _ _
  have hbound : ∀ x ∈ WaveMap.box n R,
      ∀ r ∈ Set.Icc (t - t / 4) (t + t / 4), |WaveMap.densityT u (x, r)| ≤ B := by
    intro x hx r hr
    have hb : |WaveMap.densityT u (x, r)| ≤ B₀ := by
      simpa only [Real.norm_eq_abs] using hB₀ (x, r) ⟨hx, hr⟩
    exact hb.trans (le_max_left _ _)
  have hCbox : C ⊆ WaveMap.box n R := by
    intro x hx
    have ho := hCR hx
    exact fun i hi => ⟨(ho i hi).1.le, (ho i hi).2.le⟩
  refine ⟨t / 4, B, R, by positivity, hB, hR, by linarith, ?_, ?_⟩
  · exact (integrableOn_const hfinite.ne).integrable_indicator hbox.measurableSet
  · intro h hh hsmall x
    by_cases hx : x ∈ WaveMap.box n R
    · rw [Set.indicator_of_mem hx]
      obtain ⟨c, hc, heq⟩ :=
        (@yui_aux_0001 n m u q h_H001 h_H002 h_T004 h_T005) t h ht hh hsmall x
      rw [heq]
      exact hbound x hx c hc
    · have hxC : x ∉ C := fun hc => hx (hCbox hc)
      have hz : ∀ r ∈ Set.Icc (t - t / 4) (t + t / 4),
          WaveMap.density u (x, r) = 0 := by
        intro r hr
        exact (hsections r (hslab r hr)).1.2.1 x hxC
      have htmem : t ∈ Set.Icc (t - t / 4) (t + t / 4) :=
        ⟨by linarith, by linarith⟩
      have hthmem : t + h ∈ Set.Icc (t - t / 4) (t + t / 4) := by
        have habs := abs_lt.mp hsmall
        exact ⟨by linarith [habs.1], by linarith [habs.2]⟩
      simp [Set.indicator_of_notMem hx, WaveMap.quotient, hz t htmem, hz (t + h) hthmem]

namespace Local_T007
theorem yui_aux_0001 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_T004 : (∀ t : ℝ, 0 < t → ∃ C : Set (WaveMap.X n), ∃ R : ℝ,
    WaveMap.supportGeometry u q t C R ∧ WaveMap.supportSections u t C R) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : WaveMap.X n => WaveMap.density u (x, t))) ∧
  ContinuousOn (WaveMap.density u) (WaveMap.domain n) ∧
  ContinuousOn (WaveMap.densityT u) (WaveMap.domain n)) (h_T005 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t →
  HasDerivAt (fun r : ℝ => WaveMap.density u (x, r)) (WaveMap.densityT u (x, t)) t ∧
  WaveMap.densityT u (x, t) =
    2 * WaveMap.timeProduct u (x, t) + 2 * ∑ j : Fin n, WaveMap.mixedProduct u j (x, t)) (h_T006 : ∀ t : ℝ, 0 < t → ∃ η B R : ℝ,
  0 < η ∧ 0 ≤ B ∧ 0 < R ∧ η < t ∧
  Integrable ((WaveMap.box n R).indicator (fun _ => B)) ∧
  ∀ h : ℝ, 0 < |h| → |h| < η → ∀ x : WaveMap.X n,
    |WaveMap.quotient u t h x| ≤ (WaveMap.box n R).indicator (fun _ => B) x) : yui_aux_type% "∀ t : ℝ, 0 < t → ∀ h : ℝ, 0 < t + h → Continuous (WaveMap.quotient u t h) ∧ Integrable (WaveMap.quotient u t h) ∧ (∫ x : WaveMap.X n, WaveMap.quotient u t h x) = (WaveMap.energy u (t + h) - WaveMap.energy u t) / h" := by
  intro t ht h hth
  have hc : ∀ r : ℝ, 0 < r → Continuous (fun x : WaveMap.X n => WaveMap.density u (x, r)) := by
    intro r hr
    exact h_T004.2.2.1.comp_continuous (continuous_id.prodMk continuous_const) (fun x => hr)
  refine ⟨((hc (t+h) hth).sub (hc t ht)).div_const h, ((h_T004.2.1 (t+h) hth).sub (h_T004.2.1 t ht)).div_const h, ?_⟩
  unfold WaveMap.quotient
  rw [MeasureTheory.integral_div, MeasureTheory.integral_sub (h_T004.2.1 (t+h) hth) (h_T004.2.1 t ht)]
  rfl

theorem yui_aux_0002 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_T004 : (∀ t : ℝ, 0 < t → ∃ C : Set (WaveMap.X n), ∃ R : ℝ,
    WaveMap.supportGeometry u q t C R ∧ WaveMap.supportSections u t C R) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : WaveMap.X n => WaveMap.density u (x, t))) ∧
  ContinuousOn (WaveMap.density u) (WaveMap.domain n) ∧
  ContinuousOn (WaveMap.densityT u) (WaveMap.domain n)) (h_T005 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t →
  HasDerivAt (fun r : ℝ => WaveMap.density u (x, r)) (WaveMap.densityT u (x, t)) t ∧
  WaveMap.densityT u (x, t) =
    2 * WaveMap.timeProduct u (x, t) + 2 * ∑ j : Fin n, WaveMap.mixedProduct u j (x, t)) (h_T006 : ∀ t : ℝ, 0 < t → ∃ η B R : ℝ,
  0 < η ∧ 0 ≤ B ∧ 0 < R ∧ η < t ∧
  Integrable ((WaveMap.box n R).indicator (fun _ => B)) ∧
  ∀ h : ℝ, 0 < |h| → |h| < η → ∀ x : WaveMap.X n,
    |WaveMap.quotient u t h x| ≤ (WaveMap.box n R).indicator (fun _ => B) x) : yui_aux_type% "∀ (t : ℝ), 0 < t → ∀ (a : ℕ → ℝ), Tendsto a atTop (𝓝[≠] (0 : ℝ)) → ∀ x : WaveMap.X n, Tendsto (fun k => WaveMap.quotient u t (a k) x) atTop (𝓝 (WaveMap.densityT u (x,t)))" := by
  intro t ht a ha x
  have hx := ((h_T005 x t ht).1.tendsto_slope_zero).comp ha
  simpa only [Function.comp_def, WaveMap.quotient, smul_eq_mul, div_eq_mul_inv, mul_comm] using hx

theorem yui_aux_0003 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_T004 : (∀ t : ℝ, 0 < t → ∃ C : Set (WaveMap.X n), ∃ R : ℝ,
    WaveMap.supportGeometry u q t C R ∧ WaveMap.supportSections u t C R) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : WaveMap.X n => WaveMap.density u (x, t))) ∧
  ContinuousOn (WaveMap.density u) (WaveMap.domain n) ∧
  ContinuousOn (WaveMap.densityT u) (WaveMap.domain n)) (h_T005 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t →
  HasDerivAt (fun r : ℝ => WaveMap.density u (x, r)) (WaveMap.densityT u (x, t)) t ∧
  WaveMap.densityT u (x, t) =
    2 * WaveMap.timeProduct u (x, t) + 2 * ∑ j : Fin n, WaveMap.mixedProduct u j (x, t)) (h_T006 : ∀ t : ℝ, 0 < t → ∃ η B R : ℝ,
  0 < η ∧ 0 ≤ B ∧ 0 < R ∧ η < t ∧
  Integrable ((WaveMap.box n R).indicator (fun _ => B)) ∧
  ∀ h : ℝ, 0 < |h| → |h| < η → ∀ x : WaveMap.X n,
    |WaveMap.quotient u t h x| ≤ (WaveMap.box n R).indicator (fun _ => B) x) : yui_aux_type% "∀ t : ℝ, 0 < t → ∀ η B R : ℝ, η < t → Integrable ((WaveMap.box n R).indicator (fun _ => B)) → (∀ h : ℝ, 0 < |h| → |h| < η → ∀ x : WaveMap.X n, |WaveMap.quotient u t h x| ≤ (WaveMap.box n R).indicator (fun _ => B) x) → ∀ a : ℕ → ℝ, (∀ k, 0 < |a k| ∧ |a k| < η) → Tendsto a atTop (𝓝 (0 : ℝ)) → Tendsto (fun k => (WaveMap.energy u (t + a k) - WaveMap.energy u t) / a k) atTop (𝓝 (∫ x : WaveMap.X n, WaveMap.densityT u (x,t)))" := by
  intro t ht η B R hηt hb hbound a ha halim
  have hpos : ∀ k, 0 < t + a k := by
    intro k
    have hlow := neg_abs_le (a k)
    have hu := (ha k).2
    linarith
  have hane : ∀ k, a k ≠ 0 := fun k => abs_pos.mp (ha k).1
  have haneLim : Tendsto a atTop (𝓝[≠] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨halim, Filter.Eventually.of_forall (fun k => hane k)⟩
  have hd : Tendsto (fun k => ∫ x : WaveMap.X n, WaveMap.quotient u t (a k) x) atTop (𝓝 (∫ x : WaveMap.X n, WaveMap.densityT u (x,t))) := by
    apply MeasureTheory.tendsto_integral_of_dominated_convergence ((WaveMap.box n R).indicator (fun _ => B))
    · intro k
      exact ((yui_aux_0001 n m u q h_H001 h_H002 h_T004 h_T005 h_T006 t ht (a k) (hpos k)).1).aestronglyMeasurable
    · exact hb
    · intro k
      exact Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hbound (a k) (ha k).1 (ha k).2 x)
    · apply Filter.Eventually.of_forall
      intro x
      exact yui_aux_0002 n m u q h_H001 h_H002 h_T004 h_T005 h_T006 t ht a haneLim x
  have hid : (fun k => ∫ x : WaveMap.X n, WaveMap.quotient u t (a k) x) = (fun k => (WaveMap.energy u (t + a k) - WaveMap.energy u t) / a k) := by
    funext k
    exact (yui_aux_0001 n m u q h_H001 h_H002 h_T004 h_T005 h_T006 t ht (a k) (hpos k)).2.2
  rw [hid] at hd
  exact hd

theorem yui_aux_0004 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_T004 : (∀ t : ℝ, 0 < t → ∃ C : Set (WaveMap.X n), ∃ R : ℝ,
    WaveMap.supportGeometry u q t C R ∧ WaveMap.supportSections u t C R) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : WaveMap.X n => WaveMap.density u (x, t))) ∧
  ContinuousOn (WaveMap.density u) (WaveMap.domain n) ∧
  ContinuousOn (WaveMap.densityT u) (WaveMap.domain n)) (h_T005 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t →
  HasDerivAt (fun r : ℝ => WaveMap.density u (x, r)) (WaveMap.densityT u (x, t)) t ∧
  WaveMap.densityT u (x, t) =
    2 * WaveMap.timeProduct u (x, t) + 2 * ∑ j : Fin n, WaveMap.mixedProduct u j (x, t)) (h_T006 : ∀ t : ℝ, 0 < t → ∃ η B R : ℝ,
  0 < η ∧ 0 ≤ B ∧ 0 < R ∧ η < t ∧
  Integrable ((WaveMap.box n R).indicator (fun _ => B)) ∧
  ∀ h : ℝ, 0 < |h| → |h| < η → ∀ x : WaveMap.X n,
    |WaveMap.quotient u t h x| ≤ (WaveMap.box n R).indicator (fun _ => B) x) : yui_aux_type% "∀ η : ℝ, 0 < η → ∀ a : ℕ → ℝ, Tendsto a atTop (𝓝[≠] (0 : ℝ)) → ∀ᶠ k in atTop, 0 < |a k| ∧ |a k| < η" := by
  intro η hη a ha
  have ha₀ : Tendsto a atTop (𝓝 (0 : ℝ)) := (tendsto_nhdsWithin_iff.mp ha).1
  have habs : Tendsto (fun k => |a k|) atTop (𝓝 (0 : ℝ)) := by simpa only [abs_zero] using ha₀.abs
  have hsmall : ∀ᶠ k in atTop, |a k| < η := habs.eventually (gt_mem_nhds hη)
  filter_upwards [(tendsto_nhdsWithin_iff.mp ha).2, hsmall] with k hk hkη
  exact ⟨abs_pos.mpr hk, hkη⟩

end Local_T007
open Local_T007 in
theorem T007 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_T004 : (∀ t : ℝ, 0 < t → ∃ C : Set (WaveMap.X n), ∃ R : ℝ,
    WaveMap.supportGeometry u q t C R ∧ WaveMap.supportSections u t C R) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : WaveMap.X n => WaveMap.density u (x, t))) ∧
  ContinuousOn (WaveMap.density u) (WaveMap.domain n) ∧
  ContinuousOn (WaveMap.densityT u) (WaveMap.domain n)) (h_T005 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t →
  HasDerivAt (fun r : ℝ => WaveMap.density u (x, r)) (WaveMap.densityT u (x, t)) t ∧
  WaveMap.densityT u (x, t) =
    2 * WaveMap.timeProduct u (x, t) + 2 * ∑ j : Fin n, WaveMap.mixedProduct u j (x, t)) (h_T006 : ∀ t : ℝ, 0 < t → ∃ η B R : ℝ,
  0 < η ∧ 0 ≤ B ∧ 0 < R ∧ η < t ∧
  Integrable ((WaveMap.box n R).indicator (fun _ => B)) ∧
  ∀ h : ℝ, 0 < |h| → |h| < η → ∀ x : WaveMap.X n,
    |WaveMap.quotient u t h x| ≤ (WaveMap.box n R).indicator (fun _ => B) x) :
    (∀ t : ℝ, 0 < t →
    HasDerivAt (WaveMap.energy u) (∫ x : WaveMap.X n, WaveMap.densityT u (x, t)) t ∧
    Integrable (fun x : WaveMap.X n => WaveMap.densityT u (x, t)) ∧
    Integrable (fun x : WaveMap.X n => WaveMap.timeProduct u (x, t)) ∧
    ∀ j : Fin n, Integrable (fun x : WaveMap.X n => WaveMap.mixedProduct u j (x, t))) ∧
  (∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t →
    WaveMap.densityT u (x, t) =
      2 * WaveMap.timeProduct u (x, t) + 2 * ∑ j : Fin n, WaveMap.mixedProduct u j (x, t)) := by
  constructor
  · intro t ht
    obtain ⟨C, R₀, hgeom, hsections⟩ := h_T004.1 t ht
    have hmid : t ∈ interior (WaveMap.slab t) := by
      rw [WaveMap.slab, interior_Icc]
      constructor <;> linarith
    have hs := hsections t hmid
    refine ⟨?_, hs.2.1.2.2.2, hs.2.2.1.2.2.2, fun j => (hs.2.2.2 j).1.2.2.2⟩
    obtain ⟨η, B, R, hη, hB, hR, hηt, hb, hbound⟩ := h_T006 t ht
    apply hasDerivAt_iff_tendsto_slope_zero.mpr
    have hlim : Tendsto (fun h : ℝ => (WaveMap.energy u (t+h) - WaveMap.energy u t) / h)
        (𝓝[≠] (0 : ℝ)) (𝓝 (∫ x : WaveMap.X n, WaveMap.densityT u (x,t))) := by
      apply Filter.tendsto_iff_seq_tendsto.mpr
      intro a ha
      have ha₀ : Tendsto a atTop (𝓝 (0 : ℝ)) := (tendsto_nhdsWithin_iff.mp ha).1
      have hgood := yui_aux_0004 n m u q h_H001 h_H002 h_T004 h_T005 h_T006 η hη a ha
      obtain ⟨N, hN⟩ := eventually_atTop.mp hgood
      apply (tendsto_add_atTop_iff_nat N).mp
      exact yui_aux_0003 n m u q h_H001 h_H002 h_T004 h_T005 h_T006
        t ht η B R hηt hb hbound (fun k => a (k+N))
        (fun k => hN (k+N) (Nat.le_add_left N k))
        (ha₀.comp (tendsto_add_atTop_nat N))
    simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using hlim
  · intro x t ht
    exact (h_T005 x t ht).2

namespace Local_T008
theorem yui_aux_0001 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) : yui_aux_type% "∀ (j : Fin n), MeasurePreserving (fun w : ({i : Fin n // ¬ i ≠ j} → ℝ) => w ⟨j, by simp⟩) volume volume" := by
  classical
  intro j
  let U : Unique {i : Fin n // ¬ i ≠ j} :=
    { default := ⟨j, by simp⟩
      uniq := fun i => Subtype.ext (not_ne_iff.mp i.property) }
  letI := U
  have hfin : (@Unique.fintype {i : Fin n // ¬ i ≠ j} U) =
      (Subtype.fintype (fun i : Fin n => ¬ i ≠ j)) := Subsingleton.elim _ _
  have h := volume_preserving_funUnique {i : Fin n // ¬ i ≠ j} ℝ
  rw [hfin] at h
  exact h

theorem yui_aux_0002 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) : yui_aux_type% "∀ (j : Fin n), ∃ e : WaveMap.X n ≃ᵐ ((WaveMap.Other j → ℝ) × ℝ), MeasurePreserving e ∧ ∀ (y : WaveMap.Other j → ℝ) (z : ℝ), e.symm (y, z) = WaveMap.insertCoord j y z" := by
  classical
  intro j
  letI : Unique {i : Fin n // ¬ i ≠ j} :=
    { default := ⟨j, by simp⟩
      uniq := fun i => Subtype.ext (not_ne_iff.mp i.property) }
  let e₁ := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ) (fun i => i ≠ j)
  let e₂ := (MeasurableEquiv.refl (WaveMap.Other j → ℝ)).prodCongr
    (MeasurableEquiv.funUnique {i : Fin n // ¬ i ≠ j} ℝ)
  refine ⟨e₁.trans e₂, ?_, ?_⟩
  · exact (volume_preserving_piEquivPiSubtypeProd (fun _ : Fin n => ℝ) (fun i => i ≠ j)).trans
      ((MeasurePreserving.id (volume : Measure (WaveMap.Other j → ℝ))).prod
        (@yui_aux_0001 n m u q j))
  · intro y z
    ext i
    change (if h : i ≠ j then y ⟨i, h⟩ else z) =
      (if h : i = j then z else y ⟨i, h⟩)
    by_cases h : i = j <;> simp [h]

theorem yui_aux_0003 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) : yui_aux_type% "∀ (j : Fin n) (R : ℝ) (y : WaveMap.Other j → ℝ) (z : ℝ), WaveMap.insertCoord j y z ∈ WaveMap.box n R ↔ y ∈ WaveMap.otherBox j R ∧ z ∈ Set.Icc (-R) R" := by
  classical
  intro j R y z
  simp only [WaveMap.box, WaveMap.otherBox, Set.mem_pi, Set.mem_univ, forall_const]
  constructor
  · intro h
    constructor
    · intro i
      simpa only [WaveMap.insertCoord, dif_neg i.property] using h i.val
    · simpa [WaveMap.insertCoord] using h j
  · rintro ⟨hy, hz⟩ i
    by_cases hij : i = j
    · simpa only [WaveMap.insertCoord, dif_pos hij] using hz
    · simpa only [WaveMap.insertCoord, dif_neg hij] using hy ⟨i, hij⟩

theorem yui_aux_0004 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) : yui_aux_type% "∀ (j : Fin n), (volume : Measure ((WaveMap.Other j → ℝ) × ℝ)) = (volume : Measure (WaveMap.Other j → ℝ)).prod (volume : Measure ℝ)" := by
  intro j
  exact Measure.volume_eq_prod (WaveMap.Other j → ℝ) ℝ

theorem yui_aux_0005 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) : yui_aux_type% "∀ (j : Fin n) (R : ℝ) (g : ((WaveMap.Other j → ℝ) × ℝ) → ℝ), Integrable g (((volume : Measure (WaveMap.Other j → ℝ)).prod (volume : Measure ℝ)).restrict (WaveMap.otherBox j R ×ˢ Set.Icc (-R) R)) → IntegrableOn g (WaveMap.otherBox j R ×ˢ Set.Icc (-R) R) ((volume : Measure (WaveMap.Other j → ℝ)).prod (volume : Measure ℝ))" := by
  intro j R g h
  simpa only [IntegrableOn] using h

end Local_T008
open Local_T008 in
theorem T008 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m)  :
    ∀ (j : Fin n) (R : ℝ), 0 < R → ∀ f : WaveMap.X n → ℝ,
  IntegrableOn f (WaveMap.box n R) →
  (∫ x in WaveMap.box n R, f x) =
    ∫ y in WaveMap.otherBox j R, ∫ z in Set.Icc (-R) R, f (WaveMap.insertCoord j y z) := by
  classical
  intro j R hR f hf
  obtain ⟨e, he, hinv⟩ := @yui_aux_0002 n m u q j
  have hpre : e.symm ⁻¹' WaveMap.box n R =
      WaveMap.otherBox j R ×ˢ Set.Icc (-R) R := by
    ext ⟨y, z⟩
    change e.symm (y, z) ∈ WaveMap.box n R ↔ _
    rw [hinv]
    exact @yui_aux_0003 n m u q j R y z
  have hmp : MeasurePreserving e.symm volume volume :=
    MeasurePreserving.symm e he
  have hi : IntegrableOn (fun p => f (e.symm p))
      (WaveMap.otherBox j R ×ˢ Set.Icc (-R) R)
      ((volume : Measure (WaveMap.Other j → ℝ)).prod (volume : Measure ℝ)) := by
    apply @yui_aux_0005 n m u q j R (fun p => f (e.symm p))
    have ht := (hmp.restrict_preimage_emb e.symm.measurableEmbedding
      (WaveMap.box n R)).integrable_comp_of_integrable hf
    simpa only [hpre, Function.comp_def, @yui_aux_0004 n m u q j] using ht
  calc
    (∫ x in WaveMap.box n R, f x) =
        ∫ p in WaveMap.otherBox j R ×ˢ Set.Icc (-R) R, f (e.symm p)
          ∂((volume : Measure (WaveMap.Other j → ℝ)).prod (volume : Measure ℝ)) := by
      symm
      simpa only [hpre, @yui_aux_0004 n m u q j] using
        hmp.setIntegral_preimage_emb e.symm.measurableEmbedding f (WaveMap.box n R)
    _ = ∫ y in WaveMap.otherBox j R, ∫ z in Set.Icc (-R) R,
        f (e.symm (y, z)) := setIntegral_prod _ hi
    _ = ∫ y in WaveMap.otherBox j R, ∫ z in Set.Icc (-R) R,
        f (WaveMap.insertCoord j y z) := by simp only [hinv]

namespace Local_T009
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

theorem yui_aux_0007 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_T004 : (∀ t : ℝ, 0 < t → ∃ C : Set (WaveMap.X n), ∃ R : ℝ,
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

theorem yui_aux_0008 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_T004 : (∀ t : ℝ, 0 < t → ∃ C : Set (WaveMap.X n), ∃ R : ℝ,
    WaveMap.supportGeometry u q t C R ∧ WaveMap.supportSections u t C R) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : WaveMap.X n => WaveMap.density u (x, t))) ∧
  ContinuousOn (WaveMap.density u) (WaveMap.domain n) ∧
  ContinuousOn (WaveMap.densityT u) (WaveMap.domain n)) (h_T008 : ∀ (j : Fin n) (R : ℝ), 0 < R → ∀ f : WaveMap.X n → ℝ,
  IntegrableOn f (WaveMap.box n R) →
  (∫ x in WaveMap.box n R, f x) =
    ∫ y in WaveMap.otherBox j R, ∫ z in Set.Icc (-R) R, f (WaveMap.insertCoord j y z)) : yui_aux_type% "∀ t : ℝ, 0 < t → ∀ (C : Set (WaveMap.X n)) (R : ℝ),\n  WaveMap.supportSections u t C R → ∀ j : Fin n,\n  Integrable (fun p : (WaveMap.Other j → ℝ) × ℝ =>\n    WaveMap.fluxDx u j (WaveMap.insertCoord j p.1 p.2,t))\n    ((volume.restrict (WaveMap.otherBox j R)).prod (volume.restrict (Set.Icc (-R) R)))" := by
  intro t ht C R hs j
  have hti := (yui_aux_0002 n m u q h_H001 h_H002 h_T004 h_T008 t ht).1
  have hc := ((hs t hti).2.2.2 j).2.2.1
  have hi := yui_aux_0007 n m u q h_H001 h_H002 h_T004 h_T008 j
  have hk : IsCompact (WaveMap.otherBox j R) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  have hInt : IntegrableOn (fun p : (WaveMap.Other j → ℝ) × ℝ =>
      WaveMap.fluxDx u j (WaveMap.insertCoord j p.1 p.2,t))
      ((WaveMap.otherBox j R) ×ˢ Set.Icc (-R) R)
      ((volume : Measure (WaveMap.Other j → ℝ)).prod (volume : Measure ℝ)) :=
    (hc.comp hi).continuousOn.integrableOn_compact (hk.prod isCompact_Icc)
  simpa only [IntegrableOn, Measure.prod_restrict] using hInt

end Local_T009
open Local_T009 in
theorem T009 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_T004 : (∀ t : ℝ, 0 < t → ∃ C : Set (WaveMap.X n), ∃ R : ℝ,
    WaveMap.supportGeometry u q t C R ∧ WaveMap.supportSections u t C R) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : WaveMap.X n => WaveMap.density u (x, t))) ∧
  ContinuousOn (WaveMap.density u) (WaveMap.domain n) ∧
  ContinuousOn (WaveMap.densityT u) (WaveMap.domain n)) (h_T008 : ∀ (j : Fin n) (R : ℝ), 0 < R → ∀ f : WaveMap.X n → ℝ,
  IntegrableOn f (WaveMap.box n R) →
  (∫ x in WaveMap.box n R, f x) =
    ∫ y in WaveMap.otherBox j R, ∫ z in Set.Icc (-R) R, f (WaveMap.insertCoord j y z)) :
    ∀ t : ℝ, 0 < t → ∀ j : Fin n,
  (∀ x : WaveMap.X n, WaveMap.fluxDx u j (x, t) =
    WaveMap.mixedProduct u j (x, t) + WaveMap.lapProduct u j (x, t)) ∧
  Integrable (fun x : WaveMap.X n => WaveMap.fluxDx u j (x, t)) ∧
  (∫ x : WaveMap.X n, WaveMap.fluxDx u j (x, t)) = 0 := by
  intro t ht j
  obtain ⟨C, R, hg, hs⟩ := h_T004.1 t ht
  have hti := (yui_aux_0002 n m u q h_H001 h_H002 h_T004 h_T008 t ht).1
  have hd := ((hs t hti).2.2.2 j).2.2
  have hint : Integrable (fun x : WaveMap.X n => WaveMap.fluxDx u j (x,t)) :=
    hd.2.2.2
  refine ⟨?_, hint, ?_⟩
  · intro x
    simpa only [WaveMap.fluxDx, WaveMap.flux, WaveMap.mixedProduct,
      WaveMap.lapProduct, real_inner_comm, add_comm] using
      (yui_aux_0003 n m u q h_H001 h_H002 h_T004 h_T008 t ht j x)
  · have hpi := yui_aux_0008 n m u q h_H001 h_H002 h_T004 h_T008 t ht C R hs j
    have hFub :
        (∫ y in WaveMap.otherBox j R, ∫ z in Icc (-R) R,
          WaveMap.fluxDx u j (WaveMap.insertCoord j y z,t)) =
        ∫ p : (WaveMap.Other j → ℝ) × ℝ,
          WaveMap.fluxDx u j (WaveMap.insertCoord j p.1 p.2,t)
          ∂((volume.restrict (WaveMap.otherBox j R)).prod
            (volume.restrict (Icc (-R) R))) :=
      integral_integral (f := fun y z =>
        WaveMap.fluxDx u j (WaveMap.insertCoord j y z,t)) hpi
    have hiter :
        (∫ y in WaveMap.otherBox j R, ∫ z in Icc (-R) R,
          WaveMap.fluxDx u j (WaveMap.insertCoord j y z,t)) = 0 := by
      simp only [yui_aux_0006 n m u q h_H001 h_H002 h_T004 h_T008 t ht C R hg hs j,
        integral_zero]
    have hprod := hFub.symm.trans hiter
    have hbox :
        (∫ x in WaveMap.box n R, WaveMap.fluxDx u j (x,t)) = 0 :=
      (h_T008 j R hg.2.1 _ hint.integrableOn).trans (hFub.trans hprod)
    have hCB : C ⊆ WaveMap.box n R := by
      intro x hx i hi
      have hxi := hg.2.2.1 hx i hi
      exact ⟨hxi.1.le, hxi.2.le⟩
    have hz : ∀ x : WaveMap.X n, x ∉ WaveMap.box n R →
        WaveMap.fluxDx u j (x,t) = 0 := by
      intro x hx
      exact hd.2.1 x (fun hxc => hx (hCB hxc))
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero hz).symm.trans hbox

theorem T010 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_T004 : (∀ t : ℝ, 0 < t → ∃ C : Set (WaveMap.X n), ∃ R : ℝ,
    WaveMap.supportGeometry u q t C R ∧ WaveMap.supportSections u t C R) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : WaveMap.X n => WaveMap.density u (x, t))) ∧
  ContinuousOn (WaveMap.density u) (WaveMap.domain n) ∧
  ContinuousOn (WaveMap.densityT u) (WaveMap.domain n)) (h_T009 : ∀ t : ℝ, 0 < t → ∀ j : Fin n,
  (∀ x : WaveMap.X n, WaveMap.fluxDx u j (x, t) =
    WaveMap.mixedProduct u j (x, t) + WaveMap.lapProduct u j (x, t)) ∧
  Integrable (fun x : WaveMap.X n => WaveMap.fluxDx u j (x, t)) ∧
  (∫ x : WaveMap.X n, WaveMap.fluxDx u j (x, t)) = 0) :
    ∀ t : ℝ, 0 < t → ∀ j : Fin n,
  (∫ x : WaveMap.X n, WaveMap.mixedProduct u j (x, t)) =
    -(∫ x : WaveMap.X n, WaveMap.lapProduct u j (x, t)) ∧
  Integrable (fun x : WaveMap.X n => WaveMap.mixedProduct u j (x, t)) ∧
  Integrable (fun x : WaveMap.X n => WaveMap.lapProduct u j (x, t)) := by
  intro t ht j
  obtain ⟨C, R, hgeom, hsections⟩ := h_T004.1 t ht
  have hti : t ∈ interior (WaveMap.slab t) := by
    rw [WaveMap.slab, interior_Icc]
    constructor <;> linarith
  have hproducts := (hsections t hti).2.2.2 j
  have hm : Integrable (fun x : WaveMap.X n => WaveMap.mixedProduct u j (x, t)) :=
    hproducts.1.2.2.2
  have hl : Integrable (fun x : WaveMap.X n => WaveMap.lapProduct u j (x, t)) :=
    hproducts.2.1.2.2.2
  have hid := h_T009 t ht j
  have hzero : (∫ x : WaveMap.X n, WaveMap.mixedProduct u j (x, t)) +
      (∫ x : WaveMap.X n, WaveMap.lapProduct u j (x, t)) = 0 := by
    rw [← integral_add hm hl]
    calc
      (∫ x : WaveMap.X n, WaveMap.mixedProduct u j (x, t) + WaveMap.lapProduct u j (x, t)) =
          (∫ x : WaveMap.X n, WaveMap.fluxDx u j (x, t)) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => (hid.1 x).symm)
      _ = 0 := hid.2.2
  exact ⟨by linarith, hm, hl⟩

namespace Local_T011
theorem yui_aux_0001 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_T002 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t →
  (inner ℝ (u (x, t)) (WaveMap.dt u (x, t)) = 0 ∧
   inner ℝ (WaveMap.dt u (x, t)) (WaveMap.dt (WaveMap.dt u) (x, t) - WaveMap.lap u (x, t)) = 0) ∧
  (∀ a : ℝ, WaveMap.dt (WaveMap.dt u) (x, t) - WaveMap.lap u (x, t) = a • u (x, t) →
    a = (∑ j : Fin n, ‖WaveMap.dx u j (x, t)‖ ^ 2) - ‖WaveMap.dt u (x, t)‖ ^ 2) ∧
  WaveMap.dt (WaveMap.dt u) (x, t) - WaveMap.lap u (x, t) =
    ((∑ j : Fin n, ‖WaveMap.dx u j (x, t)‖ ^ 2) - ‖WaveMap.dt u (x, t)‖ ^ 2) • u (x, t)) (h_T004 : (∀ t : ℝ, 0 < t → ∃ C : Set (WaveMap.X n), ∃ R : ℝ,
    WaveMap.supportGeometry u q t C R ∧ WaveMap.supportSections u t C R) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : WaveMap.X n => WaveMap.density u (x, t))) ∧
  ContinuousOn (WaveMap.density u) (WaveMap.domain n) ∧
  ContinuousOn (WaveMap.densityT u) (WaveMap.domain n)) (h_T007 : (∀ t : ℝ, 0 < t →
    HasDerivAt (WaveMap.energy u) (∫ x : WaveMap.X n, WaveMap.densityT u (x, t)) t ∧
    Integrable (fun x : WaveMap.X n => WaveMap.densityT u (x, t)) ∧
    Integrable (fun x : WaveMap.X n => WaveMap.timeProduct u (x, t)) ∧
    ∀ j : Fin n, Integrable (fun x : WaveMap.X n => WaveMap.mixedProduct u j (x, t))) ∧
  (∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t →
    WaveMap.densityT u (x, t) =
      2 * WaveMap.timeProduct u (x, t) + 2 * ∑ j : Fin n, WaveMap.mixedProduct u j (x, t))) (h_T010 : ∀ t : ℝ, 0 < t → ∀ j : Fin n,
  (∫ x : WaveMap.X n, WaveMap.mixedProduct u j (x, t)) =
    -(∫ x : WaveMap.X n, WaveMap.lapProduct u j (x, t)) ∧
  Integrable (fun x : WaveMap.X n => WaveMap.mixedProduct u j (x, t)) ∧
  Integrable (fun x : WaveMap.X n => WaveMap.lapProduct u j (x, t))) : yui_aux_type% "∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t → WaveMap.timeProduct u (x,t) - ∑ j : Fin n, WaveMap.lapProduct u j (x,t) = 0" := by
  intro x t ht
  have h := (h_T002 x t ht).1.2
  simpa only [WaveMap.timeProduct, WaveMap.lapProduct, WaveMap.lap, inner_sub_right, inner_sum] using h

theorem yui_aux_0002 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_T002 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t →
  (inner ℝ (u (x, t)) (WaveMap.dt u (x, t)) = 0 ∧
   inner ℝ (WaveMap.dt u (x, t)) (WaveMap.dt (WaveMap.dt u) (x, t) - WaveMap.lap u (x, t)) = 0) ∧
  (∀ a : ℝ, WaveMap.dt (WaveMap.dt u) (x, t) - WaveMap.lap u (x, t) = a • u (x, t) →
    a = (∑ j : Fin n, ‖WaveMap.dx u j (x, t)‖ ^ 2) - ‖WaveMap.dt u (x, t)‖ ^ 2) ∧
  WaveMap.dt (WaveMap.dt u) (x, t) - WaveMap.lap u (x, t) =
    ((∑ j : Fin n, ‖WaveMap.dx u j (x, t)‖ ^ 2) - ‖WaveMap.dt u (x, t)‖ ^ 2) • u (x, t)) (h_T004 : (∀ t : ℝ, 0 < t → ∃ C : Set (WaveMap.X n), ∃ R : ℝ,
    WaveMap.supportGeometry u q t C R ∧ WaveMap.supportSections u t C R) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : WaveMap.X n => WaveMap.density u (x, t))) ∧
  ContinuousOn (WaveMap.density u) (WaveMap.domain n) ∧
  ContinuousOn (WaveMap.densityT u) (WaveMap.domain n)) (h_T007 : (∀ t : ℝ, 0 < t →
    HasDerivAt (WaveMap.energy u) (∫ x : WaveMap.X n, WaveMap.densityT u (x, t)) t ∧
    Integrable (fun x : WaveMap.X n => WaveMap.densityT u (x, t)) ∧
    Integrable (fun x : WaveMap.X n => WaveMap.timeProduct u (x, t)) ∧
    ∀ j : Fin n, Integrable (fun x : WaveMap.X n => WaveMap.mixedProduct u j (x, t))) ∧
  (∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t →
    WaveMap.densityT u (x, t) =
      2 * WaveMap.timeProduct u (x, t) + 2 * ∑ j : Fin n, WaveMap.mixedProduct u j (x, t))) (h_T010 : ∀ t : ℝ, 0 < t → ∀ j : Fin n,
  (∫ x : WaveMap.X n, WaveMap.mixedProduct u j (x, t)) =
    -(∫ x : WaveMap.X n, WaveMap.lapProduct u j (x, t)) ∧
  Integrable (fun x : WaveMap.X n => WaveMap.mixedProduct u j (x, t)) ∧
  Integrable (fun x : WaveMap.X n => WaveMap.lapProduct u j (x, t))) : yui_aux_type% "∀ t : ℝ, (∑ j : Fin n, -(∫ x : WaveMap.X n, WaveMap.lapProduct u j (x,t))) = -(∑ j : Fin n, ∫ x : WaveMap.X n, WaveMap.lapProduct u j (x,t))" := by
  intro t
  simpa only [Finset.sum_neg_distrib]

end Local_T011
open Local_T011 in
theorem T011 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_T002 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t →
  (inner ℝ (u (x, t)) (WaveMap.dt u (x, t)) = 0 ∧
   inner ℝ (WaveMap.dt u (x, t)) (WaveMap.dt (WaveMap.dt u) (x, t) - WaveMap.lap u (x, t)) = 0) ∧
  (∀ a : ℝ, WaveMap.dt (WaveMap.dt u) (x, t) - WaveMap.lap u (x, t) = a • u (x, t) →
    a = (∑ j : Fin n, ‖WaveMap.dx u j (x, t)‖ ^ 2) - ‖WaveMap.dt u (x, t)‖ ^ 2) ∧
  WaveMap.dt (WaveMap.dt u) (x, t) - WaveMap.lap u (x, t) =
    ((∑ j : Fin n, ‖WaveMap.dx u j (x, t)‖ ^ 2) - ‖WaveMap.dt u (x, t)‖ ^ 2) • u (x, t)) (h_T004 : (∀ t : ℝ, 0 < t → ∃ C : Set (WaveMap.X n), ∃ R : ℝ,
    WaveMap.supportGeometry u q t C R ∧ WaveMap.supportSections u t C R) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : WaveMap.X n => WaveMap.density u (x, t))) ∧
  ContinuousOn (WaveMap.density u) (WaveMap.domain n) ∧
  ContinuousOn (WaveMap.densityT u) (WaveMap.domain n)) (h_T007 : (∀ t : ℝ, 0 < t →
    HasDerivAt (WaveMap.energy u) (∫ x : WaveMap.X n, WaveMap.densityT u (x, t)) t ∧
    Integrable (fun x : WaveMap.X n => WaveMap.densityT u (x, t)) ∧
    Integrable (fun x : WaveMap.X n => WaveMap.timeProduct u (x, t)) ∧
    ∀ j : Fin n, Integrable (fun x : WaveMap.X n => WaveMap.mixedProduct u j (x, t))) ∧
  (∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t →
    WaveMap.densityT u (x, t) =
      2 * WaveMap.timeProduct u (x, t) + 2 * ∑ j : Fin n, WaveMap.mixedProduct u j (x, t))) (h_T010 : ∀ t : ℝ, 0 < t → ∀ j : Fin n,
  (∫ x : WaveMap.X n, WaveMap.mixedProduct u j (x, t)) =
    -(∫ x : WaveMap.X n, WaveMap.lapProduct u j (x, t)) ∧
  Integrable (fun x : WaveMap.X n => WaveMap.mixedProduct u j (x, t)) ∧
  Integrable (fun x : WaveMap.X n => WaveMap.lapProduct u j (x, t))) :
    ∀ t : ℝ, 0 < t →
  Integrable (fun x : WaveMap.X n => WaveMap.density u (x, t)) ∧
  DifferentiableAt ℝ (WaveMap.energy u) t ∧ deriv (WaveMap.energy u) t = 0 := by
  intro t ht
  rcases h_T007.1 t ht with ⟨hd, hden, htime, hmixed⟩
  have hlap : ∀ j : Fin n, Integrable (fun x : WaveMap.X n => WaveMap.lapProduct u j (x, t)) :=
    fun j => (h_T010 t ht j).2.2
  have hms : Integrable (fun x : WaveMap.X n => ∑ j : Fin n, WaveMap.mixedProduct u j (x, t)) :=
    integrable_finsetSum Finset.univ (fun j _ => hmixed j)
  have hls : Integrable (fun x : WaveMap.X n => ∑ j : Fin n, WaveMap.lapProduct u j (x, t)) :=
    integrable_finsetSum Finset.univ (fun j _ => hlap j)
  have hmi :
      (∫ x : WaveMap.X n, ∑ j : Fin n, WaveMap.mixedProduct u j (x, t)) =
        ∑ j : Fin n, ∫ x : WaveMap.X n, WaveMap.mixedProduct u j (x, t) :=
    integral_finsetSum Finset.univ (fun j _ => hmixed j)
  have hli :
      (∫ x : WaveMap.X n, ∑ j : Fin n, WaveMap.lapProduct u j (x, t)) =
        ∑ j : Fin n, ∫ x : WaveMap.X n, WaveMap.lapProduct u j (x, t) :=
    integral_finsetSum Finset.univ (fun j _ => hlap j)
  have hz :
      (∫ x : WaveMap.X n, WaveMap.timeProduct u (x, t)) -
        (∑ j : Fin n, ∫ x : WaveMap.X n, WaveMap.lapProduct u j (x, t)) = 0 := by
    rw [← hli, ← integral_sub htime hls]
    have hf : (fun x : WaveMap.X n =>
        WaveMap.timeProduct u (x, t) - ∑ j : Fin n, WaveMap.lapProduct u j (x, t)) =
        fun _ => (0 : ℝ) := by
      funext x
      exact yui_aux_0001 n m u q h_H001 h_H002 h_T002 h_T004 h_T007 h_T010 x t ht
    rw [hf]
    simp
  have hexpand :
      (∫ x : WaveMap.X n, WaveMap.densityT u (x, t)) =
        2 * (∫ x : WaveMap.X n, WaveMap.timeProduct u (x, t)) +
        2 * (∑ j : Fin n, ∫ x : WaveMap.X n, WaveMap.mixedProduct u j (x, t)) := by
    calc
      _ = ∫ x : WaveMap.X n, (2 * WaveMap.timeProduct u (x, t) +
          2 * ∑ j : Fin n, WaveMap.mixedProduct u j (x, t)) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => h_T007.2 x t ht)
      _ = _ := by
        rw [integral_add (htime.const_mul 2) (hms.const_mul 2),
          integral_const_mul, integral_const_mul, hmi]
  have hip :
      (∑ j : Fin n, ∫ x : WaveMap.X n, WaveMap.mixedProduct u j (x, t)) =
        -(∑ j : Fin n, ∫ x : WaveMap.X n, WaveMap.lapProduct u j (x, t)) := by
    simp_rw [(h_T010 t ht _).1]
    exact yui_aux_0002 n m u q h_H001 h_H002 h_T002 h_T004 h_T007 h_T010 t
  refine ⟨h_T004.2.1 t ht, hd.differentiableAt, ?_⟩
  rw [hd.deriv, hexpand, hip]
  linarith [hz]

theorem T012 (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_T011 : ∀ t : ℝ, 0 < t →
  Integrable (fun x : WaveMap.X n => WaveMap.density u (x, t)) ∧
  DifferentiableAt ℝ (WaveMap.energy u) t ∧ deriv (WaveMap.energy u) t = 0) :
    (∀ t : ℝ, 0 < t →
  Integrable (fun x : WaveMap.X n => WaveMap.density u (x, t)) ∧
  DifferentiableAt ℝ (WaveMap.energy u) t ∧ deriv (WaveMap.energy u) t = 0) ∧
  ∀ s t : ℝ, 0 < s → 0 < t → WaveMap.energy u s = WaveMap.energy u t := by
  refine ⟨h_T011, ?_⟩
  have ordered : ∀ a b : ℝ, 0 < a → a < b →
      WaveMap.energy u a = WaveMap.energy u b := by
    intro a b ha hab
    have hcont : ContinuousOn (WaveMap.energy u) (Set.Icc a b) := by
      intro x hx
      exact ((h_T011 x (lt_of_lt_of_le ha hx.1)).2.1.continuousAt).continuousWithinAt
    have hderiv : ∀ x ∈ Set.Ioo a b,
        HasDerivAt (WaveMap.energy u) 0 x := by
      intro x hx
      have hxpos : 0 < x := lt_trans ha hx.1
      have hd := (h_T011 x hxpos).2.1.hasDerivAt
      rw [(h_T011 x hxpos).2.2] at hd
      exact hd
    obtain ⟨c, hc, hslope⟩ :=
      exists_hasDerivAt_eq_slope (WaveMap.energy u) (fun _ => (0 : ℝ)) hab hcont hderiv
    have hdiff : WaveMap.energy u b - WaveMap.energy u a = 0 := by
      have h := (div_eq_iff (ne_of_gt (sub_pos.mpr hab))).mp hslope.symm
      simpa only [zero_mul] using h
    exact (sub_eq_zero.mp hdiff).symm
  intro s t hs ht
  rcases lt_trichotomy s t with hst | hst | hts
  · exact ordered s t hs hst
  · rw [hst]
  · exact (ordered t s ht hts).symm

set_option Elab.async false in
theorem P (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_H003 : ‖q‖ = 1) (h_H004 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t → ‖u (x, t)‖ = 1) (h_H005 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t → ∃ a : ℝ, WaveMap.dt (WaveMap.dt u) (x, t) - WaveMap.lap u (x, t) = a • u (x, t)) (h_H006 : ∀ s t : ℝ, 0 < s → s < t → ∃ C : Set (WaveMap.X n), IsCompact C ∧ ∀ x : WaveMap.X n, x ∉ C → ∀ r ∈ Set.Icc s t, u (x, r) = q) :
    (∀ t : ℝ, 0 < t →
  Integrable (fun x : WaveMap.X n => WaveMap.density u (x, t)) ∧
  DifferentiableAt ℝ (WaveMap.energy u) t ∧ deriv (WaveMap.energy u) t = 0) ∧
  ∀ s t : ℝ, 0 < s → 0 < t → WaveMap.energy u s = WaveMap.energy u t := by
  have h_T001 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t → inner ℝ (u (x, t)) (WaveMap.dt u (x, t)) = 0 ∧ inner ℝ (WaveMap.dt u (x, t)) (WaveMap.dt (WaveMap.dt u) (x, t) - WaveMap.lap u (x, t)) = 0 := @T001 n m u q h_H001 h_H002 h_H004 h_H005
  have h_T002 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t →
  (inner ℝ (u (x, t)) (WaveMap.dt u (x, t)) = 0 ∧
   inner ℝ (WaveMap.dt u (x, t)) (WaveMap.dt (WaveMap.dt u) (x, t) - WaveMap.lap u (x, t)) = 0) ∧
  (∀ a : ℝ, WaveMap.dt (WaveMap.dt u) (x, t) - WaveMap.lap u (x, t) = a • u (x, t) →
    a = (∑ j : Fin n, ‖WaveMap.dx u j (x, t)‖ ^ 2) - ‖WaveMap.dt u (x, t)‖ ^ 2) ∧
  WaveMap.dt (WaveMap.dt u) (x, t) - WaveMap.lap u (x, t) =
    ((∑ j : Fin n, ‖WaveMap.dx u j (x, t)‖ ^ 2) - ‖WaveMap.dt u (x, t)‖ ^ 2) • u (x, t) := @T002 n m u q h_H001 h_H002 h_H004 h_H005 h_T001
  have h_T003 : ∀ t : ℝ, 0 < t → ∃ C : Set (WaveMap.X n), ∃ R : ℝ, WaveMap.supportGeometry u q t C R := @T003 n m u q h_H001 h_H002 h_H006
  have h_T004 : (∀ t : ℝ, 0 < t → ∃ C : Set (WaveMap.X n), ∃ R : ℝ,
    WaveMap.supportGeometry u q t C R ∧ WaveMap.supportSections u t C R) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : WaveMap.X n => WaveMap.density u (x, t))) ∧
  ContinuousOn (WaveMap.density u) (WaveMap.domain n) ∧
  ContinuousOn (WaveMap.densityT u) (WaveMap.domain n) := @T004 n m u q h_H001 h_H002 h_T003
  have h_T005 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t →
  HasDerivAt (fun r : ℝ => WaveMap.density u (x, r)) (WaveMap.densityT u (x, t)) t ∧
  WaveMap.densityT u (x, t) =
    2 * WaveMap.timeProduct u (x, t) + 2 * ∑ j : Fin n, WaveMap.mixedProduct u j (x, t) := @T005 n m u q h_H001 h_H002
  have h_T006 : ∀ t : ℝ, 0 < t → ∃ η B R : ℝ,
  0 < η ∧ 0 ≤ B ∧ 0 < R ∧ η < t ∧
  Integrable ((WaveMap.box n R).indicator (fun _ => B)) ∧
  ∀ h : ℝ, 0 < |h| → |h| < η → ∀ x : WaveMap.X n,
    |WaveMap.quotient u t h x| ≤ (WaveMap.box n R).indicator (fun _ => B) x := @T006 n m u q h_H001 h_H002 h_T004 h_T005
  have h_T007 : (∀ t : ℝ, 0 < t →
    HasDerivAt (WaveMap.energy u) (∫ x : WaveMap.X n, WaveMap.densityT u (x, t)) t ∧
    Integrable (fun x : WaveMap.X n => WaveMap.densityT u (x, t)) ∧
    Integrable (fun x : WaveMap.X n => WaveMap.timeProduct u (x, t)) ∧
    ∀ j : Fin n, Integrable (fun x : WaveMap.X n => WaveMap.mixedProduct u j (x, t))) ∧
  (∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t →
    WaveMap.densityT u (x, t) =
      2 * WaveMap.timeProduct u (x, t) + 2 * ∑ j : Fin n, WaveMap.mixedProduct u j (x, t)) := @T007 n m u q h_H001 h_H002 h_T004 h_T005 h_T006
  have h_T008 : ∀ (j : Fin n) (R : ℝ), 0 < R → ∀ f : WaveMap.X n → ℝ,
  IntegrableOn f (WaveMap.box n R) →
  (∫ x in WaveMap.box n R, f x) =
    ∫ y in WaveMap.otherBox j R, ∫ z in Set.Icc (-R) R, f (WaveMap.insertCoord j y z) := @T008 n m u q 
  have h_T009 : ∀ t : ℝ, 0 < t → ∀ j : Fin n,
  (∀ x : WaveMap.X n, WaveMap.fluxDx u j (x, t) =
    WaveMap.mixedProduct u j (x, t) + WaveMap.lapProduct u j (x, t)) ∧
  Integrable (fun x : WaveMap.X n => WaveMap.fluxDx u j (x, t)) ∧
  (∫ x : WaveMap.X n, WaveMap.fluxDx u j (x, t)) = 0 := @T009 n m u q h_H001 h_H002 h_T004 h_T008
  have h_T010 : ∀ t : ℝ, 0 < t → ∀ j : Fin n,
  (∫ x : WaveMap.X n, WaveMap.mixedProduct u j (x, t)) =
    -(∫ x : WaveMap.X n, WaveMap.lapProduct u j (x, t)) ∧
  Integrable (fun x : WaveMap.X n => WaveMap.mixedProduct u j (x, t)) ∧
  Integrable (fun x : WaveMap.X n => WaveMap.lapProduct u j (x, t)) := @T010 n m u q h_H001 h_T004 h_T009
  have h_T011 : ∀ t : ℝ, 0 < t →
  Integrable (fun x : WaveMap.X n => WaveMap.density u (x, t)) ∧
  DifferentiableAt ℝ (WaveMap.energy u) t ∧ deriv (WaveMap.energy u) t = 0 := @T011 n m u q h_H001 h_H002 h_T002 h_T004 h_T007 h_T010
  have h_T012 : (∀ t : ℝ, 0 < t →
  Integrable (fun x : WaveMap.X n => WaveMap.density u (x, t)) ∧
  DifferentiableAt ℝ (WaveMap.energy u) t ∧ deriv (WaveMap.energy u) t = 0) ∧
  ∀ s t : ℝ, 0 < s → 0 < t → WaveMap.energy u s = WaveMap.energy u t := @T012 n m u q h_T011
  exact h_T012

#check @P
#print axioms P

end Translation

namespace AuditBExport
set_option autoImplicit false
set_option Elab.async false in
theorem P (n : ℕ) (m : ℕ) (u : WaveMap.X n × ℝ → WaveMap.V m) (q : WaveMap.V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (WaveMap.domain n)) (h_H003 : ‖q‖ = 1) (h_H004 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t → ‖u (x, t)‖ = 1) (h_H005 : ∀ x : WaveMap.X n, ∀ t : ℝ, 0 < t → ∃ a : ℝ, WaveMap.dt (WaveMap.dt u) (x, t) - WaveMap.lap u (x, t) = a • u (x, t)) (h_H006 : ∀ s t : ℝ, 0 < s → s < t → ∃ C : Set (WaveMap.X n), IsCompact C ∧ ∀ x : WaveMap.X n, x ∉ C → ∀ r ∈ Set.Icc s t, u (x, r) = q) : (∀ t : ℝ, 0 < t →
  Integrable (fun x : WaveMap.X n => WaveMap.density u (x, t)) ∧
  DifferentiableAt ℝ (WaveMap.energy u) t ∧ deriv (WaveMap.energy u) t = 0) ∧
  ∀ s t : ℝ, 0 < s → 0 < t → WaveMap.energy u s = WaveMap.energy u t := by
  exact @Translation.P n m u q h_H001 h_H002 h_H003 h_H004 h_H005 h_H006

#check @P
#print axioms P
end AuditBExport
