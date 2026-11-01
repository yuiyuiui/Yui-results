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

#check @T006
#print axioms T006

end Translation
