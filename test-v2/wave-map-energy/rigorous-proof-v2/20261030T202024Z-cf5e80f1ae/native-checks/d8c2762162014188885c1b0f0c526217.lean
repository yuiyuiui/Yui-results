import Mathlib
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
namespace WaveEnergy
abbrev X (n : ℕ) := Fin n → ℝ
abbrev V (m : ℕ) := EuclideanSpace ℝ (Fin m)
def domain (n : ℕ) : Set (X n × ℝ) := {p | 0 < p.2}
noncomputable def mu (n : ℕ) : Measure (X n) := Measure.pi (fun _ : Fin n => (volume : Measure ℝ))
noncomputable def dt {n : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : X n × ℝ → F) (p : X n × ℝ) : F := deriv (fun r : ℝ => f (p.1, r)) p.2
noncomputable def dx {n : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : X n × ℝ → F) (j : Fin n) (p : X n × ℝ) : F :=
  fderiv ℝ (fun y : X n => f (y, p.2)) p.1 (Pi.single j 1)
noncomputable def lap {n m : ℕ} (u : X n × ℝ → V m) (p : X n × ℝ) : V m :=
  ∑ j : Fin n, dx (dx u j) j p
noncomputable def density {n m : ℕ} (u : X n × ℝ → V m) (p : X n × ℝ) : ℝ :=
  ‖dt u p‖ ^ 2 + ∑ j : Fin n, ‖dx u j p‖ ^ 2
noncomputable def energy {n m : ℕ} (u : X n × ℝ → V m) (t : ℝ) : ℝ :=
  ∫ x : X n, density u (x, t) ∂mu n
noncomputable def kinetic {n m : ℕ} (u : X n × ℝ → V m) (p : X n × ℝ) : ℝ :=
  inner ℝ (dt u p) (dt (dt u) p)
noncomputable def mixed {n m : ℕ} (u : X n × ℝ → V m) (j : Fin n) (p : X n × ℝ) : ℝ :=
  inner ℝ (dx u j p) (dx (dt u) j p)
noncomputable def lapTerm {n m : ℕ} (u : X n × ℝ → V m) (j : Fin n) (p : X n × ℝ) : ℝ :=
  inner ℝ (dt u p) (dx (dx u j) j p)
noncomputable def flux {n m : ℕ} (u : X n × ℝ → V m) (j : Fin n) (p : X n × ℝ) : ℝ :=
  inner ℝ (dt u p) (dx u j p)
def box {n : ℕ} (R : ℝ) : Set (X n) := {x | ∀ j, x j ∈ Icc (-R) R}
def scalarTerms {n m : ℕ} (u : X n × ℝ → V m) : Set (X n × ℝ → ℝ) :=
  {f | f = density u ∨ f = dt (density u) ∨ f = kinetic u ∨
    ∃ j : Fin n, f = mixed u j ∨ f = lapTerm u j ∨ f = flux u j ∨ f = dx (flux u j) j}
structure Window {n m : ℕ} (u : X n × ℝ → V m) (q : V m)
    (t0 : ℝ) (C : Set (X n)) (R : ℝ) : Prop where
  compact : IsCompact C
  radius_pos : 0 < R
  inside : ∀ x ∈ C, ∀ j : Fin n, x j ∈ Ioo (-R) R
  constant : ∀ x, x ∉ C → ∀ r ∈ Icc (t0 / 2) (3 * t0 / 2), u (x, r) = q
  box_volume : mu n (box R) = ENNReal.ofReal ((2 * R) ^ n)
  box_finite : mu n (box R) < ⊤
  derivatives_zero : ∀ k : ℕ, 0 < k → ∀ x, x ∉ C →
    ∀ r ∈ Ioo (t0 / 2) (3 * t0 / 2), iteratedFDeriv ℝ k u (x, r) = 0
  sections : ∀ f ∈ scalarTerms u, ∀ r ∈ Ioo (t0 / 2) (3 * t0 / 2),
    Continuous (fun x => f (x, r)) ∧ (∀ x, x ∉ C → f (x, r) = 0) ∧
    Integrable (fun x => f (x, r)) (mu n)
  uniform : ∀ f ∈ scalarTerms u, ∀ a b : ℝ,
    Icc a b ⊆ Ioo (t0 / 2) (3 * t0 / 2) →
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ box R, ∀ r ∈ Icc a b, |f (x, r)| ≤ B
abbrev Other (n : ℕ) (j : Fin n) := {i : Fin n // i ≠ j} → ℝ
noncomputable def otherMu {n : ℕ} (j : Fin n) : Measure (Other n j) :=
  Measure.pi (fun _ : {i : Fin n // i ≠ j} => (volume : Measure ℝ))
def otherBox {n : ℕ} (j : Fin n) (R : ℝ) : Set (Other n j) :=
  {y | ∀ i, y i ∈ Icc (-R) R}
def insert {n : ℕ} (j : Fin n) (p : Other n j × ℝ) : X n :=
  fun i => if h : i = j then p.2 else p.1 ⟨i,h⟩
end WaveEnergy
open WaveEnergy

namespace Translation
set_option autoImplicit false

theorem T001 (n : ℕ) (m : ℕ) (u : X n × ℝ → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ u (domain n)) (h_H004 : ∀ x : X n, ∀ t : ℝ, 0 < t → ‖u (x,t)‖ = 1) :
    ∀ x : X n, ∀ t : ℝ, 0 < t →
  inner ℝ (u (x,t)) (dt u (x,t)) = 0 ∧
  inner ℝ (u (x,t)) (dt (dt u) (x,t)) = -(‖dt u (x,t)‖ ^ 2) ∧
  (∀ j : Fin n, inner ℝ (u (x,t)) (dx (dx u j) j (x,t)) = -(‖dx u j (x,t)‖ ^ 2)) := by
  have unit_direction : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      (f : E → V m) (s : Set E), IsOpen s → ContDiffOn ℝ ∞ f s →
      (∀ z ∈ s, ‖f z‖ = 1) → ∀ z ∈ s, ∀ v : E,
      inner ℝ (f z) (fderiv ℝ f z v) = 0 ∧
      inner ℝ (f z) (fderiv ℝ (fun y => fderiv ℝ f y v) z v) =
        -(‖fderiv ℝ f z v‖ ^ 2) := by
    intro E _ _ f s hs hf hn
    have hd : ∀ z ∈ s, DifferentiableAt ℝ f z := fun z hz =>
      (hf.contDiffAt (hs.mem_nhds hz)).differentiableAt (by simp)
    have hfirst : ∀ z ∈ s, ∀ v : E, inner ℝ (f z) (fderiv ℝ f z v) = 0 := by
      intro z hz v
      have he : (fun y => inner ℝ (f y) (f y)) =ᶠ[nhds z] (fun _ => (1 : ℝ)) := by
        filter_upwards [hs.mem_nhds hz] with y hy
        rw [real_inner_self_eq_norm_sq, hn y hy]
        norm_num
      have he' : fderiv ℝ (fun y => inner ℝ (f y) (f y)) z v = 0 := by
        rw [he.fderiv_eq]
        simp
      rw [fderiv_inner_apply ℝ (hd z hz) (hd z hz), real_inner_comm (f z) (fderiv ℝ f z v)] at he'
      linarith
    intro z hz v
    refine ⟨hfirst z hz v, ?_⟩
    have hD : ContDiffOn ℝ 1 (fun y => fderiv ℝ f y v) s :=
      (hf.fderiv_of_isOpen hs (by
        change ((1 + 1 : ℕ∞) : WithTop ℕ∞) ≤ (⊤ : ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top)).clm_apply contDiffOn_const
    have hdD : DifferentiableAt ℝ (fun y => fderiv ℝ f y v) z :=
      (hD.contDiffAt (hs.mem_nhds hz)).differentiableAt one_ne_zero
    have he : (fun y => inner ℝ (f y) (fderiv ℝ f y v)) =ᶠ[nhds z] (fun _ => (0 : ℝ)) := by
      filter_upwards [hs.mem_nhds hz] with y hy
      exact hfirst y hy v
    have he' : fderiv ℝ (fun y => inner ℝ (f y) (fderiv ℝ f y v)) z v = 0 := by
      rw [he.fderiv_eq]
      simp
    rw [fderiv_inner_apply ℝ (hd z hz) hdD, real_inner_self_eq_norm_sq] at he'
    linarith
  intro x t ht
  have htime : ContDiffOn ℝ ∞ (fun r : ℝ => u (x, r)) (Ioi 0) :=
    h_H002.comp (contDiffOn_const.prodMk contDiffOn_id) (by
      intro r hr
      exact hr)
  have hspace : ContDiffOn ℝ ∞ (fun y : X n => u (y, t)) univ :=
    h_H002.comp (contDiffOn_id.prodMk contDiffOn_const) (by
      intro y hy
      exact ht)
  have hT := unit_direction (fun r : ℝ => u (x, r)) (Ioi 0) isOpen_Ioi
    htime (fun r hr => h_H004 x r hr) t ht 1
  refine ⟨?_, ?_, ?_⟩
  · simpa only [dt, fderiv_apply_one_eq_deriv] using hT.1
  · simpa only [dt, fderiv_apply_one_eq_deriv] using hT.2
  · intro j
    have hS := unit_direction (fun y : X n => u (y, t)) univ isOpen_univ
      hspace (fun y _ => h_H004 y t ht) x (mem_univ x) (Pi.single j 1)
    simpa only [dx] using hS.2

theorem T002 (n : ℕ) (m : ℕ) (u : X n × ℝ → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ u (domain n)) (h_H004 : ∀ x : X n, ∀ t : ℝ, 0 < t → ‖u (x,t)‖ = 1) (h_H005 : ∀ x : X n, ∀ t : ℝ, 0 < t → ∃ a : ℝ, dt (dt u) (x,t) - lap u (x,t) = a • u (x,t)) (h_T001 : ∀ x : X n, ∀ t : ℝ, 0 < t →
  inner ℝ (u (x,t)) (dt u (x,t)) = 0 ∧
  inner ℝ (u (x,t)) (dt (dt u) (x,t)) = -(‖dt u (x,t)‖ ^ 2) ∧
  (∀ j : Fin n, inner ℝ (u (x,t)) (dx (dx u j) j (x,t)) = -(‖dx u j (x,t)‖ ^ 2))) :
    ∀ x : X n, ∀ t : ℝ, 0 < t →
  inner ℝ (u (x,t)) (dt u (x,t)) = 0 ∧
  inner ℝ (u (x,t)) (dt (dt u) (x,t)) = -(‖dt u (x,t)‖ ^ 2) ∧
  (∀ j : Fin n, inner ℝ (u (x,t)) (dx (dx u j) j (x,t)) = -(‖dx u j (x,t)‖ ^ 2)) ∧
  inner ℝ (dt u (x,t)) (dt (dt u) (x,t) - lap u (x,t)) = 0 ∧
  dt (dt u) (x,t) - lap u (x,t) =
    ((∑ j : Fin n, ‖dx u j (x,t)‖ ^ 2) - ‖dt u (x,t)‖ ^ 2) • u (x,t) ∧
  (∀ a : ℝ, dt (dt u) (x,t) - lap u (x,t) = a • u (x,t) →
    a = (∑ j : Fin n, ‖dx u j (x,t)‖ ^ 2) - ‖dt u (x,t)‖ ^ 2) := by
  intro x t ht
  obtain ⟨h_tan, h_tt, h_xx⟩ := h_T001 x t ht
  have h_self : inner ℝ (u (x, t)) (u (x, t)) = 1 := by
    rw [real_inner_self_eq_norm_sq, h_H004 x t ht]
    norm_num
  have h_lap : inner ℝ (u (x, t)) (lap u (x, t)) =
      -(∑ j : Fin n, ‖dx u j (x, t)‖ ^ 2) := by
    simp only [lap, inner_sum, h_xx, Finset.sum_neg_distrib]
  have h_scalar : ∀ a : ℝ,
      dt (dt u) (x, t) - lap u (x, t) = a • u (x, t) →
      a = (∑ j : Fin n, ‖dx u j (x, t)‖ ^ 2) - ‖dt u (x, t)‖ ^ 2 := by
    intro a ha
    have h_dot := congrArg (fun v : V m => inner ℝ (u (x, t)) v) ha
    rw [inner_sub_right, inner_smul_right, h_self, h_tt, h_lap] at h_dot
    linarith
  obtain ⟨a, ha⟩ := h_H005 x t ht
  have h_rev : inner ℝ (dt u (x, t)) (u (x, t)) = 0 := by
    calc
      inner ℝ (dt u (x, t)) (u (x, t)) =
          inner ℝ (u (x, t)) (dt u (x, t)) :=
        real_inner_comm (u (x, t)) (dt u (x, t))
      _ = 0 := h_tan
  have h_orth : inner ℝ (dt u (x, t)) (dt (dt u) (x, t) - lap u (x, t)) = 0 := by
    rw [ha, inner_smul_right, h_rev, mul_zero]
  refine ⟨h_tan, h_tt, h_xx, h_orth, ?_, h_scalar⟩
  rw [ha, h_scalar a ha]

theorem T003 (n : ℕ) (m : ℕ) (u : X n × ℝ → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H006 : ∀ s t : ℝ, 0 < s → s < t → ∃ C : Set (X n), IsCompact C ∧ ∀ x : X n, x ∉ C → ∀ r : ℝ, r ∈ Icc s t → u (x,r) = q) :
    ∀ t0 : ℝ, 0 < t0 →
  ∃ C : Set (X n), ∃ R : ℝ, IsCompact C ∧ 0 < R ∧
    (∀ x ∈ C, ∀ j : Fin n, x j ∈ Ioo (-R) R) ∧
    (∀ x, x ∉ C → ∀ r ∈ Icc (t0/2) (3*t0/2), u (x,r) = q) := by
  intro t0 ht0
  obtain ⟨C, hC, hconstant⟩ := h_H006 (t0 / 2) (3 * t0 / 2) (by linarith) (by linarith)
  obtain ⟨R, hRpos, hR⟩ := hC.isBounded.exists_pos_norm_lt
  refine ⟨C, R, hC, hRpos, ?_, hconstant⟩
  intro x hx j
  have hcoord : |x j| ≤ ‖x‖ := by
    simpa only [Real.norm_eq_abs] using (norm_le_pi_norm x j)
  exact abs_lt.mp (lt_of_le_of_lt hcoord (hR x hx))

theorem T004 (n : ℕ) (m : ℕ) (u : X n × ℝ → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ u (domain n)) (h_H003 : ‖q‖ = 1) (h_H006 : ∀ s t : ℝ, 0 < s → s < t → ∃ C : Set (X n), IsCompact C ∧ ∀ x : X n, x ∉ C → ∀ r : ℝ, r ∈ Icc s t → u (x,r) = q) (h_T003 : ∀ t0 : ℝ, 0 < t0 →
  ∃ C : Set (X n), ∃ R : ℝ, IsCompact C ∧ 0 < R ∧
    (∀ x ∈ C, ∀ j : Fin n, x j ∈ Ioo (-R) R) ∧
    (∀ x, x ∉ C → ∀ r ∈ Icc (t0/2) (3*t0/2), u (x,r) = q)) :
    (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (X n), ∃ R : ℝ, Window u q t0 C R) ∧
  ContDiffOn ℝ ∞ (density u) (domain n) ∧
  ContDiffOn ℝ ∞ (dt (density u)) (domain n) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : X n => density u (x,t)) (mu n)) := by
  classical
  have hop : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : X n × ℝ → F),
      ContDiffOn ℝ ∞ f (domain n) → ContDiffOn ℝ ∞ (dt f) (domain n) ∧
      ∀ j, ContDiffOn ℝ ∞ (dx f j) (domain n) := by
    intro F _ _ f hf
    have ho : IsOpen (domain n) := isOpen_lt continuous_const continuous_snd
    constructor
    · intro p hp
      have hf' : ContDiffAt ℝ ∞ (fun z : (X n × ℝ) × ℝ => f (z.1.1, z.2)) (p, p.2) :=
        (hf.contDiffAt (ho.mem_nhds hp)).comp _ (contDiffAt_fst.fst.prodMk contDiffAt_snd)
      have hh : ContDiffAt ℝ ∞ (fun p : X n × ℝ => fderiv ℝ (fun r : ℝ => f (p.1,r)) p.2) p :=
        hf'.fderiv contDiffAt_snd (by simp)
      have he : (fun p : X n × ℝ => (fderiv ℝ (fun r : ℝ => f (p.1,r)) p.2) 1) = dt f := by
        funext p
        exact fderiv_apply_one_eq_deriv
      rw [← he]
      exact (hh.clm_apply contDiffAt_const).contDiffWithinAt
    · intro j p hp
      have hf' : ContDiffAt ℝ ∞ (fun z : (X n × ℝ) × X n => f (z.2, z.1.2)) (p, p.1) :=
        (hf.contDiffAt (ho.mem_nhds hp)).comp _ (contDiffAt_snd.prodMk contDiffAt_fst.snd)
      exact ((hf'.fderiv contDiffAt_fst (by simp)).clm_apply contDiffAt_const).contDiffWithinAt
  have ht := (hop u h_H002).1
  have hx := (hop u h_H002).2
  have htt := (hop (dt u) ht).1
  have hxt := (hop (dt u) ht).2
  have hxx := fun j => (hop (dx u j) (hx j)).2 j
  have he : ContDiffOn ℝ ∞ (density u) (domain n) := by
    exact (ht.norm_sq ℝ).add (ContDiffOn.sum (fun j _ => (hx j).norm_sq ℝ))
  have het := (hop (density u) he).1
  have hk : ContDiffOn ℝ ∞ (kinetic u) (domain n) := ht.inner ℝ htt
  have hm : ∀ j, ContDiffOn ℝ ∞ (mixed u j) (domain n) := fun j => (hx j).inner ℝ (hxt j)
  have hl : ∀ j, ContDiffOn ℝ ∞ (lapTerm u j) (domain n) := fun j => ht.inner ℝ (hxx j)
  have hf : ∀ j, ContDiffOn ℝ ∞ (flux u j) (domain n) := fun j => ht.inner ℝ (hx j)
  have hdf : ∀ j, ContDiffOn ℝ ∞ (dx (flux u j) j) (domain n) := fun j => (hop _ (hf j)).2 j
  have hsc : ∀ f ∈ scalarTerms u, ContDiffOn ℝ ∞ f (domain n) := by
    intro f h
    rcases h with rfl | rfl | rfl | ⟨j, rfl | rfl | rfl | rfl⟩
    · exact he
    · exact het
    · exact hk
    · exact hm j
    · exact hl j
    · exact hf j
    · exact hdf j
  have hzsc : ∀ (O : Set (X n × ℝ)), IsOpen O → EqOn u (fun _ => q) O →
      ∀ f ∈ scalarTerms u, EqOn f (fun _ => 0) O := by
    classical
    have hz : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
        (f : X n × ℝ → F) (c : F) (O : Set (X n × ℝ)), IsOpen O →
        EqOn f (fun _ => c) O → EqOn (dt f) (fun _ => 0) O ∧ ∀ j, EqOn (dx f j) (fun _ => 0) O := by
      intro F _ _ f c O hO he
      constructor
      · intro p hp
        have ht : (fun r : ℝ => f (p.1,r)) =ᶠ[nhds p.2] (fun _ => c) := by
          have hh : O ∈ nhds (p.1,p.2) := hO.mem_nhds hp
          filter_upwards [(continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds hh] with r hr
          exact he hr
        simpa only [dt, deriv_const] using ht.deriv_eq
      · intro j p hp
        have ht : (fun y : X n => f (y,p.2)) =ᶠ[nhds p.1] (fun _ => c) := by
          have hh : O ∈ nhds (p.1,p.2) := hO.mem_nhds hp
          filter_upwards [(continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds hh] with y hy
          exact he hy
        change (fderiv ℝ (fun y : X n => f (y,p.2)) p.1) (Pi.single j 1) = 0
        rw [ht.fderiv_eq]
        simp
    intro O hO hu
    have ht0 := (hz u q O hO hu).1
    have hx0 := (hz u q O hO hu).2
    have he0 : EqOn (density u) (fun _ => 0) O := by
      intro p hp
      simp [density, ht0 hp, fun j => hx0 j hp]
    have het0 := (hz (density u) 0 O hO he0).1
    have hf0 : ∀ j, EqOn (flux u j) (fun _ => 0) O := by
      intro j p hp
      simp [flux, ht0 hp]
    have hdf0 := fun j => (hz (flux u j) 0 O hO (hf0 j)).2 j
    intro f h
    rcases h with rfl | rfl | rfl | ⟨j, rfl | rfl | rfl | rfl⟩
    · exact he0
    · exact het0
    · intro p hp; simp [kinetic, ht0 hp]
    · intro p hp; simp [mixed, hx0 j hp]
    · intro p hp; simp [lapTerm, ht0 hp]
    · exact hf0 j
    · exact hdf0 j
  have hiter : ∀ (O : Set (X n × ℝ)), IsOpen O → EqOn u (fun _ => q) O →
      ∀ k : ℕ, 0 < k → ∀ p ∈ O, iteratedFDeriv ℝ k u p = 0 := by
    intro O hO he k hk p hp
    have ev : u =ᶠ[nhds p] (fun _ => q) := by
      filter_upwards [hO.mem_nhds hp] with y hy
      exact he hy
    have ev' : u =ᶠ[nhdsWithin p univ] (fun _ => q) := by simpa using ev
    have hh := (ev'.iteratedFDerivWithin ℝ k).eq_of_nhdsWithin (mem_univ p)
    simpa only [iteratedFDerivWithin_univ, iteratedFDeriv_const_of_ne (Nat.ne_of_gt hk), Pi.zero_apply] using hh
  have hbox : ∀ R : ℝ, 0 < R → IsCompact (box R : Set (X n)) ∧
      mu n (box R) = ENNReal.ofReal ((2 * R)^n) ∧ mu n (box R) < ⊤ := by
    intro R hR
    have hb : (box R : Set (X n)) = Set.pi univ (fun _ : Fin n => Icc (-R) R) := by
      ext x
      simp only [box, mem_setOf_eq, Set.mem_pi, mem_univ, forall_const]
    have hc : IsCompact (box R : Set (X n)) := by
      rw [hb]
      exact isCompact_univ_pi (fun _ => isCompact_Icc)
    have hv : mu n (box R) = ENNReal.ofReal ((2 * R)^n) := by
      rw [mu, hb, Measure.pi_pi]
      simp only [Real.volume_Icc, sub_neg_eq_add, ← two_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact (ENNReal.ofReal_pow (by positivity) n).symm
    exact ⟨hc, hv, by rw [hv]; exact ENNReal.ofReal_lt_top⟩
  have hint : ∀ (R : ℝ) (C : Set (X n)) (f : X n → ℝ),
      IsCompact (box R : Set (X n)) → mu n (box R) < ⊤ → C ⊆ box R →
      Continuous f → (∀ x, x ∉ C → f x = 0) → Integrable f (mu n) := by
    intro R C f hQ hfin hCQ hc hz
    obtain ⟨B, hB⟩ := hQ.exists_bound_of_continuousOn hc.continuousOn
    have hi : Integrable ((box R).indicator (fun _ : X n => max B 0)) (mu n) :=
      (integrableOn_const hfin.ne : IntegrableOn (fun _ : X n => max B 0) (box R) (mu n)).integrable_indicator hQ.measurableSet
    refine hi.mono' hc.aestronglyMeasurable (ae_of_all _ (fun x => ?_))
    by_cases hx : x ∈ box R
    · rw [Set.indicator_of_mem hx]
      exact (hB x hx).trans (le_max_left _ _)
    · have hnC : x ∉ C := fun h => hx (hCQ h)
      simp [Set.indicator_of_notMem hx, hz x hnC]
  have hw : ∀ t0 : ℝ, 0 < t0 → ∃ C : Set (X n), ∃ R : ℝ, Window u q t0 C R := by
    intro t0 ht0
    obtain ⟨C, R, hC, hR, hinside, hconst⟩ := h_T003 t0 ht0
    obtain ⟨hQ, hvol, hfin⟩ := hbox R hR
    have hCQ : C ⊆ box R := by
      intro x hx j
      exact ⟨(hinside x hx j).1.le, (hinside x hx j).2.le⟩
    let O : Set (X n × ℝ) := Cᶜ ×ˢ Ioo (t0/2) (3*t0/2)
    have hO : IsOpen O := hC.isClosed.isOpen_compl.prod isOpen_Ioo
    have huO : EqOn u (fun _ => q) O := by
      intro p hp
      exact hconst p.1 hp.1 p.2 ⟨hp.2.1.le, hp.2.2.le⟩
    have hpos : ∀ r ∈ Ioo (t0/2) (3*t0/2), 0 < r := by
      intro r hr
      linarith [hr.1]
    have hcont : ∀ f ∈ scalarTerms u, ∀ r ∈ Ioo (t0/2) (3*t0/2),
        Continuous (fun x : X n => f (x,r)) := by
      intro f hf r hr
      exact (hsc f hf).continuousOn.comp_continuous
        (continuous_id.prodMk continuous_const) (fun x => hpos r hr)
    have hzero : ∀ f ∈ scalarTerms u, ∀ r ∈ Ioo (t0/2) (3*t0/2),
        ∀ x, x ∉ C → f (x,r) = 0 := by
      intro f hf r hr x hx
      exact hzsc O hO huO f hf ⟨hx, hr⟩
    refine ⟨C, R, hC, hR, hinside, hconst, hvol, hfin, ?_, ?_, ?_⟩
    · intro k hk x hx r hr
      exact hiter O hO huO k hk (x,r) ⟨hx,hr⟩
    · intro f hf r hr
      exact ⟨hcont f hf r hr, hzero f hf r hr,
        hint R C _ hQ hfin hCQ (hcont f hf r hr) (hzero f hf r hr)⟩
    · intro f hf a b hab
      have hc : ContinuousOn f ((box R) ×ˢ Icc a b) :=
        (hsc f hf).continuousOn.mono (fun p hp => hpos p.2 (hab hp.2))
      obtain ⟨B,hB⟩ := (hQ.prod isCompact_Icc).exists_bound_of_continuousOn hc
      refine ⟨max B 0, le_max_right _ _, ?_⟩
      intro x hx r hr
      exact (hB (x,r) ⟨hx,hr⟩).trans (le_max_left _ _)
  refine ⟨hw, he, het, ?_⟩
  intro t ht
  obtain ⟨C, R, hW⟩ := hw t ht
  have htt : t ∈ Ioo (t/2) (3*t/2) := by constructor <;> linarith
  exact (hW.sections (density u) (Or.inl rfl) t htt).2.2

theorem T005 (n : ℕ) (m : ℕ) (u : X n × ℝ → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ u (domain n)) (h_T004 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (X n), ∃ R : ℝ, Window u q t0 C R) ∧
  ContDiffOn ℝ ∞ (density u) (domain n) ∧
  ContDiffOn ℝ ∞ (dt (density u)) (domain n) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : X n => density u (x,t)) (mu n))) :
    ∀ x : X n, ∀ t : ℝ, 0 < t →
  HasDerivAt (fun r : ℝ => density u (x,r)) (dt (density u) (x,t)) t ∧
  dt (density u) (x,t) = 2 * kinetic u (x,t) + 2 * ∑ j : Fin n, mixed u j (x,t) := by
  have repr : ∀ (f : X n × ℝ → V m) (p : X n × ℝ),
      DifferentiableAt ℝ f p →
      dt f p = fderiv ℝ f p (0, 1) ∧
      ∀ j, dx f j p = fderiv ℝ f p (Pi.single j 1, 0) := by
    intro f p hf
    have ht := hf.hasFDerivAt.comp_hasDerivAt p.2
      ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
    refine ⟨ht.deriv, ?_⟩
    intro j
    have hs := hf.hasFDerivAt.comp p.1
      ((hasFDerivAt_id (𝕜 := ℝ) p.1).prodMk (hasFDerivAt_const p.2 p.1))
    exact congrArg (fun L : X n →L[ℝ] V m => L (Pi.single j 1)) hs.fderiv
  have hopen : IsOpen (domain n) := isOpen_lt continuous_const continuous_snd
  have hc : ∀ p : X n × ℝ, 0 < p.2 → ContDiffAt ℝ ∞ u p := by
    intro p hp
    exact h_H002.contDiffAt (hopen.mem_nhds hp)
  have hd : ∀ p : X n × ℝ, 0 < p.2 → DifferentiableAt ℝ u p :=
    fun p hp => (hc p hp).differentiableAt (by simp)
  have heval : ∀ (p : X n × ℝ), 0 < p.2 → ∀ v : X n × ℝ,
      HasFDerivAt (fun z => fderiv ℝ u z v)
        ((fderiv ℝ (fderiv ℝ u) p).flip v) p := by
    intro p hp v
    have hD : DifferentiableAt ℝ (fderiv ℝ u) p :=
      ((hc p hp).fderiv_right (m := 1) (by exact WithTop.coe_le_coe.mpr le_top)).differentiableAt one_ne_zero
    simpa only [ContinuousLinearMap.comp_zero, zero_add] using
      hD.hasFDerivAt.clm_apply (hasFDerivAt_const v p)
  have hdt : ∀ p : X n × ℝ, 0 < p.2 →
      HasFDerivAt (dt u) ((fderiv ℝ (fderiv ℝ u) p).flip (0, 1)) p := by
    intro p hp
    apply (heval p hp (0, 1)).congr_of_eventuallyEq
    filter_upwards [hopen.mem_nhds hp] with z hz
    exact (repr u z (hd z hz)).1
  have hdx : ∀ (p : X n × ℝ), 0 < p.2 → ∀ j : Fin n,
      HasFDerivAt (dx u j)
        ((fderiv ℝ (fderiv ℝ u) p).flip (Pi.single j 1, 0)) p := by
    intro p hp j
    apply (heval p hp (Pi.single j 1, 0)).congr_of_eventuallyEq
    filter_upwards [hopen.mem_nhds hp] with z hz
    exact (repr u z (hd z hz)).2 j
  have hmix : ∀ p : X n × ℝ, 0 < p.2 → ∀ j : Fin n,
      dt (dx u j) p = dx (dt u) j p := by
    intro p hp j
    calc
      dt (dx u j) p = fderiv ℝ (dx u j) p (0,1) :=
        (repr (dx u j) p (hdx p hp j).differentiableAt).1
      _ = fderiv ℝ (fderiv ℝ u) p (0,1) (Pi.single j 1,0) :=
        congrArg (fun L : (X n × ℝ) →L[ℝ] V m => L (0,1)) (hdx p hp j).fderiv
      _ = fderiv ℝ (fderiv ℝ u) p (Pi.single j 1,0) (0,1) :=
        ((hc p hp).isSymmSndFDerivAt (by
          simp only [minSmoothness, if_pos (show IsRCLikeNormedField ℝ from inferInstance)]
          exact WithTop.coe_le_coe.mpr le_top)).eq _ _
      _ = fderiv ℝ (dt u) p (Pi.single j 1,0) :=
        (congrArg (fun L : (X n × ℝ) →L[ℝ] V m => L (Pi.single j 1,0))
          (hdt p hp).fderiv).symm
      _ = dx (dt u) j p :=
        ((repr (dt u) p (hdt p hp).differentiableAt).2 j).symm
  have hsection : ∀ (f : X n × ℝ → V m) (p : X n × ℝ),
      DifferentiableAt ℝ f p →
      HasDerivAt (fun r => f (p.1,r)) (dt f p) p.2 := by
    intro f p hf
    rw [(repr f p hf).1]
    exact hf.hasFDerivAt.comp_hasDerivAt p.2
      ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
  intro x t ht
  have hv := (hsection (dt u) (x,t) (hdt (x,t) ht).differentiableAt).norm_sq
  have hs : ∀ j : Fin n, HasDerivAt (fun r => ‖dx u j (x,r)‖ ^ 2)
      (2 * mixed u j (x,t)) t := by
    intro j
    have hj := (hsection (dx u j) (x,t) (hdx (x,t) ht j).differentiableAt).norm_sq
    rw [hmix (x,t) ht j] at hj
    exact hj
  have hall : HasDerivAt (fun r => density u (x,r))
      (2 * kinetic u (x,t) + 2 * ∑ j : Fin n, mixed u j (x,t)) t := by
    simpa only [density, kinetic, Finset.mul_sum, Pi.add_def] using
      hv.add (HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => hs j))
  have heq : dt (density u) (x,t) =
      2 * kinetic u (x,t) + 2 * ∑ j : Fin n, mixed u j (x,t) := hall.deriv
  exact ⟨by rw [heq]; exact hall, heq⟩

theorem T006 (n : ℕ) (m : ℕ) (u : X n × ℝ → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ u (domain n)) (h_T004 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (X n), ∃ R : ℝ, Window u q t0 C R) ∧
  ContDiffOn ℝ ∞ (density u) (domain n) ∧
  ContDiffOn ℝ ∞ (dt (density u)) (domain n) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : X n => density u (x,t)) (mu n))) (h_T005 : ∀ x : X n, ∀ t : ℝ, 0 < t →
  HasDerivAt (fun r : ℝ => density u (x,r)) (dt (density u) (x,t)) t ∧
  dt (density u) (x,t) = 2 * kinetic u (x,t) + 2 * ∑ j : Fin n, mixed u j (x,t)) :
    ∀ t0 : ℝ, 0 < t0 → ∃ R B : ℝ, 0 < R ∧ 0 ≤ B ∧
  Integrable ((box R).indicator (fun _ : X n => B)) (mu n) ∧
  (∀ x ∈ box R, ∀ r ∈ Icc (t0-t0/4) (t0+t0/4), |dt (density u) (x,r)| ≤ B) ∧
  (∀ x : X n, ∀ h : ℝ, 0 < |h| → |h| < t0/4 →
    |(density u (x,t0+h) - density u (x,t0))/h| ≤
      (box R).indicator (fun _ : X n => B) x) := by
  intro t0 ht0
  obtain ⟨C, R, w⟩ := h_T004.1 t0 ht0
  have hK : Icc (t0 - t0 / 4) (t0 + t0 / 4) ⊆
      Ioo (t0 / 2) (3 * t0 / 2) := by
    intro r hr
    constructor <;> linarith [hr.1, hr.2]
  obtain ⟨B, hB0, hB⟩ := w.uniform (dt (density u))
    (Or.inr (Or.inl rfl)) (t0 - t0 / 4) (t0 + t0 / 4) hK
  have hbox : MeasurableSet (box (n := n) R) := by
    change MeasurableSet {x : X n | ∀ j : Fin n, x j ∈ Icc (-R) R}
    simp only [setOf_forall]
    exact MeasurableSet.iInter (fun j => (measurable_pi_apply j) measurableSet_Icc)
  have hint : Integrable ((box R).indicator (fun _ : X n => B)) (mu n) :=
    (integrableOn_const (C := B) w.box_finite.ne).integrable_indicator hbox
  refine ⟨R, B, w.radius_pos, hB0, hint, hB, ?_⟩
  intro x h hh0 hh
  have hsmall := abs_lt.mp hh
  have htmem : t0 ∈ Icc (t0 - t0 / 4) (t0 + t0 / 4) := by
    constructor <;> linarith
  have hthmem : t0 + h ∈ Icc (t0 - t0 / 4) (t0 + t0 / 4) := by
    constructor <;> linarith [hsmall.1, hsmall.2]
  by_cases hx : x ∈ box R
  · rw [Set.indicator_of_mem hx]
    have hder : ∀ r ∈ Icc (t0 - t0 / 4) (t0 + t0 / 4),
        HasDerivAt (fun s : ℝ => density u (x, s)) (dt (density u) (x, r)) r := by
      intro r hr
      exact (h_T005 x r (by have := (hK hr).1; linarith)).1
    have hslope : ∀ a b : ℝ,
        a ∈ Icc (t0 - t0 / 4) (t0 + t0 / 4) →
        b ∈ Icc (t0 - t0 / 4) (t0 + t0 / 4) → a < b →
        |(density u (x, b) - density u (x, a)) / (b - a)| ≤ B := by
      intro a b ha hb hab
      have hsub : Icc a b ⊆ Icc (t0 - t0 / 4) (t0 + t0 / 4) := by
        intro r hr
        exact ⟨ha.1.trans hr.1, hr.2.trans hb.2⟩
      obtain ⟨c, hc, heq⟩ := exists_hasDerivAt_eq_slope
        (fun r : ℝ => density u (x, r)) (fun r : ℝ => dt (density u) (x, r))
        hab
        (fun r hr => (hder r (hsub hr)).continuousAt.continuousWithinAt)
        (fun r hr => hder r (hsub ⟨hr.1.le, hr.2.le⟩))
      rw [← heq]
      exact hB x hx c (hsub ⟨hc.1.le, hc.2.le⟩)
    have hne : h ≠ 0 := by intro hz; simp [hz] at hh0
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have hs := hslope (t0 + h) t0 hthmem htmem (by linarith)
      have heq : (density u (x, t0 + h) - density u (x, t0)) / h =
          (density u (x, t0) - density u (x, t0 + h)) / (t0 - (t0 + h)) := by
        rw [show t0 - (t0 + h) = -h by ring]
        rw [show density u (x, t0) - density u (x, t0 + h) =
          -(density u (x, t0 + h) - density u (x, t0)) by ring]
        exact (neg_div_neg_eq _ _).symm
      rw [heq]
      exact hs
    · simpa only [add_sub_cancel_left] using
        hslope t0 (t0 + h) htmem hthmem (by linarith)
  · rw [Set.indicator_of_notMem hx]
    have hxC : x ∉ C := by
      intro hxC
      apply hx
      intro j
      exact ⟨(w.inside x hxC j).1.le, (w.inside x hxC j).2.le⟩
    have hz : ∀ r ∈ Icc (t0 - t0 / 4) (t0 + t0 / 4), density u (x, r) = 0 := by
      intro r hr
      exact (w.sections (density u) (Or.inl rfl) r (hK hr)).2.1 x hxC
    rw [hz (t0 + h) hthmem, hz t0 htmem]
    simp

theorem T007 (n : ℕ) (m : ℕ) (u : X n × ℝ → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ u (domain n)) (h_T004 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (X n), ∃ R : ℝ, Window u q t0 C R) ∧
  ContDiffOn ℝ ∞ (density u) (domain n) ∧
  ContDiffOn ℝ ∞ (dt (density u)) (domain n) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : X n => density u (x,t)) (mu n))) (h_T005 : ∀ x : X n, ∀ t : ℝ, 0 < t →
  HasDerivAt (fun r : ℝ => density u (x,r)) (dt (density u) (x,t)) t ∧
  dt (density u) (x,t) = 2 * kinetic u (x,t) + 2 * ∑ j : Fin n, mixed u j (x,t)) (h_T006 : ∀ t0 : ℝ, 0 < t0 → ∃ R B : ℝ, 0 < R ∧ 0 ≤ B ∧
  Integrable ((box R).indicator (fun _ : X n => B)) (mu n) ∧
  (∀ x ∈ box R, ∀ r ∈ Icc (t0-t0/4) (t0+t0/4), |dt (density u) (x,r)| ≤ B) ∧
  (∀ x : X n, ∀ h : ℝ, 0 < |h| → |h| < t0/4 →
    |(density u (x,t0+h) - density u (x,t0))/h| ≤
      (box R).indicator (fun _ : X n => B) x)) :
    ∀ t0 : ℝ, 0 < t0 → ∀ h : ℕ → ℝ,
  (∀ k : ℕ, 0 < |h k| ∧ |h k| < t0/4) →
  Tendsto h atTop (nhds 0) →
  Tendsto (fun k : ℕ => (energy u (t0+h k) - energy u t0)/h k) atTop
    (nhds (∫ x : X n, dt (density u) (x,t0) ∂mu n)) := by
  intro t0 ht0 h hs hl
  obtain ⟨R, B, hR, hB, hBI, hbound, hdom⟩ := h_T006 t0 ht0
  obtain ⟨C, S, hW⟩ := h_T004.1 t0 ht0
  have hmid : t0 ∈ Ioo (t0 / 2) (3 * t0 / 2) := by
    constructor <;> linarith
  have hwin (k : ℕ) : t0 + h k ∈ Ioo (t0 / 2) (3 * t0 / 2) := by
    have ha := (hs k).2
    have hb := neg_abs_le (h k)
    have hc := le_abs_self (h k)
    constructor <;> linarith
  have hpos (k : ℕ) : 0 < t0 + h k := by
    have := (hwin k).1
    linarith
  have hcont (r : ℝ) (hr : r ∈ Ioo (t0 / 2) (3 * t0 / 2)) :
      Continuous (fun x : X n => density u (x,r)) :=
    (hW.sections (density u) (by exact Or.inl rfl) r hr).1
  let F : ℕ → X n → ℝ :=
    fun k x => (density u (x,t0+h k) - density u (x,t0)) / h k
  have hmeas (k : ℕ) : AEStronglyMeasurable (F k) (mu n) := by
    exact (((hcont (t0 + h k) (hwin k)).sub (hcont t0 hmid)).div_const (h k)).aestronglyMeasurable
  have hp : Tendsto h atTop (nhdsWithin 0 ({0}ᶜ : Set ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hl, Filter.Eventually.of_forall (fun k => by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
        (abs_pos.mp (hs k).1 : h k ≠ 0))⟩
  have hpoint (x : X n) :
      Tendsto (fun k => F k x) atTop (nhds (dt (density u) (x,t0))) := by
    have hd := ((h_T005 x t0 ht0).1.tendsto_slope_zero).comp hp
    simpa only [F, Function.comp_def, smul_eq_mul, div_eq_mul_inv, mul_comm] using hd
  have hlim :
      Tendsto (fun k => ∫ x : X n, F k x ∂mu n) atTop
        (nhds (∫ x : X n, dt (density u) (x,t0) ∂mu n)) := by
    apply tendsto_integral_of_dominated_convergence
      ((box R).indicator (fun _ : X n => B)) hmeas hBI
    · intro k
      exact Filter.Eventually.of_forall (fun x => by
        simpa only [F, Real.norm_eq_abs] using hdom x (h k) (hs k).1 (hs k).2)
    · exact Filter.Eventually.of_forall hpoint
  have hid (k : ℕ) :
      (∫ x : X n, F k x ∂mu n) =
        (energy u (t0+h k) - energy u t0) / h k := by
    dsimp only [F]
    rw [integral_div, integral_sub (h_T004.2.2.2 (t0+h k) (hpos k))
      (h_T004.2.2.2 t0 ht0)]
    rfl
  simpa only [hid] using hlim

theorem T008 (n : ℕ) (m : ℕ) (u : X n × ℝ → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ u (domain n)) (h_T004 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (X n), ∃ R : ℝ, Window u q t0 C R) ∧
  ContDiffOn ℝ ∞ (density u) (domain n) ∧
  ContDiffOn ℝ ∞ (dt (density u)) (domain n) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : X n => density u (x,t)) (mu n))) (h_T005 : ∀ x : X n, ∀ t : ℝ, 0 < t →
  HasDerivAt (fun r : ℝ => density u (x,r)) (dt (density u) (x,t)) t ∧
  dt (density u) (x,t) = 2 * kinetic u (x,t) + 2 * ∑ j : Fin n, mixed u j (x,t)) (h_T007 : ∀ t0 : ℝ, 0 < t0 → ∀ h : ℕ → ℝ,
  (∀ k : ℕ, 0 < |h k| ∧ |h k| < t0/4) →
  Tendsto h atTop (nhds 0) →
  Tendsto (fun k : ℕ => (energy u (t0+h k) - energy u t0)/h k) atTop
    (nhds (∫ x : X n, dt (density u) (x,t0) ∂mu n))) :
    ∀ t : ℝ, 0 < t →
  DifferentiableAt ℝ (energy u) t ∧
  deriv (energy u) t = (∫ x : X n, dt (density u) (x,t) ∂mu n) ∧
  deriv (energy u) t =
    2 * (∫ x : X n, kinetic u (x,t) ∂mu n) +
    2 * ∑ j : Fin n, (∫ x : X n, mixed u j (x,t) ∂mu n) ∧
  Integrable (fun x : X n => dt (density u) (x,t)) (mu n) ∧
  Integrable (fun x : X n => kinetic u (x,t)) (mu n) ∧
  (∀ j : Fin n, Integrable (fun x : X n => mixed u j (x,t)) (mu n)) ∧
  (∀ x : X n, dt (density u) (x,t) =
    2 * kinetic u (x,t) + 2 * ∑ j : Fin n, mixed u j (x,t)) := by
  intro t ht
  have hder : HasDerivAt (energy u) (∫ x : X n, dt (density u) (x,t) ∂mu n) t := by
    apply hasDerivAt_iff_tendsto_slope_zero.mpr
    have hlim : Tendsto (fun h : ℝ => (energy u (t+h) - energy u t)/h)
        (nhdsWithin 0 ({0}ᶜ)) (nhds (∫ x : X n, dt (density u) (x,t) ∂mu n)) := by
      apply Filter.tendsto_iff_seq_tendsto.mpr
      intro h hh
      have hh0 : Tendsto h atTop (nhds (0 : ℝ)) :=
        (tendsto_nhdsWithin_iff.mp hh).1
      have hne : ∀ᶠ k in atTop, h k ≠ 0 := by
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
          (tendsto_nhdsWithin_iff.mp hh).2
      have hsmall : ∀ᶠ k in atTop, |h k| < t/4 := by
        have ha : Tendsto (fun k => |h k|) atTop (nhds (0 : ℝ)) := by
          simpa using hh0.abs
        exact ha.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < t/4))
      obtain ⟨N, hN⟩ := eventually_atTop.mp (hne.and hsmall)
      have hs := h_T007 t ht (fun k => h (k+N))
        (fun k => ⟨abs_pos.mpr (hN (k+N) (Nat.le_add_left N k)).1,
          (hN (k+N) (Nat.le_add_left N k)).2⟩)
        (hh0.comp (tendsto_add_atTop_nat N))
      exact (tendsto_add_atTop_iff_nat N).mp hs
    simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using hlim
  obtain ⟨C, R, hw⟩ := h_T004.1 t ht
  have htwin : t ∈ Ioo (t/2) (3*t/2) := by constructor <;> linarith
  have hid : Integrable (fun x : X n => dt (density u) (x,t)) (mu n) :=
    (hw.sections (dt (density u)) (by simp [scalarTerms]) t htwin).2.2
  have hik : Integrable (fun x : X n => kinetic u (x,t)) (mu n) :=
    (hw.sections (kinetic u) (by simp [scalarTerms]) t htwin).2.2
  have him : ∀ j : Fin n, Integrable (fun x : X n => mixed u j (x,t)) (mu n) := by
    intro j
    exact (hw.sections (mixed u j)
      (by
        change _ = density u ∨ _ = dt (density u) ∨ _ = kinetic u ∨ _
        exact Or.inr (Or.inr (Or.inr ⟨j, Or.inl rfl⟩)))
      t htwin).2.2
  have hp : ∀ x : X n, dt (density u) (x,t) =
      2 * kinetic u (x,t) + 2 * ∑ j : Fin n, mixed u j (x,t) :=
    fun x => (h_T005 x t ht).2
  have his : Integrable (fun x : X n => ∑ j : Fin n, mixed u j (x,t)) (mu n) :=
    integrable_finsetSum Finset.univ (fun j _ => him j)
  have heq : (∫ x : X n, dt (density u) (x,t) ∂mu n) =
      2 * (∫ x : X n, kinetic u (x,t) ∂mu n) +
        2 * ∑ j : Fin n, (∫ x : X n, mixed u j (x,t) ∂mu n) := by
    calc
      _ = ∫ x : X n, (2 * kinetic u (x,t) +
          2 * ∑ j : Fin n, mixed u j (x,t)) ∂mu n :=
        integral_congr_ae (Filter.Eventually.of_forall hp)
      _ = _ := by
        rw [integral_add (hik.const_mul 2) (his.const_mul 2),
          integral_const_mul, integral_const_mul,
          integral_finsetSum Finset.univ (fun j _ => him j)]
  exact ⟨hder.differentiableAt, hder.deriv, hder.deriv.trans heq,
    hid, hik, him, hp⟩

theorem T009 (n : ℕ) (m : ℕ) (u : X n × ℝ → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ u (domain n)) (h_T004 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (X n), ∃ R : ℝ, Window u q t0 C R) ∧
  ContDiffOn ℝ ∞ (density u) (domain n) ∧
  ContDiffOn ℝ ∞ (dt (density u)) (domain n) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : X n => density u (x,t)) (mu n))) :
    ∀ t0 : ℝ, 0 < t0 → ∀ j : Fin n,
  ContDiff ℝ ∞ (fun x : X n => flux u j (x,t0)) ∧
  (∀ x : X n, dx (flux u j) j (x,t0) =
    inner ℝ (dx (dt u) j (x,t0)) (dx u j (x,t0)) + lapTerm u j (x,t0)) ∧
  (∀ x : X n, HasDerivAt (fun z : ℝ => flux u j (Function.update x j z,t0))
    (dx (flux u j) j (x,t0)) (x j)) ∧
  (∀ C : Set (X n), ∀ R : ℝ, Window u q t0 C R →
    ∀ x : X n, x j = -R ∨ x j = R → flux u j (x,t0) = 0) := by
  intro t0 ht0 j
  have hopen : IsOpen (domain n) := isOpen_lt continuous_const continuous_snd
  have hu : ∀ x : X n, ContDiffAt ℝ ∞ u (x,t0) :=
    fun x => h_H002.contDiffAt (hopen.mem_nhds ht0)
  have hut : ContDiff ℝ ∞ (fun x : X n => dt u (x,t0)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    have hf : ContDiffAt ℝ ∞ (Function.uncurry (fun (y : X n) (r : ℝ) => u (y,r))) (x,t0) := hu x
    have hd : ContDiffAt ℝ ∞ (fun y : X n => fderiv ℝ (fun r : ℝ => u (y,r)) t0) x :=
      hf.fderiv (g := fun _ : X n => t0) contDiffAt_const (by simp)
    simpa only [dt, fderiv_apply_one_eq_deriv] using
      hd.clm_apply (contDiffAt_const (c := (1 : ℝ)))
  have hus : ContDiff ℝ ∞ (fun x : X n => u (x,t0)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    exact (hu x).comp x (contDiffAt_id.prodMk contDiffAt_const)
  have hux : ContDiff ℝ ∞ (fun x : X n => dx u j (x,t0)) := by
    exact (hus.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hg : ContDiff ℝ ∞ (fun x : X n => flux u j (x,t0)) :=
    hut.inner ℝ hux
  refine ⟨hg, ?_, ?_, ?_⟩
  · intro x
    have ht : DifferentiableAt ℝ (fun y : X n => dt u (y,t0)) x :=
      hut.differentiable (by simp) x
    have hx : DifferentiableAt ℝ (fun y : X n => dx u j (y,t0)) x :=
      hux.differentiable (by simp) x
    simpa only [dx, flux, lapTerm, add_comm] using
      fderiv_inner_apply ℝ ht hx (Pi.single j 1)
  · intro x
    have hf : HasFDerivAt (fun y : X n => flux u j (y,t0))
        (fderiv ℝ (fun y : X n => flux u j (y,t0)) x) x :=
      (hg.differentiable (by simp) x).hasFDerivAt
    have hc := hf.comp_hasDerivAt_of_eq (x j) (hasDerivAt_update x j (x j))
      (by simp : x = Function.update x j (x j))
    simpa only [Function.comp_def, dx] using hc
  · intro C R hw x hx
    have hnot : x ∉ C := by
      intro hmem
      have hi := hw.inside x hmem j
      rcases hx with hx | hx
      · rw [hx] at hi
        exact (lt_irrefl (-R)) hi.1
      · rw [hx] at hi
        exact (lt_irrefl R) hi.2
    have htime : t0 ∈ Ioo (t0 / 2) (3 * t0 / 2) := by
      constructor <;> linarith
    have hflux : flux u j ∈ scalarTerms u := by
      exact Or.inr (Or.inr (Or.inr ⟨j, Or.inr (Or.inr (Or.inl rfl))⟩))
    exact (hw.sections (flux u j) hflux t0 htime).2.1 x hnot

theorem T010 (n : ℕ) (m : ℕ) (u : X n × ℝ → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ u (domain n)) (h_T004 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (X n), ∃ R : ℝ, Window u q t0 C R) ∧
  ContDiffOn ℝ ∞ (density u) (domain n) ∧
  ContDiffOn ℝ ∞ (dt (density u)) (domain n) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : X n => density u (x,t)) (mu n))) (h_T009 : ∀ t0 : ℝ, 0 < t0 → ∀ j : Fin n,
  ContDiff ℝ ∞ (fun x : X n => flux u j (x,t0)) ∧
  (∀ x : X n, dx (flux u j) j (x,t0) =
    inner ℝ (dx (dt u) j (x,t0)) (dx u j (x,t0)) + lapTerm u j (x,t0)) ∧
  (∀ x : X n, HasDerivAt (fun z : ℝ => flux u j (Function.update x j z,t0))
    (dx (flux u j) j (x,t0)) (x j)) ∧
  (∀ C : Set (X n), ∀ R : ℝ, Window u q t0 C R →
    ∀ x : X n, x j = -R ∨ x j = R → flux u j (x,t0) = 0)) :
    ∀ t0 : ℝ, 0 < t0 → ∀ j : Fin n,
  ∀ C : Set (X n), ∀ R : ℝ, Window u q t0 C R →
  ∀ x : X n, (∫ z in (-R)..R,
    dx (flux u j) j (Function.update x j z,t0)) = 0 := by
  intro t0 ht0 j C R hW x
  have htwin : t0 ∈ Ioo (t0 / 2) (3 * t0 / 2) := by
    constructor <;> linarith
  have hmem : dx (flux u j) j ∈ scalarTerms u := by
    change _ = density u ∨ _ = dt (density u) ∨ _ = kinetic u ∨ _
    exact Or.inr (Or.inr (Or.inr ⟨j, Or.inr (Or.inr (Or.inr rfl))⟩))
  have hdcont : Continuous (fun y : X n => dx (flux u j) j (y, t0)) :=
    (hW.sections _ hmem t0 htwin).1
  have hline : Continuous (fun z : ℝ => Function.update x j z) :=
    continuous_const.update j continuous_id
  have hfcont : Continuous (fun z : ℝ => flux u j (Function.update x j z, t0)) :=
    (h_T009 t0 ht0 j).1.continuous.comp hline
  have hdline : Continuous (fun z : ℝ => dx (flux u j) j (Function.update x j z, t0)) :=
    hdcont.comp hline
  have hderiv : ∀ z : ℝ,
      HasDerivAt (fun z : ℝ => flux u j (Function.update x j z, t0))
        (dx (flux u j) j (Function.update x j z, t0)) z := by
    intro z
    simpa only [Function.update_self, Function.update_idem] using
      (h_T009 t0 ht0 j).2.2.1 (Function.update x j z)
  have hab : -R ≤ R := by linarith [hW.radius_pos]
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    hfcont.continuousOn (fun z _ => hderiv z) (hdline.intervalIntegrable (-R) R)
  have hleft : flux u j (Function.update x j (-R), t0) = 0 :=
    (h_T009 t0 ht0 j).2.2.2 C R hW _ (Or.inl (by simp))
  have hright : flux u j (Function.update x j R, t0) = 0 :=
    (h_T009 t0 ht0 j).2.2.2 C R hW _ (Or.inr (by simp))
  simpa only [hleft, hright, sub_self] using heq

theorem T011 (n : ℕ) (m : ℕ) (u : X n × ℝ → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ u (domain n)) (h_T004 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (X n), ∃ R : ℝ, Window u q t0 C R) ∧
  ContDiffOn ℝ ∞ (density u) (domain n) ∧
  ContDiffOn ℝ ∞ (dt (density u)) (domain n) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : X n => density u (x,t)) (mu n))) (h_T009 : ∀ t0 : ℝ, 0 < t0 → ∀ j : Fin n,
  ContDiff ℝ ∞ (fun x : X n => flux u j (x,t0)) ∧
  (∀ x : X n, dx (flux u j) j (x,t0) =
    inner ℝ (dx (dt u) j (x,t0)) (dx u j (x,t0)) + lapTerm u j (x,t0)) ∧
  (∀ x : X n, HasDerivAt (fun z : ℝ => flux u j (Function.update x j z,t0))
    (dx (flux u j) j (x,t0)) (x j)) ∧
  (∀ C : Set (X n), ∀ R : ℝ, Window u q t0 C R →
    ∀ x : X n, x j = -R ∨ x j = R → flux u j (x,t0) = 0)) (h_T010 : ∀ t0 : ℝ, 0 < t0 → ∀ j : Fin n,
  ∀ C : Set (X n), ∀ R : ℝ, Window u q t0 C R →
  ∀ x : X n, (∫ z in (-R)..R,
    dx (flux u j) j (Function.update x j z,t0)) = 0) :
    ∀ t0 : ℝ, 0 < t0 → ∀ j : Fin n,
  ∀ C : Set (X n), ∀ R : ℝ, Window u q t0 C R →
  MeasurePreserving (insert j)
    (((otherMu j).restrict (otherBox j R)).prod (volume.restrict (Icc (-R) R)))
    ((mu n).restrict (box R)) ∧
  (∫ x in box R, dx (flux u j) j (x,t0) ∂mu n) = 0 := by
  classical
  have hcoord : ∀ j : Fin n, MeasurableEmbedding (WaveEnergy.insert j) ∧
      MeasurePreserving (WaveEnergy.insert j) ((otherMu j).prod volume) (mu n) := by
      intro j
      classical
      have hmeas : Measurable (WaveEnergy.insert j) := by
        apply measurable_pi_lambda
        intro i
        by_cases h : i = j
        · simpa [WaveEnergy.insert, h] using (measurable_snd : Measurable (fun p : Other n j × ℝ => p.2))
        · simp only [WaveEnergy.insert, dif_neg h]
          exact (measurable_pi_apply (⟨i,h⟩ : {k : Fin n // k ≠ j})).comp (measurable_fst : Measurable (fun p : Other n j × ℝ => p.1))
      let e : (Other n j × ℝ) ≃ᵐ X n :=
        { toFun := WaveEnergy.insert j
          invFun := fun x => (fun i => x i, x j)
          left_inv := by
            intro p
            apply Prod.ext
            · funext i
              simp [WaveEnergy.insert, i.property]
            · simp [WaveEnergy.insert]
          right_inv := by
            intro x
            funext i
            by_cases h : i = j <;> simp [WaveEnergy.insert, h]
          measurable_toFun := hmeas
          measurable_invFun := (measurable_pi_lambda _ (fun i => measurable_pi_apply i.val)).prodMk (measurable_pi_apply j) }
      refine ⟨e.measurableEmbedding, hmeas, ?_⟩
      apply Eq.symm
      apply Measure.pi_eq
      intro s hs
      have hp : WaveEnergy.insert j ⁻¹' (Set.univ.pi s) =
          (Set.univ.pi (fun i : {i : Fin n // i ≠ j} => s i.val)) ×ˢ s j := by
        ext p
        simp only [mem_preimage, mem_univ_pi, mem_prod]
        constructor
        · intro h
          exact ⟨fun i => by simpa [WaveEnergy.insert, i.property] using h i.val,
            by simpa [WaveEnergy.insert] using h j⟩
        · rintro ⟨hy,hz⟩ i
          by_cases h : i = j
          · subst i
            simpa [WaveEnergy.insert] using hz
          · simpa [WaveEnergy.insert, h] using hy ⟨i,h⟩
      rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs), hp,
        Measure.prod_prod, otherMu, Measure.pi_pi]
      rw [Fintype.prod_eq_mul_prod_subtype_ne (fun i => volume (s i)) j, mul_comm]
  intro t0 ht0 j C R hW
  obtain ⟨hemb, hmp⟩ := hcoord j
  letI : SigmaFinite (otherMu j) := by unfold otherMu; infer_instance
  letI : IsFiniteMeasureOnCompacts (otherMu j) := by unfold otherMu; infer_instance
  have hbox : MeasurableSet (box (n := n) R) := by
    have heq : box (n := n) R = Set.univ.pi (fun _ : Fin n => Icc (-R) R) := by
      ext x
      simp only [box, mem_setOf_eq, mem_univ_pi]
    rw [heq]
    exact MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  have hpre : WaveEnergy.insert j ⁻¹' box R = otherBox j R ×ˢ Icc (-R) R := by
    ext p
    change (∀ i, WaveEnergy.insert j p i ∈ Icc (-R) R) ↔
      (∀ i : {i : Fin n // i ≠ j}, p.1 i ∈ Icc (-R) R) ∧ p.2 ∈ Icc (-R) R
    constructor
    · intro h
      exact ⟨fun i => by simpa [WaveEnergy.insert, i.property] using h i.val,
        by simpa [WaveEnergy.insert] using h j⟩
    · rintro ⟨hy,hz⟩ i
      by_cases h : i = j
      · simpa [WaveEnergy.insert, h] using hz
      · simpa [WaveEnergy.insert, h] using hy ⟨i,h⟩
  have hrestricted : MeasurePreserving (WaveEnergy.insert j)
      (((otherMu j).restrict (otherBox j R)).prod (volume.restrict (Icc (-R) R)))
      ((mu n).restrict (box R)) := by
    rw [Measure.prod_restrict, ← hpre]
    exact hmp.restrict_preimage hbox
  refine ⟨hrestricted, ?_⟩
  have htwin : t0 ∈ Ioo (t0 / 2) (3 * t0 / 2) := by constructor <;> linarith
  have hfmem : dx (flux u j) j ∈ scalarTerms u := by
    exact Or.inr (Or.inr (Or.inr ⟨j, Or.inr (Or.inr (Or.inr rfl))⟩))
  have hf : Continuous (fun x : X n => dx (flux u j) j (x,t0)) :=
    (hW.sections _ hfmem t0 htwin).1
  have hins : Continuous (WaveEnergy.insert j) := by
    apply continuous_pi
    intro i
    by_cases h : i = j
    · simpa [WaveEnergy.insert, h] using (continuous_snd : Continuous (fun p : Other n j × ℝ => p.2))
    · simp only [WaveEnergy.insert, dif_neg h]
      exact (continuous_apply (⟨i,h⟩ : {k : Fin n // k ≠ j})).comp
        (continuous_fst : Continuous (fun p : Other n j × ℝ => p.1))
  have hcompact : IsCompact (otherBox j R) := by
    have heq : otherBox j R = Set.univ.pi (fun _ : {i : Fin n // i ≠ j} => Icc (-R) R) := by
      ext x
      simp only [otherBox, mem_setOf_eq, mem_univ_pi]
    rw [heq]
    exact isCompact_univ_pi (fun _ => isCompact_Icc)
  have hv : Integrable (fun p : Other n j × ℝ =>
      dx (flux u j) j (WaveEnergy.insert j p,t0))
      (((otherMu j).restrict (otherBox j R)).prod (volume.restrict (Icc (-R) R))) := by
    rw [Measure.prod_restrict]
    exact (hf.comp hins).continuousOn.integrableOn_compact (hcompact.prod isCompact_Icc)
  rw [← hrestricted.integral_comp hemb (fun x => dx (flux u j) j (x,t0)),
    integral_prod _ hv]
  have hinner : ∀ y : Other n j, (∫ z in Icc (-R) R,
      dx (flux u j) j (WaveEnergy.insert j (y,z),t0)) = 0 := by
    intro y
    have hup : ∀ z : ℝ, WaveEnergy.insert j (y,z) =
        Function.update (WaveEnergy.insert j (y,0)) j z := by
      intro z
      funext i
      by_cases h : i = j
      · subst i
        simp [WaveEnergy.insert]
      · simp [WaveEnergy.insert, h, Function.update_of_ne h]
    calc
      (∫ z in Icc (-R) R, dx (flux u j) j (WaveEnergy.insert j (y,z),t0)) =
          (∫ z in Icc (-R) R, dx (flux u j) j (Function.update (WaveEnergy.insert j (y,0)) j z,t0)) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun z =>
          congrArg (fun x : X n => dx (flux u j) j (x,t0)) (hup z))
      _ = 0 := by
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith [hW.radius_pos] : -R ≤ R)]
        exact h_T010 t0 ht0 j C R hW (WaveEnergy.insert j (y,0))
  simp only [hinner, integral_zero]

theorem T012 (n : ℕ) (m : ℕ) (u : X n × ℝ → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ u (domain n)) (h_T004 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (X n), ∃ R : ℝ, Window u q t0 C R) ∧
  ContDiffOn ℝ ∞ (density u) (domain n) ∧
  ContDiffOn ℝ ∞ (dt (density u)) (domain n) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : X n => density u (x,t)) (mu n))) (h_T009 : ∀ t0 : ℝ, 0 < t0 → ∀ j : Fin n,
  ContDiff ℝ ∞ (fun x : X n => flux u j (x,t0)) ∧
  (∀ x : X n, dx (flux u j) j (x,t0) =
    inner ℝ (dx (dt u) j (x,t0)) (dx u j (x,t0)) + lapTerm u j (x,t0)) ∧
  (∀ x : X n, HasDerivAt (fun z : ℝ => flux u j (Function.update x j z,t0))
    (dx (flux u j) j (x,t0)) (x j)) ∧
  (∀ C : Set (X n), ∀ R : ℝ, Window u q t0 C R →
    ∀ x : X n, x j = -R ∨ x j = R → flux u j (x,t0) = 0)) (h_T011 : ∀ t0 : ℝ, 0 < t0 → ∀ j : Fin n,
  ∀ C : Set (X n), ∀ R : ℝ, Window u q t0 C R →
  MeasurePreserving (insert j)
    (((otherMu j).restrict (otherBox j R)).prod (volume.restrict (Icc (-R) R)))
    ((mu n).restrict (box R)) ∧
  (∫ x in box R, dx (flux u j) j (x,t0) ∂mu n) = 0) :
    ∀ t : ℝ, 0 < t → ∀ j : Fin n,
  (∫ x : X n, mixed u j (x,t) ∂mu n) = -(∫ x : X n, lapTerm u j (x,t) ∂mu n) ∧
  Integrable (fun x : X n => mixed u j (x,t)) (mu n) ∧
  Integrable (fun x : X n => lapTerm u j (x,t)) (mu n) := by
  intro t ht j
  obtain ⟨C, R, hW⟩ := h_T004.1 t ht
  have htime : t ∈ Ioo (t / 2) (3 * t / 2) := by
    constructor <;> linarith
  have hm_mem : mixed u j ∈ scalarTerms u := by
    change mixed u j = density u ∨ mixed u j = dt (density u) ∨
      mixed u j = kinetic u ∨ ∃ k : Fin n,
        mixed u j = mixed u k ∨ mixed u j = lapTerm u k ∨
          mixed u j = flux u k ∨ mixed u j = dx (flux u k) k
    exact Or.inr (Or.inr (Or.inr ⟨j, Or.inl rfl⟩))
  have hl_mem : lapTerm u j ∈ scalarTerms u := by
    change lapTerm u j = density u ∨ lapTerm u j = dt (density u) ∨
      lapTerm u j = kinetic u ∨ ∃ k : Fin n,
        lapTerm u j = mixed u k ∨ lapTerm u j = lapTerm u k ∨
          lapTerm u j = flux u k ∨ lapTerm u j = dx (flux u k) k
    exact Or.inr (Or.inr (Or.inr ⟨j, Or.inr (Or.inl rfl)⟩))
  have hd_mem : dx (flux u j) j ∈ scalarTerms u := by
    change dx (flux u j) j = density u ∨ dx (flux u j) j = dt (density u) ∨
      dx (flux u j) j = kinetic u ∨ ∃ k : Fin n,
        dx (flux u j) j = mixed u k ∨ dx (flux u j) j = lapTerm u k ∨
          dx (flux u j) j = flux u k ∨ dx (flux u j) j = dx (flux u k) k
    exact Or.inr (Or.inr (Or.inr ⟨j, Or.inr (Or.inr (Or.inr rfl))⟩))
  have hm : Integrable (fun x : X n => mixed u j (x,t)) (mu n) :=
    (hW.sections (mixed u j) hm_mem t htime).2.2
  have hl : Integrable (fun x : X n => lapTerm u j (x,t)) (mu n) :=
    (hW.sections (lapTerm u j) hl_mem t htime).2.2
  have hCbox : C ⊆ box R := by
    intro x hx
    exact fun k => ⟨(hW.inside x hx k).1.le, (hW.inside x hx k).2.le⟩
  have hzero : ∀ x : X n, x ∉ box R → dx (flux u j) j (x,t) = 0 := by
    intro x hx
    exact (hW.sections (dx (flux u j) j) hd_mem t htime).2.1 x
      (fun hxC => hx (hCbox hxC))
  have hfull : (∫ x : X n, dx (flux u j) j (x,t) ∂mu n) = 0 := by
    calc
      (∫ x : X n, dx (flux u j) j (x,t) ∂mu n) =
          ∫ x in box R, dx (flux u j) j (x,t) ∂mu n :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
      _ = 0 := (h_T011 t ht j C R hW).2
  have hprod : ∀ x : X n, dx (flux u j) j (x,t) =
      mixed u j (x,t) + lapTerm u j (x,t) := by
    intro x
    rw [(h_T009 t ht j).2.1 x]
    unfold mixed
    rw [real_inner_comm (dx u j (x,t)) (dx (dt u) j (x,t))]
  have hsum : (∫ x : X n, mixed u j (x,t) ∂mu n) +
      (∫ x : X n, lapTerm u j (x,t) ∂mu n) = 0 := by
    calc
      (∫ x : X n, mixed u j (x,t) ∂mu n) +
          (∫ x : X n, lapTerm u j (x,t) ∂mu n) =
          ∫ x : X n, mixed u j (x,t) + lapTerm u j (x,t) ∂mu n :=
        (integral_add hm hl).symm
      _ = ∫ x : X n, dx (flux u j) j (x,t) ∂mu n :=
        integral_congr_ae (Filter.Eventually.of_forall (fun x => (hprod x).symm))
      _ = 0 := hfull
  exact ⟨by linarith, hm, hl⟩

theorem T013 (n : ℕ) (m : ℕ) (u : X n × ℝ → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ u (domain n)) (h_T002 : ∀ x : X n, ∀ t : ℝ, 0 < t →
  inner ℝ (u (x,t)) (dt u (x,t)) = 0 ∧
  inner ℝ (u (x,t)) (dt (dt u) (x,t)) = -(‖dt u (x,t)‖ ^ 2) ∧
  (∀ j : Fin n, inner ℝ (u (x,t)) (dx (dx u j) j (x,t)) = -(‖dx u j (x,t)‖ ^ 2)) ∧
  inner ℝ (dt u (x,t)) (dt (dt u) (x,t) - lap u (x,t)) = 0 ∧
  dt (dt u) (x,t) - lap u (x,t) =
    ((∑ j : Fin n, ‖dx u j (x,t)‖ ^ 2) - ‖dt u (x,t)‖ ^ 2) • u (x,t) ∧
  (∀ a : ℝ, dt (dt u) (x,t) - lap u (x,t) = a • u (x,t) →
    a = (∑ j : Fin n, ‖dx u j (x,t)‖ ^ 2) - ‖dt u (x,t)‖ ^ 2)) (h_T004 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (X n), ∃ R : ℝ, Window u q t0 C R) ∧
  ContDiffOn ℝ ∞ (density u) (domain n) ∧
  ContDiffOn ℝ ∞ (dt (density u)) (domain n) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : X n => density u (x,t)) (mu n))) (h_T008 : ∀ t : ℝ, 0 < t →
  DifferentiableAt ℝ (energy u) t ∧
  deriv (energy u) t = (∫ x : X n, dt (density u) (x,t) ∂mu n) ∧
  deriv (energy u) t =
    2 * (∫ x : X n, kinetic u (x,t) ∂mu n) +
    2 * ∑ j : Fin n, (∫ x : X n, mixed u j (x,t) ∂mu n) ∧
  Integrable (fun x : X n => dt (density u) (x,t)) (mu n) ∧
  Integrable (fun x : X n => kinetic u (x,t)) (mu n) ∧
  (∀ j : Fin n, Integrable (fun x : X n => mixed u j (x,t)) (mu n)) ∧
  (∀ x : X n, dt (density u) (x,t) =
    2 * kinetic u (x,t) + 2 * ∑ j : Fin n, mixed u j (x,t))) (h_T012 : ∀ t : ℝ, 0 < t → ∀ j : Fin n,
  (∫ x : X n, mixed u j (x,t) ∂mu n) = -(∫ x : X n, lapTerm u j (x,t) ∂mu n) ∧
  Integrable (fun x : X n => mixed u j (x,t)) (mu n) ∧
  Integrable (fun x : X n => lapTerm u j (x,t)) (mu n)) :
    ∀ t : ℝ, 0 < t →
  Integrable (fun x : X n => density u (x,t)) (mu n) ∧
  DifferentiableAt ℝ (energy u) t ∧ deriv (energy u) t = 0 := by
  intro t ht
  have he := h_T008 t ht
  have hk : Integrable (fun x : X n => kinetic u (x,t)) (mu n) :=
    he.2.2.2.2.1
  have hl : ∀ j : Fin n, Integrable (fun x : X n => lapTerm u j (x,t)) (mu n) :=
    fun j => (h_T012 t ht j).2.2
  have hs : Integrable (fun x : X n => ∑ j : Fin n, lapTerm u j (x,t)) (mu n) :=
    integrable_finsetSum Finset.univ (fun j _ => hl j)
  have hlin :
      (∫ x : X n, (kinetic u (x,t) - ∑ j : Fin n, lapTerm u j (x,t)) ∂mu n) =
        (∫ x : X n, kinetic u (x,t) ∂mu n) -
          ∑ j : Fin n, (∫ x : X n, lapTerm u j (x,t) ∂mu n) := by
    rw [integral_sub hk hs, integral_finsetSum Finset.univ (fun j _ => hl j)]
  have hform : ∀ x : X n,
      inner ℝ (dt u (x,t)) (dt (dt u) (x,t) - lap u (x,t)) =
        kinetic u (x,t) - ∑ j : Fin n, lapTerm u j (x,t) := by
    intro x
    simp only [kinetic, lapTerm, lap, inner_sub_right, inner_sum]
  have hz : ∀ x : X n,
      inner ℝ (dt u (x,t)) (dt (dt u) (x,t) - lap u (x,t)) = 0 :=
    fun x => (h_T002 x t ht).2.2.2.1
  refine ⟨h_T004.2.2.2 t ht, he.1, ?_⟩
  calc
    deriv (energy u) t =
        2 * (∫ x : X n, kinetic u (x,t) ∂mu n) +
        2 * ∑ j : Fin n, (∫ x : X n, mixed u j (x,t) ∂mu n) := he.2.2.1
    _ = 2 * ((∫ x : X n, kinetic u (x,t) ∂mu n) -
          ∑ j : Fin n, (∫ x : X n, lapTerm u j (x,t) ∂mu n)) := by
      simp_rw [(h_T012 t ht _).1]
      rw [Finset.sum_neg_distrib]
      ring
    _ = 2 * (∫ x : X n,
        inner ℝ (dt u (x,t)) (dt (dt u) (x,t) - lap u (x,t)) ∂mu n) := by
      simp_rw [hform]
      rw [hlin]
    _ = 0 := by simp [hz]

theorem T014 (n : ℕ) (m : ℕ) (u : X n × ℝ → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ u (domain n)) (h_T013 : ∀ t : ℝ, 0 < t →
  Integrable (fun x : X n => density u (x,t)) (mu n) ∧
  DifferentiableAt ℝ (energy u) t ∧ deriv (energy u) t = 0) :
    (∀ t : ℝ, 0 < t →
  Integrable (fun x : X n => density u (x,t)) (mu n) ∧
  DifferentiableAt ℝ (energy u) t ∧ deriv (energy u) t = 0) ∧
  (∀ s : ℝ, 0 < s → ∀ t : ℝ, 0 < t → energy u s = energy u t) := by
  refine ⟨h_T013, ?_⟩
  have hordered : ∀ a b : ℝ, 0 < a → a < b → energy u a = energy u b := by
    intro a b ha hab
    have hcont : ContinuousOn (energy u) (Icc a b) := by
      intro x hx
      exact ((h_T013 x (lt_of_lt_of_le ha hx.1)).2.1.continuousAt).continuousWithinAt
    have hderiv : ∀ x ∈ Ioo a b, HasDerivAt (energy u) ((fun _ : ℝ => (0 : ℝ)) x) x := by
      intro x hx
      have hxpos : 0 < x := lt_trans ha hx.1
      simpa only [(h_T013 x hxpos).2.2] using (h_T013 x hxpos).2.1.hasDerivAt
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (energy u) (fun _ : ℝ => (0 : ℝ)) hab hcont hderiv
    have hne : b - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt hab)
    have hzero : energy u b - energy u a = 0 :=
      (div_eq_zero_iff.mp hslope.symm).resolve_right hne
    exact (sub_eq_zero.mp hzero).symm
  intro s hs t ht
  rcases lt_trichotomy s t with hst | hst | hst
  · exact hordered s t hs hst
  · subst t
    rfl
  · exact (hordered t s ht hst).symm

set_option Elab.async false in
theorem P (n : ℕ) (m : ℕ) (u : X n × ℝ → V m) (q : V m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ u (domain n)) (h_H003 : ‖q‖ = 1) (h_H004 : ∀ x : X n, ∀ t : ℝ, 0 < t → ‖u (x,t)‖ = 1) (h_H005 : ∀ x : X n, ∀ t : ℝ, 0 < t → ∃ a : ℝ, dt (dt u) (x,t) - lap u (x,t) = a • u (x,t)) (h_H006 : ∀ s t : ℝ, 0 < s → s < t → ∃ C : Set (X n), IsCompact C ∧ ∀ x : X n, x ∉ C → ∀ r : ℝ, r ∈ Icc s t → u (x,r) = q) :
    (∀ t : ℝ, 0 < t →
  Integrable (fun x : X n => density u (x,t)) (mu n) ∧
  DifferentiableAt ℝ (energy u) t ∧ deriv (energy u) t = 0) ∧
  (∀ s : ℝ, 0 < s → ∀ t : ℝ, 0 < t → energy u s = energy u t) := by
  have h_T001 : ∀ x : X n, ∀ t : ℝ, 0 < t →
  inner ℝ (u (x,t)) (dt u (x,t)) = 0 ∧
  inner ℝ (u (x,t)) (dt (dt u) (x,t)) = -(‖dt u (x,t)‖ ^ 2) ∧
  (∀ j : Fin n, inner ℝ (u (x,t)) (dx (dx u j) j (x,t)) = -(‖dx u j (x,t)‖ ^ 2)) := @T001 n m u q h_H001 h_H002 h_H004
  have h_T002 : ∀ x : X n, ∀ t : ℝ, 0 < t →
  inner ℝ (u (x,t)) (dt u (x,t)) = 0 ∧
  inner ℝ (u (x,t)) (dt (dt u) (x,t)) = -(‖dt u (x,t)‖ ^ 2) ∧
  (∀ j : Fin n, inner ℝ (u (x,t)) (dx (dx u j) j (x,t)) = -(‖dx u j (x,t)‖ ^ 2)) ∧
  inner ℝ (dt u (x,t)) (dt (dt u) (x,t) - lap u (x,t)) = 0 ∧
  dt (dt u) (x,t) - lap u (x,t) =
    ((∑ j : Fin n, ‖dx u j (x,t)‖ ^ 2) - ‖dt u (x,t)‖ ^ 2) • u (x,t) ∧
  (∀ a : ℝ, dt (dt u) (x,t) - lap u (x,t) = a • u (x,t) →
    a = (∑ j : Fin n, ‖dx u j (x,t)‖ ^ 2) - ‖dt u (x,t)‖ ^ 2) := @T002 n m u q h_H001 h_H002 h_H004 h_H005 h_T001
  have h_T003 : ∀ t0 : ℝ, 0 < t0 →
  ∃ C : Set (X n), ∃ R : ℝ, IsCompact C ∧ 0 < R ∧
    (∀ x ∈ C, ∀ j : Fin n, x j ∈ Ioo (-R) R) ∧
    (∀ x, x ∉ C → ∀ r ∈ Icc (t0/2) (3*t0/2), u (x,r) = q) := @T003 n m u q h_H001 h_H006
  have h_T004 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (X n), ∃ R : ℝ, Window u q t0 C R) ∧
  ContDiffOn ℝ ∞ (density u) (domain n) ∧
  ContDiffOn ℝ ∞ (dt (density u)) (domain n) ∧
  (∀ t : ℝ, 0 < t → Integrable (fun x : X n => density u (x,t)) (mu n)) := @T004 n m u q h_H001 h_H002 h_H003 h_H006 h_T003
  have h_T005 : ∀ x : X n, ∀ t : ℝ, 0 < t →
  HasDerivAt (fun r : ℝ => density u (x,r)) (dt (density u) (x,t)) t ∧
  dt (density u) (x,t) = 2 * kinetic u (x,t) + 2 * ∑ j : Fin n, mixed u j (x,t) := @T005 n m u q h_H001 h_H002 h_T004
  have h_T006 : ∀ t0 : ℝ, 0 < t0 → ∃ R B : ℝ, 0 < R ∧ 0 ≤ B ∧
  Integrable ((box R).indicator (fun _ : X n => B)) (mu n) ∧
  (∀ x ∈ box R, ∀ r ∈ Icc (t0-t0/4) (t0+t0/4), |dt (density u) (x,r)| ≤ B) ∧
  (∀ x : X n, ∀ h : ℝ, 0 < |h| → |h| < t0/4 →
    |(density u (x,t0+h) - density u (x,t0))/h| ≤
      (box R).indicator (fun _ : X n => B) x) := @T006 n m u q h_H001 h_H002 h_T004 h_T005
  have h_T007 : ∀ t0 : ℝ, 0 < t0 → ∀ h : ℕ → ℝ,
  (∀ k : ℕ, 0 < |h k| ∧ |h k| < t0/4) →
  Tendsto h atTop (nhds 0) →
  Tendsto (fun k : ℕ => (energy u (t0+h k) - energy u t0)/h k) atTop
    (nhds (∫ x : X n, dt (density u) (x,t0) ∂mu n)) := @T007 n m u q h_H001 h_H002 h_T004 h_T005 h_T006
  have h_T008 : ∀ t : ℝ, 0 < t →
  DifferentiableAt ℝ (energy u) t ∧
  deriv (energy u) t = (∫ x : X n, dt (density u) (x,t) ∂mu n) ∧
  deriv (energy u) t =
    2 * (∫ x : X n, kinetic u (x,t) ∂mu n) +
    2 * ∑ j : Fin n, (∫ x : X n, mixed u j (x,t) ∂mu n) ∧
  Integrable (fun x : X n => dt (density u) (x,t)) (mu n) ∧
  Integrable (fun x : X n => kinetic u (x,t)) (mu n) ∧
  (∀ j : Fin n, Integrable (fun x : X n => mixed u j (x,t)) (mu n)) ∧
  (∀ x : X n, dt (density u) (x,t) =
    2 * kinetic u (x,t) + 2 * ∑ j : Fin n, mixed u j (x,t)) := @T008 n m u q h_H001 h_H002 h_T004 h_T005 h_T007
  have h_T009 : ∀ t0 : ℝ, 0 < t0 → ∀ j : Fin n,
  ContDiff ℝ ∞ (fun x : X n => flux u j (x,t0)) ∧
  (∀ x : X n, dx (flux u j) j (x,t0) =
    inner ℝ (dx (dt u) j (x,t0)) (dx u j (x,t0)) + lapTerm u j (x,t0)) ∧
  (∀ x : X n, HasDerivAt (fun z : ℝ => flux u j (Function.update x j z,t0))
    (dx (flux u j) j (x,t0)) (x j)) ∧
  (∀ C : Set (X n), ∀ R : ℝ, Window u q t0 C R →
    ∀ x : X n, x j = -R ∨ x j = R → flux u j (x,t0) = 0) := @T009 n m u q h_H001 h_H002 h_T004
  have h_T010 : ∀ t0 : ℝ, 0 < t0 → ∀ j : Fin n,
  ∀ C : Set (X n), ∀ R : ℝ, Window u q t0 C R →
  ∀ x : X n, (∫ z in (-R)..R,
    dx (flux u j) j (Function.update x j z,t0)) = 0 := @T010 n m u q h_H001 h_H002 h_T004 h_T009
  have h_T011 : ∀ t0 : ℝ, 0 < t0 → ∀ j : Fin n,
  ∀ C : Set (X n), ∀ R : ℝ, Window u q t0 C R →
  MeasurePreserving (insert j)
    (((otherMu j).restrict (otherBox j R)).prod (volume.restrict (Icc (-R) R)))
    ((mu n).restrict (box R)) ∧
  (∫ x in box R, dx (flux u j) j (x,t0) ∂mu n) = 0 := @T011 n m u q h_H001 h_H002 h_T004 h_T009 h_T010
  have h_T012 : ∀ t : ℝ, 0 < t → ∀ j : Fin n,
  (∫ x : X n, mixed u j (x,t) ∂mu n) = -(∫ x : X n, lapTerm u j (x,t) ∂mu n) ∧
  Integrable (fun x : X n => mixed u j (x,t)) (mu n) ∧
  Integrable (fun x : X n => lapTerm u j (x,t)) (mu n) := @T012 n m u q h_H001 h_H002 h_T004 h_T009 h_T011
  have h_T013 : ∀ t : ℝ, 0 < t →
  Integrable (fun x : X n => density u (x,t)) (mu n) ∧
  DifferentiableAt ℝ (energy u) t ∧ deriv (energy u) t = 0 := @T013 n m u q h_H001 h_H002 h_T002 h_T004 h_T008 h_T012
  have h_T014 : (∀ t : ℝ, 0 < t →
  Integrable (fun x : X n => density u (x,t)) (mu n) ∧
  DifferentiableAt ℝ (energy u) t ∧ deriv (energy u) t = 0) ∧
  (∀ s : ℝ, 0 < s → ∀ t : ℝ, 0 < t → energy u s = energy u t) := @T014 n m u q h_H001 h_H002 h_T013
  exact h_T014

#check @P
#print axioms P

end Translation
