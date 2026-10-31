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

#check @T004
#print axioms T004

end Translation
