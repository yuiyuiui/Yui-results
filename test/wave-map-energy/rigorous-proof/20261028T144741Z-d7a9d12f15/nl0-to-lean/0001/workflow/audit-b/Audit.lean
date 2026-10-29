import Mathlib
open MeasureTheory Set Filter
open scoped ContDiff
noncomputable abbrev WSpace (n : ℕ) := Fin n → ℝ
noncomputable abbrev WTarget (m : ℕ) := EuclideanSpace ℝ (Fin m)
noncomputable def wDx {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : WSpace n → F) (j : Fin n) (x : WSpace n) : F := fderiv ℝ f x (Pi.single j 1)
noncomputable def wT {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : WSpace n × ℝ → F) (p : WSpace n × ℝ) : F := deriv (fun r => f (p.1,r)) p.2
noncomputable def wX {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : WSpace n × ℝ → F) (j : Fin n) (p : WSpace n × ℝ) : F := wDx (fun x => f (x,p.2)) j p.1
noncomputable def wLap {n m : ℕ} (u : WSpace n × ℝ → WTarget m) (p : WSpace n × ℝ) : WTarget m := ∑ j : Fin n, wX (wX u j) j p
noncomputable def wDensity {n m : ℕ} (u : WSpace n × ℝ → WTarget m) (p : WSpace n × ℝ) : ℝ := ‖wT u p‖^2 + ∑ j : Fin n, ‖wX u j p‖^2
noncomputable def wEnergy {n m : ℕ} (u : WSpace n × ℝ → WTarget m) (t : ℝ) : ℝ := ∫ x : WSpace n, wDensity u (x,t)
noncomputable def wA {n m : ℕ} (u : WSpace n × ℝ → WTarget m) (p : WSpace n × ℝ) : ℝ := inner ℝ (wT u p) (wT (wT u) p)
noncomputable def wB {n m : ℕ} (u : WSpace n × ℝ → WTarget m) (j : Fin n) (p : WSpace n × ℝ) : ℝ := inner ℝ (wX u j p) (wX (wT u) j p)
noncomputable def wC {n m : ℕ} (u : WSpace n × ℝ → WTarget m) (j : Fin n) (p : WSpace n × ℝ) : ℝ := inner ℝ (wT u p) (wX (wX u j) j p)
noncomputable def wG {n m : ℕ} (u : WSpace n × ℝ → WTarget m) (j : Fin n) (p : WSpace n × ℝ) : ℝ := inner ℝ (wT u p) (wX u j p)
def wDomain (n : ℕ) : Set (WSpace n × ℝ) := {p | 0 < p.2}
def wBox (n : ℕ) (R : ℝ) : Set (WSpace n) := Set.Icc (fun _ => -R) (fun _ => R)
def wOpenBox (n : ℕ) (R : ℝ) : Set (WSpace n) := {x | ∀ j, -R < x j ∧ x j < R}
noncomputable def wTerms {n m : ℕ} (u : WSpace n × ℝ → WTarget m) (r : ℝ) : Set (WSpace n → ℝ) := {f | f = (fun x => wDensity u (x,r)) ∨ f = (fun x => wT (wDensity u) (x,r)) ∨ f = (fun x => wA u (x,r)) ∨ ∃ j : Fin n, f = (fun x => wB u j (x,r)) ∨ f = (fun x => wC u j (x,r)) ∨ f = (fun x => wG u j (x,r)) ∨ f = (fun x => wX (wG u j) j (x,r))}
def wNice {n : ℕ} (C : Set (WSpace n)) (f : WSpace n → ℝ) : Prop := Continuous f ∧ (∀ x, x ∉ C → f x = 0) ∧ Integrable f
noncomputable def wGeometry {n m : ℕ} (u : WSpace n × ℝ → WTarget m) (q : WTarget m) (t : ℝ) (C : Set (WSpace n)) (R : ℝ) : Prop := IsCompact C ∧ 0 < R ∧ C ⊆ wOpenBox n R ∧ (∀ x r, x ∉ C → r ∈ Set.Icc (t/2) (3*t/2) → u (x,r) = q) ∧ (∀ (k : ℕ) x r, 0 < k → x ∉ C → r ∈ Set.Ioo (t/2) (3*t/2) → iteratedFDeriv ℝ k u (x,r) = 0) ∧ volume (wBox n R) = ENNReal.ofReal ((2*R)^n) ∧ volume (wBox n R) < ⊤
noncomputable def wLocal {n m : ℕ} (u : WSpace n × ℝ → WTarget m) (q : WTarget m) (t : ℝ) (C : Set (WSpace n)) (R B : ℝ) : Prop := wGeometry u q t C R ∧ 0 ≤ B ∧ (∀ r ∈ Set.Ioo (t/2) (3*t/2), ∀ f ∈ wTerms u r, wNice C f) ∧ (∀ x ∈ wBox n R, ∀ r ∈ Set.Icc (3*t/4) (5*t/4), |wT (wDensity u) (x,r)| ≤ B)

namespace Translation
set_option autoImplicit false

theorem T001 (n : ℕ) (m : ℕ) (u : WSpace n × ℝ → WTarget m) (q : WTarget m) (h_H002 : ContDiffOn ℝ ∞ u (wDomain n)) (h_H004 : ∀ (x : WSpace n) (t : ℝ), 0 < t → ‖u (x,t)‖ = 1) :
    ∀ (x : WSpace n) (t : ℝ), 0 < t → inner ℝ (u (x,t)) (wT u (x,t)) = 0 ∧ ∀ j : Fin n, inner ℝ (u (x,t)) (wX u j (x,t)) = 0 := by
  have orth : ∀ (f : ℝ → WTarget m) (v : WTarget m) (a : ℝ),
      HasDerivAt f v a → (∀ᶠ r in nhds a, ‖f r‖ = 1) → inner ℝ (f a) v = 0 := by
    intro f v a hd hn
    have hc : HasDerivAt (fun r => inner ℝ (f r) (f r)) 0 a := by
      apply (hasDerivAt_const a (1 : ℝ)).congr_of_eventuallyEq
      filter_upwards [hn] with r hr
      simp [real_inner_self_eq_norm_sq, hr]
    have he := (hd.inner ℝ hd).unique hc
    have hs : inner ℝ v (f a) = inner ℝ (f a) v := real_inner_comm _ _
    linarith
  intro x t ht
  have ho : IsOpen (wDomain n) := isOpen_lt continuous_const continuous_snd
  have hu : DifferentiableAt ℝ u (x,t) :=
    (h_H002.differentiableOn (by simp)).differentiableAt (ho.mem_nhds ht)
  constructor
  · have hf : DifferentiableAt ℝ (fun r : ℝ => u (x,r)) t :=
      hu.comp t ((differentiableAt_const x).prodMk differentiableAt_id)
    apply orth (fun r => u (x,r)) (wT u (x,t)) t hf.hasDerivAt
    filter_upwards [Ioi_mem_nhds ht] with r hr
    exact h_H004 x r hr
  · intro j
    have hf : DifferentiableAt ℝ (fun y : WSpace n => u (y,t)) x :=
      hu.comp x (differentiableAt_id.prodMk (differentiableAt_const t))
    have hc : HasDerivAt (fun r : ℝ => x + r • Pi.single j (1 : ℝ)) (Pi.single j 1) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single j (1 : ℝ))).const_add x
    have hd : HasDerivAt (fun r : ℝ => u (x + r • Pi.single j 1,t)) (wX u j (x,t)) 0 := by
      simpa [Function.comp_def, wX, wDx] using
        hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 hc (by simp)
    have hn : ∀ᶠ r : ℝ in nhds 0, ‖u (x + r • Pi.single j 1,t)‖ = 1 :=
      Filter.Eventually.of_forall (fun r => h_H004 _ t ht)
    simpa using orth _ _ 0 hd hn

theorem T002 (n : ℕ) (m : ℕ) (u : WSpace n × ℝ → WTarget m) (q : WTarget m) (h_H002 : ContDiffOn ℝ ∞ u (wDomain n)) (h_H004 : ∀ (x : WSpace n) (t : ℝ), 0 < t → ‖u (x,t)‖ = 1) (h_H005 : ∀ (x : WSpace n) (t : ℝ), 0 < t → ∃ a : ℝ, wT (wT u) (x,t) - wLap u (x,t) = a • u (x,t)) (h_T001 : ∀ (x : WSpace n) (t : ℝ), 0 < t → inner ℝ (u (x,t)) (wT u (x,t)) = 0 ∧ ∀ j : Fin n, inner ℝ (u (x,t)) (wX u j (x,t)) = 0) :
    ∀ (x : WSpace n) (t : ℝ), 0 < t → inner ℝ (wT u (x,t)) (wT (wT u) (x,t) - wLap u (x,t)) = 0 ∧ (∀ a : ℝ, wT (wT u) (x,t) - wLap u (x,t) = a • u (x,t) → a = (∑ j : Fin n, ‖wX u j (x,t)‖^2) - ‖wT u (x,t)‖^2) := by
  have hsecond : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → WTarget m) (z v : E), ContDiffAt ℝ ∞ f z → (∀ᶠ y in nhds z, inner ℝ (f y) (fderiv ℝ f y v) = 0) → inner ℝ (f z) (fderiv ℝ (fun y => fderiv ℝ f y v) z v) = - ‖fderiv ℝ f z v‖^2 := by
    intro E _ _ f z v hf ht
    have hd : DifferentiableAt ℝ f z := hf.differentiableAt (by simp)
    have hg : DifferentiableAt ℝ (fun y => fderiv ℝ f y v) z :=
      ((hf.fderiv_right (m := 1) (WithTop.coe_le_coe.mpr le_top)).clm_apply (contDiffAt_const : ContDiffAt ℝ 1 (fun _ : E => v) z)).differentiableAt_one
    have hh := hd.hasFDerivAt.inner ℝ hg.hasFDerivAt
    have hz : HasFDerivAt (fun y : E => (0 : ℝ)) _ z := hh.congr_of_eventuallyEq (by filter_upwards [ht] with y hy; exact hy.symm)
    have he := congrArg (fun L : E →L[ℝ] ℝ => L v) (hz.unique (hasFDerivAt_const (0 : ℝ) z))
    simp [fderivInnerCLM_apply] at he
    linarith
  intro x t ht
  constructor
  · obtain ⟨a, ha⟩ := h_H005 x t ht
    have hzero : inner ℝ (wT u (x,t)) (u (x,t)) = 0 := by
      calc
        inner ℝ (wT u (x,t)) (u (x,t)) = inner ℝ (u (x,t)) (wT u (x,t)) := real_inner_comm _ _
        _ = 0 := (h_T001 x t ht).1
    rw [ha, inner_smul_right, hzero, mul_zero]
  · have ho : IsOpen (wDomain n) := isOpen_lt continuous_const continuous_snd
    have hu : ContDiffAt ℝ ∞ u (x,t) := h_H002.contDiffAt (ho.mem_nhds ht)
    have htime : ContDiffAt ℝ ∞ (fun r : ℝ => u (x,r)) t := hu.comp t (contDiffAt_const.prodMk contDiffAt_id)
    have hspace : ContDiffAt ℝ ∞ (fun y : WSpace n => u (y,t)) x := hu.comp x (contDiffAt_id.prodMk contDiffAt_const)
    have htt : inner ℝ (u (x,t)) (wT (wT u) (x,t)) = - ‖wT u (x,t)‖^2 := by
      apply hsecond (fun r : ℝ => u (x,r)) t 1 htime
      filter_upwards [isOpen_Ioi.mem_nhds ht] with r hr
      exact (h_T001 x r hr).1
    have hxx : ∀ j : Fin n, inner ℝ (u (x,t)) (wX (wX u j) j (x,t)) = - ‖wX u j (x,t)‖^2 := by
      intro j
      apply hsecond (fun y : WSpace n => u (y,t)) x (Pi.single j 1) hspace
      exact Filter.Eventually.of_forall (fun y => (h_T001 y t ht).2 j)
    intro a ha
    have he := congrArg (fun v : WTarget m => inner ℝ (u (x,t)) v) ha
    simp only [inner_sub_right, wLap, inner_sum, htt, hxx, inner_smul_right, real_inner_self_eq_norm_sq, h_H004 x t ht, one_pow, mul_one] at he
    rw [Finset.sum_neg_distrib] at he
    linarith

theorem T003 (n : ℕ) (m : ℕ) (u : WSpace n × ℝ → WTarget m) (q : WTarget m) (h_H002 : ContDiffOn ℝ ∞ u (wDomain n)) (h_T001 : ∀ (x : WSpace n) (t : ℝ), 0 < t → inner ℝ (u (x,t)) (wT u (x,t)) = 0 ∧ ∀ j : Fin n, inner ℝ (u (x,t)) (wX u j (x,t)) = 0) (h_T002 : ∀ (x : WSpace n) (t : ℝ), 0 < t → inner ℝ (wT u (x,t)) (wT (wT u) (x,t) - wLap u (x,t)) = 0 ∧ (∀ a : ℝ, wT (wT u) (x,t) - wLap u (x,t) = a • u (x,t) → a = (∑ j : Fin n, ‖wX u j (x,t)‖^2) - ‖wT u (x,t)‖^2)) :
    ContDiffOn ℝ ∞ (wDensity u) (wDomain n) ∧ ContinuousOn (wT (wDensity u)) (wDomain n) ∧ ∀ (x : WSpace n) (t : ℝ), 0 < t → inner ℝ (u (x,t)) (wT u (x,t)) = 0 ∧ inner ℝ (wT u (x,t)) (wT (wT u) (x,t) - wLap u (x,t)) = 0 ∧ (∀ a : ℝ, wT (wT u) (x,t) - wLap u (x,t) = a • u (x,t) → a = (∑ j : Fin n, ‖wX u j (x,t)‖^2) - ‖wT u (x,t)‖^2) ∧ (∀ j : Fin n, wT (wX u j) (x,t) = wX (wT u) j (x,t)) ∧ wT (wDensity u) (x,t) = 2 * wA u (x,t) + 2 * ∑ j : Fin n, wB u j (x,t) := by
  have hcoord : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : WSpace n × ℝ → F) (p : WSpace n × ℝ), DifferentiableAt ℝ f p → wT f p = fderiv ℝ f p (0, 1) ∧ ∀ j, wX f j p = fderiv ℝ f p (Pi.single j 1, 0) := by
    intro F _ _ f p hf
    constructor
    · exact (hf.hasFDerivAt.comp_hasDerivAt p.2 ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))).deriv
    · intro j
      have hh : HasFDerivAt (fun x : WSpace n => (x, p.2)) ((ContinuousLinearMap.id ℝ (WSpace n)).prod (0 : WSpace n →L[ℝ] ℝ)) p.1 := (hasFDerivAt_id p.1).prodMk (hasFDerivAt_const p.2 p.1)
      exact congrArg (fun L : WSpace n →L[ℝ] F => L (Pi.single j 1)) (hf.hasFDerivAt.comp p.1 hh).fderiv
  have hopen : IsOpen (wDomain n) := isOpen_lt continuous_const continuous_snd
  have hsmooth : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : WSpace n × ℝ → F), ContDiffOn ℝ ∞ f (wDomain n) → ContDiffOn ℝ ∞ (wT f) (wDomain n) ∧ ∀ j, ContDiffOn ℝ ∞ (wX f j) (wDomain n) := by
    intro F _ _ f hf
    have hd : ContDiffOn ℝ ∞ (fderiv ℝ f) (wDomain n) := hf.fderiv_of_isOpen hopen (by simp)
    have he (p) (hp : p ∈ wDomain n) := hcoord f p ((hf.contDiffAt (hopen.mem_nhds hp)).differentiableAt (by simp))
    constructor
    · have hh : ContDiffOn ℝ ∞ (fun p => fderiv ℝ f p (0,1)) (wDomain n) := hd.clm_apply contDiffOn_const
      exact hh.congr (fun p hp => (he p hp).1)
    · intro j
      have hh : ContDiffOn ℝ ∞ (fun p => fderiv ℝ f p (Pi.single j 1,0)) (wDomain n) := hd.clm_apply contDiffOn_const
      exact hh.congr (fun p hp => (he p hp).2 j)
  have ht := (hsmooth u h_H002).1
  have hx := (hsmooth u h_H002).2
  have he : ContDiffOn ℝ ∞ (wDensity u) (wDomain n) := by
    exact (ht.norm_sq ℝ).add (ContDiffOn.sum (fun j _ => (hx j).norm_sq ℝ))
  refine ⟨he, (hsmooth (wDensity u) he).1.continuousOn, ?_⟩
  intro x t htpos
  have hp : (x,t) ∈ wDomain n := htpos
  have hnh := hopen.mem_nhds hp
  have hdiff : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : WSpace n × ℝ → F}, ContDiffOn ℝ ∞ f (wDomain n) → DifferentiableAt ℝ f (x,t) := by
    intro F _ _ f hf
    exact (hf.contDiffAt hnh).differentiableAt (by simp)
  have hmixed : ∀ j, wT (wX u j) (x,t) = wX (wT u) j (x,t) := by
    intro j
    have hd := hdiff (h_H002.fderiv_of_isOpen hopen (m := ∞) (by simp))
    have eqX : wX u j =ᶠ[nhds (x,t)] (fun p => fderiv ℝ u p (Pi.single j 1, 0)) := by
      filter_upwards [hnh] with p hp
      exact (hcoord u p ((h_H002.contDiffAt (hopen.mem_nhds hp)).differentiableAt (by simp))).2 j
    have eqT : wT u =ᶠ[nhds (x,t)] (fun p => fderiv ℝ u p (0, 1)) := by
      filter_upwards [hnh] with p hp
      exact (hcoord u p ((h_H002.contDiffAt (hopen.mem_nhds hp)).differentiableAt (by simp))).1
    rw [(hcoord (wX u j) (x,t) (hdiff (hx j))).1, (hcoord (wT u) (x,t) (hdiff ht)).2 j, eqX.fderiv_eq, eqT.fderiv_eq]
    rw [fderiv_clm_apply hd (differentiableAt_const (Pi.single j 1, (0 : ℝ))), fderiv_clm_apply hd (differentiableAt_const ((0 : WSpace n), (1 : ℝ)))]
    simpa using (h_H002.contDiffAt hnh).isSymmSndFDerivAt (by simp; exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2) (0,1) (Pi.single j 1,0)
  refine ⟨(h_T001 x t htpos).1, (h_T002 x t htpos).1, (h_T002 x t htpos).2, hmixed, ?_⟩
  have hcurve : ∀ {f : WSpace n × ℝ → WTarget m}, ContDiffOn ℝ ∞ f (wDomain n) → HasDerivAt (fun r => f (x,r)) (wT f (x,t)) t := by
    intro f hf
    rw [(hcoord f (x,t) (hdiff hf)).1]
    exact (hdiff hf).hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_const t x).prodMk (hasDerivAt_id t))
  have h0 := (hcurve ht).norm_sq
  have hj (j : Fin n) := (hcurve (hx j)).norm_sq
  have hh := h0.add (HasDerivAt.sum (u := Finset.univ) (fun j _ => hj j))
  have hfun : ((fun r : ℝ => ‖wT u (x,r)‖^2) + ∑ j : Fin n, (fun r : ℝ => ‖wX u j (x,r)‖^2)) = (fun r => wDensity u (x,r)) := by
    ext r
    simp [wDensity]
  rw [hfun] at hh
  change deriv (fun r => wDensity u (x,r)) t = _
  rw [hh.deriv]
  simp_rw [hmixed]
  simp [wA, wB, Finset.mul_sum]

theorem T004 (n : ℕ) (m : ℕ) (u : WSpace n × ℝ → WTarget m) (q : WTarget m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ u (wDomain n)) (h_H006 : ∀ s t : ℝ, 0 < s → s < t → ∃ C : Set (WSpace n), IsCompact C ∧ ∀ x r, x ∉ C → r ∈ Set.Icc s t → u (x,r) = q) :
    ∀ t : ℝ, 0 < t → ∃ (C : Set (WSpace n)) (R : ℝ), wGeometry u q t C R := by
  intro t ht
  obtain ⟨C, hC, hu⟩ := h_H006 (t/2) (3*t/2) (by linarith) (by linarith)
  obtain ⟨L, hL⟩ := hC.exists_bound_of_continuousOn (continuous_norm.continuousOn : ContinuousOn (fun x : WSpace n => ‖x‖) C)
  let R : ℝ := max 1 (L+1)
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hLR : L < R := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hsub : C ⊆ wOpenBox n R := by
    intro x hx j
    have hxL : ‖x‖ ≤ L := by simpa only [norm_norm] using hL x hx
    have hj : |x j| < R := lt_of_le_of_lt (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x j) (lt_of_le_of_lt hxL hLR)
    exact abs_lt.mp hj
  have hv : volume (wBox n R) = ENNReal.ofReal ((2*R)^n) := by
    simp only [wBox, Real.volume_Icc_pi, sub_neg_eq_add, ← two_mul]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact (ENNReal.ofReal_pow (by positivity : 0 ≤ 2 * R) n).symm
  refine ⟨C, R, hC, hR, hsub, hu, ?_, hv, ?_⟩
  · intro k x r hk hx hr
    have hopen : IsOpen (Cᶜ ×ˢ Set.Ioo (t/2) (3*t/2)) := hC.isClosed.isOpen_compl.prod isOpen_Ioo
    have heq : u =ᶠ[nhds (x,r)] (fun _ => q) := by
      filter_upwards [hopen.mem_nhds (show (x,r) ∈ Cᶜ ×ˢ Set.Ioo (t/2) (3*t/2) from ⟨hx, hr⟩)] with p hp
      exact hu p.1 p.2 hp.1 ⟨hp.2.1.le, hp.2.2.le⟩
    rw [(heq.iteratedFDeriv ℝ k).eq_of_nhds, iteratedFDeriv_const_of_ne (Nat.ne_of_gt hk)]
    rfl
  · rw [hv]
    exact ENNReal.ofReal_lt_top

theorem T005 (n : ℕ) (m : ℕ) (u : WSpace n × ℝ → WTarget m) (q : WTarget m) (h_H002 : ContDiffOn ℝ ∞ u (wDomain n)) (h_T004 : ∀ t : ℝ, 0 < t → ∃ (C : Set (WSpace n)) (R : ℝ), wGeometry u q t C R) :
    ∀ t : ℝ, 0 < t → Integrable (fun x : WSpace n => wDensity u (x,t)) ∧ ∃ (C : Set (WSpace n)) (R B : ℝ), wLocal u q t C R B := by
  classical
  have sd : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : WSpace n × ℝ → F) (p : WSpace n × ℝ), ContDiffAt ℝ ∞ f p → ContDiffAt ℝ ∞ (wT f) p ∧ ∀ j, ContDiffAt ℝ ∞ (wX f j) p := by
    intro F _ _ f p hf
    constructor
    · have hh : ContDiffAt ℝ ∞ (fun z : (WSpace n × ℝ) × ℝ => f (z.1.1,z.2)) (p,p.2) := hf.comp _ (contDiffAt_fst.fst.prodMk contDiffAt_snd)
      exact (hh.fderiv contDiffAt_snd (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞)).clm_apply (contDiffAt_const (c := (1 : ℝ)))
    · intro j
      have hh : ContDiffAt ℝ ∞ (fun z : (WSpace n × ℝ) × WSpace n => f (z.2,z.1.2)) (p,p.1) := hf.comp _ (contDiffAt_snd.prodMk contDiffAt_fst.snd)
      exact (hh.fderiv contDiffAt_fst (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞)).clm_apply (contDiffAt_const (c := (Pi.single j 1 : WSpace n)))
  have zd : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : WSpace n × ℝ → F) (c : F) (O : Set (WSpace n × ℝ)), IsOpen O → (∀ p ∈ O, f p = c) → ∀ p ∈ O, wT f p = 0 ∧ ∀ j, wX f j p = 0 := by
    intro F _ _ f c O hO hf p hp
    have he : f =ᶠ[nhds p] (fun _ => c) := Filter.eventuallyEq_of_mem (hO.mem_nhds hp) hf
    constructor
    · have hline : (fun r => f (p.1,r)) =ᶠ[nhds p.2] (fun _ => c) := he.comp_tendsto (continuousAt_const.prodMk continuousAt_id)
      change deriv (fun r => f (p.1,r)) p.2 = 0
      rw [hline.deriv_eq, deriv_const]
    · intro j
      have hline : (fun x => f (x,p.2)) =ᶠ[nhds p.1] (fun _ => c) := he.comp_tendsto (continuousAt_id.prodMk continuousAt_const)
      change fderiv ℝ (fun x => f (x,p.2)) p.1 (Pi.single j 1) = 0
      rw [hline.fderiv_eq, fderiv_const_apply]
      rfl
  have hDom : IsOpen (wDomain n) := isOpen_lt continuous_const continuous_snd
  have su : ∀ p ∈ wDomain n, ContDiffAt ℝ ∞ u p := fun p hp => h_H002.contDiffAt (hDom.mem_nhds hp)
  have st : ∀ p ∈ wDomain n, ContDiffAt ℝ ∞ (wT u) p := fun p hp => (sd u p (su p hp)).1
  have sx : ∀ j p, p ∈ wDomain n → ContDiffAt ℝ ∞ (wX u j) p := fun j p hp => (sd u p (su p hp)).2 j
  have se : ∀ p ∈ wDomain n, ContDiffAt ℝ ∞ (wDensity u) p := by
    intro p hp
    exact ((st p hp).norm_sq ℝ).add (ContDiffAt.sum (fun j _ => (sx j p hp).norm_sq ℝ))
  have set : ∀ p ∈ wDomain n, ContDiffAt ℝ ∞ (wT (wDensity u)) p := fun p hp => (sd _ p (se p hp)).1
  have sg : ∀ j p, p ∈ wDomain n → ContDiffAt ℝ ∞ (wG u j) p := fun j p hp => (st p hp).inner ℝ (sx j p hp)
  intro t ht
  obtain ⟨C, R, hgeo⟩ := h_T004 t ht
  have hC : IsCompact C := hgeo.1
  let O : Set (WSpace n × ℝ) := Cᶜ ×ˢ Ioo (t/2) (3*t/2)
  have hO : IsOpen O := hC.isClosed.isOpen_compl.prod isOpen_Ioo
  have zu : ∀ p ∈ O, u p = q := by
    intro p hp
    exact hgeo.2.2.2.1 p.1 p.2 hp.1 ⟨hp.2.1.le, hp.2.2.le⟩
  have zt : ∀ p ∈ O, wT u p = 0 := fun p hp => (zd u q O hO zu p hp).1
  have zx : ∀ j p, p ∈ O → wX u j p = 0 := fun j p hp => (zd u q O hO zu p hp).2 j
  have ze : ∀ p ∈ O, wDensity u p = 0 := by
    intro p hp
    simp [wDensity, zt p hp, fun j => zx j p hp]
  have zet : ∀ p ∈ O, wT (wDensity u) p = 0 := fun p hp => (zd _ 0 O hO ze p hp).1
  have zg : ∀ j p, p ∈ O → wG u j p = 0 := by
    intro j p hp
    simp [wG, zt p hp]
  have zxg : ∀ j p, p ∈ O → wX (wG u j) j p = 0 := fun j p hp => (zd _ 0 O hO (zg j) p hp).2 j
  have nice : ∀ (f : WSpace n × ℝ → ℝ), (∀ p ∈ wDomain n, ContDiffAt ℝ ∞ f p) → (∀ p ∈ O, f p = 0) → ∀ r ∈ Ioo (t/2) (3*t/2), wNice C (fun x => f (x,r)) := by
    intro f hs hz r hr
    have hr0 : 0 < r := by linarith [hr.1]
    have hc : Continuous (fun x : WSpace n => f (x,r)) := by
      apply continuous_iff_continuousAt.mpr
      intro x
      exact ContinuousAt.comp (f := fun y : WSpace n => (y,r)) (hs (x,r) hr0).continuousAt (continuousAt_id.prodMk continuousAt_const)
    have hzero : ∀ x, x ∉ C → f (x,r) = 0 := fun x hx => hz (x,r) ⟨hx,hr⟩
    refine ⟨hc, hzero, hc.integrable_of_hasCompactSupport ?_⟩
    apply HasCompactSupport.of_support_subset_isCompact hC
    intro x hx
    by_contra hn
    exact hx (hzero x hn)
  have hn : ∀ r ∈ Ioo (t/2) (3*t/2), ∀ f ∈ wTerms u r, wNice C f := by
    intro r hr f hf
    rcases hf with h | h | h | ⟨j, h | h | h | h⟩
    · subst f; exact nice _ se ze r hr
    · subst f; exact nice _ set zet r hr
    · subst f
      apply nice _ (fun p hp => (st p hp).inner ℝ ((sd _ p (st p hp)).1)) ?_ r hr
      intro p hp
      simp [wA, zt p hp]
    · subst f
      apply nice _ (fun p hp => (sx j p hp).inner ℝ ((sd _ p (st p hp)).2 j)) ?_ r hr
      intro p hp
      simp [wB, zx j p hp]
    · subst f
      apply nice _ (fun p hp => (st p hp).inner ℝ ((sd _ p (sx j p hp)).2 j)) ?_ r hr
      intro p hp
      simp [wC, zt p hp]
    · subst f; exact nice _ (sg j) (zg j) r hr
    · subst f
      exact nice _ (fun p hp => (sd _ p (sg j p hp)).2 j) (zxg j) r hr
  have hti : t ∈ Ioo (t/2) (3*t/2) := by constructor <;> linarith
  have hi : Integrable (fun x : WSpace n => wDensity u (x,t)) := (nice _ se ze t hti).2.2
  have hk : IsCompact (wBox n R ×ˢ Icc (3*t/4) (5*t/4)) := isCompact_Icc.prod isCompact_Icc
  have hcont : ContinuousOn (wT (wDensity u)) (wBox n R ×ˢ Icc (3*t/4) (5*t/4)) := by
    intro p hp
    apply (set p ?_).continuousAt.continuousWithinAt
    change 0 < p.2
    linarith [hp.2.1]
  obtain ⟨B0, hB0⟩ := hk.exists_bound_of_continuousOn hcont
  refine ⟨hi, C, R, max 0 B0, hgeo, le_max_left _ _, hn, ?_⟩
  intro x hx r hr
  have hb : |wT (wDensity u) (x,r)| ≤ B0 := by simpa only [Real.norm_eq_abs] using hB0 (x,r) ⟨hx,hr⟩
  exact hb.trans (le_max_right _ _)

theorem T006 (n : ℕ) (m : ℕ) (u : WSpace n × ℝ → WTarget m) (q : WTarget m) (h_H002 : ContDiffOn ℝ ∞ u (wDomain n)) (h_T003 : ContDiffOn ℝ ∞ (wDensity u) (wDomain n) ∧ ContinuousOn (wT (wDensity u)) (wDomain n) ∧ ∀ (x : WSpace n) (t : ℝ), 0 < t → inner ℝ (u (x,t)) (wT u (x,t)) = 0 ∧ inner ℝ (wT u (x,t)) (wT (wT u) (x,t) - wLap u (x,t)) = 0 ∧ (∀ a : ℝ, wT (wT u) (x,t) - wLap u (x,t) = a • u (x,t) → a = (∑ j : Fin n, ‖wX u j (x,t)‖^2) - ‖wT u (x,t)‖^2) ∧ (∀ j : Fin n, wT (wX u j) (x,t) = wX (wT u) j (x,t)) ∧ wT (wDensity u) (x,t) = 2 * wA u (x,t) + 2 * ∑ j : Fin n, wB u j (x,t)) (h_T005 : ∀ t : ℝ, 0 < t → Integrable (fun x : WSpace n => wDensity u (x,t)) ∧ ∃ (C : Set (WSpace n)) (R B : ℝ), wLocal u q t C R B) :
    ∀ t : ℝ, 0 < t → ∀ (C : Set (WSpace n)) (R B : ℝ), wLocal u q t C R B → Integrable ((wBox n R).indicator (fun _ => B)) ∧ ∀ h : ℝ, 0 < |h| → |h| < t/4 → ∀ x : WSpace n, |(wDensity u (x,t+h) - wDensity u (x,t))/h| ≤ (wBox n R).indicator (fun _ => B) x := by
  intro t ht C R B hloc
  rcases hloc with ⟨hgeom, hB, hnice, hbound⟩
  rcases hgeom with ⟨hC, hR, hCQ, hu, hiter, hvol, hfin⟩
  have hmeas : MeasurableSet (wBox n R) := measurableSet_Icc
  constructor
  · exact (integrableOn_const (C := B) hfin.ne).integrable_indicator hmeas
  · intro h hh hsmall x
    have htJ : t ∈ Ioo (t/2) (3*t/2) := by constructor <;> linarith
    have hh' := abs_lt.mp hsmall
    have hthJ : t+h ∈ Ioo (t/2) (3*t/2) := by constructor <;> linarith
    by_cases hx : x ∈ wBox n R
    · rw [Set.indicator_of_mem hx]
      have hd : ∀ r ∈ Icc (3*t/4) (5*t/4), DifferentiableAt ℝ (fun s : ℝ => wDensity u (x,s)) r := by
        intro r hr
        have hopen : IsOpen (wDomain n) := isOpen_Ioi.preimage continuous_snd
        have hp : (x,r) ∈ wDomain n := by change 0 < r; linarith [hr.1]
        have hd : DifferentiableAt ℝ (wDensity u) (x,r) :=
          (h_T003.1.contDiffAt (hopen.mem_nhds hp)).differentiableAt (by simp)
        exact hd.comp r ((differentiableAt_const x).prodMk differentiableAt_id)
      have hb : ∀ r ∈ Icc (3*t/4) (5*t/4), ‖deriv (fun s : ℝ => wDensity u (x,s)) r‖ ≤ B := by
        intro r hr
        exact hbound x hx r hr
      have htI : t ∈ Icc (3*t/4) (5*t/4) := by constructor <;> linarith
      have hthI : t+h ∈ Icc (3*t/4) (5*t/4) := by constructor <;> linarith
      have hm := Convex.norm_image_sub_le_of_norm_deriv_le hd hb (convex_Icc _ _) htI hthI
      have hm' : |wDensity u (x,t+h) - wDensity u (x,t)| ≤ B * |h| := by
        simpa only [Real.norm_eq_abs, add_sub_cancel_left] using hm
      rw [abs_div]
      exact (div_le_iff₀ hh).2 hm'
    · rw [Set.indicator_of_notMem hx]
      have hxC : x ∉ C := by
        intro hc
        apply hx
        have hc' := hCQ hc
        change (fun _ => -R) ≤ x ∧ x ≤ (fun _ => R)
        exact ⟨fun j => (hc' j).1.le, fun j => (hc' j).2.le⟩
      have hz (r : ℝ) (hr : r ∈ Ioo (t/2) (3*t/2)) : wDensity u (x,r) = 0 := by
        have hn : wNice C (fun y => wDensity u (y,r)) := hnice r hr _ (Or.inl rfl)
        exact hn.2.1 x hxC
      rw [hz (t+h) hthJ, hz t htJ]
      simp

theorem T007 (n : ℕ) (m : ℕ) (u : WSpace n × ℝ → WTarget m) (q : WTarget m) (h_H002 : ContDiffOn ℝ ∞ u (wDomain n)) (h_T003 : ContDiffOn ℝ ∞ (wDensity u) (wDomain n) ∧ ContinuousOn (wT (wDensity u)) (wDomain n) ∧ ∀ (x : WSpace n) (t : ℝ), 0 < t → inner ℝ (u (x,t)) (wT u (x,t)) = 0 ∧ inner ℝ (wT u (x,t)) (wT (wT u) (x,t) - wLap u (x,t)) = 0 ∧ (∀ a : ℝ, wT (wT u) (x,t) - wLap u (x,t) = a • u (x,t) → a = (∑ j : Fin n, ‖wX u j (x,t)‖^2) - ‖wT u (x,t)‖^2) ∧ (∀ j : Fin n, wT (wX u j) (x,t) = wX (wT u) j (x,t)) ∧ wT (wDensity u) (x,t) = 2 * wA u (x,t) + 2 * ∑ j : Fin n, wB u j (x,t)) (h_T005 : ∀ t : ℝ, 0 < t → Integrable (fun x : WSpace n => wDensity u (x,t)) ∧ ∃ (C : Set (WSpace n)) (R B : ℝ), wLocal u q t C R B) (h_T006 : ∀ t : ℝ, 0 < t → ∀ (C : Set (WSpace n)) (R B : ℝ), wLocal u q t C R B → Integrable ((wBox n R).indicator (fun _ => B)) ∧ ∀ h : ℝ, 0 < |h| → |h| < t/4 → ∀ x : WSpace n, |(wDensity u (x,t+h) - wDensity u (x,t))/h| ≤ (wBox n R).indicator (fun _ => B) x) :
    ∀ t : ℝ, 0 < t → Filter.Tendsto (fun h : ℝ => ∫ x : WSpace n, (wDensity u (x,t+h) - wDensity u (x,t))/h) (nhdsWithin 0 ({0}ᶜ)) (nhds (∫ x : WSpace n, wT (wDensity u) (x,t))) := by
  intro t ht
  obtain ⟨C, R, B, hloc⟩ := (h_T005 t ht).2
  obtain ⟨hb, hbound⟩ := h_T006 t ht C R B hloc
  have hsmall : ∀ᶠ h : ℝ in nhdsWithin 0 ({0}ᶜ), |h| < t/4 := by
    have he := eventually_norm_sub_lt (0 : ℝ) (show 0 < t/4 by linarith)
    exact (he.mono (fun h hh => by simpa using hh)).filter_mono nhdsWithin_le_nhds
  have hne : ∀ᶠ h : ℝ in nhdsWithin 0 ({0}ᶜ), h ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact hh
  apply tendsto_integral_filter_of_dominated_convergence ((wBox n R).indicator (fun _ => B))
  · filter_upwards [hsmall] with h hh
    have hpos : 0 < t+h := by have := neg_abs_le h; linarith
    exact (((h_T005 (t+h) hpos).1.sub (h_T005 t ht).1).div_const h).aestronglyMeasurable
  · filter_upwards [hsmall, hne] with h hh hn
    exact Filter.Eventually.of_forall (fun x => by
      simpa only [Real.norm_eq_abs] using hbound h (abs_pos.mpr hn) hh x)
  · exact hb
  · apply Filter.Eventually.of_forall
    intro x
    have hopen : IsOpen (wDomain n) := isOpen_lt continuous_const continuous_snd
    have hd : DifferentiableAt ℝ (wDensity u) (x,t) :=
      (h_T003.1.differentiableOn (by simp)).differentiableAt (hopen.mem_nhds ht)
    have hc : DifferentiableAt ℝ (fun r : ℝ => wDensity u (x,r)) t :=
      hd.comp t ((differentiableAt_const x).prodMk differentiableAt_id)
    simpa only [wT, smul_eq_mul, div_eq_mul_inv, mul_comm] using hc.hasDerivAt.tendsto_slope_zero

theorem T008 (n : ℕ) (m : ℕ) (u : WSpace n × ℝ → WTarget m) (q : WTarget m) (h_H002 : ContDiffOn ℝ ∞ u (wDomain n)) (h_T003 : ContDiffOn ℝ ∞ (wDensity u) (wDomain n) ∧ ContinuousOn (wT (wDensity u)) (wDomain n) ∧ ∀ (x : WSpace n) (t : ℝ), 0 < t → inner ℝ (u (x,t)) (wT u (x,t)) = 0 ∧ inner ℝ (wT u (x,t)) (wT (wT u) (x,t) - wLap u (x,t)) = 0 ∧ (∀ a : ℝ, wT (wT u) (x,t) - wLap u (x,t) = a • u (x,t) → a = (∑ j : Fin n, ‖wX u j (x,t)‖^2) - ‖wT u (x,t)‖^2) ∧ (∀ j : Fin n, wT (wX u j) (x,t) = wX (wT u) j (x,t)) ∧ wT (wDensity u) (x,t) = 2 * wA u (x,t) + 2 * ∑ j : Fin n, wB u j (x,t)) (h_T005 : ∀ t : ℝ, 0 < t → Integrable (fun x : WSpace n => wDensity u (x,t)) ∧ ∃ (C : Set (WSpace n)) (R B : ℝ), wLocal u q t C R B) (h_T007 : ∀ t : ℝ, 0 < t → Filter.Tendsto (fun h : ℝ => ∫ x : WSpace n, (wDensity u (x,t+h) - wDensity u (x,t))/h) (nhdsWithin 0 ({0}ᶜ)) (nhds (∫ x : WSpace n, wT (wDensity u) (x,t)))) :
    ∀ t : ℝ, 0 < t → DifferentiableAt ℝ (wEnergy u) t ∧ deriv (wEnergy u) t = ∫ x : WSpace n, wT (wDensity u) (x,t) ∧ HasDerivAt (wEnergy u) (∫ x : WSpace n, 2 * wA u (x,t) + 2 * ∑ j : Fin n, wB u j (x,t)) t ∧ Integrable (fun x : WSpace n => wT (wDensity u) (x,t)) ∧ Integrable (fun x : WSpace n => wA u (x,t)) ∧ ∀ j : Fin n, Integrable (fun x : WSpace n => wB u j (x,t)) := by
  intro t ht
  obtain ⟨hden, C, R, B, hloc⟩ := h_T005 t ht
  have htime : t ∈ Set.Ioo (t/2) (3*t/2) := by constructor <;> linarith
  have hn := hloc.2.2.1 t htime
  have hiT : Integrable (fun x : WSpace n => wT (wDensity u) (x,t)) := by
    exact (hn _ (Or.inr (Or.inl rfl))).2.2
  have hiA : Integrable (fun x : WSpace n => wA u (x,t)) := by
    exact (hn _ (Or.inr (Or.inr (Or.inl rfl)))).2.2
  have hiB : ∀ j : Fin n, Integrable (fun x : WSpace n => wB u j (x,t)) := by
    intro j
    exact (hn _ (Or.inr (Or.inr (Or.inr ⟨j, Or.inl rfl⟩)))).2.2
  have heq : ∀ᶠ h : ℝ in nhdsWithin 0 ({0}ᶜ),
      (∫ x : WSpace n, (wDensity u (x,t+h) - wDensity u (x,t))/h) =
        h⁻¹ • (wEnergy u (t+h) - wEnergy u t) := by
    have hsmall : ∀ᶠ h : ℝ in nhds (0 : ℝ), -t < h :=
      lt_mem_nhds (show -t < (0 : ℝ) by linarith)
    filter_upwards [hsmall.filter_mono nhdsWithin_le_nhds] with h hh
    have hth : 0 < t+h := by linarith
    rw [integral_div, integral_sub (h_T005 (t+h) hth).1 hden]
    simp only [wEnergy, smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hd : HasDerivAt (wEnergy u) (∫ x : WSpace n, wT (wDensity u) (x,t)) t := by
    apply hasDerivAt_iff_tendsto_slope_zero.mpr
    exact (h_T007 t ht).congr' heq
  have hident : (fun x : WSpace n => wT (wDensity u) (x,t)) =
      (fun x => 2 * wA u (x,t) + 2 * ∑ j : Fin n, wB u j (x,t)) := by
    funext x
    exact (h_T003.2.2 x t ht).2.2.2.2
  refine ⟨hd.differentiableAt, hd.deriv, ?_, hiT, hiA, hiB⟩
  rw [← hident]
  exact hd

theorem T009 (n : ℕ) (m : ℕ) (u : WSpace n × ℝ → WTarget m) (q : WTarget m) (h_H002 : ContDiffOn ℝ ∞ u (wDomain n)) (h_T005 : ∀ t : ℝ, 0 < t → Integrable (fun x : WSpace n => wDensity u (x,t)) ∧ ∃ (C : Set (WSpace n)) (R B : ℝ), wLocal u q t C R B) :
    ∀ t : ℝ, 0 < t → ∀ j : Fin n, ContDiff ℝ ∞ (fun x : WSpace n => wG u j (x,t)) ∧ HasCompactSupport (fun x : WSpace n => wG u j (x,t)) ∧ ∀ x : WSpace n, wX (wG u j) j (x,t) = wB u j (x,t) + wC u j (x,t) := by
  intro t ht j
  have hopen : IsOpen (wDomain n) := isOpen_lt continuous_const continuous_snd
  have hslice : ContDiff ℝ ∞ (fun x : WSpace n => (x,t)) := contDiff_id.prodMk contDiff_const
  have hu : ContDiff ℝ ∞ (fun x : WSpace n => u (x,t)) :=
    h_H002.comp_contDiff hslice (fun _ => ht)
  have htime : ∀ x : WSpace n, wT u (x,t) = fderiv ℝ u (x,t) (0,1) := by
    intro x
    have hd : DifferentiableAt ℝ u (x,t) :=
      (h_H002.contDiffAt (hopen.mem_nhds ht)).differentiableAt (by simp)
    have hc : HasDerivAt (fun r : ℝ => (x,r)) (0,1) t :=
      (hasDerivAt_const t x).prodMk (hasDerivAt_id t)
    exact (hd.hasFDerivAt.comp_hasDerivAt t hc).deriv
  have hT : ContDiff ℝ ∞ (fun x : WSpace n => wT u (x,t)) := by
    have hd : ContDiffOn ℝ ∞ (fderiv ℝ u) (wDomain n) :=
      h_H002.fderiv_of_isOpen hopen (by simp)
    have hh : ContDiff ℝ ∞ (fun x : WSpace n => fderiv ℝ u (x,t) (0,1)) :=
      (hd.comp_contDiff hslice (fun _ => ht)).clm_apply contDiff_const
    simpa only [← htime] using hh
  have hX : ContDiff ℝ ∞ (fun x : WSpace n => wX u j (x,t)) := by
    exact (hu.fderiv_right (by simp)).clm_apply contDiff_const
  refine ⟨hT.inner ℝ hX, ?_, ?_⟩
  · obtain ⟨C, R, B, hloc⟩ := (h_T005 t ht).2
    have hc : IsCompact C := hloc.1.1
    have hnice : wNice C (fun x => wG u j (x,t)) :=
      hloc.2.2.1 t (by constructor <;> linarith) _ (by
        right; right; right; exact ⟨j, Or.inr (Or.inr (Or.inl rfl))⟩)
    exact HasCompactSupport.intro hc hnice.2.1
  · intro x
    have hdT := (hT.differentiable (by simp) x).hasFDerivAt
    have hdX := (hX.differentiable (by simp) x).hasFDerivAt
    have he := congrArg (fun L : WSpace n →L[ℝ] ℝ => L (Pi.single j 1))
      ((hdT.inner ℝ hdX).fderiv)
    simpa [wX, wDx, wG, wB, wC, fderivInnerCLM_apply, real_inner_comm, add_comm] using he

theorem T010 (n : ℕ) (m : ℕ) (u : WSpace n × ℝ → WTarget m) (q : WTarget m)  :
    ∀ (d : ℕ) (j : Fin (d+1)) (R : ℝ), MeasureTheory.MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => ℝ) j) (volume.restrict (wBox (d+1) R)) ((volume.restrict (Set.Icc (-R) R)).prod (volume.restrict (wBox d R))) := by
  intro d j R
  have hBox (k : ℕ) : (volume.restrict (wBox k R) : Measure (WSpace k)) =
      Measure.pi (fun _ : Fin k => (volume : Measure ℝ).restrict (Set.Icc (-R) R)) := by
    rw [wBox, volume_pi, ← Set.pi_univ_Icc, Measure.restrict_pi_pi]
  rw [hBox (d+1), hBox d]
  exact measurePreserving_piFinSuccAbove
    (fun _ : Fin (d+1) => (volume : Measure ℝ).restrict (Set.Icc (-R) R)) j

theorem T011 (n : ℕ) (m : ℕ) (u : WSpace n × ℝ → WTarget m) (q : WTarget m) (h_T010 : ∀ (d : ℕ) (j : Fin (d+1)) (R : ℝ), MeasureTheory.MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => ℝ) j) (volume.restrict (wBox (d+1) R)) ((volume.restrict (Set.Icc (-R) R)).prod (volume.restrict (wBox d R)))) :
    ∀ (f : WSpace n → ℝ), ContDiff ℝ ∞ f → HasCompactSupport f → ∀ j : Fin n, Integrable (fun x : WSpace n => wDx f j x) ∧ (∫ x : WSpace n, wDx f j x) = 0 := by
  classical
  intro f hf hc j
  cases n with
  | zero => exact Fin.elim0 j
  | succ d =>
    have hcont : Continuous (fun x => wDx f j x) :=
      (hf.continuous_fderiv (by simp)).clm_apply continuous_const
    have hint : Integrable (fun x => wDx f j x) :=
      hcont.integrable_of_hasCompactSupport (hc.fderiv_apply ℝ (Pi.single j 1))
    refine ⟨hint, ?_⟩
    obtain ⟨R, hR, hbound⟩ := hc.isCompact.isBounded.subset_ball_lt 0 (0 : WSpace (d+1))
    have hcoord : ∀ x ∈ tsupport f, ∀ i, |x i| < R := by
      intro x hx i
      have hn : ‖x‖ < R := by simpa [Metric.mem_ball, dist_zero_right] using hbound hx
      exact lt_of_le_of_lt (by simpa [Real.norm_eq_abs] using norm_le_pi_norm x i) hn
    have hout : ∀ x, x ∉ wBox (d+1) R → wDx f j x = 0 := by
      intro x hx
      have hnot : x ∉ tsupport f := by
        intro h
        apply hx
        constructor <;> intro i
        · exact (abs_lt.mp (hcoord x h i)).1.le
        · exact (abs_lt.mp (hcoord x h i)).2.le
      simp [wDx, fderiv_of_notMem_tsupport ℝ hnot]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hout]
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => ℝ) j
    let μ : Measure ℝ := volume.restrict (Icc (-R) R)
    let ν : Measure (WSpace d) := volume.restrict (wBox d R)
    have hem : MeasurePreserving e (volume.restrict (wBox (d+1) R)) (μ.prod ν) := h_T010 d j R
    have hes : MeasurePreserving e.symm (μ.prod ν) (volume.restrict (wBox (d+1) R)) := hem.symm e
    let k : ℝ × WSpace d → ℝ := fun p => wDx f j (e.symm p)
    have hk : Integrable k (μ.prod ν) :=
      (hes.integrable_comp_emb e.symm.measurableEmbedding).mpr hint.integrableOn
    haveI : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr (isCompact_Icc.measure_lt_top.ne)
    haveI : IsFiniteMeasure μ := by dsimp [μ]; infer_instance
    rw [← hes.integral_comp' (fun x => wDx f j x), integral_prod_symm _ hk]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem (show MeasurableSet (wBox d R) from measurableSet_Icc)] with y hy
    have hline : ∀ r, HasDerivAt (fun s => f (j.insertNth s y)) (wDx f j (j.insertNth r y)) r := by
      intro r
      have hi : HasDerivAt (fun s : ℝ => Fin.insertNth (α := fun _ => ℝ) j s y) (Pi.single j 1) r := by
        apply hasDerivAt_pi.mpr
        intro i
        refine Fin.succAboveCases j ?_ (fun l => ?_) i
        · convert hasDerivAt_id r using 0 <;> simp only [Fin.insertNth_apply_same, Pi.single_eq_same] <;> rfl
        · simpa [Fin.insertNth_apply_succAbove, Pi.single_apply, j.succAbove_ne] using (hasDerivAt_const r (y l))
      convert (hf.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt r hi using 0 <;> rfl
    have hend : ∀ r : ℝ, |r| = R → f (j.insertNth r y) = 0 := by
      intro r hr
      apply image_eq_zero_of_notMem_tsupport
      intro hx
      have hh := hcoord _ hx j
      simpa [hr] using hh
    have hcLine : Continuous (fun r : ℝ => wDx f j (j.insertNth r y)) :=
      hcont.comp (Continuous.finInsertNth (A := fun _ : Fin (d+1) => ℝ) j continuous_id (continuous_const : Continuous (fun _ : ℝ => y)))
    change (∫ r in Icc (-R) R, wDx f j (e.symm (r,y))) = 0
    simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Equiv.coe_fn_mk]
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : -R ≤ R)]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hline r) (hcLine.intervalIntegrable (-R) R)]
    rw [hend R (abs_of_pos hR), hend (-R) (by rw [abs_neg, abs_of_pos hR]), sub_self]

theorem T012 (n : ℕ) (m : ℕ) (u : WSpace n × ℝ → WTarget m) (q : WTarget m) (h_T005 : ∀ t : ℝ, 0 < t → Integrable (fun x : WSpace n => wDensity u (x,t)) ∧ ∃ (C : Set (WSpace n)) (R B : ℝ), wLocal u q t C R B) (h_T009 : ∀ t : ℝ, 0 < t → ∀ j : Fin n, ContDiff ℝ ∞ (fun x : WSpace n => wG u j (x,t)) ∧ HasCompactSupport (fun x : WSpace n => wG u j (x,t)) ∧ ∀ x : WSpace n, wX (wG u j) j (x,t) = wB u j (x,t) + wC u j (x,t)) (h_T011 : ∀ (f : WSpace n → ℝ), ContDiff ℝ ∞ f → HasCompactSupport f → ∀ j : Fin n, Integrable (fun x : WSpace n => wDx f j x) ∧ (∫ x : WSpace n, wDx f j x) = 0) :
    ∀ t : ℝ, 0 < t → ∀ j : Fin n, Integrable (fun x : WSpace n => wB u j (x,t)) ∧ Integrable (fun x : WSpace n => wC u j (x,t)) ∧ (∫ x : WSpace n, wB u j (x,t)) = -(∫ x : WSpace n, wC u j (x,t)) := by
  intro t ht j
  obtain ⟨_, C, R, B, hloc⟩ := h_T005 t ht
  have htime : t ∈ Set.Ioo (t / 2) (3 * t / 2) := by
    constructor <;> linarith
  have hBmem : (fun x => wB u j (x,t)) ∈ wTerms u t := by
    exact Or.inr (Or.inr (Or.inr ⟨j, Or.inl rfl⟩))
  have hCmem : (fun x => wC u j (x,t)) ∈ wTerms u t := by
    exact Or.inr (Or.inr (Or.inr ⟨j, Or.inr (Or.inl rfl)⟩))
  have hB : Integrable (fun x : WSpace n => wB u j (x,t)) :=
    (hloc.2.2.1 t htime _ hBmem).2.2
  have hC : Integrable (fun x : WSpace n => wC u j (x,t)) :=
    (hloc.2.2.1 t htime _ hCmem).2.2
  obtain ⟨hsmooth, hsupp, hprod⟩ := h_T009 t ht j
  have hz := (h_T011 (fun x => wG u j (x,t)) hsmooth hsupp j).2
  have hfun : (fun x => wDx (fun y => wG u j (y,t)) j x) =
      (fun x => wB u j (x,t) + wC u j (x,t)) := by
    funext x
    exact hprod x
  rw [hfun, MeasureTheory.integral_add hB hC] at hz
  exact ⟨hB, hC, by linarith⟩

theorem T013 (n : ℕ) (m : ℕ) (u : WSpace n × ℝ → WTarget m) (q : WTarget m) (h_H002 : ContDiffOn ℝ ∞ u (wDomain n)) (h_T005 : ∀ t : ℝ, 0 < t → Integrable (fun x : WSpace n => wDensity u (x,t)) ∧ ∃ (C : Set (WSpace n)) (R B : ℝ), wLocal u q t C R B) (h_T008 : ∀ t : ℝ, 0 < t → DifferentiableAt ℝ (wEnergy u) t ∧ deriv (wEnergy u) t = ∫ x : WSpace n, wT (wDensity u) (x,t) ∧ HasDerivAt (wEnergy u) (∫ x : WSpace n, 2 * wA u (x,t) + 2 * ∑ j : Fin n, wB u j (x,t)) t ∧ Integrable (fun x : WSpace n => wT (wDensity u) (x,t)) ∧ Integrable (fun x : WSpace n => wA u (x,t)) ∧ ∀ j : Fin n, Integrable (fun x : WSpace n => wB u j (x,t))) (h_T012 : ∀ t : ℝ, 0 < t → ∀ j : Fin n, Integrable (fun x : WSpace n => wB u j (x,t)) ∧ Integrable (fun x : WSpace n => wC u j (x,t)) ∧ (∫ x : WSpace n, wB u j (x,t)) = -(∫ x : WSpace n, wC u j (x,t))) :
    ∀ t : ℝ, 0 < t → HasDerivAt (wEnergy u) (2 * ∫ x : WSpace n, inner ℝ (wT u (x,t)) (wT (wT u) (x,t) - wLap u (x,t))) t := by
  intro t ht
  rcases h_T008 t ht with ⟨_, _, hd, _, hA, hB⟩
  have hC : ∀ j : Fin n, Integrable (fun x : WSpace n => wC u j (x,t)) :=
    fun j => (h_T012 t ht j).2.1
  have hSB : Integrable (fun x : WSpace n => ∑ j : Fin n, wB u j (x,t)) :=
    integrable_finsetSum Finset.univ (fun j _ => hB j)
  have hSC : Integrable (fun x : WSpace n => ∑ j : Fin n, wC u j (x,t)) :=
    integrable_finsetSum Finset.univ (fun j _ => hC j)
  have hp (x : WSpace n) : inner ℝ (wT u (x,t)) (wT (wT u) (x,t) - wLap u (x,t)) =
      wA u (x,t) - ∑ j : Fin n, wC u j (x,t) := by
    simp only [inner_sub_right, wLap, inner_sum, wA, wC]
  have heq : (∫ x : WSpace n, 2 * wA u (x,t) + 2 * ∑ j : Fin n, wB u j (x,t)) =
      2 * ∫ x : WSpace n, inner ℝ (wT u (x,t)) (wT (wT u) (x,t) - wLap u (x,t)) := by
    simp_rw [hp]
    rw [integral_add (hA.const_mul 2) (hSB.const_mul 2), integral_const_mul,
      integral_const_mul, integral_sub hA hSC,
      integral_finsetSum Finset.univ (fun j _ => hB j),
      integral_finsetSum Finset.univ (fun j _ => hC j)]
    simp_rw [(h_T012 t ht _).2.2]
    rw [Finset.sum_neg_distrib]
    ring
  rw [← heq]
  exact hd

theorem T014 (n : ℕ) (m : ℕ) (u : WSpace n × ℝ → WTarget m) (q : WTarget m) (h_T003 : ContDiffOn ℝ ∞ (wDensity u) (wDomain n) ∧ ContinuousOn (wT (wDensity u)) (wDomain n) ∧ ∀ (x : WSpace n) (t : ℝ), 0 < t → inner ℝ (u (x,t)) (wT u (x,t)) = 0 ∧ inner ℝ (wT u (x,t)) (wT (wT u) (x,t) - wLap u (x,t)) = 0 ∧ (∀ a : ℝ, wT (wT u) (x,t) - wLap u (x,t) = a • u (x,t) → a = (∑ j : Fin n, ‖wX u j (x,t)‖^2) - ‖wT u (x,t)‖^2) ∧ (∀ j : Fin n, wT (wX u j) (x,t) = wX (wT u) j (x,t)) ∧ wT (wDensity u) (x,t) = 2 * wA u (x,t) + 2 * ∑ j : Fin n, wB u j (x,t)) (h_T005 : ∀ t : ℝ, 0 < t → Integrable (fun x : WSpace n => wDensity u (x,t)) ∧ ∃ (C : Set (WSpace n)) (R B : ℝ), wLocal u q t C R B) (h_T013 : ∀ t : ℝ, 0 < t → HasDerivAt (wEnergy u) (2 * ∫ x : WSpace n, inner ℝ (wT u (x,t)) (wT (wT u) (x,t) - wLap u (x,t))) t) :
    ∀ t : ℝ, 0 < t → Integrable (fun x : WSpace n => wDensity u (x,t)) ∧ HasDerivAt (wEnergy u) 0 t := by
  intro t ht
  refine ⟨(h_T005 t ht).1, ?_⟩
  have hz : (fun x : WSpace n => inner ℝ (wT u (x,t)) (wT (wT u) (x,t) - wLap u (x,t))) = fun _ => (0 : ℝ) := by
    funext x
    exact (h_T003.2.2 x t ht).2.1
  have hd := h_T013 t ht
  rw [hz] at hd
  simpa using hd

theorem T015 (n : ℕ) (m : ℕ) (u : WSpace n × ℝ → WTarget m) (q : WTarget m) (h_T014 : ∀ t : ℝ, 0 < t → Integrable (fun x : WSpace n => wDensity u (x,t)) ∧ HasDerivAt (wEnergy u) 0 t) :
    (∀ t : ℝ, 0 < t → Integrable (fun x : WSpace n => wDensity u (x,t)) ∧ DifferentiableAt ℝ (wEnergy u) t ∧ deriv (wEnergy u) t = 0) ∧ (∀ a b : ℝ, 0 < a → 0 < b → wEnergy u b = wEnergy u a) := by
  constructor
  · intro t ht
    obtain ⟨hi, hd⟩ := h_T014 t ht
    exact ⟨hi, hd.differentiableAt, hd.deriv⟩
  · intro a b ha hb
    have hpos : ∀ x ∈ Set.Icc (min a b) (max a b), 0 < x := by
      intro x hx
      exact lt_of_lt_of_le (lt_min ha hb) hx.1
    have hd : ∀ x ∈ Set.Icc (min a b) (max a b), DifferentiableAt ℝ (wEnergy u) x := by
      intro x hx
      exact (h_T014 x (hpos x hx)).2.differentiableAt
    have hbound : ∀ x ∈ Set.Icc (min a b) (max a b), ‖deriv (wEnergy u) x‖ ≤ (0 : ℝ) := by
      intro x hx
      rw [(h_T014 x (hpos x hx)).2.deriv]
      simp
    have h := Convex.norm_image_sub_le_of_norm_deriv_le hd hbound (convex_Icc (min a b) (max a b))
      (show a ∈ Set.Icc (min a b) (max a b) from ⟨min_le_left _ _, le_max_left _ _⟩)
      (show b ∈ Set.Icc (min a b) (max a b) from ⟨min_le_right _ _, le_max_right _ _⟩)
    have hz : ‖wEnergy u b - wEnergy u a‖ = 0 := le_antisymm (by simpa using h) (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)

set_option Elab.async false in
theorem P (n : ℕ) (m : ℕ) (u : WSpace n × ℝ → WTarget m) (q : WTarget m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ u (wDomain n)) (h_H003 : ‖q‖ = 1) (h_H004 : ∀ (x : WSpace n) (t : ℝ), 0 < t → ‖u (x,t)‖ = 1) (h_H005 : ∀ (x : WSpace n) (t : ℝ), 0 < t → ∃ a : ℝ, wT (wT u) (x,t) - wLap u (x,t) = a • u (x,t)) (h_H006 : ∀ s t : ℝ, 0 < s → s < t → ∃ C : Set (WSpace n), IsCompact C ∧ ∀ x r, x ∉ C → r ∈ Set.Icc s t → u (x,r) = q) :
    (∀ t : ℝ, 0 < t → Integrable (fun x : WSpace n => wDensity u (x,t)) ∧ DifferentiableAt ℝ (wEnergy u) t ∧ deriv (wEnergy u) t = 0) ∧ (∀ a b : ℝ, 0 < a → 0 < b → wEnergy u b = wEnergy u a) := by
  have h_T001 : ∀ (x : WSpace n) (t : ℝ), 0 < t → inner ℝ (u (x,t)) (wT u (x,t)) = 0 ∧ ∀ j : Fin n, inner ℝ (u (x,t)) (wX u j (x,t)) = 0 := @T001 n m u q h_H002 h_H004
  have h_T002 : ∀ (x : WSpace n) (t : ℝ), 0 < t → inner ℝ (wT u (x,t)) (wT (wT u) (x,t) - wLap u (x,t)) = 0 ∧ (∀ a : ℝ, wT (wT u) (x,t) - wLap u (x,t) = a • u (x,t) → a = (∑ j : Fin n, ‖wX u j (x,t)‖^2) - ‖wT u (x,t)‖^2) := @T002 n m u q h_H002 h_H004 h_H005 h_T001
  have h_T003 : ContDiffOn ℝ ∞ (wDensity u) (wDomain n) ∧ ContinuousOn (wT (wDensity u)) (wDomain n) ∧ ∀ (x : WSpace n) (t : ℝ), 0 < t → inner ℝ (u (x,t)) (wT u (x,t)) = 0 ∧ inner ℝ (wT u (x,t)) (wT (wT u) (x,t) - wLap u (x,t)) = 0 ∧ (∀ a : ℝ, wT (wT u) (x,t) - wLap u (x,t) = a • u (x,t) → a = (∑ j : Fin n, ‖wX u j (x,t)‖^2) - ‖wT u (x,t)‖^2) ∧ (∀ j : Fin n, wT (wX u j) (x,t) = wX (wT u) j (x,t)) ∧ wT (wDensity u) (x,t) = 2 * wA u (x,t) + 2 * ∑ j : Fin n, wB u j (x,t) := @T003 n m u q h_H002 h_T001 h_T002
  have h_T004 : ∀ t : ℝ, 0 < t → ∃ (C : Set (WSpace n)) (R : ℝ), wGeometry u q t C R := @T004 n m u q h_H001 h_H002 h_H006
  have h_T005 : ∀ t : ℝ, 0 < t → Integrable (fun x : WSpace n => wDensity u (x,t)) ∧ ∃ (C : Set (WSpace n)) (R B : ℝ), wLocal u q t C R B := @T005 n m u q h_H002 h_T004
  have h_T006 : ∀ t : ℝ, 0 < t → ∀ (C : Set (WSpace n)) (R B : ℝ), wLocal u q t C R B → Integrable ((wBox n R).indicator (fun _ => B)) ∧ ∀ h : ℝ, 0 < |h| → |h| < t/4 → ∀ x : WSpace n, |(wDensity u (x,t+h) - wDensity u (x,t))/h| ≤ (wBox n R).indicator (fun _ => B) x := @T006 n m u q h_H002 h_T003 h_T005
  have h_T007 : ∀ t : ℝ, 0 < t → Filter.Tendsto (fun h : ℝ => ∫ x : WSpace n, (wDensity u (x,t+h) - wDensity u (x,t))/h) (nhdsWithin 0 ({0}ᶜ)) (nhds (∫ x : WSpace n, wT (wDensity u) (x,t))) := @T007 n m u q h_H002 h_T003 h_T005 h_T006
  have h_T008 : ∀ t : ℝ, 0 < t → DifferentiableAt ℝ (wEnergy u) t ∧ deriv (wEnergy u) t = ∫ x : WSpace n, wT (wDensity u) (x,t) ∧ HasDerivAt (wEnergy u) (∫ x : WSpace n, 2 * wA u (x,t) + 2 * ∑ j : Fin n, wB u j (x,t)) t ∧ Integrable (fun x : WSpace n => wT (wDensity u) (x,t)) ∧ Integrable (fun x : WSpace n => wA u (x,t)) ∧ ∀ j : Fin n, Integrable (fun x : WSpace n => wB u j (x,t)) := @T008 n m u q h_H002 h_T003 h_T005 h_T007
  have h_T009 : ∀ t : ℝ, 0 < t → ∀ j : Fin n, ContDiff ℝ ∞ (fun x : WSpace n => wG u j (x,t)) ∧ HasCompactSupport (fun x : WSpace n => wG u j (x,t)) ∧ ∀ x : WSpace n, wX (wG u j) j (x,t) = wB u j (x,t) + wC u j (x,t) := @T009 n m u q h_H002 h_T005
  have h_T010 : ∀ (d : ℕ) (j : Fin (d+1)) (R : ℝ), MeasureTheory.MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => ℝ) j) (volume.restrict (wBox (d+1) R)) ((volume.restrict (Set.Icc (-R) R)).prod (volume.restrict (wBox d R))) := @T010 n m u q 
  have h_T011 : ∀ (f : WSpace n → ℝ), ContDiff ℝ ∞ f → HasCompactSupport f → ∀ j : Fin n, Integrable (fun x : WSpace n => wDx f j x) ∧ (∫ x : WSpace n, wDx f j x) = 0 := @T011 n m u q h_T010
  have h_T012 : ∀ t : ℝ, 0 < t → ∀ j : Fin n, Integrable (fun x : WSpace n => wB u j (x,t)) ∧ Integrable (fun x : WSpace n => wC u j (x,t)) ∧ (∫ x : WSpace n, wB u j (x,t)) = -(∫ x : WSpace n, wC u j (x,t)) := @T012 n m u q h_T005 h_T009 h_T011
  have h_T013 : ∀ t : ℝ, 0 < t → HasDerivAt (wEnergy u) (2 * ∫ x : WSpace n, inner ℝ (wT u (x,t)) (wT (wT u) (x,t) - wLap u (x,t))) t := @T013 n m u q h_H002 h_T005 h_T008 h_T012
  have h_T014 : ∀ t : ℝ, 0 < t → Integrable (fun x : WSpace n => wDensity u (x,t)) ∧ HasDerivAt (wEnergy u) 0 t := @T014 n m u q h_T003 h_T005 h_T013
  have h_T015 : (∀ t : ℝ, 0 < t → Integrable (fun x : WSpace n => wDensity u (x,t)) ∧ DifferentiableAt ℝ (wEnergy u) t ∧ deriv (wEnergy u) t = 0) ∧ (∀ a b : ℝ, 0 < a → 0 < b → wEnergy u b = wEnergy u a) := @T015 n m u q h_T014
  exact h_T015

#check @P
#print axioms P

end Translation

namespace AuditBExport
set_option autoImplicit false
set_option Elab.async false in
theorem P (n : ℕ) (m : ℕ) (u : WSpace n × ℝ → WTarget m) (q : WTarget m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ u (wDomain n)) (h_H003 : ‖q‖ = 1) (h_H004 : ∀ (x : WSpace n) (t : ℝ), 0 < t → ‖u (x,t)‖ = 1) (h_H005 : ∀ (x : WSpace n) (t : ℝ), 0 < t → ∃ a : ℝ, wT (wT u) (x,t) - wLap u (x,t) = a • u (x,t)) (h_H006 : ∀ s t : ℝ, 0 < s → s < t → ∃ C : Set (WSpace n), IsCompact C ∧ ∀ x r, x ∉ C → r ∈ Set.Icc s t → u (x,r) = q) : (∀ t : ℝ, 0 < t → Integrable (fun x : WSpace n => wDensity u (x,t)) ∧ DifferentiableAt ℝ (wEnergy u) t ∧ deriv (wEnergy u) t = 0) ∧ (∀ a b : ℝ, 0 < a → 0 < b → wEnergy u b = wEnergy u a) := by
  exact @Translation.P n m u q h_H001 h_H002 h_H003 h_H004 h_H005 h_H006

#check @P
#print axioms P
end AuditBExport

/- Trusted inspector appended after the generated proof, never a worker tool.
   Its only substitution is an array of escaped (id, selector, expected type) strings. -/
namespace NL2LeanAuditProbe
open Lean Meta Elab Command Term

private def nameOf (parts : Array String) : Name :=
  parts.foldl Name.str .anonymous

private def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quotient"

private def binderKind : BinderInfo → String
  | .default => "explicit"
  | .implicit => "implicit"
  | .strictImplicit => "strict_implicit"
  | .instImplicit => "instance"

private def showType (e : Expr) : MetaM String := do
  return (← ppExpr e).pretty

private def binderInventory (type : Expr) : MetaM Json :=
  forallTelescope type fun xs body => do
    let mut rows : Array Json := #[]
    for x in xs do
      let d ← getFVarLocalDecl x
      rows := rows.push <| Json.mkObj [
        ("name", toJson d.userName.toString), ("kind", toJson (binderKind d.binderInfo)),
        ("type", toJson (← showType d.type)), ("proof_valued", toJson (← isProp d.type))]
    return Json.mkObj [("binders", toJson rows), ("result", toJson (← showType body))]

private def mergeUses (a b : NameSet × NameSet) : NameSet × NameSet := Id.run do
  let mut result := a
  for name in b.1.toArray do result := (result.1.insert name, result.2)
  for name in b.2.toArray do result := (result.1, result.2.insert name)
  return result

/- Distinguish actual proof use from canonical typeclass evidence inserted as
   an instance argument. Never infer this distinction from a name prefix. -/
private partial def proofUses (e : Expr) (insideInstance := false) : MetaM (NameSet × NameSet) := do
  match e with
  | .const name _ =>
    let info ← getConstInfo name
    if ← isProp info.type then
      if insideInstance then return ({}, ({} : NameSet).insert name)
      else return (({} : NameSet).insert name, {})
    return ({}, {})
  | .app .. =>
    let fn := e.getAppFn
    let mut result ← proofUses fn insideInstance
    let mut type ← inferType fn
    for arg in e.getAppArgs do
      if !type.isForall then type ← whnf type
      match type with
      | .forallE _ _ body bi =>
        result := mergeUses result (← proofUses arg (insideInstance || bi == .instImplicit))
        type := body.instantiate1 arg
      | _ => throwError "Application has no function binder in dependency inspection"
    return result
  | .lam name type body bi | .forallE name type body bi =>
    let before ← proofUses type insideInstance
    let after ← withLocalDecl name bi type fun x => proofUses (body.instantiate1 x) insideInstance
    return mergeUses before after
  | .letE name type value body _ =>
    let before := mergeUses (← proofUses type insideInstance) (← proofUses value insideInstance)
    let after ← withLetDecl name type value fun x => proofUses (body.instantiate1 x) insideInstance
    return mergeUses before after
  | .mdata _ value | .proj _ _ value => proofUses value insideInstance
  | _ => return ({}, {})

private def record (name : Name) : MetaM Json := do
  let info ← getConstInfo name
  let env ← getEnv
  let imported := env.isImportedConst name
  let uses ← if imported then pure (({} : NameSet), ({} : NameSet))
    else match info.value? (allowOpaque := true) with
      | some value => proofUses value
      | none => pure (({} : NameSet), ({} : NameSet))
  let moduleName := match env.getModuleIdxFor? name with
    | some idx => (env.header.moduleNames[idx.toNat]!).toString
    | none => env.mainModule.toString
  return Json.mkObj [
    ("name", toJson name.toString), ("kind", toJson (kindOf info)),
    ("imported", toJson imported), ("module", toJson moduleName),
    ("proof_valued", toJson (← isProp info.type)),
    ("instance_declaration", toJson (isInstanceCore env name)),
    ("proof_uses", Json.mkObj [
      ("ordinary", toJson (uses.1.toArray.map Name.toString)),
      ("instance_argument", toJson (uses.2.toArray.map Name.toString))]),
    ("type", toJson (← showType info.type)),
    ("signature", ← binderInventory info.type),
    ("levels", toJson (info.levelParams.map Name.toString)),
    ("direct_constants", toJson ((info.getUsedConstantsAsSet.toArray.qsort Name.lt).map Name.toString)),
    ("axioms", toJson ((← collectAxioms name).map Name.toString))]

private def inspect (roots : Array Name) : MetaM Json := do
  let mut pending := roots
  let mut seen : NameSet := {}
  let mut rows : Array Json := #[]
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let info ← getConstInfo name
    rows := rows.push (← record name)
    if !(← getEnv).isImportedConst name then
      pending := pending ++ info.getUsedConstantsAsSet.toArray
      if let .inductInfo value := info then
        pending := pending ++ value.ctors.toArray
  return Json.mkObj [("declarations", toJson rows), ("truncated", toJson (!pending.isEmpty))]

private def actualType (selector : String) (parts : Array String) : TermElabM Expr := do
  if selector.startsWith "decl:" then
    return (← getConstInfo (nameOf parts)).type
  if selector.startsWith "premise:" then
    let wanted := "h_" ++ (selector.drop 8).toString
    let root ← getConstInfo `AuditBExport.P
    return ← forallTelescope root.type fun xs _ => do
      let mut context : Array Expr := #[]
      for x in xs do
        let binder ← getFVarLocalDecl x
        if binder.userName.toString == wanted then
          return ← mkForallFVars context binder.type
        context := context.push x
      throwError "Missing actual root premise {wanted}"
  throwError "Unsupported selector {selector}"

/- Universe parameter names belong to each declaration's binder scope.
   Rename them bijectively, retaining repetitions and all level expressions.
   This is alpha-equivalence, not a proof of logical equivalence. -/
private def sameSignature (actual expected : Expr) : MetaM (Bool × String) := do
  if ← withoutModifyingState <| isDefEq actual expected then
    return (true, "definitional")
  let actualParams := (collectLevelParams {} actual).params.toList
  let expectedParams := (collectLevelParams {} expected).params.toList
  if actualParams.length != expectedParams.length then
    return (false, "different_universe_binders")
  let levels := (List.range actualParams.length).map fun i =>
    Level.param (Name.mkSimple ("_yuiAuditLevel" ++ toString i))
  let equal ← withoutModifyingState <| isDefEq
    (actual.instantiateLevelParams actualParams levels)
    (expected.instantiateLevelParams expectedParams levels)
  return (equal, "bijective_universe_renaming")

elab "#nl2lean_audit_probe" : command => do
  let result ← liftTermElabM <| withOptions
      (fun o => (o.setBool `pp.all true).setBool `pp.universes true) do
    let checks : Array (String × String × String × Array String) := #[("P", "decl:AuditBExport.P", "∀ (n : ℕ) (m : ℕ) (u : WSpace n × ℝ → WTarget m) (q : WTarget m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ u (wDomain n)) (h_H003 : ‖q‖ = 1) (h_H004 : ∀ (x : WSpace n) (t : ℝ), 0 < t → ‖u (x,t)‖ = 1) (h_H005 : ∀ (x : WSpace n) (t : ℝ), 0 < t → ∃ a : ℝ, wT (wT u) (x,t) - wLap u (x,t) = a • u (x,t)) (h_H006 : ∀ s t : ℝ, 0 < s → s < t → ∃ C : Set (WSpace n), IsCompact C ∧ ∀ x r, x ∉ C → r ∈ Set.Icc s t → u (x,r) = q), (∀ t : ℝ, 0 < t → Integrable (fun x : WSpace n => wDensity u (x,t)) ∧ DifferentiableAt ℝ (wEnergy u) t ∧ deriv (wEnergy u) t = 0) ∧ (∀ a b : ℝ, 0 < a → 0 < b → wEnergy u b = wEnergy u a)", #["AuditBExport", "P"])]
    let mut comparisons : Array Json := #[]
    let mut roots : Array Name := #[`AuditBExport.P]
    for (id, selector, expectedText, parts) in checks do
      let stx ← ofExcept <| Parser.runParserCategory (← getEnv) `term expectedText
      let expected ← Term.elabTerm stx none
      Term.synthesizeSyntheticMVarsNoPostponing
      let expected ← instantiateMVars expected
      let actual ← actualType selector parts
      let (equal, method) ← sameSignature actual expected
      comparisons := comparisons.push <| Json.mkObj [
        ("id", toJson id), ("selector", toJson selector),
        ("expected_type", toJson (← showType expected)),
        ("actual_type", toJson (← showType actual)), ("definitionally_equal", toJson equal),
        ("comparison_method", toJson method)]
      if selector.startsWith "decl:" then
        roots := roots.push (nameOf parts)
    let dependencies ← inspect roots
    return Json.mkObj [("comparisons", toJson comparisons), ("dependencies", dependencies)]
  logInfo m!"NL2LEAN_AUDIT_JSON:{result.compress}"

set_option maxHeartbeats 0 in
#nl2lean_audit_probe
end NL2LeanAuditProbe
