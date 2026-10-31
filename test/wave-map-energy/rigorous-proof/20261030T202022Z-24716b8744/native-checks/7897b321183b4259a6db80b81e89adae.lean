import Mathlib
open scoped ContDiff Topology BigOperators
open Set MeasureTheory
noncomputable section
namespace WaveMap
abbrev V (n : ℕ) := Fin n → ℝ
abbrev W (m : ℕ) := EuclideanSpace ℝ (Fin m)
def domain (n : ℕ) : Set (V n × ℝ) := {p | 0 < p.2}
def box (n : ℕ) (R : ℝ) : Set (V n) := Set.Icc (fun _ => -R) (fun _ => R)
def innerBox (n : ℕ) (R : ℝ) : Set (V n) := {x | ∀ j, -R < x j ∧ x j < R}
def ut {n m : ℕ} (u : V n × ℝ → W m) (x : V n) (t : ℝ) : W m :=
  deriv (fun s => u (x,s)) t
def utt {n m : ℕ} (u : V n × ℝ → W m) (x : V n) (t : ℝ) : W m :=
  deriv (fun s => ut u x s) t
def ux {n m : ℕ} (u : V n × ℝ → W m) (j : Fin n) (x : V n) (t : ℝ) : W m :=
  fderiv ℝ (fun y => u (y,t)) x (Pi.single j 1)
def uxx {n m : ℕ} (u : V n × ℝ → W m) (j : Fin n) (x : V n) (t : ℝ) : W m :=
  fderiv ℝ (fun y => ux u j y t) x (Pi.single j 1)
def uxt {n m : ℕ} (u : V n × ℝ → W m) (j : Fin n) (x : V n) (t : ℝ) : W m :=
  fderiv ℝ (fun y => ut u y t) x (Pi.single j 1)
def lap {n m : ℕ} (u : V n × ℝ → W m) (x : V n) (t : ℝ) : W m :=
  ∑ j, uxx u j x t
def e {n m : ℕ} (u : V n × ℝ → W m) (x : V n) (t : ℝ) : ℝ :=
  ‖ut u x t‖ ^ 2 + ∑ j, ‖ux u j x t‖ ^ 2
def et {n m : ℕ} (u : V n × ℝ → W m) (x : V n) (t : ℝ) : ℝ :=
  deriv (fun s => e u x s) t
def A {n m : ℕ} (u : V n × ℝ → W m) (x : V n) (t : ℝ) : ℝ :=
  inner ℝ (ut u x t) (utt u x t)
def B {n m : ℕ} (u : V n × ℝ → W m) (j : Fin n) (x : V n) (t : ℝ) : ℝ :=
  inner ℝ (ux u j x t) (uxt u j x t)
def T {n m : ℕ} (u : V n × ℝ → W m) (j : Fin n) (x : V n) (t : ℝ) : ℝ :=
  inner ℝ (ut u x t) (uxx u j x t)
def g {n m : ℕ} (u : V n × ℝ → W m) (j : Fin n) (x : V n) (t : ℝ) : ℝ :=
  inner ℝ (ut u x t) (ux u j x t)
def dg {n m : ℕ} (u : V n × ℝ → W m) (j : Fin n) (x : V n) (t : ℝ) : ℝ :=
  fderiv ℝ (fun y => g u j y t) x (Pi.single j 1)
def energy {n m : ℕ} (u : V n × ℝ → W m) (t : ℝ) : ℝ :=
  ∫ x, e u x t
def fields {n m : ℕ} (u : V n × ℝ → W m) : Set ((V n × ℝ) → ℝ) :=
  {f | f = (fun p => e u p.1 p.2) ∨ f = (fun p => et u p.1 p.2) ∨
    f = (fun p => A u p.1 p.2) ∨
    (∃ j, f = (fun p => B u j p.1 p.2)) ∨
    (∃ j, f = (fun p => T u j p.1 p.2)) ∨
    (∃ j, f = (fun p => g u j p.1 p.2)) ∨
    (∃ j, f = (fun p => dg u j p.1 p.2))}
end WaveMap
open WaveMap

namespace Translation
set_option autoImplicit false

theorem T002 (n : ℕ) (m : ℕ) (u : V n × ℝ → W m) (q : W m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ u (domain n)) (h_H006 : ∀ s t : ℝ, 0 < s → s < t → ∃ C : Set (V n), IsCompact C ∧ ∀ x, x ∉ C → ∀ r ∈ Set.Icc s t, u (x,r) = q) :
    ∀ t0 : ℝ, 0 < t0 → ∃ C : Set (V n), ∃ R : ℝ,
IsCompact C ∧ 0 < R ∧ C ⊆ innerBox n R ∧ C ⊆ interior (box n R) ∧
IsCompact (box n R) ∧ MeasurableSet (box n R) ∧
volume (box n R) = ENNReal.ofReal ((2*R)^n) ∧ volume (box n R) < ⊤ ∧
(∀ x, x ∉ C → ∀ r ∈ Set.Icc (t0/2) (3*t0/2), u (x,r) = q) ∧
(∀ k : ℕ, 0 < k → ∀ x, x ∉ C → ∀ r ∈ Set.Ioo (t0/2) (3*t0/2),
iteratedFDeriv ℝ k u (x,r) = 0) := by
  intro t0 ht0
  have ha : 0 < t0 / 2 := by linarith
  have hab : t0 / 2 < 3 * t0 / 2 := by linarith
  obtain ⟨C, hC, hu⟩ := h_H006 (t0 / 2) (3 * t0 / 2) ha hab
  obtain ⟨L, hL⟩ := hC.exists_bound_of_continuousOn
    (continuous_id.continuousOn : ContinuousOn (fun x : V n => x) C)
  let R : ℝ := max L 0 + 1
  have hR : 0 < R := by
    dsimp [R]
    have := le_max_right L 0
    linarith
  have hsub : C ⊆ innerBox n R := by
    intro x hx j
    have hcoord : ‖x j‖ ≤ ‖x‖ := norm_le_pi_norm x j
    have hLR : L < R := by
      dsimp [R]
      have := le_max_left L 0
      linarith
    have habs : |x j| < R := by
      simpa only [Real.norm_eq_abs] using
        hcoord.trans_lt ((hL x hx).trans_lt hLR)
    exact abs_lt.mp habs
  have hint : interior (box n R) = innerBox n R := by
    change interior (Set.Icc (fun _ : Fin n => -R) (fun _ => R)) = _
    rw [← Set.pi_univ_Icc, interior_pi_set Set.finite_univ]
    ext x
    simp [innerBox, interior_Icc]
  have hbox : IsCompact (box n R) := isCompact_Icc
  have hvol : volume (box n R) = ENNReal.ofReal ((2 * R)^n) := by
    have hconv : ENNReal.ofReal ((2 * R)^n) = (ENNReal.ofReal (2 * R))^n :=
      ENNReal.ofReal_pow (mul_nonneg (by norm_num) hR.le) n
    change volume (Set.Icc (fun _ : Fin n => -R) (fun _ => R)) = _
    rw [Real.volume_Icc_pi, hconv]
    simp [sub_neg_eq_add, ← two_mul]
  refine ⟨C, R, hC, hR, hsub, ?_, hbox, hbox.isClosed.measurableSet, hvol, ?_, hu, ?_⟩
  · rw [hint]
    exact hsub
  · rw [hvol]
    exact ENNReal.ofReal_lt_top
  · intro k hk x hx r hr
    have hopen : IsOpen (Cᶜ ×ˢ Set.Ioo (t0 / 2) (3 * t0 / 2)) :=
      hC.isClosed.isOpen_compl.prod isOpen_Ioo
    have hmem : (x,r) ∈ Cᶜ ×ˢ Set.Ioo (t0 / 2) (3 * t0 / 2) := ⟨hx, hr⟩
    have heq : u =ᶠ[𝓝 (x,r)] (fun _ : V n × ℝ => q) := by
      filter_upwards [hopen.mem_nhds hmem] with p hp
      exact hu p.1 hp.1 p.2 ⟨hp.2.1.le, hp.2.2.le⟩
    have hd := (heq.iteratedFDeriv ℝ k).eq_of_nhds
    rw [hd, iteratedFDeriv_const_of_ne (Nat.ne_of_gt hk) q]
    rfl

theorem T003 (n : ℕ) (m : ℕ) (u : V n × ℝ → W m) (q : W m) (h_T002 : ∀ t0 : ℝ, 0 < t0 → ∃ C : Set (V n), ∃ R : ℝ,
IsCompact C ∧ 0 < R ∧ C ⊆ innerBox n R ∧ C ⊆ interior (box n R) ∧
IsCompact (box n R) ∧ MeasurableSet (box n R) ∧
volume (box n R) = ENNReal.ofReal ((2*R)^n) ∧ volume (box n R) < ⊤ ∧
(∀ x, x ∉ C → ∀ r ∈ Set.Icc (t0/2) (3*t0/2), u (x,r) = q) ∧
(∀ k : ℕ, 0 < k → ∀ x, x ∉ C → ∀ r ∈ Set.Ioo (t0/2) (3*t0/2),
iteratedFDeriv ℝ k u (x,r) = 0)) (h_H002 : ContDiffOn ℝ ∞ u (domain n)) :
    (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (V n), ∃ R : ℝ,
IsCompact C ∧ 0 < R ∧ C ⊆ innerBox n R ∧ C ⊆ interior (box n R) ∧
IsCompact (box n R) ∧ MeasurableSet (box n R) ∧
volume (box n R) = ENNReal.ofReal ((2*R)^n) ∧ volume (box n R) < ⊤ ∧
(∀ x, x ∉ C → ∀ r ∈ Set.Icc (t0/2) (3*t0/2), u (x,r) = q) ∧
(∀ k : ℕ, 0 < k → ∀ x, x ∉ C → ∀ r ∈ Set.Ioo (t0/2) (3*t0/2),
iteratedFDeriv ℝ k u (x,r) = 0 ) ∧ (∀ f ∈ fields u, ∀ r ∈ Set.Ioo (t0/2) (3*t0/2),
Continuous (fun x => f (x,r)) ∧
(∀ x, x ∉ C → f (x,r) = 0) ∧
HasCompactSupport (fun x => f (x,r)) ∧ Integrable (fun x => f (x,r)) ∧
(∃ K : ℝ, 0 ≤ K ∧ (∀ x ∈ box n R, |f (x,r)| ≤ K) ∧
(∫ x, |f (x,r)|) ≤ K * (volume (box n R)).toReal) ∧
(∃ U : Set (V n), IsOpen U ∧ frontier (box n R) ⊆ U ∧ ∀ x ∈ U, f (x,r) = 0))) ∧ (∀ r : ℝ, 0 < r → Integrable (fun x => e u x r)) := by
  classical
  have hsmooth : ∀ f ∈ fields u, ContDiffOn ℝ ∞ f (domain n) := by
    have partSmooth : ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (v : V n × ℝ → F), ContDiffOn ℝ ∞ v (domain n) → ContDiffOn ℝ ∞ (fun p : V n × ℝ => deriv (fun s => v (p.1,s)) p.2) (domain n) ∧ ∀ j : Fin n, ContDiffOn ℝ ∞ (fun p : V n × ℝ => fderiv ℝ (fun y => v (y,p.2)) p.1 (Pi.single j 1)) (domain n) := by
      intro F _ _ v hv
      have ho : IsOpen (domain n) := isOpen_lt continuous_const continuous_snd
      have hd : ContDiffOn ℝ ∞ (fderiv ℝ v) (domain n) :=
        (contDiffOn_infty_iff_fderiv_of_isOpen ho).mp hv |>.2
      have hvd (p : V n × ℝ) (hp : p ∈ domain n) : DifferentiableAt ℝ v p :=
        (hv.differentiableOn (by simp) p hp).differentiableAt (ho.mem_nhds hp)
      constructor
      · have hh := hd.clm_apply (contDiffOn_const (c := ((0 : V n), (1 : ℝ))))
        apply hh.congr
        intro p hp
        have h := (hvd p hp).hasFDerivAt.comp p.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) p.1 p.2)
        simpa [Function.comp_def] using h.hasDerivAt.deriv
      · intro j
        have hh := hd.clm_apply (contDiffOn_const (c := ((Pi.single j 1 : V n), (0 : ℝ))))
        apply hh.congr
        intro p hp
        have h := (hvd p hp).hasFDerivAt.comp p.1 (hasFDerivAt_prodMk_left (𝕜 := ℝ) p.1 p.2)
        have he := congrArg (fun L : V n →L[ℝ] F => L (Pi.single j 1)) h.fderiv
        simpa [Function.comp_def] using he
    have ht : ContDiffOn ℝ ∞ (fun p : V n × ℝ => ut u p.1 p.2) (domain n) :=
      (partSmooth (W m) u h_H002).1
    have hx (j : Fin n) : ContDiffOn ℝ ∞ (fun p : V n × ℝ => ux u j p.1 p.2) (domain n) :=
      (partSmooth (W m) u h_H002).2 j
    have htt : ContDiffOn ℝ ∞ (fun p : V n × ℝ => utt u p.1 p.2) (domain n) :=
      (partSmooth (W m) _ ht).1
    have hxx (j : Fin n) : ContDiffOn ℝ ∞ (fun p : V n × ℝ => uxx u j p.1 p.2) (domain n) :=
      (partSmooth (W m) _ (hx j)).2 j
    have hxt (j : Fin n) : ContDiffOn ℝ ∞ (fun p : V n × ℝ => uxt u j p.1 p.2) (domain n) :=
      (partSmooth (W m) _ ht).2 j
    have he : ContDiffOn ℝ ∞ (fun p : V n × ℝ => e u p.1 p.2) (domain n) :=
      (ht.norm_sq ℝ).add (ContDiffOn.sum (fun j _ => (hx j).norm_sq ℝ))
    have hg (j : Fin n) : ContDiffOn ℝ ∞ (fun p : V n × ℝ => g u j p.1 p.2) (domain n) :=
      ht.inner ℝ (hx j)
    intro f hf
    rcases hf with hf | hf | hf | ⟨j,hf⟩ | ⟨j,hf⟩ | ⟨j,hf⟩ | ⟨j,hf⟩
    · subst f; exact he
    · subst f; exact (partSmooth ℝ _ he).1
    · subst f; exact ht.inner ℝ htt
    · subst f; exact (hx j).inner ℝ (hxt j)
    · subst f; exact ht.inner ℝ (hxx j)
    · subst f; exact hg j
    · subst f; exact (partSmooth ℝ _ (hg j)).2 j
  have hzero : ∀ (C : Set (V n)) (a b : ℝ), IsClosed C → (∀ x, x ∉ C → ∀ r ∈ Set.Icc a b, u (x,r) = q) → ∀ f ∈ fields u, ∀ r ∈ Set.Ioo a b, ∀ x, x ∉ C → f (x,r) = 0 := by
    intro C a b hC hu
    have hut (x : V n) (hx : x ∉ C) (r : ℝ) (hr : r ∈ Ioo a b) : ut u x r = 0 := by
      have he : (fun s => u (x,s)) =ᶠ[𝓝 r] (fun _ => q) :=
        Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hr) (fun s hs => hu x hx s ⟨hs.1.le, hs.2.le⟩)
      simpa [ut] using he.deriv_eq
    have hux (j : Fin n) (x : V n) (hx : x ∉ C) (r : ℝ) (hr : r ∈ Ioo a b) : ux u j x r = 0 := by
      have he : (fun y => u (y,r)) =ᶠ[𝓝 x] (fun _ => q) :=
        Filter.eventually_of_mem (hC.isOpen_compl.mem_nhds hx) (fun y hy => hu y hy r ⟨hr.1.le, hr.2.le⟩)
      have hh := congrArg (fun L : V n →L[ℝ] W m => L (Pi.single j 1)) (he.fderiv_eq (𝕜 := ℝ))
      simpa [ux] using hh
    have he (x : V n) (hx : x ∉ C) (r : ℝ) (hr : r ∈ Ioo a b) : e u x r = 0 := by
      simp [e, hut x hx r hr, hux _ x hx r hr]
    have hg (j : Fin n) (x : V n) (hx : x ∉ C) (r : ℝ) (hr : r ∈ Ioo a b) : g u j x r = 0 := by
      simp [g, hut x hx r hr]
    intro f hf r hr x hx
    rcases hf with hf | hf | hf | ⟨j,hf⟩ | ⟨j,hf⟩ | ⟨j,hf⟩ | ⟨j,hf⟩
    · subst f; exact he x hx r hr
    · subst f
      have hh : (fun s => e u x s) =ᶠ[𝓝 r] (fun _ => (0 : ℝ)) :=
        Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hr) (fun s hs => he x hx s hs)
      simpa [et] using hh.deriv_eq
    · subst f; simp [A, hut x hx r hr]
    · subst f; simp [B, hux j x hx r hr]
    · subst f; simp [T, hut x hx r hr]
    · subst f; exact hg j x hx r hr
    · subst f
      have hh : (fun y => g u j y r) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) :=
        Filter.eventually_of_mem (hC.isOpen_compl.mem_nhds hx) (fun y hy => hg j y hy r hr)
      have hh' := congrArg (fun L : V n →L[ℝ] ℝ => L (Pi.single j 1)) (hh.fderiv_eq (𝕜 := ℝ))
      simpa [dg] using hh'
  have hcompact : ∀ (C Q : Set (V n)) (f : V n → ℝ), IsCompact C → C ⊆ interior Q →
  IsCompact Q → volume Q < ⊤ → Continuous f → (∀ x, x ∉ C → f x = 0) →
  HasCompactSupport f ∧ Integrable f ∧
  (∃ K : ℝ, 0 ≤ K ∧ (∀ x ∈ Q, |f x| ≤ K) ∧ (∫ x, |f x|) ≤ K * (volume Q).toReal) ∧
  (∃ U : Set (V n), IsOpen U ∧ frontier Q ⊆ U ∧ ∀ x ∈ U, f x = 0) := by
    intro C Q f hC hCQ hQ hvol hf hz
    have hs : Function.support f ⊆ C := by
      intro x hx
      by_contra h
      exact hx (hz x h)
    have hc : HasCompactSupport f := HasCompactSupport.of_support_subset_isCompact hC hs
    refine ⟨hc, hf.integrable_of_hasCompactSupport hc, ?_, ?_⟩
    · obtain ⟨K, hK⟩ := hQ.exists_bound_of_continuousOn hf.continuousOn
      refine ⟨max K 0, le_max_right _ _, ?_, ?_⟩
      · intro x hx
        exact (show |f x| ≤ K by simpa [Real.norm_eq_abs] using hK x hx).trans (le_max_left _ _)
      · have hzQ : ∀ x, x ∉ Q → |f x| = 0 := by
          intro x hx
          rw [hz x (fun h => hx (interior_subset (hCQ h))), abs_zero]
        have hbound : ∀ x ∈ Q, ‖|f x|‖ ≤ max K 0 := by
          intro x hx
          simpa [Real.norm_eq_abs, abs_abs] using (hK x hx).trans (le_max_left K 0)
        have hb := norm_setIntegral_le_of_norm_le_const (μ := volume) hvol hbound
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzQ] at hb
        have hb' : |(∫ x, |f x|)| ≤ max K 0 * (volume Q).toReal := by
          simpa only [Real.norm_eq_abs, measureReal_def] using hb
        exact (le_abs_self _).trans hb'
    · refine ⟨Cᶜ, hC.isClosed.isOpen_compl, ?_, fun x hx => hz x hx⟩
      intro x hx hxC
      exact hx.2 (hCQ hxC)
  have hcontinuous (f : V n × ℝ → ℝ) (hf : f ∈ fields u) (r : ℝ) (hr : 0 < r) :
      Continuous (fun x : V n => f (x,r)) := by
    exact (hsmooth f hf).continuousOn.comp_continuous (continuous_id.prodMk continuous_const)
      (fun x => hr)
  have hInt (r : ℝ) (hr : 0 < r) : Integrable (fun x => e u x r) := by
    obtain ⟨C, R, hC, hR, hCi, hCQ, hQ, hmQ, hvQ, hfin, hu, hdu⟩ := h_T002 r hr
    have hf : (fun p : V n × ℝ => e u p.1 p.2) ∈ fields u := Or.inl rfl
    have htime : r ∈ Ioo (r/2) (3*r/2) := by constructor <;> linarith
    exact (hcompact C (box n R) (fun x => e u x r) hC hCQ hQ hfin
      (hcontinuous _ hf r hr) (hzero C _ _ hC.isClosed hu _ hf r htime)).2.1
  refine ⟨?_, hInt⟩
  intro t0 ht0
  obtain ⟨C, R, hC, hR, hCi, hCQ, hQ, hmQ, hvQ, hfin, hu, hdu⟩ := h_T002 t0 ht0
  refine ⟨C, R, hC, hR, hCi, hCQ, hQ, hmQ, hvQ, hfin, hu, hdu, ?_⟩
  intro f hf r hr
  have hrpos : 0 < r := by have := hr.1; linarith
  have hc := hcontinuous f hf r hrpos
  have hz := hzero C _ _ hC.isClosed hu f hf r hr
  exact ⟨hc, hz, hcompact C (box n R) (fun x => f (x,r)) hC hCQ hQ hfin hc hz⟩

theorem T004 (n : ℕ) (m : ℕ) (u : V n × ℝ → W m) (q : W m) (h_H002 : ContDiffOn ℝ ∞ u (domain n)) :
    ContDiffOn ℝ ∞ (fun p : V n × ℝ => e u p.1 p.2) (domain n) ∧
(∀ j : Fin n, ContDiffOn ℝ ∞ (fun p : V n × ℝ => g u j p.1 p.2) (domain n)) ∧
(∀ x t, 0 < t →
(∀ j : Fin n, deriv (fun s => ux u j x s) t = uxt u j x t) ∧
et u x t = 2*A u x t + 2*(∑ j, B u j x t) ∧
(∀ j : Fin n, dg u j x t = B u j x t + T u j x t)) ∧
(∀ f ∈ fields u, ContinuousOn f (domain n)) ∧
(∀ j : Fin n, ContinuousOn (fun p : V n × ℝ => uxt u j p.1 p.2) (domain n)) := by
  classical
  have ho : IsOpen (domain n) := isOpen_lt continuous_const continuous_snd
  have hd : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
      (f : V n × ℝ → F), ContDiffOn ℝ ∞ f (domain n) →
      ∀ p ∈ domain n, DifferentiableAt ℝ f p := by
    intro F _ _ f hf p hp
    exact (hf.contDiffAt (ho.mem_nhds hp)).differentiableAt (by simp)
  have bridge : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
      (f : V n × ℝ → F) (x : V n) (t : ℝ), DifferentiableAt ℝ f (x,t) →
      (deriv (fun s => f (x,s)) t = fderiv ℝ f (x,t) (0,1)) ∧
      (∀ v : V n, fderiv ℝ (fun y => f (y,t)) x v = fderiv ℝ f (x,t) (v,0)) := by
    intro F _ _ f x t hf
    constructor
    · exact (hf.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_const t x).prodMk (hasDerivAt_id t))).deriv
    · intro v
      have hi : HasFDerivAt (fun y : V n => (y,t)) ((ContinuousLinearMap.id ℝ (V n)).prod (0 : V n →L[ℝ] ℝ)) x := (hasFDerivAt_id x).prodMk (hasFDerivAt_const t x)
      have h := hf.hasFDerivAt.comp x hi
      exact congrArg (fun L : V n →L[ℝ] F => L v) h.fderiv
  have dt : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
      (f : V n × ℝ → F), ContDiffOn ℝ ∞ f (domain n) →
      ContDiffOn ℝ ∞ (fun p : V n × ℝ => deriv (fun s => f (p.1,s)) p.2) (domain n) := by
    intro F _ _ f hf
    have hf' : ContDiffOn ℝ ∞ (fderiv ℝ f) (domain n) :=
      hf.fderiv_of_isOpen ho (by simp)
    apply (hf'.clm_apply (contDiffOn_const (c := ((0 : V n), (1 : ℝ))))).congr
    intro p hp
    exact (bridge f p.1 p.2 (hd f hf p hp)).1
  have dx : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
      (f : V n × ℝ → F), ContDiffOn ℝ ∞ f (domain n) →
      ∀ v : V n, ContDiffOn ℝ ∞
        (fun p : V n × ℝ => fderiv ℝ (fun y => f (y,p.2)) p.1 v) (domain n) := by
    intro F _ _ f hf v
    have hf' : ContDiffOn ℝ ∞ (fderiv ℝ f) (domain n) :=
      hf.fderiv_of_isOpen ho (by simp)
    apply (hf'.clm_apply (contDiffOn_const (c := (v,(0 : ℝ))))).congr
    intro p hp
    exact (bridge f p.1 p.2 (hd f hf p hp)).2 v
  have hut : ContDiffOn ℝ ∞ (fun p : V n × ℝ => ut u p.1 p.2) (domain n) :=
    dt u h_H002
  have hux : ∀ j, ContDiffOn ℝ ∞ (fun p : V n × ℝ => ux u j p.1 p.2) (domain n) :=
    fun j => dx u h_H002 (Pi.single j 1)
  have hutt : ContDiffOn ℝ ∞ (fun p : V n × ℝ => utt u p.1 p.2) (domain n) :=
    dt _ hut
  have huxx : ∀ j, ContDiffOn ℝ ∞ (fun p : V n × ℝ => uxx u j p.1 p.2) (domain n) :=
    fun j => dx _ (hux j) (Pi.single j 1)
  have huxt : ∀ j, ContDiffOn ℝ ∞ (fun p : V n × ℝ => uxt u j p.1 p.2) (domain n) :=
    fun j => dx _ hut (Pi.single j 1)
  have he : ContDiffOn ℝ ∞ (fun p : V n × ℝ => e u p.1 p.2) (domain n) :=
    (hut.norm_sq (𝕜 := ℝ)).add (ContDiffOn.sum (fun j _ => (hux j).norm_sq (𝕜 := ℝ)))
  have hg : ∀ j, ContDiffOn ℝ ∞ (fun p : V n × ℝ => g u j p.1 p.2) (domain n) :=
    fun j => hut.inner ℝ (hux j)
  have hmix : ∀ x t, 0 < t → ∀ j : Fin n,
      deriv (fun s => ux u j x s) t = uxt u j x t := by
    intro x t ht j
    have hp : (x,t) ∈ domain n := ht
    have hdf : ContDiffOn ℝ ∞ (fderiv ℝ u) (domain n) :=
      h_H002.fderiv_of_isOpen ho (by simp)
    have dcoord : ∀ v w : V n × ℝ,
        fderiv ℝ (fun p => fderiv ℝ u p v) (x,t) w =
        fderiv ℝ (fderiv ℝ u) (x,t) w v := by
      intro v w
      have hh := (hd _ hdf (x,t) hp).hasFDerivAt.clm_apply (hasFDerivAt_const v (x,t))
      simpa using congrArg (fun L : (V n × ℝ) →L[ℝ] W m => L w) hh.fderiv
    have eut : (fun p : V n × ℝ => ut u p.1 p.2) =ᶠ[𝓝 (x,t)]
        (fun p => fderiv ℝ u p (0,1)) := by
      filter_upwards [ho.mem_nhds hp] with p h
      exact (bridge u p.1 p.2 (hd u h_H002 p h)).1
    have eux : (fun p : V n × ℝ => ux u j p.1 p.2) =ᶠ[𝓝 (x,t)]
        (fun p => fderiv ℝ u p (Pi.single j 1,0)) := by
      filter_upwards [ho.mem_nhds hp] with p h
      exact (bridge u p.1 p.2 (hd u h_H002 p h)).2 (Pi.single j 1)
    have htux := (bridge _ x t (hd _ (hux j) (x,t) hp)).1
    have hxut := (bridge _ x t (hd _ hut (x,t) hp)).2 (Pi.single j 1)
    change deriv (fun s => ux u j x s) t =
      fderiv ℝ (fun y => ut u y t) x (Pi.single j 1)
    rw [htux, hxut, eux.fderiv_eq, eut.fderiv_eq, dcoord, dcoord]
    have htwo : ContDiffAt ℝ 2 u (x,t) :=
      (h_H002.contDiffAt (ho.mem_nhds hp)).of_le (WithTop.coe_le_coe.mpr le_top)
    exact htwo.isSymmSndFDerivAt (by simp) (0,1) (Pi.single j 1,0)
  have htime : ∀ (f : V n × ℝ → W m), ContDiffOn ℝ ∞ f (domain n) →
      ∀ x t, 0 < t → HasDerivAt (fun s => f (x,s))
        (deriv (fun s => f (x,s)) t) t := by
    intro f hf x t ht
    have hh := (hd f hf (x,t) ht).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_const t x).prodMk (hasDerivAt_id t))
    exact hh.differentiableAt.hasDerivAt
  have henergy : ∀ x t, 0 < t →
      et u x t = 2*A u x t + 2*(∑ j, B u j x t) := by
    intro x t ht
    have htut : HasDerivAt (fun s => ut u x s) (utt u x t) t :=
      htime _ hut x t ht
    have htux : ∀ j, HasDerivAt (fun s => ux u j x s) (uxt u j x t) t := by
      intro j
      rw [← hmix x t ht j]
      exact htime _ (hux j) x t ht
    have hh := (htut.norm_sq).add (HasDerivAt.fun_sum (fun j (_ : j ∈ Finset.univ) => (htux j).norm_sq))
    have heq : et u x t =
        2 * inner ℝ (ut u x t) (utt u x t) +
        ∑ j, 2 * inner ℝ (ux u j x t) (uxt u j x t) := hh.deriv
    simpa only [A, B, Finset.mul_sum] using heq
  have hflux : ∀ x t, 0 < t → ∀ j, dg u j x t = B u j x t + T u j x t := by
    intro x t ht j
    have hslice : ∀ (f : V n × ℝ → W m), ContDiffOn ℝ ∞ f (domain n) →
        DifferentiableAt ℝ (fun y => f (y,t)) x := by
      intro f hf
      have hi : HasFDerivAt (fun y : V n => (y,t))
          ((ContinuousLinearMap.id ℝ (V n)).prod (0 : V n →L[ℝ] ℝ)) x :=
        (hasFDerivAt_id x).prodMk (hasFDerivAt_const t x)
      exact ((hd f hf (x,t) ht).hasFDerivAt.comp x hi).differentiableAt
    have hh := (hslice _ hut).hasFDerivAt.inner ℝ (hslice _ (hux j)).hasFDerivAt
    have heq : dg u j x t =
        inner ℝ (ut u x t) (uxx u j x t) +
        inner ℝ (uxt u j x t) (ux u j x t) := by
      simpa [dg, g, uxx, uxt, fderivInnerCLM_apply] using
        congrArg (fun L : V n →L[ℝ] ℝ => L (Pi.single j 1)) hh.fderiv
    rw [heq]
    simp only [B, T, real_inner_comm (uxt u j x t) (ux u j x t), add_comm]
  refine ⟨he, hg, ?_, ?_, fun j => (huxt j).continuousOn⟩
  · intro x t ht
    exact ⟨hmix x t ht, henergy x t ht, hflux x t ht⟩
  · intro f hf
    rcases hf with rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact he.continuousOn
    · exact (dt _ he).continuousOn
    · exact (hut.inner ℝ hutt).continuousOn
    · exact ((hux j).inner ℝ (huxt j)).continuousOn
    · exact (hut.inner ℝ (huxx j)).continuousOn
    · exact (hg j).continuousOn
    · exact (dx _ (hg j) (Pi.single j 1)).continuousOn

theorem T005 (n : ℕ) (m : ℕ) (u : V n × ℝ → W m) (q : W m) (h_T003 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (V n), ∃ R : ℝ,
IsCompact C ∧ 0 < R ∧ C ⊆ innerBox n R ∧ C ⊆ interior (box n R) ∧
IsCompact (box n R) ∧ MeasurableSet (box n R) ∧
volume (box n R) = ENNReal.ofReal ((2*R)^n) ∧ volume (box n R) < ⊤ ∧
(∀ x, x ∉ C → ∀ r ∈ Set.Icc (t0/2) (3*t0/2), u (x,r) = q) ∧
(∀ k : ℕ, 0 < k → ∀ x, x ∉ C → ∀ r ∈ Set.Ioo (t0/2) (3*t0/2),
iteratedFDeriv ℝ k u (x,r) = 0 ) ∧ (∀ f ∈ fields u, ∀ r ∈ Set.Ioo (t0/2) (3*t0/2),
Continuous (fun x => f (x,r)) ∧
(∀ x, x ∉ C → f (x,r) = 0) ∧
HasCompactSupport (fun x => f (x,r)) ∧ Integrable (fun x => f (x,r)) ∧
(∃ K : ℝ, 0 ≤ K ∧ (∀ x ∈ box n R, |f (x,r)| ≤ K) ∧
(∫ x, |f (x,r)|) ≤ K * (volume (box n R)).toReal) ∧
(∃ U : Set (V n), IsOpen U ∧ frontier (box n R) ⊆ U ∧ ∀ x ∈ U, f (x,r) = 0))) ∧ (∀ r : ℝ, 0 < r → Integrable (fun x => e u x r))) (h_T004 : ContDiffOn ℝ ∞ (fun p : V n × ℝ => e u p.1 p.2) (domain n) ∧
(∀ j : Fin n, ContDiffOn ℝ ∞ (fun p : V n × ℝ => g u j p.1 p.2) (domain n)) ∧
(∀ x t, 0 < t →
(∀ j : Fin n, deriv (fun s => ux u j x s) t = uxt u j x t) ∧
et u x t = 2*A u x t + 2*(∑ j, B u j x t) ∧
(∀ j : Fin n, dg u j x t = B u j x t + T u j x t)) ∧
(∀ f ∈ fields u, ContinuousOn f (domain n)) ∧
(∀ j : Fin n, ContinuousOn (fun p : V n × ℝ => uxt u j p.1 p.2) (domain n))) :
    ∀ t0 : ℝ, 0 < t0 → ∃ η R K : ℝ,
0 < η ∧ η < t0 ∧ 0 < R ∧ 0 ≤ K ∧
Integrable ((box n R).indicator (fun _ : V n => K)) ∧
(∀ h : ℝ, 0 < |h| → |h| < η →
Integrable (fun x => (e u x (t0+h) - e u x t0)/h) ∧
(∀ x : V n, |(e u x (t0+h) - e u x t0)/h| ≤
(box n R).indicator (fun _ : V n => K) x)) ∧
(∀ x : V n, Filter.Tendsto
(fun h : ℝ => (e u x (t0+h) - e u x t0)/h)
(nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (et u x t0))) := by
  classical
  intro t0 ht0
  obtain ⟨C, R, hC, hR, hCi, hCQ, hQ, hQm, hvol, hfin, hu, hder, hf⟩ :=
    h_T003.1 t0 ht0
  let η : ℝ := t0 / 4
  have hη : 0 < η := by dsimp [η]; linarith
  have hηt : η < t0 := by dsimp [η]; linarith
  have hI : ∀ r ∈ Set.Icc (t0-η) (t0+η),
      r ∈ Set.Ioo (t0/2) (3*t0/2) := by
    intro r hr
    dsimp [η] at hr
    constructor <;> linarith [hr.1, hr.2]
  have hpos : ∀ r ∈ Set.Icc (t0-η) (t0+η), 0 < r := by
    intro r hr
    have := (hI r hr).1
    linarith
  have htime : ∀ x : V n, ∀ t : ℝ, 0 < t →
      HasDerivAt (fun s => e u x s) (et u x t) t := by
    intro x t ht
    have hopen : IsOpen (domain n) := isOpen_lt continuous_const continuous_snd
    have hd : DifferentiableAt ℝ (fun p : V n × ℝ => e u p.1 p.2) (x,t) :=
      (h_T004.1.contDiffAt (hopen.mem_nhds ht)).differentiableAt (by simp)
    have hc : DifferentiableAt ℝ (fun s : ℝ => (x,s)) t :=
      (differentiableAt_const x).prodMk differentiableAt_id
    exact (hd.comp t hc).hasDerivAt
  have hefield : (fun p : V n × ℝ => e u p.1 p.2) ∈ fields u := by
    exact Or.inl rfl
  have hetfield : (fun p : V n × ℝ => et u p.1 p.2) ∈ fields u := by
    exact Or.inr (Or.inl rfl)
  have hct : ContinuousOn (fun p : V n × ℝ => et u p.1 p.2)
      ((box n R) ×ˢ Set.Icc (t0-η) (t0+η)) :=
    (h_T004.2.2.2.1 _ hetfield).mono (by
      intro p hp
      exact hpos p.2 hp.2)
  obtain ⟨L, hL⟩ := (hQ.prod isCompact_Icc).bddAbove_image hct.abs
  let K : ℝ := max L 0
  have hK : 0 ≤ K := le_max_right _ _
  have hbound : ∀ x ∈ box n R, ∀ r ∈ Set.Icc (t0-η) (t0+η),
      |et u x r| ≤ K := by
    intro x hx r hr
    exact le_trans (hL ⟨(x,r), ⟨hx,hr⟩, rfl⟩) (le_max_left _ _)
  have hind : Integrable ((box n R).indicator (fun _ : V n => K)) :=
    (integrable_indicator_iff hQm).2 (integrableOn_const hfin.ne)
  refine ⟨η, R, K, hη, hηt, hR, hK, hind, ?_, ?_⟩
  · intro h hh hsmall
    have habs : -η < h ∧ h < η := abs_lt.mp hsmall
    have htI : t0 ∈ Set.Icc (t0-η) (t0+η) := by constructor <;> linarith
    have hthI : t0+h ∈ Set.Icc (t0-η) (t0+η) := by constructor <;> linarith [habs.1,habs.2]
    refine ⟨((h_T003.2 (t0+h) (hpos _ hthI)).sub (h_T003.2 t0 ht0)).div_const h, ?_⟩
    intro x
    by_cases hx : x ∈ box n R
    · rw [Set.indicator_of_mem hx]
      have hest : |e u x (t0+h) - e u x t0| ≤ K * |h| := by
        rcases lt_or_gt_of_ne (abs_pos.mp hh) with hneg | hpositive
        · have hstep := norm_image_sub_le_of_norm_deriv_le_segment'
            (f := fun r : ℝ => e u x r) (f' := fun r => et u x r)
            (a := t0+h) (b := t0) (C := K)
            (fun r hr => (htime x r (hpos r (by
              constructor <;> linarith [hr.1, hr.2, habs.1, habs.2]))).hasDerivWithinAt)
            (fun r hr => by
              rw [Real.norm_eq_abs]
              exact hbound x hx r (by constructor <;> linarith [hr.1, hr.2, habs.1, habs.2]))
            t0 (by constructor <;> linarith)
          rw [Real.norm_eq_abs, abs_sub_comm] at hstep
          rw [abs_of_neg hneg]
          convert hstep using 1 <;> ring
        · have hstep := norm_image_sub_le_of_norm_deriv_le_segment'
            (f := fun r : ℝ => e u x r) (f' := fun r => et u x r)
            (a := t0) (b := t0+h) (C := K)
            (fun r hr => (htime x r (hpos r (by
              constructor <;> linarith [hr.1, hr.2, habs.1, habs.2]))).hasDerivWithinAt)
            (fun r hr => by
              rw [Real.norm_eq_abs]
              exact hbound x hx r (by constructor <;> linarith [hr.1, hr.2, habs.1, habs.2]))
            (t0+h) (by constructor <;> linarith)
          simpa only [Real.norm_eq_abs, add_sub_cancel_left, abs_of_pos hpositive] using hstep
      rw [abs_div]
      exact (div_le_iff₀ hh).2 hest
    · rw [Set.indicator_of_notMem hx]
      have hxC : x ∉ C := fun hc => hx (interior_subset (hCQ hc))
      have hz1 : e u x (t0+h) = 0 := (hf _ hefield _ (hI _ hthI)).2.1 x hxC
      have hz0 : e u x t0 = 0 := (hf _ hefield _ (hI _ htI)).2.1 x hxC
      simp [hz1,hz0]
  · intro x
    simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using
      (htime x t0 ht0).tendsto_slope_zero

theorem T006 (n : ℕ) (m : ℕ) (u : V n × ℝ → W m) (q : W m) (h_T003 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (V n), ∃ R : ℝ,
IsCompact C ∧ 0 < R ∧ C ⊆ innerBox n R ∧ C ⊆ interior (box n R) ∧
IsCompact (box n R) ∧ MeasurableSet (box n R) ∧
volume (box n R) = ENNReal.ofReal ((2*R)^n) ∧ volume (box n R) < ⊤ ∧
(∀ x, x ∉ C → ∀ r ∈ Set.Icc (t0/2) (3*t0/2), u (x,r) = q) ∧
(∀ k : ℕ, 0 < k → ∀ x, x ∉ C → ∀ r ∈ Set.Ioo (t0/2) (3*t0/2),
iteratedFDeriv ℝ k u (x,r) = 0 ) ∧ (∀ f ∈ fields u, ∀ r ∈ Set.Ioo (t0/2) (3*t0/2),
Continuous (fun x => f (x,r)) ∧
(∀ x, x ∉ C → f (x,r) = 0) ∧
HasCompactSupport (fun x => f (x,r)) ∧ Integrable (fun x => f (x,r)) ∧
(∃ K : ℝ, 0 ≤ K ∧ (∀ x ∈ box n R, |f (x,r)| ≤ K) ∧
(∫ x, |f (x,r)|) ≤ K * (volume (box n R)).toReal) ∧
(∃ U : Set (V n), IsOpen U ∧ frontier (box n R) ⊆ U ∧ ∀ x ∈ U, f (x,r) = 0))) ∧ (∀ r : ℝ, 0 < r → Integrable (fun x => e u x r))) (h_T004 : ContDiffOn ℝ ∞ (fun p : V n × ℝ => e u p.1 p.2) (domain n) ∧
(∀ j : Fin n, ContDiffOn ℝ ∞ (fun p : V n × ℝ => g u j p.1 p.2) (domain n)) ∧
(∀ x t, 0 < t →
(∀ j : Fin n, deriv (fun s => ux u j x s) t = uxt u j x t) ∧
et u x t = 2*A u x t + 2*(∑ j, B u j x t) ∧
(∀ j : Fin n, dg u j x t = B u j x t + T u j x t)) ∧
(∀ f ∈ fields u, ContinuousOn f (domain n)) ∧
(∀ j : Fin n, ContinuousOn (fun p : V n × ℝ => uxt u j p.1 p.2) (domain n))) (h_T005 : ∀ t0 : ℝ, 0 < t0 → ∃ η R K : ℝ,
0 < η ∧ η < t0 ∧ 0 < R ∧ 0 ≤ K ∧
Integrable ((box n R).indicator (fun _ : V n => K)) ∧
(∀ h : ℝ, 0 < |h| → |h| < η →
Integrable (fun x => (e u x (t0+h) - e u x t0)/h) ∧
(∀ x : V n, |(e u x (t0+h) - e u x t0)/h| ≤
(box n R).indicator (fun _ : V n => K) x)) ∧
(∀ x : V n, Filter.Tendsto
(fun h : ℝ => (e u x (t0+h) - e u x t0)/h)
(nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (et u x t0)))) :
    (∀ t0 : ℝ, 0 < t0 →
HasDerivAt (energy u) (∫ x, et u x t0) t0 ∧
deriv (energy u) t0 = ∫ x, et u x t0) ∧ DifferentiableOn ℝ (energy u) (Set.Ioi 0) := by
  have hderiv : ∀ t0 : ℝ, 0 < t0 → HasDerivAt (energy u) (∫ x, et u x t0) t0 := by
    intro t0 ht0
    obtain ⟨η, R, K, hη, hηt, hR, hK, hbound, hquot, hpoint⟩ := h_T005 t0 ht0
    have hsmall : ∀ᶠ h : ℝ in nhdsWithin 0 ({0}ᶜ), 0 < |h| ∧ |h| < η := by
      rw [eventually_nhdsWithin_iff]
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hη] with h hh hn
      have hh' : |h| < η := by simpa [Metric.mem_ball, Real.dist_eq] using hh
      have hn' : h ≠ 0 := by simpa using hn
      exact ⟨abs_pos.mpr hn', hh'⟩
    have hmeas : ∀ᶠ h : ℝ in nhdsWithin 0 ({0}ᶜ),
        AEStronglyMeasurable (fun x : V n => (e u x (t0+h) - e u x t0)/h) volume := by
      filter_upwards [hsmall] with h hh
      exact (hquot h hh.1 hh.2).1.aestronglyMeasurable
    have hdom : ∀ᶠ h : ℝ in nhdsWithin 0 ({0}ᶜ), ∀ᵐ x : V n,
        ‖(e u x (t0+h) - e u x t0)/h‖ ≤ (box n R).indicator (fun _ : V n => K) x := by
      filter_upwards [hsmall] with h hh
      exact Filter.Eventually.of_forall (fun x => by
        simpa only [Real.norm_eq_abs] using (hquot h hh.1 hh.2).2 x)
    have hlim : Filter.Tendsto
        (fun h : ℝ => ∫ x : V n, (e u x (t0+h) - e u x t0)/h)
        (nhdsWithin 0 ({0}ᶜ)) (nhds (∫ x : V n, et u x t0)) :=
      tendsto_integral_filter_of_dominated_convergence
        ((box n R).indicator (fun _ : V n => K)) hmeas hdom hbound
        (Filter.Eventually.of_forall hpoint)
    have heq : (fun h : ℝ => ∫ x : V n, (e u x (t0+h) - e u x t0)/h)
        =ᶠ[nhdsWithin 0 ({0}ᶜ)] (fun h : ℝ => (energy u (t0+h) - energy u t0)/h) := by
      filter_upwards [hsmall] with h hh
      have hpos : 0 < t0 + h := by
        have hneg := neg_abs_le h
        linarith [hh.2]
      rw [integral_div, integral_sub (h_T003.2 (t0+h) hpos) (h_T003.2 t0 ht0)]
      rfl
    apply hasDerivAt_iff_tendsto_slope_zero.mpr
    simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using (hlim.congr' heq)
  constructor
  · intro t0 ht0
    exact ⟨hderiv t0 ht0, (hderiv t0 ht0).deriv⟩
  · intro t0 ht0
    exact (hderiv t0 ht0).differentiableAt.differentiableWithinAt

theorem T001 (n : ℕ) (m : ℕ) (u : V n × ℝ → W m) (q : W m) (h_H002 : ContDiffOn ℝ ∞ u (domain n)) (h_H004 : ∀ x t, 0 < t → ‖u (x,t)‖ = 1) (h_H005 : ∀ x t, 0 < t → ∃ a : ℝ, utt u x t - lap u x t = a • u (x,t)) :
    ∀ x t, 0 < t →
inner ℝ (u (x,t)) (ut u x t) = 0 ∧
inner ℝ (ut u x t) (utt u x t - lap u x t) = 0 ∧
inner ℝ (u (x,t)) (utt u x t) = -(‖ut u x t‖^2) ∧
(∀ j : Fin n, inner ℝ (u (x,t)) (uxx u j x t) = -(‖ux u j x t‖^2)) ∧
(∀ a : ℝ, utt u x t - lap u x t = a • u (x,t) →
a = (∑ j, ‖ux u j x t‖^2) - ‖ut u x t‖^2) ∧
utt u x t - lap u x t = ((∑ j, ‖ux u j x t‖^2) - ‖ut u x t‖^2) • u (x,t) := by
  classical
  have geometry : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → W m) (s : Set E), IsOpen s →
    (∀ y ∈ s, ContDiffAt ℝ 2 f y) →
    (∀ y ∈ s, ‖f y‖ = 1) →
    ∀ z ∈ s, ∀ v : E,
      inner ℝ (f z) (fderiv ℝ f z v) = 0 ∧
      inner ℝ (f z) (fderiv ℝ (fun y => fderiv ℝ f y v) z v) =
        -(‖fderiv ℝ f z v‖ ^ 2) := by
    intro E _ _ f s hs hf hn
    have first : ∀ z ∈ s, ∀ v : E, inner ℝ (f z) (fderiv ℝ f z v) = 0 := by
      intro z hz v
      have heq : (fun y => inner ℝ (f y) (f y)) =ᶠ[𝓝 z] (fun _ => (1 : ℝ)) := by
        filter_upwards [hs.mem_nhds hz] with y hy
        rw [real_inner_self_eq_norm_sq, hn y hy]
        norm_num
      have hd := ((hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) z).congr_of_eventuallyEq heq).fderiv
      have he := congrArg (fun L : E →L[ℝ] ℝ => L v) hd
      rw [fderiv_inner_apply ℝ (hf z hz |>.differentiableAt (by norm_num))
        (hf z hz |>.differentiableAt (by norm_num)) v] at he
      simp only [ContinuousLinearMap.zero_apply] at he
      rw [real_inner_comm (f z) (fderiv ℝ f z v)] at he
      linarith
    intro z hz v
    refine ⟨first z hz v, ?_⟩
    have hdf : DifferentiableAt ℝ f z := (hf z hz).differentiableAt (by norm_num)
    have hcd : ContDiffAt ℝ 1 (fun y => fderiv ℝ f y v) z :=
      ((hf z hz).fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
    have heq : (fun y => inner ℝ (f y) (fderiv ℝ f y v)) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
      filter_upwards [hs.mem_nhds hz] with y hy
      exact first y hy v
    have hd := ((hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) z).congr_of_eventuallyEq heq).fderiv
    have he := congrArg (fun L : E →L[ℝ] ℝ => L v) hd
    rw [fderiv_inner_apply ℝ hdf hcd.differentiableAt_one v] at he
    simp only [ContinuousLinearMap.zero_apply, real_inner_self_eq_norm_sq] at he
    linarith
  have slices : ∀ x t, 0 < t →
    (∀ r ∈ Set.Ioi (0 : ℝ), ContDiffAt ℝ 2 (fun s => u (x,s)) r) ∧
    (∀ y : V n, ContDiffAt ℝ 2 (fun z => u (z,t)) y) := by
    have hopen : IsOpen (domain n) := isOpen_lt continuous_const continuous_snd
    have smooth : ∀ x t, 0 < t → ContDiffAt ℝ 2 u (x,t) := by
      intro x t ht
      exact (h_H002.contDiffAt (hopen.mem_nhds ht)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    intro x t ht
    constructor
    · intro r hr
      exact (smooth x r hr).comp r (contDiffAt_const.prodMk contDiffAt_id)
    · intro y
      exact (smooth y t ht).comp y (contDiffAt_id.prodMk contDiffAt_const)
  intro x t ht
  have htime := geometry ℝ (fun s => u (x,s)) (Set.Ioi 0) isOpen_Ioi
    (slices x t ht).1 (fun r hr => h_H004 x r hr) t ht 1
  have hfirst : inner ℝ (u (x,t)) (ut u x t) = 0 := htime.1
  have hsecond : inner ℝ (u (x,t)) (utt u x t) = -(‖ut u x t‖ ^ 2) := htime.2
  have hspace : ∀ j : Fin n, inner ℝ (u (x,t)) (uxx u j x t) = -(‖ux u j x t‖ ^ 2) := by
    intro j
    exact (geometry (V n) (fun y => u (y,t)) Set.univ isOpen_univ
      (fun y _ => (slices x t ht).2 y)
      (fun y _ => h_H004 y t ht) x (Set.mem_univ x) (Pi.single j 1)).2
  obtain ⟨a, ha⟩ := h_H005 x t ht
  have hnormal : inner ℝ (ut u x t) (utt u x t - lap u x t) = 0 := by
    rw [ha, real_inner_smul_right, real_inner_comm (u (x,t)) (ut u x t), hfirst, mul_zero]
  have hscalar : ∀ a : ℝ, utt u x t - lap u x t = a • u (x,t) →
      a = (∑ j, ‖ux u j x t‖ ^ 2) - ‖ut u x t‖ ^ 2 := by
    intro b hb
    have he := congrArg (fun w : W m => inner ℝ (u (x,t)) w) hb
    rw [inner_sub_right, hsecond, lap, inner_sum] at he
    simp_rw [hspace] at he
    rw [Finset.sum_neg_distrib, real_inner_smul_right, real_inner_self_eq_norm_sq,
      h_H004 x t ht] at he
    norm_num at he
    linarith
  refine ⟨hfirst, hnormal, hsecond, hspace, hscalar, ?_⟩
  rw [ha, hscalar a ha]

theorem T007 (n : ℕ) (m : ℕ) (u : V n × ℝ → W m) (q : W m) (h_T003 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (V n), ∃ R : ℝ,
IsCompact C ∧ 0 < R ∧ C ⊆ innerBox n R ∧ C ⊆ interior (box n R) ∧
IsCompact (box n R) ∧ MeasurableSet (box n R) ∧
volume (box n R) = ENNReal.ofReal ((2*R)^n) ∧ volume (box n R) < ⊤ ∧
(∀ x, x ∉ C → ∀ r ∈ Set.Icc (t0/2) (3*t0/2), u (x,r) = q) ∧
(∀ k : ℕ, 0 < k → ∀ x, x ∉ C → ∀ r ∈ Set.Ioo (t0/2) (3*t0/2),
iteratedFDeriv ℝ k u (x,r) = 0 ) ∧ (∀ f ∈ fields u, ∀ r ∈ Set.Ioo (t0/2) (3*t0/2),
Continuous (fun x => f (x,r)) ∧
(∀ x, x ∉ C → f (x,r) = 0) ∧
HasCompactSupport (fun x => f (x,r)) ∧ Integrable (fun x => f (x,r)) ∧
(∃ K : ℝ, 0 ≤ K ∧ (∀ x ∈ box n R, |f (x,r)| ≤ K) ∧
(∫ x, |f (x,r)|) ≤ K * (volume (box n R)).toReal) ∧
(∃ U : Set (V n), IsOpen U ∧ frontier (box n R) ⊆ U ∧ ∀ x ∈ U, f (x,r) = 0))) ∧ (∀ r : ℝ, 0 < r → Integrable (fun x => e u x r))) (h_T004 : ContDiffOn ℝ ∞ (fun p : V n × ℝ => e u p.1 p.2) (domain n) ∧
(∀ j : Fin n, ContDiffOn ℝ ∞ (fun p : V n × ℝ => g u j p.1 p.2) (domain n)) ∧
(∀ x t, 0 < t →
(∀ j : Fin n, deriv (fun s => ux u j x s) t = uxt u j x t) ∧
et u x t = 2*A u x t + 2*(∑ j, B u j x t) ∧
(∀ j : Fin n, dg u j x t = B u j x t + T u j x t)) ∧
(∀ f ∈ fields u, ContinuousOn f (domain n)) ∧
(∀ j : Fin n, ContinuousOn (fun p : V n × ℝ => uxt u j p.1 p.2) (domain n))) :
    ∀ t0 : ℝ, 0 < t0 → ∀ j : Fin n,
Integrable (fun x => dg u j x t0) ∧ (∫ x, dg u j x t0) = 0 := by
  intro t0 ht0 j
  classical
  obtain ⟨C, R, hC, hR, hCinner, hCint, hQ, hQmeas, hQvol, hQfin, hu, huD, hfields⟩ :=
    h_T003.1 t0 ht0
  have htwin : t0 ∈ Ioo (t0 / 2) (3*t0 / 2) := by constructor <;> linarith
  have hgfield : (fun p : V n × ℝ => g u j p.1 p.2) ∈ fields u := by
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j, rfl⟩)))))
  have hdfield : (fun p : V n × ℝ => dg u j p.1 p.2) ∈ fields u := by
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨j, rfl⟩)))))
  have hgdata := hfields _ hgfield t0 htwin
  have hddata := hfields _ hdfield t0 htwin
  have hgcont : Continuous (fun x => g u j x t0) := hgdata.1
  have hdcont : Continuous (fun x => dg u j x t0) := hddata.1
  have hgzero : ∀ x, x ∉ C → g u j x t0 = 0 := hgdata.2.1
  have hdzero : ∀ x, x ∉ C → dg u j x t0 = 0 := hddata.2.1
  have hdint : Integrable (fun x => dg u j x t0) := hddata.2.2.2.1
  have hgsmooth : ContDiff ℝ ∞ (fun x : V n => g u j x t0) :=
    (h_T004.2.1 j).comp_contDiff (contDiff_id.prodMk contDiff_const) (fun _ => ht0)
  have hgdiff : Differentiable ℝ (fun x : V n => g u j x t0) :=
    hgsmooth.differentiable (by simp)
  classical
  let I := {i : Fin n // i ≠ j}
  let J := {i : Fin n // ¬ i ≠ j}
  letI : Unique J := ⟨⟨j, by simp⟩, fun a => Subtype.ext (by simpa using a.property)⟩
  let χ : V n ≃ᵐ ((I → ℝ) × ℝ) :=
    (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ) (fun i => i ≠ j)).trans
      ((MeasurableEquiv.refl (I → ℝ)).prodCongr
        (MeasurableEquiv.piUnique (fun _ : J => ℝ)))
  have hχ : MeasurePreserving χ volume volume :=
    ((MeasurePreserving.id (volume : Measure (I → ℝ))).prod
      (measurePreserving_piUnique (fun _ : J => (volume : Measure ℝ)))).comp
      (measurePreserving_piEquivPiSubtypeProd (fun _ : Fin n => (volume : Measure ℝ)) (fun i => i ≠ j))
  have hχinv (y : I → ℝ) (z : ℝ) (i : Fin n) :
      χ.symm (y,z) i = if h : i ≠ j then y ⟨i,h⟩ else z := rfl
  have hχj (y : I → ℝ) (z : ℝ) : χ.symm (y,z) j = z := by
    simp [hχinv]

  have hχcont : Continuous χ := by
    change Continuous (fun x : V n => ((fun i : I => x i), x j))
    exact (continuous_pi (fun i => continuous_apply i.val)).prodMk (continuous_apply j)
  have hinvcont : Continuous χ.symm := by
    apply continuous_pi
    intro i
    by_cases h : i ≠ j
    · simpa only [hχinv, dif_pos h, Function.comp_def] using! (continuous_apply (⟨i,h⟩ : I)).comp continuous_fst
    · simpa only [hχinv, dif_neg h] using (continuous_snd : Continuous (fun p : (I → ℝ) × ℝ => p.2))
  have hline (y : I → ℝ) (z : ℝ) :
      HasDerivAt (fun s => χ.symm (y,s)) (Pi.single j 1) z := by
    apply hasDerivAt_pi.mpr
    intro i
    by_cases h : i = j
    · subst i
      simpa only [hχj, Pi.single_eq_same] using! (hasDerivAt_id z)
    · simpa [hχinv, h, Ne.symm h, Pi.single_apply] using
        (hasDerivAt_const z (y ⟨i,h⟩))
  have hGderiv (y : I → ℝ) (z : ℝ) :
      HasDerivAt (fun s => g u j (χ.symm (y,s)) t0)
        (dg u j (χ.symm (y,z)) t0) z := by
    exact (hgdiff (χ.symm (y,z))).hasFDerivAt.comp_hasDerivAt z (hline y z)

  have houtC (y : I → ℝ) (z : ℝ) (hz : z ≤ -R ∨ R ≤ z) :
      χ.symm (y,z) ∉ C := by
    intro hx
    have hi := hCinner hx j
    rw [hχj] at hi
    rcases hz with hz | hz <;> linarith [hi.1, hi.2]
  have hinner (y : I → ℝ) :
      (∫ z : ℝ, dg u j (χ.symm (y,z)) t0) = 0 := by
    let G : ℝ → ℝ := fun z => g u j (χ.symm (y,z)) t0
    let D : ℝ → ℝ := fun z => dg u j (χ.symm (y,z)) t0
    have hDc : Continuous D :=
      hdcont.comp (hinvcont.comp (continuous_const.prodMk continuous_id))
    have hderiv : deriv G = D := funext (fun z => (hGderiv y z).deriv)
    have hGneg : G (-R) = 0 := hgzero _ (houtC y (-R) (Or.inl le_rfl))
    have hGpos : G R = 0 := hgzero _ (houtC y R (Or.inr le_rfl))
    have hDout : ∀ z, z ∉ Icc (-R) R → D z = 0 := by
      intro z hz
      apply hdzero
      apply houtC
      by_cases h : z ≤ -R
      · exact Or.inl h
      · right
        by_contra hh
        apply hz
        constructor <;> linarith
    have hDsupp : HasCompactSupport D := HasCompactSupport.intro isCompact_Icc hDout
    have hDint : Integrable D := hDc.integrable_of_hasCompactSupport hDsupp
    have hDi : IntervalIntegrable (deriv G) volume (-R) R := by
      rw [hderiv]
      exact hDc.continuousOn.intervalIntegrable
    have hft : (∫ z in (-R)..R, D z) = 0 := by
      rw [← hderiv]
      rw [intervalIntegral.integral_deriv_eq_sub
        (fun z _ => (hGderiv y z).differentiableAt) hDi]
      change G R - G (-R) = 0
      rw [hGpos, hGneg, sub_self]
    have hclosed : (∫ z in Icc (-R) R, D z) = 0 := by
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by linarith : -R ≤ R)]
      exact hft
    calc
      (∫ z : ℝ, D z) = ∫ z in Icc (-R) R, D z :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero hDout).symm
      _ = 0 := hclosed
  let H : ((I → ℝ) × ℝ) → ℝ := fun p => dg u j (χ.symm p) t0
  have hHcont : Continuous H := hdcont.comp hinvcont
  have hHsupp : HasCompactSupport H := by
    apply HasCompactSupport.intro (hQ.image hχcont)
    intro p hp
    apply hdzero
    intro hc
    apply hp
    exact ⟨χ.symm p, interior_subset (hCint hc), χ.apply_symm_apply p⟩
  have hHint : Integrable H := hHcont.integrable_of_hasCompactSupport hHsupp
  refine ⟨hdint, ?_⟩
  calc
    (∫ x, dg u j x t0) = ∫ p, H p := by
      simpa only [H, χ.symm_apply_apply] using (hχ.integral_comp χ.measurableEmbedding H)
    _ = ∫ y : I → ℝ, ∫ z : ℝ, H (y,z) := integral_prod H hHint
    _ = 0 := by
      have hz : (fun y : I → ℝ => ∫ z : ℝ, H (y,z)) = fun _ => 0 :=
        funext hinner
      rw [hz, integral_zero]

theorem T008 (n : ℕ) (m : ℕ) (u : V n × ℝ → W m) (q : W m) (h_T003 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (V n), ∃ R : ℝ,
IsCompact C ∧ 0 < R ∧ C ⊆ innerBox n R ∧ C ⊆ interior (box n R) ∧
IsCompact (box n R) ∧ MeasurableSet (box n R) ∧
volume (box n R) = ENNReal.ofReal ((2*R)^n) ∧ volume (box n R) < ⊤ ∧
(∀ x, x ∉ C → ∀ r ∈ Set.Icc (t0/2) (3*t0/2), u (x,r) = q) ∧
(∀ k : ℕ, 0 < k → ∀ x, x ∉ C → ∀ r ∈ Set.Ioo (t0/2) (3*t0/2),
iteratedFDeriv ℝ k u (x,r) = 0 ) ∧ (∀ f ∈ fields u, ∀ r ∈ Set.Ioo (t0/2) (3*t0/2),
Continuous (fun x => f (x,r)) ∧
(∀ x, x ∉ C → f (x,r) = 0) ∧
HasCompactSupport (fun x => f (x,r)) ∧ Integrable (fun x => f (x,r)) ∧
(∃ K : ℝ, 0 ≤ K ∧ (∀ x ∈ box n R, |f (x,r)| ≤ K) ∧
(∫ x, |f (x,r)|) ≤ K * (volume (box n R)).toReal) ∧
(∃ U : Set (V n), IsOpen U ∧ frontier (box n R) ⊆ U ∧ ∀ x ∈ U, f (x,r) = 0))) ∧ (∀ r : ℝ, 0 < r → Integrable (fun x => e u x r))) (h_T004 : ContDiffOn ℝ ∞ (fun p : V n × ℝ => e u p.1 p.2) (domain n) ∧
(∀ j : Fin n, ContDiffOn ℝ ∞ (fun p : V n × ℝ => g u j p.1 p.2) (domain n)) ∧
(∀ x t, 0 < t →
(∀ j : Fin n, deriv (fun s => ux u j x s) t = uxt u j x t) ∧
et u x t = 2*A u x t + 2*(∑ j, B u j x t) ∧
(∀ j : Fin n, dg u j x t = B u j x t + T u j x t)) ∧
(∀ f ∈ fields u, ContinuousOn f (domain n)) ∧
(∀ j : Fin n, ContinuousOn (fun p : V n × ℝ => uxt u j p.1 p.2) (domain n))) (h_T007 : ∀ t0 : ℝ, 0 < t0 → ∀ j : Fin n,
Integrable (fun x => dg u j x t0) ∧ (∫ x, dg u j x t0) = 0) :
    ∀ t0 : ℝ, 0 < t0 → ∀ j : Fin n,
Integrable (fun x => dg u j x t0) ∧ Integrable (fun x => B u j x t0) ∧
Integrable (fun x => T u j x t0) ∧
(∫ x, dg u j x t0) = 0 ∧
(∫ x, B u j x t0) = -(∫ x, T u j x t0) ∧
(∫ x, inner ℝ (ux u j x t0) (uxt u j x t0)) =
-(∫ x, inner ℝ (ut u x t0) (uxx u j x t0)) := by
  intro t0 ht0 j
  rcases h_T003.1 t0 ht0 with
    ⟨C, R, hC, hR, hCi, hCb, hbox, hmeas, hvol, hfin, hu, hder, hfields⟩
  have htime : t0 ∈ Set.Ioo (t0 / 2) (3 * t0 / 2) := by
    constructor <;> linarith
  have hf : ∀ f ∈ fields u, Integrable (fun x => f (x, t0)) := by
    intro f hmem
    exact (hfields f hmem t0 htime).2.2.2.1
  have hB : Integrable (fun x => B u j x t0) := by
    apply hf (fun p => B u j p.1 p.2)
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨j, rfl⟩)))
  have hT : Integrable (fun x => T u j x t0) := by
    apply hf (fun p => T u j p.1 p.2)
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j, rfl⟩))))
  have hdg : Integrable (fun x => dg u j x t0) := by
    apply hf (fun p => dg u j p.1 p.2)
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨j, rfl⟩)))))
  have hzero : (∫ x, dg u j x t0) = 0 := (h_T007 t0 ht0 j).2
  have hid : (fun x => dg u j x t0) =
      (fun x => B u j x t0 + T u j x t0) := by
    funext x
    exact (h_T004.2.2.1 x t0 ht0).2.2 j
  have hsum : (∫ x, B u j x t0) + (∫ x, T u j x t0) = 0 := by
    rw [← MeasureTheory.integral_add hB hT, ← hid]
    exact hzero
  have hneg : (∫ x, B u j x t0) = -(∫ x, T u j x t0) := by
    linarith
  exact ⟨hdg, hB, hT, hzero, hneg, by simpa only [B, T] using hneg⟩

theorem T009 (n : ℕ) (m : ℕ) (u : V n × ℝ → W m) (q : W m) (h_T001 : ∀ x t, 0 < t →
inner ℝ (u (x,t)) (ut u x t) = 0 ∧
inner ℝ (ut u x t) (utt u x t - lap u x t) = 0 ∧
inner ℝ (u (x,t)) (utt u x t) = -(‖ut u x t‖^2) ∧
(∀ j : Fin n, inner ℝ (u (x,t)) (uxx u j x t) = -(‖ux u j x t‖^2)) ∧
(∀ a : ℝ, utt u x t - lap u x t = a • u (x,t) →
a = (∑ j, ‖ux u j x t‖^2) - ‖ut u x t‖^2) ∧
utt u x t - lap u x t = ((∑ j, ‖ux u j x t‖^2) - ‖ut u x t‖^2) • u (x,t)) (h_T003 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (V n), ∃ R : ℝ,
IsCompact C ∧ 0 < R ∧ C ⊆ innerBox n R ∧ C ⊆ interior (box n R) ∧
IsCompact (box n R) ∧ MeasurableSet (box n R) ∧
volume (box n R) = ENNReal.ofReal ((2*R)^n) ∧ volume (box n R) < ⊤ ∧
(∀ x, x ∉ C → ∀ r ∈ Set.Icc (t0/2) (3*t0/2), u (x,r) = q) ∧
(∀ k : ℕ, 0 < k → ∀ x, x ∉ C → ∀ r ∈ Set.Ioo (t0/2) (3*t0/2),
iteratedFDeriv ℝ k u (x,r) = 0 ) ∧ (∀ f ∈ fields u, ∀ r ∈ Set.Ioo (t0/2) (3*t0/2),
Continuous (fun x => f (x,r)) ∧
(∀ x, x ∉ C → f (x,r) = 0) ∧
HasCompactSupport (fun x => f (x,r)) ∧ Integrable (fun x => f (x,r)) ∧
(∃ K : ℝ, 0 ≤ K ∧ (∀ x ∈ box n R, |f (x,r)| ≤ K) ∧
(∫ x, |f (x,r)|) ≤ K * (volume (box n R)).toReal) ∧
(∃ U : Set (V n), IsOpen U ∧ frontier (box n R) ⊆ U ∧ ∀ x ∈ U, f (x,r) = 0))) ∧ (∀ r : ℝ, 0 < r → Integrable (fun x => e u x r))) (h_T004 : ContDiffOn ℝ ∞ (fun p : V n × ℝ => e u p.1 p.2) (domain n) ∧
(∀ j : Fin n, ContDiffOn ℝ ∞ (fun p : V n × ℝ => g u j p.1 p.2) (domain n)) ∧
(∀ x t, 0 < t →
(∀ j : Fin n, deriv (fun s => ux u j x s) t = uxt u j x t) ∧
et u x t = 2*A u x t + 2*(∑ j, B u j x t) ∧
(∀ j : Fin n, dg u j x t = B u j x t + T u j x t)) ∧
(∀ f ∈ fields u, ContinuousOn f (domain n)) ∧
(∀ j : Fin n, ContinuousOn (fun p : V n × ℝ => uxt u j p.1 p.2) (domain n))) (h_T006 : (∀ t0 : ℝ, 0 < t0 →
HasDerivAt (energy u) (∫ x, et u x t0) t0 ∧
deriv (energy u) t0 = ∫ x, et u x t0) ∧ DifferentiableOn ℝ (energy u) (Set.Ioi 0)) (h_T008 : ∀ t0 : ℝ, 0 < t0 → ∀ j : Fin n,
Integrable (fun x => dg u j x t0) ∧ Integrable (fun x => B u j x t0) ∧
Integrable (fun x => T u j x t0) ∧
(∫ x, dg u j x t0) = 0 ∧
(∫ x, B u j x t0) = -(∫ x, T u j x t0) ∧
(∫ x, inner ℝ (ux u j x t0) (uxt u j x t0)) =
-(∫ x, inner ℝ (ut u x t0) (uxx u j x t0))) :
    ∀ t0 : ℝ, 0 < t0 →
deriv (energy u) t0 = 2*(∫ x, A u x t0) + 2*(∑ j, ∫ x, B u j x t0) ∧
deriv (energy u) t0 = 2*(∫ x, A u x t0) - 2*(∑ j, ∫ x, T u j x t0) ∧
deriv (energy u) t0 = 2*(∫ x, inner ℝ (ut u x t0) (utt u x t0 - lap u x t0)) ∧
HasDerivAt (energy u) 0 t0 := by
  intro t0 ht
  rcases h_T003.1 t0 ht with ⟨C, R, hC, hR, hCi, hCb, hbc, hbm, hbv, hbfin, hout, hit, hf⟩
  have hm : (fun p : V n × ℝ => A u p.1 p.2) ∈ fields u := by
    exact Or.inr (Or.inr (Or.inl rfl))
  have htime : t0 ∈ Set.Ioo (t0 / 2) (3 * t0 / 2) := by
    constructor <;> linarith
  have hA : Integrable (fun x => A u x t0) := (hf _ hm t0 htime).2.2.2.1
  have hB (j : Fin n) : Integrable (fun x => B u j x t0) :=
    (h_T008 t0 ht j).2.1
  have hT (j : Fin n) : Integrable (fun x => T u j x t0) :=
    (h_T008 t0 ht j).2.2.1
  have hBs : Integrable (fun x => ∑ j, B u j x t0) :=
    integrable_finsetSum Finset.univ (fun j _ => hB j)
  have hTs : Integrable (fun x => ∑ j, T u j x t0) :=
    integrable_finsetSum Finset.univ (fun j _ => hT j)
  have hBi : (∫ x, ∑ j, B u j x t0) = ∑ j, ∫ x, B u j x t0 :=
    integral_finsetSum Finset.univ (fun j _ => hB j)
  have hTi : (∫ x, ∑ j, T u j x t0) = ∑ j, ∫ x, T u j x t0 :=
    integral_finsetSum Finset.univ (fun j _ => hT j)
  have h2A : Integrable (fun x => 2 * A u x t0) := by
    have h : Integrable (fun x => (2 : ℝ) • A u x t0) := hA.smul (2 : ℝ)
    simpa only [smul_eq_mul] using h
  have h2B : Integrable (fun x => 2 * ∑ j, B u j x t0) := by
    have h : Integrable (fun x => (2 : ℝ) • ∑ j, B u j x t0) := hBs.smul (2 : ℝ)
    simpa only [smul_eq_mul] using h
  have hfirst : deriv (energy u) t0 =
      2 * (∫ x, A u x t0) + 2 * (∑ j, ∫ x, B u j x t0) := by
    calc
      deriv (energy u) t0 = ∫ x, et u x t0 := (h_T006.1 t0 ht).2
      _ = ∫ x, (2 * A u x t0 + 2 * ∑ j, B u j x t0) :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => (h_T004.2.2.1 x t0 ht).2.1)
      _ = (∫ x, 2 * A u x t0) + ∫ x, 2 * ∑ j, B u j x t0 :=
        integral_add h2A h2B
      _ = 2 * (∫ x, A u x t0) + 2 * (∑ j, ∫ x, B u j x t0) := by
        rw [integral_const_mul, integral_const_mul, hBi]
  have hBT : (∑ j, ∫ x, B u j x t0) = -(∑ j, ∫ x, T u j x t0) := by
    calc
      _ = ∑ j, -(∫ x, T u j x t0) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact (h_T008 t0 ht j).2.2.2.2.1
      _ = _ := Finset.sum_neg_distrib (fun j : Fin n => ∫ x, T u j x t0)
  have hsecond : deriv (energy u) t0 =
      2 * (∫ x, A u x t0) - 2 * (∑ j, ∫ x, T u j x t0) := by
    rw [hfirst, hBT]
    ring
  have hpoint (x : V n) :
      A u x t0 - ∑ j, T u j x t0 =
        inner ℝ (ut u x t0) (utt u x t0 - lap u x t0) := by
    simp only [A, T, lap, inner_sub_right, inner_sum]
  have hcombined :
      (∫ x, inner ℝ (ut u x t0) (utt u x t0 - lap u x t0)) =
        (∫ x, A u x t0) - ∑ j, ∫ x, T u j x t0 := by
    calc
      _ = ∫ x, (A u x t0 - ∑ j, T u j x t0) :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => (hpoint x).symm)
      _ = (∫ x, A u x t0) - ∫ x, ∑ j, T u j x t0 := integral_sub hA hTs
      _ = _ := by rw [hTi]
  have hthird : deriv (energy u) t0 =
      2 * (∫ x, inner ℝ (ut u x t0) (utt u x t0 - lap u x t0)) := by
    rw [hcombined, hsecond]
    ring
  have hintzero :
      (∫ x, inner ℝ (ut u x t0) (utt u x t0 - lap u x t0)) = 0 := by
    calc
      _ = ∫ _ : V n, (0 : ℝ) :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => (h_T001 x t0 ht).2.1)
      _ = 0 := integral_zero _ _
  have hz : deriv (energy u) t0 = 0 := by rw [hthird, hintzero, mul_zero]
  have hetzero : (∫ x, et u x t0) = 0 := (h_T006.1 t0 ht).2.symm.trans hz
  refine ⟨hfirst, hsecond, hthird, ?_⟩
  simpa only [hetzero] using (h_T006.1 t0 ht).1

theorem T010 (n : ℕ) (m : ℕ) (u : V n × ℝ → W m) (q : W m) (h_T003 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (V n), ∃ R : ℝ,
IsCompact C ∧ 0 < R ∧ C ⊆ innerBox n R ∧ C ⊆ interior (box n R) ∧
IsCompact (box n R) ∧ MeasurableSet (box n R) ∧
volume (box n R) = ENNReal.ofReal ((2*R)^n) ∧ volume (box n R) < ⊤ ∧
(∀ x, x ∉ C → ∀ r ∈ Set.Icc (t0/2) (3*t0/2), u (x,r) = q) ∧
(∀ k : ℕ, 0 < k → ∀ x, x ∉ C → ∀ r ∈ Set.Ioo (t0/2) (3*t0/2),
iteratedFDeriv ℝ k u (x,r) = 0 ) ∧ (∀ f ∈ fields u, ∀ r ∈ Set.Ioo (t0/2) (3*t0/2),
Continuous (fun x => f (x,r)) ∧
(∀ x, x ∉ C → f (x,r) = 0) ∧
HasCompactSupport (fun x => f (x,r)) ∧ Integrable (fun x => f (x,r)) ∧
(∃ K : ℝ, 0 ≤ K ∧ (∀ x ∈ box n R, |f (x,r)| ≤ K) ∧
(∫ x, |f (x,r)|) ≤ K * (volume (box n R)).toReal) ∧
(∃ U : Set (V n), IsOpen U ∧ frontier (box n R) ⊆ U ∧ ∀ x ∈ U, f (x,r) = 0))) ∧ (∀ r : ℝ, 0 < r → Integrable (fun x => e u x r))) (h_T006 : (∀ t0 : ℝ, 0 < t0 →
HasDerivAt (energy u) (∫ x, et u x t0) t0 ∧
deriv (energy u) t0 = ∫ x, et u x t0) ∧ DifferentiableOn ℝ (energy u) (Set.Ioi 0)) (h_T009 : ∀ t0 : ℝ, 0 < t0 →
deriv (energy u) t0 = 2*(∫ x, A u x t0) + 2*(∑ j, ∫ x, B u j x t0) ∧
deriv (energy u) t0 = 2*(∫ x, A u x t0) - 2*(∑ j, ∫ x, T u j x t0) ∧
deriv (energy u) t0 = 2*(∫ x, inner ℝ (ut u x t0) (utt u x t0 - lap u x t0)) ∧
HasDerivAt (energy u) 0 t0) :
    (∀ r : ℝ, 0 < r → Integrable (fun x => e u x r)) ∧
DifferentiableOn ℝ (energy u) (Set.Ioi 0) ∧
(∀ r : ℝ, 0 < r → deriv (energy u) r = 0) ∧
(∀ s t : ℝ, 0 < s → 0 < t → energy u s = energy u t) := by
  have hzero : ∀ r : ℝ, 0 < r → deriv (energy u) r = 0 := by
    intro r hr
    exact (h_T009 r hr).2.2.2.deriv
  refine ⟨h_T003.2, h_T006.2, hzero, ?_⟩
  have hinterval : ∀ a b : ℝ, 0 < a → a < b → energy u b = energy u a := by
    intro a b ha hab
    have hdiff : DifferentiableOn ℝ (energy u) (Set.Icc a b) := by
      intro x hx
      exact ((h_T009 x (lt_of_lt_of_le ha hx.1)).2.2.2).differentiableAt.differentiableWithinAt
    have hwithin : ∀ x ∈ Set.Icc a b, derivWithin (energy u) (Set.Icc a b) x = 0 := by
      intro x hx
      exact ((h_T009 x (lt_of_lt_of_le ha hx.1)).2.2.2).hasDerivWithinAt.derivWithin
        (uniqueDiffOn_Icc hab x hx)
    have hbound : ∀ x ∈ Set.Ico a b, ‖derivWithin (energy u) (Set.Icc a b) x‖ ≤ (0 : ℝ) := by
      intro x hx
      rw [hwithin x ⟨hx.1, le_of_lt hx.2⟩, norm_zero]
    have h := norm_image_sub_le_of_norm_deriv_le_segment hdiff hbound b ⟨le_of_lt hab, le_rfl⟩
    simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using h
  intro s t hs ht
  rcases lt_trichotomy s t with hst | hst | hts
  · exact (hinterval s t hs hst).symm
  · rw [hst]
  · exact hinterval t s ht hts

set_option Elab.async false in
theorem P (n : ℕ) (m : ℕ) (u : V n × ℝ → W m) (q : W m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ u (domain n)) (h_H003 : ‖q‖ = 1) (h_H004 : ∀ x t, 0 < t → ‖u (x,t)‖ = 1) (h_H005 : ∀ x t, 0 < t → ∃ a : ℝ, utt u x t - lap u x t = a • u (x,t)) (h_H006 : ∀ s t : ℝ, 0 < s → s < t → ∃ C : Set (V n), IsCompact C ∧ ∀ x, x ∉ C → ∀ r ∈ Set.Icc s t, u (x,r) = q) :
    (∀ r : ℝ, 0 < r → Integrable (fun x => e u x r)) ∧
DifferentiableOn ℝ (energy u) (Set.Ioi 0) ∧
(∀ r : ℝ, 0 < r → deriv (energy u) r = 0) ∧
(∀ s t : ℝ, 0 < s → 0 < t → energy u s = energy u t) := by
  have h_T002 : ∀ t0 : ℝ, 0 < t0 → ∃ C : Set (V n), ∃ R : ℝ,
IsCompact C ∧ 0 < R ∧ C ⊆ innerBox n R ∧ C ⊆ interior (box n R) ∧
IsCompact (box n R) ∧ MeasurableSet (box n R) ∧
volume (box n R) = ENNReal.ofReal ((2*R)^n) ∧ volume (box n R) < ⊤ ∧
(∀ x, x ∉ C → ∀ r ∈ Set.Icc (t0/2) (3*t0/2), u (x,r) = q) ∧
(∀ k : ℕ, 0 < k → ∀ x, x ∉ C → ∀ r ∈ Set.Ioo (t0/2) (3*t0/2),
iteratedFDeriv ℝ k u (x,r) = 0) := @T002 n m u q h_H001 h_H002 h_H006
  have h_T003 : (∀ t0 : ℝ, 0 < t0 → ∃ C : Set (V n), ∃ R : ℝ,
IsCompact C ∧ 0 < R ∧ C ⊆ innerBox n R ∧ C ⊆ interior (box n R) ∧
IsCompact (box n R) ∧ MeasurableSet (box n R) ∧
volume (box n R) = ENNReal.ofReal ((2*R)^n) ∧ volume (box n R) < ⊤ ∧
(∀ x, x ∉ C → ∀ r ∈ Set.Icc (t0/2) (3*t0/2), u (x,r) = q) ∧
(∀ k : ℕ, 0 < k → ∀ x, x ∉ C → ∀ r ∈ Set.Ioo (t0/2) (3*t0/2),
iteratedFDeriv ℝ k u (x,r) = 0 ) ∧ (∀ f ∈ fields u, ∀ r ∈ Set.Ioo (t0/2) (3*t0/2),
Continuous (fun x => f (x,r)) ∧
(∀ x, x ∉ C → f (x,r) = 0) ∧
HasCompactSupport (fun x => f (x,r)) ∧ Integrable (fun x => f (x,r)) ∧
(∃ K : ℝ, 0 ≤ K ∧ (∀ x ∈ box n R, |f (x,r)| ≤ K) ∧
(∫ x, |f (x,r)|) ≤ K * (volume (box n R)).toReal) ∧
(∃ U : Set (V n), IsOpen U ∧ frontier (box n R) ⊆ U ∧ ∀ x ∈ U, f (x,r) = 0))) ∧ (∀ r : ℝ, 0 < r → Integrable (fun x => e u x r)) := @T003 n m u q h_T002 h_H002
  have h_T004 : ContDiffOn ℝ ∞ (fun p : V n × ℝ => e u p.1 p.2) (domain n) ∧
(∀ j : Fin n, ContDiffOn ℝ ∞ (fun p : V n × ℝ => g u j p.1 p.2) (domain n)) ∧
(∀ x t, 0 < t →
(∀ j : Fin n, deriv (fun s => ux u j x s) t = uxt u j x t) ∧
et u x t = 2*A u x t + 2*(∑ j, B u j x t) ∧
(∀ j : Fin n, dg u j x t = B u j x t + T u j x t)) ∧
(∀ f ∈ fields u, ContinuousOn f (domain n)) ∧
(∀ j : Fin n, ContinuousOn (fun p : V n × ℝ => uxt u j p.1 p.2) (domain n)) := @T004 n m u q h_H002
  have h_T005 : ∀ t0 : ℝ, 0 < t0 → ∃ η R K : ℝ,
0 < η ∧ η < t0 ∧ 0 < R ∧ 0 ≤ K ∧
Integrable ((box n R).indicator (fun _ : V n => K)) ∧
(∀ h : ℝ, 0 < |h| → |h| < η →
Integrable (fun x => (e u x (t0+h) - e u x t0)/h) ∧
(∀ x : V n, |(e u x (t0+h) - e u x t0)/h| ≤
(box n R).indicator (fun _ : V n => K) x)) ∧
(∀ x : V n, Filter.Tendsto
(fun h : ℝ => (e u x (t0+h) - e u x t0)/h)
(nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (et u x t0))) := @T005 n m u q h_T003 h_T004
  have h_T006 : (∀ t0 : ℝ, 0 < t0 →
HasDerivAt (energy u) (∫ x, et u x t0) t0 ∧
deriv (energy u) t0 = ∫ x, et u x t0) ∧ DifferentiableOn ℝ (energy u) (Set.Ioi 0) := @T006 n m u q h_T003 h_T004 h_T005
  have h_T001 : ∀ x t, 0 < t →
inner ℝ (u (x,t)) (ut u x t) = 0 ∧
inner ℝ (ut u x t) (utt u x t - lap u x t) = 0 ∧
inner ℝ (u (x,t)) (utt u x t) = -(‖ut u x t‖^2) ∧
(∀ j : Fin n, inner ℝ (u (x,t)) (uxx u j x t) = -(‖ux u j x t‖^2)) ∧
(∀ a : ℝ, utt u x t - lap u x t = a • u (x,t) →
a = (∑ j, ‖ux u j x t‖^2) - ‖ut u x t‖^2) ∧
utt u x t - lap u x t = ((∑ j, ‖ux u j x t‖^2) - ‖ut u x t‖^2) • u (x,t) := @T001 n m u q h_H002 h_H004 h_H005
  have h_T007 : ∀ t0 : ℝ, 0 < t0 → ∀ j : Fin n,
Integrable (fun x => dg u j x t0) ∧ (∫ x, dg u j x t0) = 0 := @T007 n m u q h_T003 h_T004
  have h_T008 : ∀ t0 : ℝ, 0 < t0 → ∀ j : Fin n,
Integrable (fun x => dg u j x t0) ∧ Integrable (fun x => B u j x t0) ∧
Integrable (fun x => T u j x t0) ∧
(∫ x, dg u j x t0) = 0 ∧
(∫ x, B u j x t0) = -(∫ x, T u j x t0) ∧
(∫ x, inner ℝ (ux u j x t0) (uxt u j x t0)) =
-(∫ x, inner ℝ (ut u x t0) (uxx u j x t0)) := @T008 n m u q h_T003 h_T004 h_T007
  have h_T009 : ∀ t0 : ℝ, 0 < t0 →
deriv (energy u) t0 = 2*(∫ x, A u x t0) + 2*(∑ j, ∫ x, B u j x t0) ∧
deriv (energy u) t0 = 2*(∫ x, A u x t0) - 2*(∑ j, ∫ x, T u j x t0) ∧
deriv (energy u) t0 = 2*(∫ x, inner ℝ (ut u x t0) (utt u x t0 - lap u x t0)) ∧
HasDerivAt (energy u) 0 t0 := @T009 n m u q h_T001 h_T003 h_T004 h_T006 h_T008
  have h_T010 : (∀ r : ℝ, 0 < r → Integrable (fun x => e u x r)) ∧
DifferentiableOn ℝ (energy u) (Set.Ioi 0) ∧
(∀ r : ℝ, 0 < r → deriv (energy u) r = 0) ∧
(∀ s t : ℝ, 0 < s → 0 < t → energy u s = energy u t) := @T010 n m u q h_T003 h_T006 h_T009
  exact h_T010

#check @P
#print axioms P

end Translation

namespace AuditBExport
set_option autoImplicit false
set_option Elab.async false in
theorem P (n : ℕ) (m : ℕ) (u : V n × ℝ → W m) (q : W m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ u (domain n)) (h_H003 : ‖q‖ = 1) (h_H004 : ∀ x t, 0 < t → ‖u (x,t)‖ = 1) (h_H005 : ∀ x t, 0 < t → ∃ a : ℝ, utt u x t - lap u x t = a • u (x,t)) (h_H006 : ∀ s t : ℝ, 0 < s → s < t → ∃ C : Set (V n), IsCompact C ∧ ∀ x, x ∉ C → ∀ r ∈ Set.Icc s t, u (x,r) = q) : (∀ r : ℝ, 0 < r → Integrable (fun x => e u x r)) ∧
DifferentiableOn ℝ (energy u) (Set.Ioi 0) ∧
(∀ r : ℝ, 0 < r → deriv (energy u) r = 0) ∧
(∀ s t : ℝ, 0 < s → 0 < t → energy u s = energy u t) := by
  exact @Translation.P n m u q h_H001 h_H002 h_H003 h_H004 h_H005 h_H006

#check @P
#print axioms P
end AuditBExport
