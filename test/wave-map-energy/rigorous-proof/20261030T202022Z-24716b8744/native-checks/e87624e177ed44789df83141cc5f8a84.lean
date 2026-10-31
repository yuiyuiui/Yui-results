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

#check @T003
#print axioms T003

end Translation
