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

#check @T007
#print axioms T007

end Translation
