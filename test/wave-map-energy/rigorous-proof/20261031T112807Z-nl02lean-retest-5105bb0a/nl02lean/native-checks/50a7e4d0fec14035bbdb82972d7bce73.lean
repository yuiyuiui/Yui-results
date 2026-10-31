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

namespace Translation
set_option autoImplicit false

theorem T003 (n : ℕ) (m : ℕ) (u : WaveMap.Space n × ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ (∞ : ℕ∞ω) u (WaveMap.positive n)) (h_T002 : ∀ t0 : ℝ, 0 < t0 → ∃ (C : Set (WaveMap.Space n)) (R : ℝ),
  IsCompact C ∧ 0 < R ∧ C ⊆ WaveMap.openBox n R ∧
  (∀ x : WaveMap.Space n, x ∉ C → ∀ r ∈ WaveMap.timeInterval t0, u (x,r) = q) ∧
  (∀ (k : ℕ) (x : WaveMap.Space n) (r : ℝ), 0 < k → x ∉ C →
    r ∈ WaveMap.timeInterior t0 → iteratedFDeriv ℝ k u (x,r) = 0)) :
    (∀ t : ℝ, 0 < t → Integrable (fun x => WaveMap.density u x t)) ∧
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
    (∀ x ∈ WaveMap.box n R, ∀ r ∈ Icc (t0 - η) (t0 + η), |WaveMap.densityTime u x r| ≤ B) := by
  classical
  have smoothD : ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (f : WaveMap.Space n × ℝ → F), ContDiffOn ℝ (∞ : ℕ∞ω) f (WaveMap.positive n) → ContDiffOn ℝ (∞ : ℕ∞ω) (fun p : WaveMap.Space n × ℝ => deriv (fun r => f (p.1,r)) p.2) (WaveMap.positive n) ∧ ∀ j : Fin n, ContDiffOn ℝ (∞ : ℕ∞ω) (fun p : WaveMap.Space n × ℝ => WaveMap.spatial (fun y => f (y,p.2)) j p.1) (WaveMap.positive n) := by
    intro F _ _ f hf
    have ho : IsOpen (WaveMap.positive n) := isOpen_lt continuous_const continuous_snd
    constructor
    · intro p hp
      have h : ContDiffAt ℝ (∞ : ℕ∞ω) (Function.uncurry (fun (z : WaveMap.Space n × ℝ) (r : ℝ) => f (z.1,r))) (p,p.2) :=
        (hf.contDiffAt (ho.mem_nhds hp)).comp _ (contDiffAt_fst.fst.prodMk contDiffAt_snd)
      have hh : ContDiffAt ℝ (∞ : ℕ∞ω) (fun z : WaveMap.Space n × ℝ => fderiv ℝ (fun r => f (z.1,r)) z.2) p :=
        ContDiffAt.fderiv (f := fun (z : WaveMap.Space n × ℝ) (r : ℝ) => f (z.1,r)) (g := fun z => z.2) h contDiffAt_snd (by simp)
      exact (hh.clm_apply (contDiffAt_const (c := (1 : ℝ)))).contDiffWithinAt
    · intro j p hp
      have h : ContDiffAt ℝ (∞ : ℕ∞ω) (Function.uncurry (fun (z : WaveMap.Space n × ℝ) (y : WaveMap.Space n) => f (y,z.2))) (p,p.1) :=
        (hf.contDiffAt (ho.mem_nhds hp)).comp _ (contDiffAt_snd.prodMk contDiffAt_fst.snd)
      have hh : ContDiffAt ℝ (∞ : ℕ∞ω) (fun z : WaveMap.Space n × ℝ => fderiv ℝ (fun y => f (y,z.2)) z.1) p :=
        ContDiffAt.fderiv (f := fun (z : WaveMap.Space n × ℝ) (y : WaveMap.Space n) => f (y,z.2)) (g := fun z => z.1) h contDiffAt_fst (by simp)
      exact (hh.clm_apply (contDiffAt_const (c := PiLp.single 2 j 1))).contDiffWithinAt
  have sut : ContDiffOn ℝ (∞ : ℕ∞ω) (fun p => WaveMap.ut u p.1 p.2) (WaveMap.positive n) := (smoothD _ u h_H002).1
  have sux (j : Fin n) : ContDiffOn ℝ (∞ : ℕ∞ω) (fun p => WaveMap.ux u j p.1 p.2) (WaveMap.positive n) := (smoothD _ u h_H002).2 j
  have sutt : ContDiffOn ℝ (∞ : ℕ∞ω) (fun p => WaveMap.utt u p.1 p.2) (WaveMap.positive n) := (smoothD _ _ sut).1
  have sutx (j : Fin n) : ContDiffOn ℝ (∞ : ℕ∞ω) (fun p => WaveMap.utx u j p.1 p.2) (WaveMap.positive n) := (smoothD _ _ sut).2 j
  have suxx (j : Fin n) : ContDiffOn ℝ (∞ : ℕ∞ω) (fun p => WaveMap.uxx u j p.1 p.2) (WaveMap.positive n) := (smoothD _ _ (sux j)).2 j
  have se : ContDiffOn ℝ (∞ : ℕ∞ω) (fun p => WaveMap.density u p.1 p.2) (WaveMap.positive n) := by
    exact (sut.norm_sq (𝕜 := ℝ)).add (ContDiffOn.sum (fun j _ => (sux j).norm_sq (𝕜 := ℝ)))
  have set : ContDiffOn ℝ (∞ : ℕ∞ω) (fun p => WaveMap.densityTime u p.1 p.2) (WaveMap.positive n) := (smoothD _ _ se).1
  have sk : ContDiffOn ℝ (∞ : ℕ∞ω) (fun p => WaveMap.kineticProduct u p.2 p.1) (WaveMap.positive n) := sut.inner ℝ sutt
  have sg (j : Fin n) : ContDiffOn ℝ (∞ : ℕ∞ω) (fun p => WaveMap.gradientProduct u j p.2 p.1) (WaveMap.positive n) := (sux j).inner ℝ (sutx j)
  have sl (j : Fin n) : ContDiffOn ℝ (∞ : ℕ∞ω) (fun p => WaveMap.laplaceProduct u j p.2 p.1) (WaveMap.positive n) := sut.inner ℝ (suxx j)
  have sf (j : Fin n) : ContDiffOn ℝ (∞ : ℕ∞ω) (fun p => WaveMap.flux u j p.2 p.1) (WaveMap.positive n) := sut.inner ℝ (sux j)
  have sdf (j : Fin n) : ContDiffOn ℝ (∞ : ℕ∞ω) (fun p => WaveMap.spatial (WaveMap.flux u j p.2) j p.1) (WaveMap.positive n) := (smoothD _ _ (sf j)).2 j

  have termcont : ∀ (r : ℝ), 0 < r → ∀ (j : Fin n) (f : WaveMap.Space n → ℝ), f ∈ WaveMap.terms u r j → Continuous f := by
    intro r hr j f hf
    have slice (g : WaveMap.Space n × ℝ → ℝ) (hg : ContDiffOn ℝ (∞ : ℕ∞ω) g (WaveMap.positive n)) : Continuous (fun x => g (x,r)) := by
      apply continuous_iff_continuousAt.mpr
      intro x
      exact (hg.contDiffAt ((isOpen_lt continuous_const continuous_snd : IsOpen (WaveMap.positive n)).mem_nhds hr)).continuousAt.comp (continuousAt_id.prodMk continuousAt_const)
    simp only [WaveMap.terms, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact slice _ se
    · exact slice _ set
    · exact slice _ sk
    · exact slice _ (sg j)
    · exact slice _ (sl j)
    · exact slice _ (sf j)
    · exact slice _ (sdf j)

  have zeroD : ∀ (C : Set (WaveMap.Space n)) (t0 : ℝ), IsCompact C → ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (f : WaveMap.Space n × ℝ → F) (c : F), (∀ x, x ∉ C → ∀ r ∈ WaveMap.timeInterior t0, f (x,r) = c) → (∀ x, x ∉ C → ∀ r ∈ WaveMap.timeInterior t0, deriv (fun s => f (x,s)) r = 0) ∧ (∀ j : Fin n, ∀ x, x ∉ C → ∀ r ∈ WaveMap.timeInterior t0, WaveMap.spatial (fun y => f (y,r)) j x = 0) := by
    intro C t0 hc F _ _ f c hf
    constructor
    · intro x hx r hr
      have hh : (fun s => f (x,s)) =ᶠ[nhds r] (fun _ => c) :=
        Filter.Eventually.mono (isOpen_Ioo.mem_nhds hr) (fun s hs => hf x hx s hs)
      simpa using hh.deriv_eq
    · intro j x hx r hr
      have hh : (fun y => f (y,r)) =ᶠ[nhds x] (fun _ => c) :=
        Filter.Eventually.mono (hc.isClosed.isOpen_compl.mem_nhds hx) (fun y hy => hf y hy r hr)
      simp [WaveMap.spatial, hh.fderiv_eq]

  have termsupport : ∀ (C : Set (WaveMap.Space n)) (t0 : ℝ), IsCompact C → (∀ x, x ∉ C → ∀ r ∈ WaveMap.timeInterval t0, u (x,r) = q) → ∀ r ∈ WaveMap.timeInterior t0, ∀ (j : Fin n) (f : WaveMap.Space n → ℝ), f ∈ WaveMap.terms u r j → Function.support f ⊆ C := by
    intro C t0 hc hu
    have hu' : ∀ x, x ∉ C → ∀ r ∈ WaveMap.timeInterior t0, u (x,r) = q := by
      intro x hx r hr
      exact hu x hx r ⟨hr.1.le,hr.2.le⟩
    have zu := zeroD C t0 hc _ u q hu'
    have zut : ∀ x, x ∉ C → ∀ r ∈ WaveMap.timeInterior t0, WaveMap.ut u x r = 0 := zu.1
    have zux : ∀ j, ∀ x, x ∉ C → ∀ r ∈ WaveMap.timeInterior t0, WaveMap.ux u j x r = 0 := zu.2
    have ze : ∀ x, x ∉ C → ∀ r ∈ WaveMap.timeInterior t0, WaveMap.density u x r = 0 := by
      intro x hx r hr
      simp [WaveMap.density, zut x hx r hr, fun j => zux j x hx r hr]
    have zet : ∀ x, x ∉ C → ∀ r ∈ WaveMap.timeInterior t0, WaveMap.densityTime u x r = 0 :=
      (zeroD C t0 hc ℝ (fun p => WaveMap.density u p.1 p.2) 0 ze).1
    have zf (j : Fin n) : ∀ x, x ∉ C → ∀ r ∈ WaveMap.timeInterior t0, WaveMap.flux u j r x = 0 := by
      intro x hx r hr
      simp [WaveMap.flux, zut x hx r hr]
    have zdf (j : Fin n) : ∀ x, x ∉ C → ∀ r ∈ WaveMap.timeInterior t0, WaveMap.spatial (WaveMap.flux u j r) j x = 0 :=
      (zeroD C t0 hc ℝ (fun p => WaveMap.flux u j p.2 p.1) 0 (zf j)).2 j
    intro r hr j f hf x hx
    by_contra hxc
    have heq : f x = 0 := by
      simp only [WaveMap.terms, List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ze x hxc r hr
      · exact zet x hxc r hr
      · simp [WaveMap.kineticProduct, zut x hxc r hr]
      · simp [WaveMap.gradientProduct, zux j x hxc r hr]
      · simp [WaveMap.laplaceProduct, zut x hxc r hr]
      · exact zf j x hxc r hr
      · exact zdf j x hxc r hr
    exact hx heq

  have boxfacts : ∀ R : ℝ, 0 < R → IsCompact (WaveMap.box n R) ∧ volume (WaveMap.box n R) = ENNReal.ofReal ((2 * R) ^ n) := by
    intro R hR
    have he : WaveMap.box n R = (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)) ⁻¹' Set.pi Set.univ (fun _ => Icc (-R) R) := by
      ext x
      change (∀ j, x j ∈ Icc (-R) R) ↔ (∀ j ∈ (Set.univ : Set (Fin n)), x j ∈ Icc (-R) R)
      simp only [mem_univ, forall_true_left]
    constructor
    · rw [he]
      exact (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).isCompact_preimage.mpr (isCompact_univ_pi fun _ => isCompact_Icc)
    · have he' : WaveMap.box n R = (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm ⁻¹' Set.pi Set.univ (fun _ : Fin n => Icc (-R) R) := by
        ext x
        change (∀ j, x j ∈ Icc (-R) R) ↔ (∀ j ∈ (Set.univ : Set (Fin n)), x j ∈ Icc (-R) R)
        simp only [mem_univ, forall_true_left]
      rw [he', (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n)).measure_preimage_equiv, volume_pi_pi]
      simp only [Real.volume_Icc, sub_neg_eq_add, ← two_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact (ENNReal.ofReal_pow (by positivity : 0 ≤ 2 * R) n).symm
  refine ⟨?_, se, set, ?_⟩
  · intro t ht
    obtain ⟨C, R, hc, hR, hsub, hu, hd⟩ := h_T002 t ht
    let j : Fin n := ⟨0, by omega⟩
    have htI : t ∈ WaveMap.timeInterior t := by
      change t / 2 < t ∧ t < 3 * t / 2
      constructor <;> linarith
    have hf : (fun x => WaveMap.density u x t) ∈ WaveMap.terms u t j := by simp [WaveMap.terms]
    have hcont := termcont t ht j _ hf
    have hsupp := termsupport C t hc hu t htI j _ hf
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_support_subset_isCompact hc hsupp)
  · intro t0 ht0
    obtain ⟨C, R, hc, hR, hsub, hu, hd⟩ := h_T002 t0 ht0
    obtain ⟨hQ, hvol⟩ := boxfacts R hR
    let η : ℝ := t0 / 4
    have hη : 0 < η := by dsimp [η]; positivity
    have hint : Icc (t0 - η) (t0 + η) ⊆ WaveMap.timeInterior t0 := by
      intro r hr
      constructor <;> dsimp [η] at * <;> linarith [hr.1,hr.2]
    have hpos : ∀ r ∈ WaveMap.timeInterior t0, 0 < r := by
      intro r hr
      have := hr.1
      change t0 / 2 < r at this
      linarith
    have hcts : ContinuousOn (fun p : WaveMap.Space n × ℝ => WaveMap.densityTime u p.1 p.2) ((WaveMap.box n R) ×ˢ Icc (t0 - η) (t0 + η)) :=
      set.continuousOn.mono (by intro p hp; exact hpos p.2 (hint hp.2))
    obtain ⟨B, hB⟩ := (hQ.prod isCompact_Icc).exists_bound_of_continuousOn hcts
    refine ⟨C, R, η, max B 0, hc, hR, hη, le_max_right _ _, hsub, hQ, hvol, ?_, hint, hu, hd, ?_, ?_⟩
    · rw [hvol]
      exact ENNReal.ofReal_ne_top
    · intro r hr j f hf
      have hcont := termcont r (hpos r hr) j f hf
      have hsupp := termsupport C t0 hc hu r hr j f hf
      obtain ⟨K, hK⟩ := hQ.exists_bound_of_continuousOn hcont.continuousOn
      refine ⟨hcont, hsupp, ⟨max K 0, le_max_right _ _, ?_⟩, hcont.measurable, ?_⟩
      · intro x hx
        have hb : |f x| ≤ K := by simpa only [Real.norm_eq_abs] using hK x hx
        exact hb.trans (le_max_left _ _)
      · exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_support_subset_isCompact hc hsupp)
    · intro x hx r hr
      have hb : |WaveMap.densityTime u x r| ≤ B := by simpa only [Real.norm_eq_abs] using hB (x,r) ⟨hx,hr⟩
      exact hb.trans (le_max_left _ _)

#check @T003
#print axioms T003

end Translation
