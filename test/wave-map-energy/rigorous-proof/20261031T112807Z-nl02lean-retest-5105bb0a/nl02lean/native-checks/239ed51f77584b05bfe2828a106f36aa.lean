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

theorem T002 (n : ℕ) (m : ℕ) (u : WaveMap.Space n × ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ (∞ : ℕ∞ω) u (WaveMap.positive n)) (h_H006 : ∀ (s t : ℝ), 0 < s → s < t → ∃ C : Set (WaveMap.Space n), IsCompact C ∧ ∀ x : WaveMap.Space n, x ∉ C → ∀ r ∈ Icc s t, u (x,r) = q) :
    ∀ t0 : ℝ, 0 < t0 → ∃ (C : Set (WaveMap.Space n)) (R : ℝ),
  IsCompact C ∧ 0 < R ∧ C ⊆ WaveMap.openBox n R ∧
  (∀ x : WaveMap.Space n, x ∉ C → ∀ r ∈ WaveMap.timeInterval t0, u (x,r) = q) ∧
  (∀ (k : ℕ) (x : WaveMap.Space n) (r : ℝ), 0 < k → x ∉ C →
    r ∈ WaveMap.timeInterior t0 → iteratedFDeriv ℝ k u (x,r) = 0) := by
  intro t0 ht0
  obtain ⟨C, hC, hconst⟩ := h_H006 (t0 / 2) (3 * t0 / 2) (by linarith) (by linarith)
  obtain ⟨R, hR, hbound⟩ := hC.isBounded.exists_pos_norm_lt
  refine ⟨C, R, hC, hR, ?_, ?_, ?_⟩
  · intro x hx
    change ∀ j, x j ∈ Ioo (-R) R
    intro j
    have hj : ‖x j‖ < R := lt_of_le_of_lt (PiLp.norm_apply_le x j) (hbound x hx)
    simpa only [Real.norm_eq_abs, abs_lt, Set.mem_Ioo] using hj
  · intro x hx r hr
    exact hconst x hx r hr
  · intro k x r hk hx hr
    have hlocal : u =ᶠ[nhds (x, r)] (fun _ : WaveMap.Space n × ℝ => q) := by
      have hopen : IsOpen (Cᶜ ×ˢ WaveMap.timeInterior t0) :=
        hC.isClosed.isOpen_compl.prod isOpen_Ioo
      have hmem : (x, r) ∈ Cᶜ ×ˢ WaveMap.timeInterior t0 := ⟨hx, hr⟩
      filter_upwards [hopen.mem_nhds hmem] with p hp
      exact hconst p.1 hp.1 p.2 ⟨le_of_lt hp.2.1, le_of_lt hp.2.2⟩
    have heq := (hlocal.iteratedFDeriv ℝ k).eq_of_nhds
    rw [heq, iteratedFDeriv_const_of_ne (Nat.ne_of_gt hk)]
    rfl

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

theorem T001 (n : ℕ) (m : ℕ) (u : WaveMap.Space n × ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H002 : ContDiffOn ℝ (∞ : ℕ∞ω) u (WaveMap.positive n)) (h_H004 : ∀ (x : WaveMap.Space n) (t : ℝ), 0 < t → ‖u (x,t)‖ = 1) (h_H005 : ∀ (x : WaveMap.Space n) (t : ℝ), 0 < t → ∃ a : ℝ, WaveMap.utt u x t - WaveMap.laplace u x t = a • u (x,t)) :
    ∀ (x : WaveMap.Space n) (t : ℝ), 0 < t →
  inner ℝ (u (x,t)) (WaveMap.ut u x t) = 0 ∧
  inner ℝ (WaveMap.ut u x t) (WaveMap.utt u x t - WaveMap.laplace u x t) = 0 ∧
  inner ℝ (u (x,t)) (WaveMap.utt u x t) = -(‖WaveMap.ut u x t‖ ^ 2) ∧
  (∀ j : Fin n, inner ℝ (u (x,t)) (WaveMap.uxx u j x t) = -(‖WaveMap.ux u j x t‖ ^ 2)) ∧
  (∀ a : ℝ, WaveMap.utt u x t - WaveMap.laplace u x t = a • u (x,t) →
    a = (∑ j, ‖WaveMap.ux u j x t‖ ^ 2) - ‖WaveMap.ut u x t‖ ^ 2) ∧
  WaveMap.utt u x t - WaveMap.laplace u x t =
    ((∑ j, ‖WaveMap.ux u j x t‖ ^ 2) - ‖WaveMap.ut u x t‖ ^ 2) • u (x,t) := by
  have unit_derivatives : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
      (f : E → WaveMap.Space m) (s : Set E),
      IsOpen s → ContDiffOn ℝ (∞ : ℕ∞ω) f s →
      (∀ y ∈ s, ‖f y‖ = 1) →
      ∀ x ∈ s, ∀ v : E,
        inner ℝ (f x) (fderiv ℝ f x v) = 0 ∧
        inner ℝ (f x) (fderiv ℝ (fun y => fderiv ℝ f y v) x v) =
          -(‖fderiv ℝ f x v‖ ^ 2) := by
    intro E _ _ f s hs hf hn
    have hd : ∀ x ∈ s, DifferentiableAt ℝ f x := by
      intro x hx
      exact (hf.contDiffAt (hs.mem_nhds hx)).differentiableAt (by simp)
    have hfirst : ∀ x ∈ s, ∀ v : E, inner ℝ (f x) (fderiv ℝ f x v) = 0 := by
      intro x hx v
      have he : (fun y => inner ℝ (f y) (f y)) =ᶠ[nhds x] (fun _ => (1 : ℝ)) := by
        filter_upwards [hs.mem_nhds hx] with y hy
        simp [real_inner_self_eq_norm_sq, hn y hy]
      have hz : fderiv ℝ (fun y => inner ℝ (f y) (f y)) x v = 0 := by
        rw [he.fderiv_eq]
        simp
      rw [fderiv_inner_apply ℝ (hd x hx) (hd x hx), real_inner_comm (f x) (fderiv ℝ f x v)] at hz
      linarith
    intro x hx v
    refine ⟨hfirst x hx v, ?_⟩
    have hdf : ContDiffOn ℝ (1 : ℕ∞ω) (fun y => fderiv ℝ f y v) s :=
      (hf.fderiv_of_isOpen (m := 1) hs (by decide)).clm_apply contDiffOn_const
    have hdd : DifferentiableAt ℝ (fun y => fderiv ℝ f y v) x :=
      (hdf.contDiffAt (hs.mem_nhds hx)).differentiableAt (by simp)
    have he : (fun y => inner ℝ (f y) (fderiv ℝ f y v)) =ᶠ[nhds x] (fun _ => (0 : ℝ)) := by
      filter_upwards [hs.mem_nhds hx] with y hy
      exact hfirst y hy v
    have hz : fderiv ℝ (fun y => inner ℝ (f y) (fderiv ℝ f y v)) x v = 0 := by
      rw [he.fderiv_eq]
      simp
    rw [fderiv_inner_apply ℝ (hd x hx) hdd, real_inner_self_eq_norm_sq] at hz
    linarith
  intro x t ht
  have htimeSmooth : ContDiffOn ℝ (∞ : ℕ∞ω) (fun r : ℝ => u (x,r)) (Ioi (0 : ℝ)) :=
    h_H002.comp (contDiffOn_const.prodMk contDiffOn_id) (by intro r hr; exact hr)
  have hspaceSmooth : ContDiffOn ℝ (∞ : ℕ∞ω) (fun y : WaveMap.Space n => u (y,t)) univ :=
    h_H002.comp (contDiffOn_id.prodMk contDiffOn_const) (by intro y hy; exact ht)
  have htime := unit_derivatives ℝ (fun r => u (x,r)) (Ioi (0 : ℝ))
    isOpen_Ioi htimeSmooth (fun r hr => h_H004 x r hr) t ht 1
  change inner ℝ (u (x,t)) (WaveMap.ut u x t) = 0 ∧
    inner ℝ (u (x,t)) (WaveMap.utt u x t) = -(‖WaveMap.ut u x t‖ ^ 2) at htime
  have hspace : ∀ j : Fin n, inner ℝ (u (x,t)) (WaveMap.uxx u j x t) =
      -(‖WaveMap.ux u j x t‖ ^ 2) := by
    intro j
    exact (unit_derivatives (WaveMap.Space n) (fun y => u (y,t)) univ
      isOpen_univ hspaceSmooth (fun y _ => h_H004 y t ht) x (mem_univ x)
      (PiLp.single 2 j 1)).2
  obtain ⟨a, ha⟩ := h_H005 x t ht
  have hnormal : inner ℝ (WaveMap.ut u x t)
      (WaveMap.utt u x t - WaveMap.laplace u x t) = 0 := by
    rw [ha, inner_smul_right, real_inner_comm (u (x,t)) (WaveMap.ut u x t),
      htime.1, mul_zero]
  have hu : inner ℝ (u (x,t)) (u (x,t)) = 1 := by
    rw [real_inner_self_eq_norm_sq, h_H004 x t ht]
    norm_num
  have hcoefficient : ∀ a : ℝ, WaveMap.utt u x t - WaveMap.laplace u x t = a • u (x,t) →
      a = (∑ j, ‖WaveMap.ux u j x t‖ ^ 2) - ‖WaveMap.ut u x t‖ ^ 2 := by
    intro b hb
    have heq := congrArg (fun v : WaveMap.Space m => inner ℝ (u (x,t)) v) hb
    rw [inner_sub_right, inner_smul_right, hu, mul_one, htime.2] at heq
    simp only [WaveMap.laplace, inner_sum, hspace, Finset.sum_neg_distrib] at heq
    linarith
  refine ⟨htime.1, hnormal, htime.2, hspace, hcoefficient, ?_⟩
  rw [ha, hcoefficient a ha]

theorem T004 (n : ℕ) (m : ℕ) (u : WaveMap.Space n × ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H002 : ContDiffOn ℝ (∞ : ℕ∞ω) u (WaveMap.positive n)) :
    ∀ (x : WaveMap.Space n) (t : ℝ), 0 < t →
  HasDerivAt (WaveMap.density u x) (WaveMap.densityTime u x t) t ∧
  WaveMap.densityTime u x t = 2 * WaveMap.kineticProduct u t x +
    2 * ∑ j, WaveMap.gradientProduct u j t x := by
  have hderivs : ∀ (x : WaveMap.Space n) (t : ℝ), 0 < t →
      HasDerivAt (WaveMap.ut u x) (WaveMap.utt u x t) t ∧
        ∀ j : Fin n, HasDerivAt (fun r => WaveMap.ux u j x r) (WaveMap.utx u j x t) t := by
    have hopen : IsOpen (WaveMap.positive n) := isOpen_lt continuous_const continuous_snd
    have hsmooth (y : WaveMap.Space n) (s : ℝ) (hs : 0 < s) :
        ContDiffAt ℝ (∞ : ℕ∞ω) u (y, s) :=
      h_H002.contDiffAt (hopen.mem_nhds hs)
    have htime (y : WaveMap.Space n) (s : ℝ) (hs : 0 < s) :
        WaveMap.ut u y s = fderiv ℝ u (y, s) (0, 1) := by
      have hd := ((hsmooth y s hs).differentiableAt (by simp)).hasFDerivAt
      simpa [WaveMap.ut, Function.comp_def] using
        (hd.comp_hasDerivAt s ((hasDerivAt_const s y).prodMk (hasDerivAt_id s))).deriv
    have hspace (y : WaveMap.Space n) (s : ℝ) (hs : 0 < s) (j : Fin n) :
        WaveMap.ux u j y s =
          fderiv ℝ u (y, s) (PiLp.single 2 j 1, 0) := by
      have hd := ((hsmooth y s hs).differentiableAt (by simp)).hasFDerivAt
      have he := (hd.comp y (hasFDerivAt_prodMk_left (𝕜 := ℝ) y s)).fderiv
      simp only [Function.comp_def] at he
      simp only [WaveMap.ux, WaveMap.spatial, he, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.inl_apply]
    intro x t ht
    have h := hsmooth x t ht
    have hdf : DifferentiableAt ℝ (fderiv ℝ u) (x, t) :=
      (h.fderiv_right (m := 1) (by
        change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top)).differentiableAt one_ne_zero
    have hdir (v : WaveMap.Space n × ℝ) :
        HasFDerivAt (fun p => fderiv ℝ u p v)
          ((fderiv ℝ (fderiv ℝ u) (x, t)).flip v) (x, t) := by
      simpa using hdf.hasFDerivAt.clm_apply (hasFDerivAt_const v (x, t))
    have hT : HasFDerivAt (fun p : WaveMap.Space n × ℝ => WaveMap.ut u p.1 p.2)
        ((fderiv ℝ (fderiv ℝ u) (x, t)).flip (0, 1)) (x, t) := by
      apply (hdir (0, 1)).congr_of_eventuallyEq
      filter_upwards [hopen.mem_nhds ht] with p hp
      exact htime p.1 p.2 hp
    constructor
    · exact (hT.comp_hasDerivAt t
        ((hasDerivAt_const t x).prodMk (hasDerivAt_id t))).differentiableAt.hasDerivAt
    · intro j
      have hX : HasFDerivAt (fun p : WaveMap.Space n × ℝ => WaveMap.ux u j p.1 p.2)
          ((fderiv ℝ (fderiv ℝ u) (x, t)).flip (PiLp.single 2 j 1, 0)) (x, t) := by
        apply (hdir (PiLp.single 2 j 1, 0)).congr_of_eventuallyEq
        filter_upwards [hopen.mem_nhds ht] with p hp
        exact hspace p.1 p.2 hp j
      have htx : WaveMap.utx u j x t =
          fderiv ℝ (fderiv ℝ u) (x, t) (PiLp.single 2 j 1, 0) (0, 1) := by
        have he := (hT.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x t)).fderiv
        simp only [Function.comp_def] at he
        simp [WaveMap.utx, WaveMap.spatial, he]
      have hsym := h.isSymmSndFDerivAt (by
        simp only [minSmoothness_of_isRCLikeNormedField]
        change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top)
      have hd := hX.comp_hasDerivAt t
        ((hasDerivAt_const t x).prodMk (hasDerivAt_id t))
      simpa only [Function.comp_def, ContinuousLinearMap.flip_apply,
        htx, hsym.eq (0, 1) (PiLp.single 2 j 1, 0)] using hd
  intro x t ht
  obtain ⟨hT, hX⟩ := hderivs x t ht
  have hd : HasDerivAt (WaveMap.density u x)
      (2 * WaveMap.kineticProduct u t x +
        2 * ∑ j, WaveMap.gradientProduct u j t x) t := by
    change HasDerivAt (fun r => ‖WaveMap.ut u x r‖ ^ 2 +
      ∑ j : Fin n, ‖WaveMap.ux u j x r‖ ^ 2) _ t
    simpa [WaveMap.kineticProduct, WaveMap.gradientProduct,
      Finset.mul_sum] using
      hT.norm_sq.fun_add (HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => (hX j).norm_sq))
  exact ⟨by simpa only [WaveMap.densityTime, hd.deriv] using hd, hd.deriv⟩

theorem T005 (n : ℕ) (m : ℕ) (u : WaveMap.Space n × ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_T003 : (∀ t : ℝ, 0 < t → Integrable (fun x => WaveMap.density u x t)) ∧
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
    (∀ x ∈ WaveMap.box n R, ∀ r ∈ Icc (t0 - η) (t0 + η), |WaveMap.densityTime u x r| ≤ B)) (h_T004 : ∀ (x : WaveMap.Space n) (t : ℝ), 0 < t →
  HasDerivAt (WaveMap.density u x) (WaveMap.densityTime u x t) t ∧
  WaveMap.densityTime u x t = 2 * WaveMap.kineticProduct u t x +
    2 * ∑ j, WaveMap.gradientProduct u j t x) :
    ∀ t0 : ℝ, 0 < t0 → ∃ R η B : ℝ,
  0 < R ∧ 0 < η ∧ 0 ≤ B ∧ Icc (t0 - η) (t0 + η) ⊆ Ioi (0 : ℝ) ∧
  Integrable (WaveMap.bound n R B) ∧
  ∀ h : ℝ, 0 < |h| → |h| < η → ∀ x : WaveMap.Space n,
    |WaveMap.quotient u t0 h x| ≤ WaveMap.bound n R B x := by
  classical
  intro t0 ht0
  rcases h_T003.2.2.2 t0 ht0 with
    ⟨C, R, η, B, hC, hR, hη, hB, hCopen, hbox, hvol, hfinite,
      htime, hu, hiter, hterms, hbound⟩
  have hpositive : Icc (t0 - η) (t0 + η) ⊆ Ioi (0 : ℝ) := by
    intro r hr
    have hr' := (htime hr).1
    change t0 / 2 < r at hr'
    change 0 < r
    linarith
  have hint : Integrable (WaveMap.bound n R B) := by
    exact (integrable_indicator_iff hbox.measurableSet).2
      (integrableOn_const (C := B) hfinite)
  refine ⟨R, η, B, hR, hη, hB, hpositive, hint, ?_⟩
  intro h hh hhη x
  have hbounds := abs_lt.mp hhη
  have htmem : t0 ∈ Icc (t0 - η) (t0 + η) := ⟨by linarith, by linarith⟩
  have hthmem : t0 + h ∈ Icc (t0 - η) (t0 + η) := ⟨by linarith, by linarith⟩
  by_cases hx : x ∈ WaveMap.box n R
  · rw [WaveMap.bound, Set.indicator_of_mem hx]
    change |(WaveMap.density u x (t0 + h) - WaveMap.density u x t0) / h| ≤ B
    have hne : h ≠ 0 := by intro he; simp [he] at hh
    have hseg : Icc (min t0 (t0 + h)) (max t0 (t0 + h)) ⊆
        Icc (t0 - η) (t0 + η) := by
      intro r hr
      exact ⟨le_trans (le_min htmem.1 hthmem.1) hr.1,
        le_trans hr.2 (max_le htmem.2 hthmem.2)⟩
    have hab : min t0 (t0 + h) < max t0 (t0 + h) := by
      rcases lt_or_gt_of_ne hne with hn | hp
      · rw [min_eq_right (by linarith), max_eq_left (by linarith)]
        linarith
      · rw [min_eq_left (by linarith), max_eq_right (by linarith)]
        linarith
    have hc : ContinuousOn (WaveMap.density u x)
        (Icc (min t0 (t0 + h)) (max t0 (t0 + h))) :=
      fun r hr => (h_T004 x r (hpositive (hseg hr))).1.continuousAt.continuousWithinAt
    obtain ⟨c, hcmem, heq⟩ := exists_hasDerivAt_eq_slope
      (WaveMap.density u x) (WaveMap.densityTime u x) hab hc
      (fun r hr => (h_T004 x r (hpositive (hseg ⟨hr.1.le, hr.2.le⟩))).1)
    have hcB := hbound x hx c (hseg ⟨hcmem.1.le, hcmem.2.le⟩)
    have hslope :
        (WaveMap.density u x (max t0 (t0 + h)) -
          WaveMap.density u x (min t0 (t0 + h))) /
        (max t0 (t0 + h) - min t0 (t0 + h)) =
        (WaveMap.density u x (t0 + h) - WaveMap.density u x t0) / h := by
      rcases lt_or_gt_of_ne hne with hn | hp
      · rw [min_eq_right (by linarith), max_eq_left (by linarith)]
        have he : t0 - (t0 + h) = -h := by ring
        rw [he, div_neg, ← neg_div, neg_sub]
      · rw [min_eq_left (by linarith), max_eq_right (by linarith)]
        congr 1
        ring
    rw [heq, hslope] at hcB
    exact hcB
  · have hxC : x ∉ C := by
      intro hxc
      apply hx
      intro j
      exact ⟨(hCopen hxc j).1.le, (hCopen hxc j).2.le⟩
    have hex : ∃ j : Fin n, x j ∉ Icc (-R) R := by
      simpa only [WaveMap.box, mem_setOf_eq, not_forall] using hx
    obtain ⟨j, hj⟩ := hex
    have hzero : ∀ r ∈ Icc (t0 - η) (t0 + η), WaveMap.density u x r = 0 := by
      intro r hr
      have hs : Function.support (fun y => WaveMap.density u y r) ⊆ C :=
        (hterms r (htime hr) j (fun y => WaveMap.density u y r)
          (by simp [WaveMap.terms])).2.1
      by_contra hn
      exact hxC (hs hn)
    simp [WaveMap.bound, Set.indicator_of_notMem hx, WaveMap.quotient,
      hzero t0 htmem, hzero (t0 + h) hthmem]

theorem T006 (n : ℕ) (m : ℕ) (u : WaveMap.Space n × ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H002 : ContDiffOn ℝ (∞ : ℕ∞ω) u (WaveMap.positive n)) (h_T003 : (∀ t : ℝ, 0 < t → Integrable (fun x => WaveMap.density u x t)) ∧
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
    (∀ x ∈ WaveMap.box n R, ∀ r ∈ Icc (t0 - η) (t0 + η), |WaveMap.densityTime u x r| ≤ B)) (h_T004 : ∀ (x : WaveMap.Space n) (t : ℝ), 0 < t →
  HasDerivAt (WaveMap.density u x) (WaveMap.densityTime u x t) t ∧
  WaveMap.densityTime u x t = 2 * WaveMap.kineticProduct u t x +
    2 * ∑ j, WaveMap.gradientProduct u j t x) (h_T005 : ∀ t0 : ℝ, 0 < t0 → ∃ R η B : ℝ,
  0 < R ∧ 0 < η ∧ 0 ≤ B ∧ Icc (t0 - η) (t0 + η) ⊆ Ioi (0 : ℝ) ∧
  Integrable (WaveMap.bound n R B) ∧
  ∀ h : ℝ, 0 < |h| → |h| < η → ∀ x : WaveMap.Space n,
    |WaveMap.quotient u t0 h x| ≤ WaveMap.bound n R B x) :
    ∀ t : ℝ, 0 < t →
  HasDerivAt (WaveMap.energy u) (∫ x, WaveMap.densityTime u x t) t ∧
  (∀ x : WaveMap.Space n, WaveMap.densityTime u x t =
    2 * WaveMap.kineticProduct u t x + 2 * ∑ j, WaveMap.gradientProduct u j t x) ∧
  Integrable (fun x => WaveMap.densityTime u x t) ∧
  Integrable (WaveMap.kineticProduct u t) ∧
  (∀ j : Fin n, Integrable (WaveMap.gradientProduct u j t)) := by
  intro t ht
  have hcontD : Continuous (fun x : WaveMap.Space n => WaveMap.densityTime u x t) := by
    have hc : ContinuousOn (fun p : WaveMap.Space n × ℝ => WaveMap.densityTime u p.1 p.2) (WaveMap.positive n) := h_T003.2.2.1.continuousOn
    have hp : Continuous (fun x : WaveMap.Space n => (x,t)) := continuous_id.prodMk continuous_const
    exact ContinuousOn.comp_continuous (g := fun p : WaveMap.Space n × ℝ => WaveMap.densityTime u p.1 p.2) (f := fun x : WaveMap.Space n => (x,t)) hc hp (fun x => ht)
  have hpoint : ∀ x : WaveMap.Space n, Tendsto (fun h : ℝ => WaveMap.quotient u t h x)
      (nhdsWithin 0 ({0}ᶜ)) (nhds (WaveMap.densityTime u x t)) := by
    intro x
    simpa only [WaveMap.quotient, smul_eq_mul, div_eq_mul_inv, mul_comm] using
      (h_T004 x t ht).1.tendsto_slope_zero
  obtain ⟨R, η, B, hR, hη, hB, hpos, hboundint, hbound⟩ := h_T005 t ht
  have hwindow : ∀ᶠ h : ℝ in nhdsWithin 0 ({0}ᶜ), 0 < |h| ∧ |h| < η := by
    have ha : ∀ᶠ h : ℝ in nhds (0 : ℝ), |h| < η :=
      (continuous_abs.tendsto 0).eventually (gt_mem_nhds (by simpa using hη))
    filter_upwards [ha.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with h hh hn
    exact ⟨abs_pos.mpr hn, hh⟩
  have hDint : Integrable (fun x => WaveMap.densityTime u x t) := by
    apply hboundint.mono' hcontD.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    apply le_of_tendsto (hpoint x).norm
    filter_upwards [hwindow] with h hh
    simpa only [Real.norm_eq_abs] using hbound h hh.1 hh.2 x
  have htime : ∀ h : ℝ, |h| < η → 0 < t + h := by
    intro h hh
    apply hpos
    have hab := abs_lt.mp hh
    constructor <;> linarith
  have hquotint : ∀ h : ℝ, |h| < η → Integrable (WaveMap.quotient u t h) := by
    intro h hh
    exact ((h_T003.1 (t+h) (htime h hh)).sub (h_T003.1 t ht)).div_const h
  have hintegral : ∀ h : ℝ, |h| < η →
      (∫ x, WaveMap.quotient u t h x) = (WaveMap.energy u (t+h) - WaveMap.energy u t) / h := by
    intro h hh
    unfold WaveMap.quotient WaveMap.energy
    rw [integral_div, integral_sub (h_T003.1 (t+h) (htime h hh)) (h_T003.1 t ht)]
  have hseq : ∀ s : ℕ → ℝ, (∀ k, 0 < |s k| ∧ |s k| < η) →
      Tendsto s atTop (nhdsWithin 0 ({0}ᶜ)) →
      Tendsto (fun k => (WaveMap.energy u (t+s k) - WaveMap.energy u t) / s k)
        atTop (nhds (∫ x, WaveMap.densityTime u x t)) := by
    intro s hs hslim
    have hdct : Tendsto (fun k => ∫ x, WaveMap.quotient u t (s k) x)
        atTop (nhds (∫ x, WaveMap.densityTime u x t)) := by
      apply tendsto_integral_of_dominated_convergence (WaveMap.bound n R B)
      · intro k
        exact (hquotint (s k) (hs k).2).aestronglyMeasurable
      · exact hboundint
      · intro k
        exact Filter.Eventually.of_forall (fun x => by
          simpa only [Real.norm_eq_abs] using hbound (s k) (hs k).1 (hs k).2 x)
      · exact Filter.Eventually.of_forall (fun x => (hpoint x).comp hslim)
    simpa only [hintegral _ (hs _).2] using hdct
  have hlim : Tendsto (fun h : ℝ => (WaveMap.energy u (t+h) - WaveMap.energy u t) / h)
      (nhdsWithin 0 ({0}ᶜ)) (nhds (∫ x, WaveMap.densityTime u x t)) := by
    apply Filter.tendsto_of_seq_tendsto
    intro s hs
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hs.eventually hwindow)
    have hh := hseq (fun k => s (k+N)) (fun k => hN (k+N) (Nat.le_add_left N k))
      (hs.comp (tendsto_add_atTop_nat N))
    exact (tendsto_add_atTop_iff_nat N).mp hh
  have hderiv : HasDerivAt (WaveMap.energy u) (∫ x, WaveMap.densityTime u x t) t := by
    apply hasDerivAt_iff_tendsto_slope_zero.mpr
    simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using hlim
  obtain ⟨C, R', η', B', hc, hR', hη', hB', hsub, hbox, hvol, hfin, hwin, hu, hiter, hterms, hbd⟩ :=
    h_T003.2.2.2 t ht
  have htinterior : t ∈ WaveMap.timeInterior t := by
    change t/2 < t ∧ t < 3*t/2
    constructor <;> linarith
  have hGint : ∀ j : Fin n, Integrable (WaveMap.gradientProduct u j t) := by
    intro j
    exact (hterms t htinterior j (WaveMap.gradientProduct u j t) (by simp [WaveMap.terms])).2.2.2.2
  have hsumint : Integrable (fun x => ∑ j, WaveMap.gradientProduct u j t x) :=
    integrable_finsetSum Finset.univ (fun j _ => hGint j)
  have hKint : Integrable (WaveMap.kineticProduct u t) := by
    have hi := (hDint.sub (hsumint.const_mul 2)).div_const 2
    apply hi.congr
    apply Filter.Eventually.of_forall
    intro x
    dsimp
    rw [(h_T004 x t ht).2]
    ring
  exact ⟨hderiv, (fun x => (h_T004 x t ht).2), hDint, hKint, hGint⟩

theorem T007 (n : ℕ) (m : ℕ) (u : WaveMap.Space n × ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H002 : ContDiffOn ℝ (∞ : ℕ∞ω) u (WaveMap.positive n)) (h_T003 : (∀ t : ℝ, 0 < t → Integrable (fun x => WaveMap.density u x t)) ∧
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
    (∀ x ∈ WaveMap.box n R, ∀ r ∈ Icc (t0 - η) (t0 + η), |WaveMap.densityTime u x r| ≤ B)) :
    ∀ (t : ℝ), 0 < t → ∀ j : Fin n,
  ContDiff ℝ (∞ : ℕ∞ω) (WaveMap.flux u j t) ∧ HasCompactSupport (WaveMap.flux u j t) ∧
  (∀ x : WaveMap.Space n, WaveMap.spatial (WaveMap.flux u j t) j x =
    WaveMap.gradientProduct u j t x + WaveMap.laplaceProduct u j t x) ∧
  Integrable (WaveMap.spatial (WaveMap.flux u j t) j) ∧
  Integrable (WaveMap.gradientProduct u j t) ∧ Integrable (WaveMap.laplaceProduct u j t) := by
  intro t ht j
  have hop : IsOpen (WaveMap.positive n) :=
    isOpen_lt continuous_const continuous_snd
  have hut : ContDiff ℝ (∞ : ℕ∞ω) (fun x => WaveMap.ut u x t) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    have hu : ContDiffAt ℝ (∞ : ℕ∞ω) u (x,t) :=
      h_H002.contDiffAt (hop.mem_nhds ht)
    have hd : ContDiffAt ℝ (∞ : ℕ∞ω)
        (fun y : WaveMap.Space n => fderiv ℝ (fun r : ℝ => u (y,r)) t) x :=
      hu.fderiv (f := fun y r => u (y,r)) contDiffAt_const (by simp)
    simpa only [WaveMap.ut, deriv] using
      hd.clm_apply (contDiffAt_const (c := (1 : ℝ)))
  have hs : ContDiff ℝ (∞ : ℕ∞ω) (fun x : WaveMap.Space n => u (x,t)) :=
    h_H002.comp_contDiff (contDiff_id.prodMk contDiff_const) (fun x => ht)
  have hux : ContDiff ℝ (∞ : ℕ∞ω) (fun x => WaveMap.ux u j x t) :=
    (hs.fderiv_right (m := (∞ : ℕ∞ω)) (by simp)).clm_apply contDiff_const
  have hflux : ContDiff ℝ (∞ : ℕ∞ω) (WaveMap.flux u j t) :=
    hut.inner ℝ hux
  rcases h_T003.2.2.2 t ht with
    ⟨C, R, η, B, hC, hR, hη, hB, hsub, hbox, hvol, hfin,
      htime, hconst, hiter, hterms, hbound⟩
  have htI : t ∈ WaveMap.timeInterior t := by
    change t / 2 < t ∧ t < 3 * t / 2
    constructor <;> linarith
  have hfdata := hterms t htI j (WaveMap.flux u j t) (by simp [WaveMap.terms])
  have hddata := hterms t htI j (WaveMap.spatial (WaveMap.flux u j t) j)
    (by simp [WaveMap.terms])
  have hgdata := hterms t htI j (WaveMap.gradientProduct u j t)
    (by simp [WaveMap.terms])
  have hldata := hterms t htI j (WaveMap.laplaceProduct u j t)
    (by simp [WaveMap.terms])
  refine ⟨hflux, HasCompactSupport.of_support_subset_isCompact hC hfdata.2.1,
    ?_, hddata.2.2.2.2, hgdata.2.2.2.2, hldata.2.2.2.2⟩
  intro x
  change fderiv ℝ (fun y => inner ℝ (WaveMap.ut u y t) (WaveMap.ux u j y t))
      x (PiLp.single 2 j 1) =
    inner ℝ (WaveMap.ux u j x t) (WaveMap.utx u j x t) +
      inner ℝ (WaveMap.ut u x t) (WaveMap.uxx u j x t)
  calc
    _ = inner ℝ (WaveMap.ut u x t) (WaveMap.uxx u j x t) +
        inner ℝ (WaveMap.utx u j x t) (WaveMap.ux u j x t) :=
      fderiv_inner_apply ℝ (hut.differentiable (by simp) x)
        (hux.differentiable (by simp) x) (PiLp.single 2 j 1)
    _ = _ := by
      rw [real_inner_comm (WaveMap.utx u j x t) (WaveMap.ux u j x t)]
      exact add_comm _ _

theorem T008 (n : ℕ) (m : ℕ) (u : WaveMap.Space n × ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_T003 : (∀ t : ℝ, 0 < t → Integrable (fun x => WaveMap.density u x t)) ∧
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
    (∀ x ∈ WaveMap.box n R, ∀ r ∈ Icc (t0 - η) (t0 + η), |WaveMap.densityTime u x r| ≤ B)) (h_T007 : ∀ (t : ℝ), 0 < t → ∀ j : Fin n,
  ContDiff ℝ (∞ : ℕ∞ω) (WaveMap.flux u j t) ∧ HasCompactSupport (WaveMap.flux u j t) ∧
  (∀ x : WaveMap.Space n, WaveMap.spatial (WaveMap.flux u j t) j x =
    WaveMap.gradientProduct u j t x + WaveMap.laplaceProduct u j t x) ∧
  Integrable (WaveMap.spatial (WaveMap.flux u j t) j) ∧
  Integrable (WaveMap.gradientProduct u j t) ∧ Integrable (WaveMap.laplaceProduct u j t)) :
    ∀ (t : ℝ), 0 < t → ∀ j : Fin n,
  (∫ x, WaveMap.gradientProduct u j t x) = -(∫ x, WaveMap.laplaceProduct u j t x) ∧
  Integrable (WaveMap.gradientProduct u j t) ∧ Integrable (WaveMap.laplaceProduct u j t) := by
  classical
  have hzero : ∀ (k : ℕ) (j : Fin (k+1)) (g : WaveMap.Space (k+1) → ℝ) (R : ℝ), ContDiff ℝ (∞ : ℕ∞ω) g → 0 < R → IsCompact (WaveMap.box (k+1) R) → Function.support g ⊆ WaveMap.openBox (k+1) R → Function.support (WaveMap.spatial g j) ⊆ WaveMap.box (k+1) R → (∫ x, WaveMap.spatial g j x) = 0 := by
    classical
    have hline : ∀ (k : ℕ) (j : Fin (k + 1)) (g : WaveMap.Space (k+1) → ℝ), ContDiff ℝ (∞ : ℕ∞ω) g → ∀ (y : Fin k → ℝ) (r : ℝ), HasDerivAt (fun s => g (WithLp.toLp 2 (j.insertNth s y))) (WaveMap.spatial g j (WithLp.toLp 2 (j.insertNth r y))) r := by
      intro k j g hg y r
      have heq : (fun s : ℝ => (WithLp.toLp 2 (j.insertNth s y) : WaveMap.Space (k+1))) =
          (fun s => (WithLp.toLp 2 (j.insertNth 0 y) : WaveMap.Space (k+1)) +
            s • (PiLp.single 2 j 1 : WaveMap.Space (k+1))) := by
        funext s
        apply PiLp.ext
        intro i
        rcases j.eq_self_or_eq_succAbove i with hi | ⟨a, ha⟩
        · subst i
          simp
        · subst i
          simp [Fin.succAbove_ne]
      have hi : HasDerivAt
          (fun s : ℝ => (WithLp.toLp 2 (j.insertNth s y) : WaveMap.Space (k+1)))
          (PiLp.single 2 j 1) r := by
        rw [heq]
        simpa using ((hasDerivAt_id r).smul_const
          (PiLp.single 2 j 1 : WaveMap.Space (k+1))).const_add
          (WithLp.toLp 2 (j.insertNth 0 y))
      exact (hg.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt r hi
    have htransport : ∀ (k : ℕ) (j : Fin (k+1)) (R : ℝ), IsCompact (WaveMap.box (k+1) R) → let e : (ℝ × (Fin k → ℝ)) ≃ᵐ WaveMap.Space (k+1) :=   (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k+1) => ℝ) j).symm.trans     (MeasurableEquiv.toLp 2 (Fin (k+1) → ℝ)); MeasurePreserving e   ((volume.restrict (Icc (-R) R)).prod     (Measure.pi (fun _ : Fin k => (volume : Measure ℝ).restrict (Icc (-R) R))))   (volume.restrict (WaveMap.box (k+1) R)) := by
      have hpre : ∀ (k : ℕ) (j : Fin (k+1)) (R : ℝ),
      let e : (ℝ × (Fin k → ℝ)) ≃ᵐ WaveMap.Space (k+1) :=
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k+1) => ℝ) j).symm.trans
          (MeasurableEquiv.toLp 2 (Fin (k+1) → ℝ))
      e ⁻¹' WaveMap.box (k+1) R = Icc (-R) R ×ˢ (Set.univ.pi (fun _ : Fin k => Icc (-R) R)) := by
        intro k j R e
        ext p
        rcases p with ⟨r,y⟩
        simp only [Set.mem_prod, Set.mem_pi, Set.mem_univ, forall_const]
        change (∀ i, Fin.insertNth (α := fun _ => ℝ) j r y i ∈ Icc (-R) R) ↔
          (r ∈ Icc (-R) R ∧ ∀ a, y a ∈ Icc (-R) R)
        simp only [j.forall_iff_succAbove, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
      intro k j R hQ e
      have hfull : MeasurePreserving e (volume : Measure (ℝ × (Fin k → ℝ))) volume :=
        (PiLp.volume_preserving_toLp (Fin (k+1))).comp
          (volume_preserving_piFinSuccAbove (fun _ : Fin (k+1) => ℝ) j).symm
      have hres := hfull.restrict_preimage hQ.measurableSet
      rw [hpre k j R] at hres
      change MeasurePreserving e
        (((volume : Measure ℝ).prod (volume : Measure (Fin k → ℝ))).restrict
          (Icc (-R) R ×ˢ Set.univ.pi (fun _ : Fin k => Icc (-R) R)))
        (volume.restrict (WaveMap.box (k+1) R)) at hres
      rw [← Measure.prod_restrict, volume_pi, Measure.restrict_pi_pi] at hres
      exact hres
    intro k j g R hg hR hQ hs hd
    let e : (ℝ × (Fin k → ℝ)) ≃ᵐ WaveMap.Space (k+1) :=
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k+1) => ℝ) j).symm.trans
        (MeasurableEquiv.toLp 2 (Fin (k+1) → ℝ))
    let μ : Measure ℝ := volume.restrict (Icc (-R) R)
    let ν : Measure (Fin k → ℝ) := Measure.pi (fun _ : Fin k => μ)
    have hμ : IsFiniteMeasure μ := by dsimp [μ]; infer_instance
    have hν : IsFiniteMeasure ν := by
      dsimp [ν]
      cases k with
      | zero =>
        -- For n = 1 the remaining-coordinate space is a singleton of mass one.
        have hmass : (Measure.pi (fun _ : Fin 0 => μ)) Set.univ = 1 :=
          Measure.pi_empty_univ _
        exact ⟨by rw [hmass]; exact ENNReal.one_lt_top⟩
      | succ k => infer_instance
    letI := hμ
    letI := hν
    have hmp : MeasurePreserving e (μ.prod ν)
        (volume.restrict (WaveMap.box (k+1) R)) := htransport k j R hQ
    have hc : Continuous (WaveMap.spatial g j) := by
      exact (hg.fderiv_right (m := 0) (by simp)).continuous.clm_apply continuous_const
    have hinner : ∀ y : Fin k → ℝ, ∫ r in Icc (-R) R,
        WaveMap.spatial g j (e (r,y)) = 0 := by
      intro y
      have hi : Continuous (fun r : ℝ => (e (r,y) : WaveMap.Space (k+1))) := by
        change Continuous (fun r : ℝ =>
          (WithLp.toLp 2 (j.insertNth r y) : WaveMap.Space (k+1)))
        have heq : (fun s : ℝ => (WithLp.toLp 2 (j.insertNth s y) : WaveMap.Space (k+1))) =
            (fun s => (WithLp.toLp 2 (j.insertNth 0 y) : WaveMap.Space (k+1)) +
              s • (PiLp.single 2 j 1 : WaveMap.Space (k+1))) := by
          funext s
          apply PiLp.ext
          intro i
          rcases j.eq_self_or_eq_succAbove i with hi | ⟨a, ha⟩
          · subst i
            simp
          · subst i
            simp [Fin.succAbove_ne]
        rw [heq]
        fun_prop
      have hp : g (e (R,y)) = 0 := by
        apply Function.notMem_support.mp
        intro hx
        have hb := (hs hx) j
        have : R < R := by simpa [e] using hb.2
        exact lt_irrefl R this
      have hm : g (e (-R,y)) = 0 := by
        apply Function.notMem_support.mp
        intro hx
        have hb := (hs hx) j
        have : -R < -R := by simpa [e] using hb.1
        exact lt_irrefl (-R) this
      have hftc : (∫ r in (-R)..R, WaveMap.spatial g j (e (r,y))) =
          g (e (R,y)) - g (e (-R,y)) :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun r _ => hline k j g hg y r)
          ((hc.comp hi).intervalIntegrable (-R) R)
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (show -R ≤ R by linarith), hftc, hp, hm, sub_self]
    have hboxint : Integrable (WaveMap.spatial g j)
        (volume.restrict (WaveMap.box (k+1) R)) :=
      hc.continuousOn.integrableOn_compact hQ
    have hprodint : Integrable (fun p => WaveMap.spatial g j (e p)) (μ.prod ν) :=
      hmp.integrable_comp_of_integrable hboxint
    have hboxzero : (∫ x in WaveMap.box (k+1) R, WaveMap.spatial g j x) = 0 := by
      rw [← hmp.integral_comp' (WaveMap.spatial g j),
        integral_prod_symm _ hprodint]
      change (∫ y, (∫ r in Icc (-R) R, WaveMap.spatial g j (e (r,y))) ∂ν) = 0
      simp only [hinner, integral_zero]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := WaveMap.box (k+1) R) (fun x hx => Function.notMem_support.mp
        (fun h => hx (hd h)))]
    exact hboxzero
  intro t ht j
  cases n with
  | zero => exact Fin.elim0 j
  | succ k =>
    obtain ⟨C, R, η, B, hC, hR, hη, hB, hCopen, hQ, hvol, hfinite,
      hwindow, hu, hder, hterms, hbound⟩ := h_T003.2.2.2 t ht
    have htt : t ∈ WaveMap.timeInterior t := by
      change t / 2 < t ∧ t < 3 * t / 2
      constructor <;> linarith
    have hgs : Function.support (WaveMap.flux u j t) ⊆ C :=
      (hterms t htt j (WaveMap.flux u j t) (by simp [WaveMap.terms])).2.1
    have hds : Function.support (WaveMap.spatial (WaveMap.flux u j t) j) ⊆ C :=
      (hterms t htt j (WaveMap.spatial (WaveMap.flux u j t) j)
        (by simp [WaveMap.terms])).2.1
    have hCbox : C ⊆ WaveMap.box (k+1) R := by
      intro x hx i
      exact ⟨(hCopen hx i).1.le, (hCopen hx i).2.le⟩
    obtain ⟨hg, hgc, hprod, hdi, hai, hbi⟩ := h_T007 t ht j
    have hz : (∫ x, WaveMap.spatial (WaveMap.flux u j t) j x) = 0 :=
      hzero k j (WaveMap.flux u j t) R hg hR hQ
        (hgs.trans hCopen) (hds.trans hCbox)
    have hsum : (∫ x, WaveMap.spatial (WaveMap.flux u j t) j x) =
        (∫ x, WaveMap.gradientProduct u j t x) +
        (∫ x, WaveMap.laplaceProduct u j t x) := by
      simp_rw [hprod]
      exact integral_add hai hbi
    exact ⟨by linarith, hai, hbi⟩

theorem T009 (n : ℕ) (m : ℕ) (u : WaveMap.Space n × ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H002 : ContDiffOn ℝ (∞ : ℕ∞ω) u (WaveMap.positive n)) (h_T001 : ∀ (x : WaveMap.Space n) (t : ℝ), 0 < t →
  inner ℝ (u (x,t)) (WaveMap.ut u x t) = 0 ∧
  inner ℝ (WaveMap.ut u x t) (WaveMap.utt u x t - WaveMap.laplace u x t) = 0 ∧
  inner ℝ (u (x,t)) (WaveMap.utt u x t) = -(‖WaveMap.ut u x t‖ ^ 2) ∧
  (∀ j : Fin n, inner ℝ (u (x,t)) (WaveMap.uxx u j x t) = -(‖WaveMap.ux u j x t‖ ^ 2)) ∧
  (∀ a : ℝ, WaveMap.utt u x t - WaveMap.laplace u x t = a • u (x,t) →
    a = (∑ j, ‖WaveMap.ux u j x t‖ ^ 2) - ‖WaveMap.ut u x t‖ ^ 2) ∧
  WaveMap.utt u x t - WaveMap.laplace u x t =
    ((∑ j, ‖WaveMap.ux u j x t‖ ^ 2) - ‖WaveMap.ut u x t‖ ^ 2) • u (x,t)) (h_T003 : (∀ t : ℝ, 0 < t → Integrable (fun x => WaveMap.density u x t)) ∧
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
    (∀ x ∈ WaveMap.box n R, ∀ r ∈ Icc (t0 - η) (t0 + η), |WaveMap.densityTime u x r| ≤ B)) (h_T006 : ∀ t : ℝ, 0 < t →
  HasDerivAt (WaveMap.energy u) (∫ x, WaveMap.densityTime u x t) t ∧
  (∀ x : WaveMap.Space n, WaveMap.densityTime u x t =
    2 * WaveMap.kineticProduct u t x + 2 * ∑ j, WaveMap.gradientProduct u j t x) ∧
  Integrable (fun x => WaveMap.densityTime u x t) ∧
  Integrable (WaveMap.kineticProduct u t) ∧
  (∀ j : Fin n, Integrable (WaveMap.gradientProduct u j t))) (h_T008 : ∀ (t : ℝ), 0 < t → ∀ j : Fin n,
  (∫ x, WaveMap.gradientProduct u j t x) = -(∫ x, WaveMap.laplaceProduct u j t x) ∧
  Integrable (WaveMap.gradientProduct u j t) ∧ Integrable (WaveMap.laplaceProduct u j t)) :
    ∀ t : ℝ, 0 < t → HasDerivAt (WaveMap.energy u) 0 t := by
  intro t ht
  rcases h_T006 t ht with ⟨hd, hformula, hD, hK, hG⟩
  have hL : ∀ j : Fin n, Integrable (WaveMap.laplaceProduct u j t) :=
    fun j => (h_T008 t ht j).2.2
  have hGsum : Integrable (fun x => ∑ j : Fin n, WaveMap.gradientProduct u j t x) :=
    integrable_finsetSum Finset.univ (fun j _ => hG j)
  have hLsum : Integrable (fun x => ∑ j : Fin n, WaveMap.laplaceProduct u j t x) :=
    integrable_finsetSum Finset.univ (fun j _ => hL j)
  have hIBP : ∀ j : Fin n,
      (∫ x, WaveMap.gradientProduct u j t x) =
        -(∫ x, WaveMap.laplaceProduct u j t x) :=
    fun j => (h_T008 t ht j).1
  have hdiff :
      (fun x => inner ℝ (WaveMap.ut u x t)
        (WaveMap.utt u x t - WaveMap.laplace u x t)) =
      (fun x => WaveMap.kineticProduct u t x -
        ∑ j : Fin n, WaveMap.laplaceProduct u j t x) := by
    funext x
    simp only [WaveMap.kineticProduct, WaveMap.laplaceProduct,
      WaveMap.laplace, inner_sub_right, inner_sum]
  have hz : (∫ x, WaveMap.densityTime u x t) = 0 := by
    calc
      (∫ x, WaveMap.densityTime u x t) =
          ∫ x, (2 * WaveMap.kineticProduct u t x +
            2 * ∑ j : Fin n, WaveMap.gradientProduct u j t x) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hformula
      _ = 2 * (∫ x, WaveMap.kineticProduct u t x) +
          2 * ∑ j : Fin n, (∫ x, WaveMap.gradientProduct u j t x) := by
        rw [integral_add (hK.const_mul 2) (hGsum.const_mul 2),
          integral_const_mul, integral_const_mul,
          integral_finsetSum Finset.univ (fun j _ => hG j)]
      _ = 2 * (∫ x, WaveMap.kineticProduct u t x) -
          2 * ∑ j : Fin n, (∫ x, WaveMap.laplaceProduct u j t x) := by
        simp_rw [hIBP]
        rw [Finset.sum_neg_distrib]
        ring
      _ = 2 * (∫ x, inner ℝ (WaveMap.ut u x t)
          (WaveMap.utt u x t - WaveMap.laplace u x t)) := by
        rw [hdiff, integral_sub hK hLsum,
          integral_finsetSum Finset.univ (fun j _ => hL j)]
        ring
      _ = 0 := by
        have hzero :
            (fun x => inner ℝ (WaveMap.ut u x t)
              (WaveMap.utt u x t - WaveMap.laplace u x t)) =
            (fun _ : WaveMap.Space n => (0 : ℝ)) := by
          funext x
          exact (h_T001 x t ht).2.1
        rw [hzero]
        simp
  simpa only [hz] using hd

theorem T010 (n : ℕ) (m : ℕ) (u : WaveMap.Space n × ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_T003 : (∀ t : ℝ, 0 < t → Integrable (fun x => WaveMap.density u x t)) ∧
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
    (∀ x ∈ WaveMap.box n R, ∀ r ∈ Icc (t0 - η) (t0 + η), |WaveMap.densityTime u x r| ≤ B)) (h_T009 : ∀ t : ℝ, 0 < t → HasDerivAt (WaveMap.energy u) 0 t) :
    (∀ t : ℝ, 0 < t → Integrable (fun x => WaveMap.density u x t)) ∧
  (∀ t : ℝ, 0 < t → HasDerivAt (WaveMap.energy u) 0 t) ∧
  (∀ (s t : ℝ), 0 < s → 0 < t → WaveMap.energy u s = WaveMap.energy u t) := by
  refine ⟨h_T003.1, h_T009, ?_⟩
  have ordered : ∀ (s t : ℝ), 0 < s → s < t → WaveMap.energy u s = WaveMap.energy u t := by
    intro s t hs hst
    have hcont : ContinuousOn (WaveMap.energy u) (Icc s t) := by
      intro r hr
      exact (h_T009 r (lt_of_lt_of_le hs hr.1)).continuousAt.continuousWithinAt
    have hderiv : ∀ r ∈ Ioo s t, HasDerivAt (WaveMap.energy u) ((fun _ : ℝ => (0 : ℝ)) r) r := by
      intro r hr
      exact h_T009 r (lt_trans hs hr.1)
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (WaveMap.energy u) (fun _ : ℝ => (0 : ℝ)) hst hcont hderiv
    have hmul := (eq_div_iff (ne_of_gt (sub_pos.mpr hst))).mp hslope
    linarith
  intro s t hs ht
  rcases lt_trichotomy s t with hst | hst | hts
  · exact ordered s t hs hst
  · subst t
    rfl
  · exact (ordered t s ht hts).symm

set_option Elab.async false in
theorem P (n : ℕ) (m : ℕ) (u : WaveMap.Space n × ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ (∞ : ℕ∞ω) u (WaveMap.positive n)) (h_H003 : ‖q‖ = 1) (h_H004 : ∀ (x : WaveMap.Space n) (t : ℝ), 0 < t → ‖u (x,t)‖ = 1) (h_H005 : ∀ (x : WaveMap.Space n) (t : ℝ), 0 < t → ∃ a : ℝ, WaveMap.utt u x t - WaveMap.laplace u x t = a • u (x,t)) (h_H006 : ∀ (s t : ℝ), 0 < s → s < t → ∃ C : Set (WaveMap.Space n), IsCompact C ∧ ∀ x : WaveMap.Space n, x ∉ C → ∀ r ∈ Icc s t, u (x,r) = q) :
    (∀ t : ℝ, 0 < t → Integrable (fun x => WaveMap.density u x t)) ∧
  (∀ t : ℝ, 0 < t → HasDerivAt (WaveMap.energy u) 0 t) ∧
  (∀ (s t : ℝ), 0 < s → 0 < t → WaveMap.energy u s = WaveMap.energy u t) := by
  have h_T002 : ∀ t0 : ℝ, 0 < t0 → ∃ (C : Set (WaveMap.Space n)) (R : ℝ),
  IsCompact C ∧ 0 < R ∧ C ⊆ WaveMap.openBox n R ∧
  (∀ x : WaveMap.Space n, x ∉ C → ∀ r ∈ WaveMap.timeInterval t0, u (x,r) = q) ∧
  (∀ (k : ℕ) (x : WaveMap.Space n) (r : ℝ), 0 < k → x ∉ C →
    r ∈ WaveMap.timeInterior t0 → iteratedFDeriv ℝ k u (x,r) = 0) := @T002 n m u q h_H001 h_H002 h_H006
  have h_T003 : (∀ t : ℝ, 0 < t → Integrable (fun x => WaveMap.density u x t)) ∧
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
    (∀ x ∈ WaveMap.box n R, ∀ r ∈ Icc (t0 - η) (t0 + η), |WaveMap.densityTime u x r| ≤ B) := @T003 n m u q h_H001 h_H002 h_T002
  have h_T001 : ∀ (x : WaveMap.Space n) (t : ℝ), 0 < t →
  inner ℝ (u (x,t)) (WaveMap.ut u x t) = 0 ∧
  inner ℝ (WaveMap.ut u x t) (WaveMap.utt u x t - WaveMap.laplace u x t) = 0 ∧
  inner ℝ (u (x,t)) (WaveMap.utt u x t) = -(‖WaveMap.ut u x t‖ ^ 2) ∧
  (∀ j : Fin n, inner ℝ (u (x,t)) (WaveMap.uxx u j x t) = -(‖WaveMap.ux u j x t‖ ^ 2)) ∧
  (∀ a : ℝ, WaveMap.utt u x t - WaveMap.laplace u x t = a • u (x,t) →
    a = (∑ j, ‖WaveMap.ux u j x t‖ ^ 2) - ‖WaveMap.ut u x t‖ ^ 2) ∧
  WaveMap.utt u x t - WaveMap.laplace u x t =
    ((∑ j, ‖WaveMap.ux u j x t‖ ^ 2) - ‖WaveMap.ut u x t‖ ^ 2) • u (x,t) := @T001 n m u q h_H002 h_H004 h_H005
  have h_T004 : ∀ (x : WaveMap.Space n) (t : ℝ), 0 < t →
  HasDerivAt (WaveMap.density u x) (WaveMap.densityTime u x t) t ∧
  WaveMap.densityTime u x t = 2 * WaveMap.kineticProduct u t x +
    2 * ∑ j, WaveMap.gradientProduct u j t x := @T004 n m u q h_H002
  have h_T005 : ∀ t0 : ℝ, 0 < t0 → ∃ R η B : ℝ,
  0 < R ∧ 0 < η ∧ 0 ≤ B ∧ Icc (t0 - η) (t0 + η) ⊆ Ioi (0 : ℝ) ∧
  Integrable (WaveMap.bound n R B) ∧
  ∀ h : ℝ, 0 < |h| → |h| < η → ∀ x : WaveMap.Space n,
    |WaveMap.quotient u t0 h x| ≤ WaveMap.bound n R B x := @T005 n m u q h_T003 h_T004
  have h_T006 : ∀ t : ℝ, 0 < t →
  HasDerivAt (WaveMap.energy u) (∫ x, WaveMap.densityTime u x t) t ∧
  (∀ x : WaveMap.Space n, WaveMap.densityTime u x t =
    2 * WaveMap.kineticProduct u t x + 2 * ∑ j, WaveMap.gradientProduct u j t x) ∧
  Integrable (fun x => WaveMap.densityTime u x t) ∧
  Integrable (WaveMap.kineticProduct u t) ∧
  (∀ j : Fin n, Integrable (WaveMap.gradientProduct u j t)) := @T006 n m u q h_H002 h_T003 h_T004 h_T005
  have h_T007 : ∀ (t : ℝ), 0 < t → ∀ j : Fin n,
  ContDiff ℝ (∞ : ℕ∞ω) (WaveMap.flux u j t) ∧ HasCompactSupport (WaveMap.flux u j t) ∧
  (∀ x : WaveMap.Space n, WaveMap.spatial (WaveMap.flux u j t) j x =
    WaveMap.gradientProduct u j t x + WaveMap.laplaceProduct u j t x) ∧
  Integrable (WaveMap.spatial (WaveMap.flux u j t) j) ∧
  Integrable (WaveMap.gradientProduct u j t) ∧ Integrable (WaveMap.laplaceProduct u j t) := @T007 n m u q h_H002 h_T003
  have h_T008 : ∀ (t : ℝ), 0 < t → ∀ j : Fin n,
  (∫ x, WaveMap.gradientProduct u j t x) = -(∫ x, WaveMap.laplaceProduct u j t x) ∧
  Integrable (WaveMap.gradientProduct u j t) ∧ Integrable (WaveMap.laplaceProduct u j t) := @T008 n m u q h_H001 h_T003 h_T007
  have h_T009 : ∀ t : ℝ, 0 < t → HasDerivAt (WaveMap.energy u) 0 t := @T009 n m u q h_H002 h_T001 h_T003 h_T006 h_T008
  have h_T010 : (∀ t : ℝ, 0 < t → Integrable (fun x => WaveMap.density u x t)) ∧
  (∀ t : ℝ, 0 < t → HasDerivAt (WaveMap.energy u) 0 t) ∧
  (∀ (s t : ℝ), 0 < s → 0 < t → WaveMap.energy u s = WaveMap.energy u t) := @T010 n m u q h_T003 h_T009
  exact h_T010

#check @P
#print axioms P

end Translation

namespace AuditBExport
set_option autoImplicit false
set_option Elab.async false in
theorem P (n : ℕ) (m : ℕ) (u : WaveMap.Space n × ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ (∞ : ℕ∞ω) u (WaveMap.positive n)) (h_H003 : ‖q‖ = 1) (h_H004 : ∀ (x : WaveMap.Space n) (t : ℝ), 0 < t → ‖u (x,t)‖ = 1) (h_H005 : ∀ (x : WaveMap.Space n) (t : ℝ), 0 < t → ∃ a : ℝ, WaveMap.utt u x t - WaveMap.laplace u x t = a • u (x,t)) (h_H006 : ∀ (s t : ℝ), 0 < s → s < t → ∃ C : Set (WaveMap.Space n), IsCompact C ∧ ∀ x : WaveMap.Space n, x ∉ C → ∀ r ∈ Icc s t, u (x,r) = q) : (∀ t : ℝ, 0 < t → Integrable (fun x => WaveMap.density u x t)) ∧
  (∀ t : ℝ, 0 < t → HasDerivAt (WaveMap.energy u) 0 t) ∧
  (∀ (s t : ℝ), 0 < s → 0 < t → WaveMap.energy u s = WaveMap.energy u t) := by
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

private def record (name : Name) : MetaM Json := do
  let info ← getConstInfo name
  let env ← getEnv
  let imported := env.isImportedConst name
  let moduleName := match env.getModuleIdxFor? name with
    | some idx => (env.header.moduleNames[idx.toNat]!).toString
    | none => env.mainModule.toString
  return Json.mkObj [
    ("name", toJson name.toString), ("kind", toJson (kindOf info)),
    ("imported", toJson imported), ("module", toJson moduleName),
    ("proof_valued", toJson (← isProp info.type)),
    ("instance_declaration", toJson (isInstanceCore env name)),
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
    let checks : Array (String × String × String × Array String) := #[("P", "decl:AuditBExport.P", "∀ (n : ℕ) (m : ℕ) (u : WaveMap.Space n × ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ (∞ : ℕ∞ω) u (WaveMap.positive n)) (h_H003 : ‖q‖ = 1) (h_H004 : ∀ (x : WaveMap.Space n) (t : ℝ), 0 < t → ‖u (x,t)‖ = 1) (h_H005 : ∀ (x : WaveMap.Space n) (t : ℝ), 0 < t → ∃ a : ℝ, WaveMap.utt u x t - WaveMap.laplace u x t = a • u (x,t)) (h_H006 : ∀ (s t : ℝ), 0 < s → s < t → ∃ C : Set (WaveMap.Space n), IsCompact C ∧ ∀ x : WaveMap.Space n, x ∉ C → ∀ r ∈ Icc s t, u (x,r) = q), (∀ t : ℝ, 0 < t → Integrable (fun x => WaveMap.density u x t)) ∧\n  (∀ t : ℝ, 0 < t → HasDerivAt (WaveMap.energy u) 0 t) ∧\n  (∀ (s t : ℝ), 0 < s → 0 < t → WaveMap.energy u s = WaveMap.energy u t)", #["AuditBExport", "P"]), ("__frozen__P", "decl:AuditBExport.P", "∀ (n : ℕ) (m : ℕ) (u : WaveMap.Space n × ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ (∞ : ℕ∞ω) u (WaveMap.positive n)) (h_H003 : ‖q‖ = 1) (h_H004 : ∀ (x : WaveMap.Space n) (t : ℝ), 0 < t → ‖u (x,t)‖ = 1) (h_H005 : ∀ (x : WaveMap.Space n) (t : ℝ), 0 < t → ∃ a : ℝ, WaveMap.utt u x t - WaveMap.laplace u x t = a • u (x,t)) (h_H006 : ∀ (s t : ℝ), 0 < s → s < t → ∃ C : Set (WaveMap.Space n), IsCompact C ∧ ∀ x : WaveMap.Space n, x ∉ C → ∀ r ∈ Icc s t, u (x,r) = q), (∀ t : ℝ, 0 < t → Integrable (fun x => WaveMap.density u x t)) ∧\n  (∀ t : ℝ, 0 < t → HasDerivAt (WaveMap.energy u) 0 t) ∧\n  (∀ (s t : ℝ), 0 < s → 0 < t → WaveMap.energy u s = WaveMap.energy u t)", #["AuditBExport", "P"])]
    let mut comparisons : Array Json := #[]
    let mut frozenComparisons : Array Json := #[]
    let mut roots : Array Name := #[`AuditBExport.P]
    for (id, selector, expectedText, parts) in checks do
      let stx ← ofExcept <| Parser.runParserCategory (← getEnv) `term expectedText
      let expected ← Term.elabTerm stx none
      Term.synthesizeSyntheticMVarsNoPostponing
      let expected ← instantiateMVars expected
      let actual ← actualType selector parts
      let (equal, method) ← sameSignature actual expected
      let row := Json.mkObj [
        ("id", toJson id), ("selector", toJson selector),
        ("expected_type", toJson (← showType expected)),
        ("actual_type", toJson (← showType actual)), ("definitionally_equal", toJson equal),
        ("comparison_method", toJson method)]
      if id.startsWith "__frozen__" then
        frozenComparisons := frozenComparisons.push row
      else
        comparisons := comparisons.push row
      if selector.startsWith "decl:" then
        roots := roots.push (nameOf parts)
    let dependencies ← inspect roots
    return Json.mkObj [("comparisons", toJson comparisons),
      ("frozen_comparisons", toJson frozenComparisons), ("dependencies", dependencies)]
  logInfo m!"NL2LEAN_AUDIT_JSON:{result.compress}"

set_option maxHeartbeats 0 in
#nl2lean_audit_probe
end NL2LeanAuditProbe
