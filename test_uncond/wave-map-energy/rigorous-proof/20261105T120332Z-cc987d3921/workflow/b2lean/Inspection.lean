import Mathlib
open scoped Topology ContDiff
open MeasureTheory Filter
namespace WaveMapEnergy
abbrev Space (n : ℕ) := Fin n → ℝ
abbrev Value (m : ℕ) := Fin m → ℝ
def dot {m : ℕ} (v w : Value m) : ℝ := ∑ k, v k * w k
def normSq {m : ℕ} (v : Value m) : ℝ := dot v v
noncomputable def velocity {n m : ℕ} (u : Space n × ℝ → Value m)
    (x : Space n) (t : ℝ) : Value m :=
  fun k => deriv (fun r => u (x, r) k) t
noncomputable def acceleration {n m : ℕ} (u : Space n × ℝ → Value m)
    (x : Space n) (t : ℝ) : Value m :=
  fun k => deriv (fun r => velocity u x r k) t
noncomputable def spatial {n m : ℕ} (u : Space n × ℝ → Value m)
    (j : Fin n) (x : Space n) (t : ℝ) : Value m :=
  fun k => fderiv ℝ (fun y => u (y, t) k) x (Pi.single j 1)
noncomputable def spatialSecond {n m : ℕ} (u : Space n × ℝ → Value m)
    (j : Fin n) (x : Space n) (t : ℝ) : Value m :=
  fun k => fderiv ℝ (fun y => spatial u j y t k) x (Pi.single j 1)
noncomputable def laplacian {n m : ℕ} (u : Space n × ℝ → Value m)
    (x : Space n) (t : ℝ) : Value m := ∑ j, spatialSecond u j x t
noncomputable def density {n m : ℕ} (u : Space n × ℝ → Value m)
    (x : Space n) (t : ℝ) : ℝ :=
  normSq (velocity u x t) + ∑ j, normSq (spatial u j x t)
noncomputable def energy {n m : ℕ} (u : Space n × ℝ → Value m) (t : ℝ) : ℝ :=
  ∫ x, density u x t
def Smooth {n m : ℕ} (u : Space n × ℝ → Value m) : Prop :=
  ContDiffOn ℝ ∞ u {p | 0 < p.2}
def UnitValued {n m : ℕ} (u : Space n × ℝ → Value m) : Prop :=
  ∀ x t, 0 < t → normSq (u (x, t)) = 1
def Normal {n m : ℕ} (u : Space n × ℝ → Value m) : Prop :=
  ∀ x t, 0 < t → ∃ a : ℝ, acceleration u x t - laplacian u x t = a • u (x, t)
def CompactPerturbation {n m : ℕ} (u : Space n × ℝ → Value m) (q : Value m) : Prop :=
  ∀ s t : ℝ, 0 < s → s < t → ∃ C : Set (Space n), IsCompact C ∧
    ∀ x r, x ∉ C → r ∈ Set.Icc s t → u (x, r) = q
end WaveMapEnergy

namespace WaveMapEnergy
noncomputable def ubar {n m : ℕ}
    (u : Space n × Set.Ioi (0 : ℝ) → Value m) (q : Value m)
    (p : Space n × ℝ) : Value m :=
  if h : 0 < p.2 then u (p.1, ⟨p.2, h⟩) else q
noncomputable def mixed {n m : ℕ} (v : Space n × ℝ → Value m)
    (j : Fin n) (x : Space n) (t : ℝ) : Value m :=
  fun k => fderiv ℝ (fun y => velocity v y t k) x (Pi.single j 1)
noncomputable def densityRate {n m : ℕ} (v : Space n × ℝ → Value m)
    (x : Space n) (t : ℝ) : ℝ :=
  2 * dot (velocity v x t) (acceleration v x t) +
    2 * ∑ j, dot (spatial v j x t) (mixed v j x t)
def FirstCalculus {n m : ℕ} (v : Space n × ℝ → Value m) : Prop :=
  Smooth v ∧
  ContDiffOn ℝ ∞ (fun p : Space n × ℝ => velocity v p.1 p.2) {p | 0 < p.2} ∧
  (∀ j : Fin n, ContDiffOn ℝ ∞
    (fun p : Space n × ℝ => spatial v j p.1 p.2) {p | 0 < p.2}) ∧
  (∀ (x : Space n) (t : ℝ), 0 < t → ∀ k : Fin m,
    HasDerivAt (fun r => v (x,r) k) (velocity v x t k) t) ∧
  (∀ (x : Space n) (t : ℝ), 0 < t → ∀ k : Fin m,
    HasFDerivAt (fun y => v (y,t) k) (fderiv ℝ (fun y => v (y,t) k) x) x)
def SecondCalculus {n m : ℕ} (v : Space n × ℝ → Value m) : Prop :=
  ContDiffOn ℝ ∞ (fun p : Space n × ℝ => acceleration v p.1 p.2) {p | 0 < p.2} ∧
  (∀ j : Fin n, ContDiffOn ℝ ∞
    (fun p : Space n × ℝ => spatialSecond v j p.1 p.2) {p | 0 < p.2}) ∧
  (∀ j : Fin n, ContDiffOn ℝ ∞
    (fun p : Space n × ℝ => mixed v j p.1 p.2) {p | 0 < p.2}) ∧
  (∀ (x : Space n) (t : ℝ), 0 < t → ∀ k : Fin m,
    HasDerivAt (fun r => velocity v x r k) (acceleration v x t k) t) ∧
  (∀ (j : Fin n) (x : Space n) (t : ℝ), 0 < t → ∀ k : Fin m,
    HasDerivAt (fun r => spatial v j x r k) (mixed v j x t k) t) ∧
  (∀ (j : Fin n) (x : Space n) (t : ℝ), 0 < t → ∀ k : Fin m,
    HasFDerivAt (fun y => velocity v y t k)
      (fderiv ℝ (fun y => velocity v y t k) x) x ∧
    HasFDerivAt (fun y => spatial v j y t k)
      (fderiv ℝ (fun y => spatial v j y t k) x) x)
noncomputable def sections {n m : ℕ} (v : Space n × ℝ → Value m)
    (t : ℝ) : Set (Space n → ℝ) :=
  {h | h = (fun x => density v x t) ∨ h = (fun x => densityRate v x t) ∨
    (∃ k : Fin m, h = (fun x => velocity v x t k) ∨
      h = (fun x => acceleration v x t k) ∨
      h = (fun x => velocity v x t k * acceleration v x t k)) ∨
    (∃ (j : Fin n) (k : Fin m),
      h = (fun x => spatial v j x t k) ∨
      h = (fun x => spatialSecond v j x t k) ∨
      h = (fun x => mixed v j x t k) ∨
      h = (fun x => spatial v j x t k * mixed v j x t k) ∨
      h = (fun x => velocity v x t k * spatialSecond v j x t k) ∨
      h = (fun x => velocity v x t k * spatial v j x t k) ∨
      h = (fun x => mixed v j x t k * spatial v j x t k)) ∨
    h = (fun x => dot (velocity v x t) (acceleration v x t)) ∨
    (∃ j : Fin n,
      h = (fun x => dot (spatial v j x t) (mixed v j x t)) ∨
      h = (fun x => dot (velocity v x t) (spatialSecond v j x t)) ∨
      h = (fun x => dot (velocity v x t) (spatial v j x t)) ∨
      h = (fun x => dot (mixed v j x t) (spatial v j x t)))}
def SupportedSection {n : ℕ} (C : Set (Space n)) (h : Space n → ℝ) : Prop :=
  Continuous h ∧ tsupport h ⊆ C ∧ HasCompactSupport h ∧ Integrable h
def SlabVanishing {n m : ℕ} (v : Space n × ℝ → Value m) (q : Value m)
    (t₀ : ℝ) (C : Set (Space n)) : Prop :=
  IsCompact C ∧
  (∀ x r, x ∉ C → r ∈ Set.Icc (t₀/2) (3*t₀/2) → v (x,r) = q) ∧
  (∀ (ell : ℕ), 0 < ell → ∀ x r,
    x ∉ C → r ∈ Set.Ioo (t₀/2) (3*t₀/2) → iteratedFDeriv ℝ ell v (x,r) = 0) ∧
  (∀ x r, x ∉ C → r ∈ Set.Ioo (t₀/2) (3*t₀/2) →
    velocity v x r = 0 ∧ acceleration v x r = 0 ∧
    (∀ j, spatial v j x r = 0 ∧ spatialSecond v j x r = 0 ∧ mixed v j x r = 0) ∧
    density v x r = 0 ∧ densityRate v x r = 0)
end WaveMapEnergy
open WaveMapEnergy

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace Translation
set_option autoImplicit false

namespace Local_T001
theorem yui_aux_0001 (n : ℕ) (m : ℕ) (u : Space n × Set.Ioi (0 : ℝ) → Value m) (q : Value m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : Smooth (ubar u q)) : yui_aux_type% "∀ (k : Fin m) (x : Space n) (t : ℝ), DifferentiableAt ℝ (fun p : Space n × ℝ => ubar u q p k) (x,t) → HasDerivAt (fun r => ubar u q (x,r) k) (fderiv ℝ (fun p : Space n × ℝ => ubar u q p k) (x,t) (0,1)) t ∧ HasFDerivAt (fun y => ubar u q (y,t) k) ((fderiv ℝ (fun p : Space n × ℝ => ubar u q p k) (x,t)).comp (ContinuousLinearMap.inl ℝ (Space n) ℝ)) x" := by
  intro k x t hd
  constructor
  · have hc := hd.hasFDerivAt.comp t (hasFDerivAt_prodMk_right (𝕜 := ℝ) x t)
    simpa [Function.comp_def] using hc.hasDerivAt
  · exact hd.hasFDerivAt.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x t)

end Local_T001
open Local_T001 in
theorem T001 (n : ℕ) (m : ℕ) (u : Space n × Set.Ioi (0 : ℝ) → Value m) (q : Value m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : Smooth (ubar u q)) :
    FirstCalculus (ubar u q) := by
  have hs : IsOpen {p : Space n × ℝ | 0 < p.2} := isOpen_lt continuous_const continuous_snd
  have hk : ∀ k : Fin m, ContDiffOn ℝ ∞ (fun p : Space n × ℝ => ubar u q p k) {p | 0 < p.2} := contDiffOn_pi.mp h_H002
  have hd : ∀ (k : Fin m) (x : Space n) (t : ℝ), 0 < t → DifferentiableAt ℝ (fun p : Space n × ℝ => ubar u q p k) (x,t) := by
    intro k x t ht
    exact ((hk k).contDiffAt (hs.mem_nhds ht)).differentiableAt (by simp)
  have hslice := fun k x t ht => (@yui_aux_0001 n m u q h_H001 h_H002 k x t (hd k x t ht))
  have hdf : ∀ k : Fin m, ContDiffOn ℝ ∞ (fderiv ℝ (fun p : Space n × ℝ => ubar u q p k)) {p | 0 < p.2} := by
    intro k
    exact ((contDiffOn_infty_iff_fderiv_of_isOpen hs).mp (hk k)).2
  have hv : ∀ (x : Space n) (t : ℝ), 0 < t → ∀ k : Fin m, velocity (ubar u q) x t k = fderiv ℝ (fun p : Space n × ℝ => ubar u q p k) (x,t) (0,1) := by
    intro x t ht k
    exact (hslice k x t ht).1.deriv
  have hp : ∀ (j : Fin n) (x : Space n) (t : ℝ), 0 < t → ∀ k : Fin m, spatial (ubar u q) j x t k = fderiv ℝ (fun p : Space n × ℝ => ubar u q p k) (x,t) (Pi.single j 1,0) := by
    intro j x t ht k
    change (fderiv ℝ (fun y => ubar u q (y,t) k) x) (Pi.single j 1) = _
    rw [(hslice k x t ht).2.fderiv]
    rfl
  refine ⟨h_H002, ?_, ?_, ?_, ?_⟩
  · apply contDiffOn_pi.mpr
    intro k
    exact ((hdf k).clm_apply (contDiffOn_const (c := ((0 : Space n), (1 : ℝ))))).congr (fun p ht => hv p.1 p.2 ht k)
  · intro j
    apply contDiffOn_pi.mpr
    intro k
    exact ((hdf k).clm_apply (contDiffOn_const (c := (Pi.single j (1 : ℝ), (0 : ℝ))))).congr (fun p ht => hp j p.1 p.2 ht k)
  · intro x t ht k
    rw [hv x t ht k]
    exact (hslice k x t ht).1
  · intro x t ht k
    exact (hslice k x t ht).2.differentiableAt.hasFDerivAt

namespace Local_T002
theorem yui_aux_0001 (n : ℕ) (m : ℕ) (u : Space n × Set.Ioi (0 : ℝ) → Value m) (q : Value m) (h_T001 : FirstCalculus (ubar u q)) : yui_aux_type% "∀ (x : Space n) (t : ℝ), HasFDerivAt (fun _ : Space n => t) (0 : Space n →L[ℝ] ℝ) x" := by
  intro x t
  exact hasFDerivAt_const t x

theorem yui_aux_0002 (n : ℕ) (m : ℕ) (u : Space n × Set.Ioi (0 : ℝ) → Value m) (q : Value m) (h_T001 : FirstCalculus (ubar u q)) : yui_aux_type% "∀ (f : Space n × ℝ → ℝ), ContDiffOn ℝ ∞ f {p | 0 < p.2} → ∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (fun r => f (x,r)) (fderiv ℝ f (x,t) (0,1)) t ∧ HasFDerivAt (fun y => f (y,t)) ((fderiv ℝ f (x,t)).comp ((ContinuousLinearMap.id ℝ (Space n)).prod 0)) x" := by
  intro f hf x t ht
  have ho : IsOpen {p : Space n × ℝ | 0 < p.2} := isOpen_lt continuous_const continuous_snd
  have hd : HasFDerivAt f (fderiv ℝ f (x,t)) (x,t) :=
    ((hf.contDiffAt (ho.mem_nhds ht)).differentiableAt (by simp)).hasFDerivAt
  constructor
  · exact hd.comp_hasDerivAt t ((hasDerivAt_const t x).prodMk (hasDerivAt_id t))
  · exact hd.comp x ((hasFDerivAt_id x).prodMk (@yui_aux_0001 n m u q h_T001 x t))

theorem yui_aux_0003 (n : ℕ) (m : ℕ) (u : Space n × Set.Ioi (0 : ℝ) → Value m) (q : Value m) (h_T001 : FirstCalculus (ubar u q)) : yui_aux_type% "∀ (f : Space n × ℝ → ℝ), ContDiffOn ℝ ∞ f {p | 0 < p.2} → (ContDiffOn ℝ ∞ (fun p : Space n × ℝ => deriv (fun r => f (p.1,r)) p.2) {p | 0 < p.2}) ∧ (∀ a : Space n, ContDiffOn ℝ ∞ (fun p : Space n × ℝ => fderiv ℝ (fun y => f (y,p.2)) p.1 a) {p | 0 < p.2}) ∧ (∀ (x : Space n) (t : ℝ), 0 < t → deriv (fun r => f (x,r)) t = fderiv ℝ f (x,t) (0,1) ∧ ∀ a : Space n, fderiv ℝ (fun y => f (y,t)) x a = fderiv ℝ f (x,t) (a,0))" := by
  intro f hf
  have ho : IsOpen {p : Space n × ℝ | 0 < p.2} := isOpen_lt continuous_const continuous_snd
  have hid := @yui_aux_0002 n m u q h_T001 f hf
  have he : ∀ (x : Space n) (t : ℝ), 0 < t → deriv (fun r => f (x,r)) t = fderiv ℝ f (x,t) (0,1) ∧ ∀ a : Space n, fderiv ℝ (fun y => f (y,t)) x a = fderiv ℝ f (x,t) (a,0) := by
    intro x t ht
    refine ⟨(hid x t ht).1.deriv, ?_⟩
    intro a
    rw [(hid x t ht).2.fderiv]
    simp
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ f) {p | 0 < p.2} := hf.fderiv_of_isOpen ho (by simp)
  refine ⟨?_, ?_, he⟩
  · exact (hD.clm_apply (contDiffOn_const (c := ((0 : Space n), (1 : ℝ))))).congr (fun p hp => (he p.1 p.2 hp).1)
  · intro a
    exact (hD.clm_apply (contDiffOn_const (c := (a, (0 : ℝ))))).congr (fun p hp => (he p.1 p.2 hp).2 a)

theorem yui_aux_0004 (n : ℕ) (m : ℕ) (u : Space n × Set.Ioi (0 : ℝ) → Value m) (q : Value m) (h_T001 : FirstCalculus (ubar u q)) : yui_aux_type% "∀ (f : Space n × ℝ → ℝ) (p : Space n × ℝ), ContDiffAt ℝ ∞ f p → IsSymmSndFDerivAt ℝ f p" := by
  intro f p hf
  apply hf.isSymmSndFDerivAt
  simp only [minSmoothness_of_isRCLikeNormedField]
  show ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
  exact WithTop.coe_le_coe.mpr le_top

theorem yui_aux_0005 (n : ℕ) (m : ℕ) (u : Space n × Set.Ioi (0 : ℝ) → Value m) (q : Value m) (h_T001 : FirstCalculus (ubar u q)) : yui_aux_type% "∀ (f : Space n × ℝ → ℝ), ContDiffOn ℝ ∞ f {p | 0 < p.2} → ∀ (a : Space n) (x : Space n) (t : ℝ), 0 < t → HasDerivAt (fun r => fderiv ℝ (fun y => f (y,r)) x a) (fderiv ℝ (fun y => deriv (fun r => f (y,r)) t) x a) t" := by
  intro f hf a x t ht
  have ho : IsOpen {p : Space n × ℝ | 0 < p.2} := isOpen_lt continuous_const continuous_snd
  have hp : {p : Space n × ℝ | 0 < p.2} ∈ 𝓝 (x,t) := ho.mem_nhds ht
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ f) {p | 0 < p.2} := hf.fderiv_of_isOpen ho (by simp)
  have hDD := ((hD.contDiffAt hp).differentiableAt (by simp)).hasFDerivAt
  have hg : HasFDerivAt (fun p : Space n × ℝ => fderiv ℝ (fun y => f (y,p.2)) p.1 a)
      ((fderiv ℝ (fderiv ℝ f) (x,t)).flip (a,0)) (x,t) := by
    have hbase : HasFDerivAt (fun p => fderiv ℝ f p (a,0))
        ((fderiv ℝ (fderiv ℝ f) (x,t)).flip (a,0)) (x,t) := by
      simpa using hDD.clm_apply (hasFDerivAt_const (a, (0 : ℝ)) (x,t))
    apply hbase.congr_of_eventuallyEq
    filter_upwards [hp] with p hp'
    exact ((@yui_aux_0003 n m u q h_T001 f hf).2.2 p.1 p.2 hp').2 a
  have hh : HasFDerivAt (fun p : Space n × ℝ => deriv (fun r => f (p.1,r)) p.2)
      ((fderiv ℝ (fderiv ℝ f) (x,t)).flip (0,1)) (x,t) := by
    have hbase : HasFDerivAt (fun p => fderiv ℝ f p (0,1))
        ((fderiv ℝ (fderiv ℝ f) (x,t)).flip (0,1)) (x,t) := by
      simpa using hDD.clm_apply (hasFDerivAt_const ((0 : Space n), (1 : ℝ)) (x,t))
    apply hbase.congr_of_eventuallyEq
    filter_upwards [hp] with p hp'
    exact ((@yui_aux_0003 n m u q h_T001 f hf).2.2 p.1 p.2 hp').1
  have hs := hh.comp x ((hasFDerivAt_id x).prodMk (@yui_aux_0001 n m u q h_T001 x t))
  have he : fderiv ℝ (fun y => deriv (fun r => f (y,r)) t) x a =
      fderiv ℝ (fderiv ℝ f) (x,t) (a,0) (0,1) := by
    simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.zero_apply, ContinuousLinearMap.flip_apply] using
      congrArg (fun L : Space n →L[ℝ] ℝ => L a) hs.fderiv
  rw [he]
  have hsym : fderiv ℝ (fderiv ℝ f) (x,t) (0,1) (a,0) =
      fderiv ℝ (fderiv ℝ f) (x,t) (a,0) (0,1) :=
    (@yui_aux_0004 n m u q h_T001 f (x,t) (hf.contDiffAt hp)) (0,1) (a,0)
  rw [← hsym]
  exact hg.comp_hasDerivAt t ((hasDerivAt_const t x).prodMk (hasDerivAt_id t))

end Local_T002
open Local_T002 in
theorem T002 (n : ℕ) (m : ℕ) (u : Space n × Set.Ioi (0 : ℝ) → Value m) (q : Value m) (h_T001 : FirstCalculus (ubar u q)) :
    SecondCalculus (ubar u q) := by
  have hfirst := h_T001
  rcases hfirst with ⟨hs, hv, hsp, _, _⟩
  have hvk : ∀ k : Fin m, ContDiffOn ℝ ∞
      (fun p : Space n × ℝ => velocity (ubar u q) p.1 p.2 k) {p | 0 < p.2} :=
    contDiffOn_pi.mp hv
  have hspk : ∀ (j : Fin n) (k : Fin m), ContDiffOn ℝ ∞
      (fun p : Space n × ℝ => spatial (ubar u q) j p.1 p.2 k) {p | 0 < p.2} :=
    fun j => contDiffOn_pi.mp (hsp j)
  have huk : ∀ k : Fin m, ContDiffOn ℝ ∞
      (fun p : Space n × ℝ => ubar u q p k) {p | 0 < p.2} :=
    contDiffOn_pi.mp hs
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply contDiffOn_pi.mpr
    intro k
    exact (@yui_aux_0003 n m u q h_T001
      (fun p => velocity (ubar u q) p.1 p.2 k) (hvk k)).1
  · intro j
    apply contDiffOn_pi.mpr
    intro k
    exact (@yui_aux_0003 n m u q h_T001
      (fun p => spatial (ubar u q) j p.1 p.2 k) (hspk j k)).2.1 (Pi.single j 1)
  · intro j
    apply contDiffOn_pi.mpr
    intro k
    exact (@yui_aux_0003 n m u q h_T001
      (fun p => velocity (ubar u q) p.1 p.2 k) (hvk k)).2.1 (Pi.single j 1)
  · intro x t ht k
    exact ((@yui_aux_0002 n m u q h_T001
      (fun p => velocity (ubar u q) p.1 p.2 k) (hvk k) x t ht).1).differentiableAt.hasDerivAt
  · intro j x t ht k
    exact @yui_aux_0005 n m u q h_T001
      (fun p => ubar u q p k) (huk k) (Pi.single j 1) x t ht
  · intro j x t ht k
    constructor
    · exact ((@yui_aux_0002 n m u q h_T001
        (fun p => velocity (ubar u q) p.1 p.2 k) (hvk k) x t ht).2).differentiableAt.hasFDerivAt
    · exact ((@yui_aux_0002 n m u q h_T001
        (fun p => spatial (ubar u q) j p.1 p.2 k) (hspk j k) x t ht).2).differentiableAt.hasFDerivAt

namespace Local_T003
theorem yui_aux_0001 (n : ℕ) (m : ℕ) (u : Space n × Set.Ioi (0 : ℝ) → Value m) (q : Value m) (h_T001 : FirstCalculus (ubar u q)) (h_T002 : SecondCalculus (ubar u q)) : yui_aux_type% "ContDiffOn ℝ ∞ (fun p : Space n × ℝ => density (ubar u q) p.1 p.2) {p | 0 < p.2} ∧ ContDiffOn ℝ ∞ (fun p : Space n × ℝ => densityRate (ubar u q) p.1 p.2) {p | 0 < p.2}" := by
  have hdot : ∀ (f g : Space n × ℝ → Value m),
      ContDiffOn ℝ ∞ f {p | 0 < p.2} →
      ContDiffOn ℝ ∞ g {p | 0 < p.2} →
      ContDiffOn ℝ ∞ (fun p => dot (f p) (g p)) {p | 0 < p.2} := by
    intro f g hf hg
    unfold dot
    exact ContDiffOn.sum (fun k _ =>
      (contDiffOn_pi.mp hf k).mul (contDiffOn_pi.mp hg k))
  have hv := h_T001.2.1
  have hp := h_T001.2.2.1
  have ha := h_T002.1
  have hw := h_T002.2.2.1
  constructor
  · unfold density normSq
    exact (hdot _ _ hv hv).add (ContDiffOn.sum (fun j _ => hdot _ _ (hp j) (hp j)))
  · unfold densityRate
    exact (contDiffOn_const.mul (hdot _ _ hv ha)).add
      (contDiffOn_const.mul (ContDiffOn.sum (fun j _ => hdot _ _ (hp j) (hw j))))

theorem yui_aux_0002 (n : ℕ) (m : ℕ) (u : Space n × Set.Ioi (0 : ℝ) → Value m) (q : Value m) (h_T001 : FirstCalculus (ubar u q)) (h_T002 : SecondCalculus (ubar u q)) : yui_aux_type% "∀ (f : ℝ → ℝ) (a t : ℝ), HasDerivAt f a t → HasDerivAt (fun r => f r * f r) (2 * (f t * a)) t" := by
  intro f a t hf
  have heq : a * f t + f t * a = 2 * (f t * a) := by ring
  simpa only [heq] using hf.fun_mul hf

theorem yui_aux_0003 (n : ℕ) (m : ℕ) (u : Space n × Set.Ioi (0 : ℝ) → Value m) (q : Value m) (h_T001 : FirstCalculus (ubar u q)) (h_T002 : SecondCalculus (ubar u q)) : yui_aux_type% "∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (fun r => density (ubar u q) x r) (densityRate (ubar u q) x t) t" := by
  intro x t ht
  have hsquare : ∀ (f : ℝ → Value m) (a : Value m),
      (∀ k, HasDerivAt (fun r => f r k) (a k) t) →
      HasDerivAt (fun r => normSq (f r)) (2 * dot (f t) a) t := by
    intro f a hf
    have hk : ∀ k : Fin m, HasDerivAt (fun r => f r k * f r k)
        (2 * (f t k * a k)) t := by
      intro k
      exact (@yui_aux_0002 n m u q h_T001 h_T002) (fun r => f r k) (a k) t (hf k)
    have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ => hk k)
    simpa only [normSq, dot, Finset.mul_sum] using hsum
  have hv := hsquare (fun r => velocity (ubar u q) x r) (acceleration (ubar u q) x t)
    (h_T002.2.2.2.1 x t ht)
  have hp : ∀ j : Fin n, HasDerivAt (fun r => normSq (spatial (ubar u q) j x r))
      (2 * dot (spatial (ubar u q) j x t) (mixed (ubar u q) j x t)) t := by
    intro j
    exact hsquare _ _ (h_T002.2.2.2.2.1 j x t ht)
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => hp j)
  simpa only [density, densityRate, Finset.mul_sum] using hv.fun_add hsum

theorem yui_aux_0004 (n : ℕ) (m : ℕ) (u : Space n × Set.Ioi (0 : ℝ) → Value m) (q : Value m) (h_T001 : FirstCalculus (ubar u q)) (h_T002 : SecondCalculus (ubar u q)) : yui_aux_type% "∀ (x : Space n) (t : Set.Ioi (0 : ℝ)), (ubar u q) (x,t) = u (x,t)" := by
  intro x t
  exact dif_pos (show 0 < (t : ℝ) from t.property)

end Local_T003
open Local_T003 in
theorem T003 (n : ℕ) (m : ℕ) (u : Space n × Set.Ioi (0 : ℝ) → Value m) (q : Value m) (h_T001 : FirstCalculus (ubar u q)) (h_T002 : SecondCalculus (ubar u q)) :
    FirstCalculus (ubar u q) ∧ SecondCalculus (ubar u q) ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => density (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => densityRate (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
(∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (fun r => density (ubar u q) x r) (densityRate (ubar u q) x t) t) ∧
(∀ (j : Fin n) (x : Space n) (t : ℝ), 0 < t → ∀ k : Fin m,
 fderiv ℝ (fun y => (ubar u q) (y,t) k) x (Pi.single j 1) = spatial (ubar u q) j x t k ∧
 fderiv ℝ (fun y => velocity (ubar u q) y t k) x (Pi.single j 1) = mixed (ubar u q) j x t k ∧
 fderiv ℝ (fun y => spatial (ubar u q) j y t k) x (Pi.single j 1) = spatialSecond (ubar u q) j x t k) ∧
(∀ (x : Space n) (t : Set.Ioi (0 : ℝ)), (ubar u q) (x,t) = u (x,t)) ∧
(∀ (x : Space n) (t : ℝ), t ≤ 0 → (ubar u q) (x,t) = q) := by
  have hs := @yui_aux_0001 n m u q h_T001 h_T002
  refine ⟨h_T001, h_T002, hs.1, hs.2,
    @yui_aux_0003 n m u q h_T001 h_T002, ?_,
    @yui_aux_0004 n m u q h_T001 h_T002, ?_⟩
  · intro j x t ht k
    exact ⟨rfl, rfl, rfl⟩
  · intro x t ht
    exact dif_neg (not_lt.mpr ht)

namespace Local_T004
theorem yui_aux_0001 (n : ℕ) (m : ℕ) (u : Space n × Set.Ioi (0 : ℝ) → Value m) (q : Value m) (h_H006 : CompactPerturbation (ubar u q) q) (h_T003 : FirstCalculus (ubar u q) ∧ SecondCalculus (ubar u q) ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => density (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => densityRate (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
(∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (fun r => density (ubar u q) x r) (densityRate (ubar u q) x t) t) ∧
(∀ (j : Fin n) (x : Space n) (t : ℝ), 0 < t → ∀ k : Fin m,
 fderiv ℝ (fun y => (ubar u q) (y,t) k) x (Pi.single j 1) = spatial (ubar u q) j x t k ∧
 fderiv ℝ (fun y => velocity (ubar u q) y t k) x (Pi.single j 1) = mixed (ubar u q) j x t k ∧
 fderiv ℝ (fun y => spatial (ubar u q) j y t k) x (Pi.single j 1) = spatialSecond (ubar u q) j x t k) ∧
(∀ (x : Space n) (t : Set.Ioi (0 : ℝ)), (ubar u q) (x,t) = u (x,t)) ∧
(∀ (x : Space n) (t : ℝ), t ≤ 0 → (ubar u q) (x,t) = q)) : yui_aux_type% "∀ (f : Space n → ℝ) (x : Space n) (c : ℝ), f =ᶠ[𝓝 x] (fun _ => c) → fderiv ℝ f x = 0" := by
  intro f x c he
  rw [he.fderiv_eq, fderiv_const_apply]

theorem yui_aux_0002 (n : ℕ) (m : ℕ) (u : Space n × Set.Ioi (0 : ℝ) → Value m) (q : Value m) (h_H006 : CompactPerturbation (ubar u q) q) (h_T003 : FirstCalculus (ubar u q) ∧ SecondCalculus (ubar u q) ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => density (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => densityRate (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
(∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (fun r => density (ubar u q) x r) (densityRate (ubar u q) x t) t) ∧
(∀ (j : Fin n) (x : Space n) (t : ℝ), 0 < t → ∀ k : Fin m,
 fderiv ℝ (fun y => (ubar u q) (y,t) k) x (Pi.single j 1) = spatial (ubar u q) j x t k ∧
 fderiv ℝ (fun y => velocity (ubar u q) y t k) x (Pi.single j 1) = mixed (ubar u q) j x t k ∧
 fderiv ℝ (fun y => spatial (ubar u q) j y t k) x (Pi.single j 1) = spatialSecond (ubar u q) j x t k) ∧
(∀ (x : Space n) (t : Set.Ioi (0 : ℝ)), (ubar u q) (x,t) = u (x,t)) ∧
(∀ (x : Space n) (t : ℝ), t ≤ 0 → (ubar u q) (x,t) = q)) : yui_aux_type% "∀ (C : Set (Space n)) (a b : ℝ), IsClosed C → (∀ x r, x ∉ C → r ∈ Set.Ioo a b → (ubar u q) (x,r) = q) → ∀ x r, x ∉ C → r ∈ Set.Ioo a b → velocity (ubar u q) x r = 0 ∧ ∀ j, spatial (ubar u q) j x r = 0" := by
  intro C a b hC hv x r hx hr
  constructor
  · funext k
    have he : (fun s => (ubar u q) (x,s) k) =ᶠ[𝓝 r] (fun _ => q k) := by
      filter_upwards [isOpen_Ioo.mem_nhds hr] with s hs
      exact congrFun (hv x s hx hs) k
    change deriv (fun s => (ubar u q) (x,s) k) r = 0
    rw [he.deriv_eq, deriv_const]
  · intro j
    funext k
    have he : (fun y => (ubar u q) (y,r) k) =ᶠ[𝓝 x] (fun _ => q k) := by
      filter_upwards [hC.isOpen_compl.mem_nhds hx] with y hy
      exact congrFun (hv y r hy hr) k
    change fderiv ℝ (fun y => (ubar u q) (y,r) k) x (Pi.single j 1) = 0
    rw [@yui_aux_0001 n m u q h_H006 h_T003 _ x (q k) he]
    rfl

end Local_T004
open Local_T004 in
theorem T004 (n : ℕ) (m : ℕ) (u : Space n × Set.Ioi (0 : ℝ) → Value m) (q : Value m) (h_H006 : CompactPerturbation (ubar u q) q) (h_T003 : FirstCalculus (ubar u q) ∧ SecondCalculus (ubar u q) ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => density (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => densityRate (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
(∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (fun r => density (ubar u q) x r) (densityRate (ubar u q) x t) t) ∧
(∀ (j : Fin n) (x : Space n) (t : ℝ), 0 < t → ∀ k : Fin m,
 fderiv ℝ (fun y => (ubar u q) (y,t) k) x (Pi.single j 1) = spatial (ubar u q) j x t k ∧
 fderiv ℝ (fun y => velocity (ubar u q) y t k) x (Pi.single j 1) = mixed (ubar u q) j x t k ∧
 fderiv ℝ (fun y => spatial (ubar u q) j y t k) x (Pi.single j 1) = spatialSecond (ubar u q) j x t k) ∧
(∀ (x : Space n) (t : Set.Ioi (0 : ℝ)), (ubar u q) (x,t) = u (x,t)) ∧
(∀ (x : Space n) (t : ℝ), t ≤ 0 → (ubar u q) (x,t) = q)) :
    ∀ t₀ : ℝ, 0 < t₀ → ∃ C : Set (Space n), SlabVanishing (ubar u q) q t₀ C := by
  intro t₀ ht₀
  obtain ⟨C, hC, hv⟩ := h_H006 (t₀ / 2) (3 * t₀ / 2) (by linarith) (by linarith)
  have hv' : ∀ x r, x ∉ C → r ∈ Set.Ioo (t₀ / 2) (3 * t₀ / 2) →
      (ubar u q) (x,r) = q := by
    intro x r hx hr
    exact hv x r hx ⟨hr.1.le, hr.2.le⟩
  have hfirst := @yui_aux_0002 n m u q h_H006 h_T003 C (t₀ / 2) (3 * t₀ / 2)
    hC.isClosed hv'
  refine ⟨C, hC, hv, ?_, ?_⟩
  · intro ell hell x r hx hr
    have hO : IsOpen (Cᶜ ×ˢ Set.Ioo (t₀ / 2) (3 * t₀ / 2)) :=
      hC.isClosed.isOpen_compl.prod isOpen_Ioo
    have he : ubar u q =ᶠ[𝓝 (x,r)] (fun _ => q) := by
      filter_upwards [hO.mem_nhds ⟨hx, hr⟩] with p hp
      exact hv' p.1 p.2 hp.1 hp.2
    rw [(he.iteratedFDeriv ℝ ell).self_of_nhds,
      iteratedFDeriv_const_of_ne (Nat.ne_of_gt hell)]
    rfl
  · intro x r hx hr
    obtain ⟨hV, hP⟩ := hfirst x r hx hr
    have hA : acceleration (ubar u q) x r = 0 := by
      funext k
      have he : (fun s => velocity (ubar u q) x s k) =ᶠ[𝓝 r] (fun _ => (0 : ℝ)) := by
        filter_upwards [isOpen_Ioo.mem_nhds hr] with s hs
        exact congrFun (hfirst x s hx hs).1 k
      change deriv (fun s => velocity (ubar u q) x s k) r = 0
      rw [he.deriv_eq, deriv_const]
    have hS : ∀ j, spatialSecond (ubar u q) j x r = 0 := by
      intro j
      funext k
      have he : (fun y => spatial (ubar u q) j y r k) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
        filter_upwards [hC.isClosed.isOpen_compl.mem_nhds hx] with y hy
        exact congrFun ((hfirst y r hy hr).2 j) k
      change fderiv ℝ (fun y => spatial (ubar u q) j y r k) x (Pi.single j 1) = 0
      rw [@yui_aux_0001 n m u q h_H006 h_T003 _ x 0 he]
      rfl
    have hW : ∀ j, mixed (ubar u q) j x r = 0 := by
      intro j
      funext k
      have he : (fun y => velocity (ubar u q) y r k) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
        filter_upwards [hC.isClosed.isOpen_compl.mem_nhds hx] with y hy
        exact congrFun (hfirst y r hy hr).1 k
      change fderiv ℝ (fun y => velocity (ubar u q) y r k) x (Pi.single j 1) = 0
      rw [@yui_aux_0001 n m u q h_H006 h_T003 _ x 0 he]
      rfl
    refine ⟨hV, hA, (fun j => ⟨hP j, hS j, hW j⟩), ?_, ?_⟩
    · simp [density, hV, hP, normSq, dot]
    · simp [densityRate, hV, hP, dot]

namespace Local_T005
theorem yui_aux_0001 (n : ℕ) (m : ℕ) (u : Space n × Set.Ioi (0 : ℝ) → Value m) (q : Value m) (h_T003 : FirstCalculus (ubar u q) ∧ SecondCalculus (ubar u q) ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => density (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => densityRate (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
(∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (fun r => density (ubar u q) x r) (densityRate (ubar u q) x t) t) ∧
(∀ (j : Fin n) (x : Space n) (t : ℝ), 0 < t → ∀ k : Fin m,
 fderiv ℝ (fun y => (ubar u q) (y,t) k) x (Pi.single j 1) = spatial (ubar u q) j x t k ∧
 fderiv ℝ (fun y => velocity (ubar u q) y t k) x (Pi.single j 1) = mixed (ubar u q) j x t k ∧
 fderiv ℝ (fun y => spatial (ubar u q) j y t k) x (Pi.single j 1) = spatialSecond (ubar u q) j x t k) ∧
(∀ (x : Space n) (t : Set.Ioi (0 : ℝ)), (ubar u q) (x,t) = u (x,t)) ∧
(∀ (x : Space n) (t : ℝ), t ≤ 0 → (ubar u q) (x,t) = q)) (h_T004 : ∀ t₀ : ℝ, 0 < t₀ → ∃ C : Set (Space n), SlabVanishing (ubar u q) q t₀ C) : yui_aux_type% "∀ r : ℝ, 0 < r → Continuous (fun x : Space n => velocity (ubar u q) x r)" := by
  intro r hr
  exact h_T003.1.2.1.continuousOn.comp_continuous
    (continuous_id.prodMk continuous_const) (fun x => hr)

theorem yui_aux_0002 (n : ℕ) (m : ℕ) (u : Space n × Set.Ioi (0 : ℝ) → Value m) (q : Value m) (h_T003 : FirstCalculus (ubar u q) ∧ SecondCalculus (ubar u q) ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => density (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => densityRate (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
(∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (fun r => density (ubar u q) x r) (densityRate (ubar u q) x t) t) ∧
(∀ (j : Fin n) (x : Space n) (t : ℝ), 0 < t → ∀ k : Fin m,
 fderiv ℝ (fun y => (ubar u q) (y,t) k) x (Pi.single j 1) = spatial (ubar u q) j x t k ∧
 fderiv ℝ (fun y => velocity (ubar u q) y t k) x (Pi.single j 1) = mixed (ubar u q) j x t k ∧
 fderiv ℝ (fun y => spatial (ubar u q) j y t k) x (Pi.single j 1) = spatialSecond (ubar u q) j x t k) ∧
(∀ (x : Space n) (t : Set.Ioi (0 : ℝ)), (ubar u q) (x,t) = u (x,t)) ∧
(∀ (x : Space n) (t : ℝ), t ≤ 0 → (ubar u q) (x,t) = q)) (h_T004 : ∀ t₀ : ℝ, 0 < t₀ → ∃ C : Set (Space n), SlabVanishing (ubar u q) q t₀ C) : yui_aux_type% "∀ (r : ℝ), 0 < r → ∀ h ∈ sections (ubar u q) r, Continuous h" := by
  intro r hr
  have slice {F : Type} [TopologicalSpace F] (f : Space n × ℝ → F)
      (hf : ContinuousOn f {p | 0 < p.2}) :
      Continuous (fun x : Space n => f (x,r)) :=
    hf.comp_continuous (continuous_id.prodMk continuous_const) (fun x => hr)
  have hv := yui_aux_0001 n m u q h_T003 h_T004 r hr
  have ha := slice _ h_T003.2.1.1.continuousOn
  have hs (j : Fin n) := slice _ (h_T003.1.2.2.1 j).continuousOn
  have hss (j : Fin n) := slice _ (h_T003.2.1.2.1 j).continuousOn
  have hm (j : Fin n) := slice _ (h_T003.2.1.2.2.1 j).continuousOn
  have he := slice _ h_T003.2.2.1.continuousOn
  have hd := slice _ h_T003.2.2.2.1.continuousOn
  have hvk (k : Fin m) := (continuous_apply k).comp hv
  have hak (k : Fin m) := (continuous_apply k).comp ha
  have hsk (j : Fin n) (k : Fin m) := (continuous_apply k).comp (hs j)
  have hssk (j : Fin n) (k : Fin m) := (continuous_apply k).comp (hss j)
  have hmk (j : Fin n) (k : Fin m) := (continuous_apply k).comp (hm j)
  intro h hh
  rcases hh with hh | hh | ⟨k,hh⟩ | ⟨j,k,hh⟩ | hh | ⟨j,hh⟩
  · subst h; exact he
  · subst h; exact hd
  · rcases hh with hh | hh | hh <;> subst h <;> fun_prop
  · rcases hh with hh | hh | hh | hh | hh | hh | hh <;> subst h <;> fun_prop
  · subst h
    unfold dot
    fun_prop
  · rcases hh with hh | hh | hh | hh <;> subst h <;> unfold dot <;> fun_prop

theorem yui_aux_0003 (n : ℕ) (m : ℕ) (u : Space n × Set.Ioi (0 : ℝ) → Value m) (q : Value m) (h_T003 : FirstCalculus (ubar u q) ∧ SecondCalculus (ubar u q) ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => density (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => densityRate (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
(∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (fun r => density (ubar u q) x r) (densityRate (ubar u q) x t) t) ∧
(∀ (j : Fin n) (x : Space n) (t : ℝ), 0 < t → ∀ k : Fin m,
 fderiv ℝ (fun y => (ubar u q) (y,t) k) x (Pi.single j 1) = spatial (ubar u q) j x t k ∧
 fderiv ℝ (fun y => velocity (ubar u q) y t k) x (Pi.single j 1) = mixed (ubar u q) j x t k ∧
 fderiv ℝ (fun y => spatial (ubar u q) j y t k) x (Pi.single j 1) = spatialSecond (ubar u q) j x t k) ∧
(∀ (x : Space n) (t : Set.Ioi (0 : ℝ)), (ubar u q) (x,t) = u (x,t)) ∧
(∀ (x : Space n) (t : ℝ), t ≤ 0 → (ubar u q) (x,t) = q)) (h_T004 : ∀ t₀ : ℝ, 0 < t₀ → ∃ C : Set (Space n), SlabVanishing (ubar u q) q t₀ C) : yui_aux_type% "∀ (t₀ : ℝ) (C : Set (Space n)), SlabVanishing (ubar u q) q t₀ C → ∀ r ∈ Set.Ioo (t₀/2) (3*t₀/2), ∀ h ∈ sections (ubar u q) r, ∀ x, x ∉ C → h x = 0" := by
  intro t₀ C hC r hr h hh x hx
  obtain ⟨hv, ha, hs, he, hd⟩ := hC.2.2.2 x r hx hr
  have hsp (j : Fin n) := (hs j).1
  have hss (j : Fin n) := (hs j).2.1
  have hm (j : Fin n) := (hs j).2.2
  rcases hh with hh | hh | ⟨k,hh⟩ | ⟨j,k,hh⟩ | hh | ⟨j,hh⟩
  · subst h; exact he
  · subst h; exact hd
  · rcases hh with hh | hh | hh <;> subst h <;> simp [hv, ha]
  · rcases hh with hh | hh | hh | hh | hh | hh | hh <;> subst h <;>
      simp [hv, ha, hsp, hss, hm]
  · subst h; simp [dot, hv, ha]
  · rcases hh with hh | hh | hh | hh <;> subst h <;> simp [dot, hv, hsp, hss, hm]

theorem yui_aux_0004 (n : ℕ) (m : ℕ) (u : Space n × Set.Ioi (0 : ℝ) → Value m) (q : Value m) (h_T003 : FirstCalculus (ubar u q) ∧ SecondCalculus (ubar u q) ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => density (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => densityRate (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
(∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (fun r => density (ubar u q) x r) (densityRate (ubar u q) x t) t) ∧
(∀ (j : Fin n) (x : Space n) (t : ℝ), 0 < t → ∀ k : Fin m,
 fderiv ℝ (fun y => (ubar u q) (y,t) k) x (Pi.single j 1) = spatial (ubar u q) j x t k ∧
 fderiv ℝ (fun y => velocity (ubar u q) y t k) x (Pi.single j 1) = mixed (ubar u q) j x t k ∧
 fderiv ℝ (fun y => spatial (ubar u q) j y t k) x (Pi.single j 1) = spatialSecond (ubar u q) j x t k) ∧
(∀ (x : Space n) (t : Set.Ioi (0 : ℝ)), (ubar u q) (x,t) = u (x,t)) ∧
(∀ (x : Space n) (t : ℝ), t ≤ 0 → (ubar u q) (x,t) = q)) (h_T004 : ∀ t₀ : ℝ, 0 < t₀ → ∃ C : Set (Space n), SlabVanishing (ubar u q) q t₀ C) : yui_aux_type% "∀ (C : Set (Space n)) (h : Space n → ℝ), IsCompact C → Continuous h → (∀ x, x ∉ C → h x = 0) → SupportedSection C h" := by
  intro C h hC hc hz
  have hs : Function.support h ⊆ C := by
    intro x hx
    by_contra hn
    exact hx (hz x hn)
  have ht : tsupport h ⊆ C := closure_minimal hs hC.isClosed
  have hk : HasCompactSupport h := hC.of_isClosed_subset (isClosed_tsupport h) ht
  exact ⟨hc, ht, hk, hc.integrable_of_hasCompactSupport hk⟩

end Local_T005
open Local_T005 in
theorem T005 (n : ℕ) (m : ℕ) (u : Space n × Set.Ioi (0 : ℝ) → Value m) (q : Value m) (h_T003 : FirstCalculus (ubar u q) ∧ SecondCalculus (ubar u q) ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => density (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => densityRate (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
(∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (fun r => density (ubar u q) x r) (densityRate (ubar u q) x t) t) ∧
(∀ (j : Fin n) (x : Space n) (t : ℝ), 0 < t → ∀ k : Fin m,
 fderiv ℝ (fun y => (ubar u q) (y,t) k) x (Pi.single j 1) = spatial (ubar u q) j x t k ∧
 fderiv ℝ (fun y => velocity (ubar u q) y t k) x (Pi.single j 1) = mixed (ubar u q) j x t k ∧
 fderiv ℝ (fun y => spatial (ubar u q) j y t k) x (Pi.single j 1) = spatialSecond (ubar u q) j x t k) ∧
(∀ (x : Space n) (t : Set.Ioi (0 : ℝ)), (ubar u q) (x,t) = u (x,t)) ∧
(∀ (x : Space n) (t : ℝ), t ≤ 0 → (ubar u q) (x,t) = q)) (h_T004 : ∀ t₀ : ℝ, 0 < t₀ → ∃ C : Set (Space n), SlabVanishing (ubar u q) q t₀ C) :
    (∀ t₀ : ℝ, 0 < t₀ → ∃ C : Set (Space n),
 SlabVanishing (ubar u q) q t₀ C ∧
 ∀ r ∈ Set.Ioo (t₀/2) (3*t₀/2),
 ∀ h ∈ Submodule.span ℝ (sections (ubar u q) r), SupportedSection C h) ∧
(∀ t : ℝ, 0 < t → Integrable (fun x => density (ubar u q) x t)) := by
  classical
  have hall : ∀ t₀ : ℝ, 0 < t₀ → ∃ C : Set (Space n),
      SlabVanishing (ubar u q) q t₀ C ∧
      ∀ r ∈ Set.Ioo (t₀/2) (3*t₀/2),
      ∀ h ∈ Submodule.span ℝ (sections (ubar u q) r), SupportedSection C h := by
    intro t₀ ht₀
    obtain ⟨C, hC⟩ := h_T004 t₀ ht₀
    refine ⟨C, hC, ?_⟩
    intro r hr h hh
    have hrpos : 0 < r := by linarith [hr.1]
    have hp : Continuous h ∧ ∀ x, x ∉ C → h x = 0 := by
      induction hh using Submodule.span_induction with
      | mem f hf =>
        exact ⟨yui_aux_0002 n m u q h_T003 h_T004 r hrpos f hf,
          yui_aux_0003 n m u q h_T003 h_T004 t₀ C hC r hr f hf⟩
      | zero =>
        exact ⟨continuous_const, fun x hx => rfl⟩
      | add f g hf hg hpf hpg =>
        refine ⟨hpf.1.add hpg.1, ?_⟩
        intro x hx
        change f x + g x = 0
        rw [hpf.2 x hx, hpg.2 x hx, add_zero]
      | smul a f hf hpf =>
        refine ⟨continuous_const.smul hpf.1, ?_⟩
        intro x hx
        change a • f x = 0
        rw [hpf.2 x hx, smul_zero]
    exact yui_aux_0004 n m u q h_T003 h_T004 C h hC.1 hp.1 hp.2
  refine ⟨hall, ?_⟩
  intro t ht
  obtain ⟨C, hC, hs⟩ := hall t ht
  have hmem : t ∈ Set.Ioo (t/2) (3*t/2) := by constructor <;> linarith
  have hgen : (fun x => density (ubar u q) x t) ∈ sections (ubar u q) t :=
    Or.inl rfl
  exact (hs t hmem _ (Submodule.subset_span hgen)).2.2.2

namespace Local_T006
theorem yui_aux_0001 (n : ℕ) (m : ℕ) (u : Space n × Set.Ioi (0 : ℝ) → Value m) (q : Value m) (h_T003 : FirstCalculus (ubar u q) ∧ SecondCalculus (ubar u q) ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => density (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => densityRate (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
(∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (fun r => density (ubar u q) x r) (densityRate (ubar u q) x t) t) ∧
(∀ (j : Fin n) (x : Space n) (t : ℝ), 0 < t → ∀ k : Fin m,
 fderiv ℝ (fun y => (ubar u q) (y,t) k) x (Pi.single j 1) = spatial (ubar u q) j x t k ∧
 fderiv ℝ (fun y => velocity (ubar u q) y t k) x (Pi.single j 1) = mixed (ubar u q) j x t k ∧
 fderiv ℝ (fun y => spatial (ubar u q) j y t k) x (Pi.single j 1) = spatialSecond (ubar u q) j x t k) ∧
(∀ (x : Space n) (t : Set.Ioi (0 : ℝ)), (ubar u q) (x,t) = u (x,t)) ∧
(∀ (x : Space n) (t : ℝ), t ≤ 0 → (ubar u q) (x,t) = q)) (h_T005 : (∀ t₀ : ℝ, 0 < t₀ → ∃ C : Set (Space n),
 SlabVanishing (ubar u q) q t₀ C ∧
 ∀ r ∈ Set.Ioo (t₀/2) (3*t₀/2),
 ∀ h ∈ Submodule.span ℝ (sections (ubar u q) r), SupportedSection C h) ∧
(∀ t : ℝ, 0 < t → Integrable (fun x => density (ubar u q) x t))) : yui_aux_type% "∀ (t₀ : ℝ), 0 < t₀ → ∀ C : Set (Space n), IsCompact C → ∃ B : ℝ, 0 ≤ B ∧ Integrable (C.indicator (fun _ => B)) volume ∧ ∀ x ∈ C, ∀ r ∈ Set.Icc (t₀-t₀/4) (t₀+t₀/4), ‖densityRate (ubar u q) x r‖ ≤ B" := by
  intro t₀ ht C hC
  have hK : IsCompact (C ×ˢ Set.Icc (t₀-t₀/4) (t₀+t₀/4)) := hC.prod isCompact_Icc
  have hc : ContinuousOn (fun p : Space n × ℝ => densityRate (ubar u q) p.1 p.2) (C ×ˢ Set.Icc (t₀-t₀/4) (t₀+t₀/4)) := by
    apply h_T003.2.2.2.1.continuousOn.mono
    intro p hp
    change 0 < p.2
    have hl := hp.2.1
    linarith
  obtain ⟨B₀, hB₀⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨max B₀ 0, le_max_right _ _, ?_, ?_⟩
  · have hi : IntegrableOn (fun _ : Space n => max B₀ 0) C volume := integrableOn_const hC.measure_ne_top
    exact hi.integrable_indicator hC.measurableSet
  · intro x hx r hr
    exact (hB₀ (x,r) ⟨hx,hr⟩).trans (le_max_left _ _)

end Local_T006
open Local_T006 in
theorem T006 (n : ℕ) (m : ℕ) (u : Space n × Set.Ioi (0 : ℝ) → Value m) (q : Value m) (h_T003 : FirstCalculus (ubar u q) ∧ SecondCalculus (ubar u q) ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => density (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => densityRate (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
(∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (fun r => density (ubar u q) x r) (densityRate (ubar u q) x t) t) ∧
(∀ (j : Fin n) (x : Space n) (t : ℝ), 0 < t → ∀ k : Fin m,
 fderiv ℝ (fun y => (ubar u q) (y,t) k) x (Pi.single j 1) = spatial (ubar u q) j x t k ∧
 fderiv ℝ (fun y => velocity (ubar u q) y t k) x (Pi.single j 1) = mixed (ubar u q) j x t k ∧
 fderiv ℝ (fun y => spatial (ubar u q) j y t k) x (Pi.single j 1) = spatialSecond (ubar u q) j x t k) ∧
(∀ (x : Space n) (t : Set.Ioi (0 : ℝ)), (ubar u q) (x,t) = u (x,t)) ∧
(∀ (x : Space n) (t : ℝ), t ≤ 0 → (ubar u q) (x,t) = q)) (h_T005 : (∀ t₀ : ℝ, 0 < t₀ → ∃ C : Set (Space n),
 SlabVanishing (ubar u q) q t₀ C ∧
 ∀ r ∈ Set.Ioo (t₀/2) (3*t₀/2),
 ∀ h ∈ Submodule.span ℝ (sections (ubar u q) r), SupportedSection C h) ∧
(∀ t : ℝ, 0 < t → Integrable (fun x => density (ubar u q) x t))) :
    ∀ t₀ : ℝ, 0 < t₀ →
 ∃ b : Space n → ℝ,
 (Set.Ioo (t₀-t₀/4) (t₀+t₀/4)) ∈ 𝓝 t₀ ∧ (Set.Ioo (t₀-t₀/4) (t₀+t₀/4)) ⊆ Set.Ioi (0 : ℝ) ∧
 (∀ᶠ r in 𝓝 t₀, AEStronglyMeasurable (fun x => density (ubar u q) x r) volume) ∧
 Integrable (fun x => density (ubar u q) x t₀) ∧
 AEStronglyMeasurable (fun x => densityRate (ubar u q) x t₀) volume ∧
 (∀ᵐ x ∂volume, ∀ r ∈ (Set.Ioo (t₀-t₀/4) (t₀+t₀/4)), ‖densityRate (ubar u q) x r‖ ≤ b x) ∧
 Integrable b ∧
 (∀ᵐ x ∂volume, ∀ r ∈ (Set.Ioo (t₀-t₀/4) (t₀+t₀/4)), HasDerivAt (fun a => density (ubar u q) x a) (densityRate (ubar u q) x r) r) := by
  intro t₀ ht₀
  obtain ⟨C, hslab, hsections⟩ := h_T005.1 t₀ ht₀
  obtain ⟨B, hB, hbi, hbound⟩ := yui_aux_0001 n m u q h_T003 h_T005 t₀ ht₀ C hslab.1
  have hnh : Set.Ioo (t₀-t₀/4) (t₀+t₀/4) ∈ 𝓝 t₀ := Ioo_mem_nhds (by linarith) (by linarith)
  have hpos : Set.Ioo (t₀-t₀/4) (t₀+t₀/4) ⊆ Set.Ioi (0 : ℝ) := by
    intro r hr
    change 0 < r
    have := hr.1
    linarith
  have hinside : Set.Ioo (t₀-t₀/4) (t₀+t₀/4) ⊆ Set.Ioo (t₀/2) (3*t₀/2) := by
    intro r hr
    constructor <;> (rcases hr with ⟨hl,hu⟩; linarith)
  have htI : t₀ ∈ Set.Ioo (t₀/2) (3*t₀/2) := ⟨by linarith, by linarith⟩
  have hrate : SupportedSection C (fun x => densityRate (ubar u q) x t₀) :=
    hsections t₀ htI _ (Submodule.subset_span (show (fun x => densityRate (ubar u q) x t₀) ∈ sections (ubar u q) t₀ from Or.inr (Or.inl rfl)))
  refine ⟨C.indicator (fun _ => B), hnh, hpos, ?_, h_T005.2 t₀ ht₀, hrate.1.aestronglyMeasurable, ?_, hbi, ?_⟩
  · filter_upwards [hnh] with r hr
    have he : SupportedSection C (fun x => density (ubar u q) x r) :=
      hsections r (hinside hr) _ (Submodule.subset_span (show (fun x => density (ubar u q) x r) ∈ sections (ubar u q) r from Or.inl rfl))
    exact he.1.aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro x r hr
    by_cases hx : x ∈ C
    · rw [Set.indicator_of_mem hx]
      exact hbound x hx r ⟨le_of_lt hr.1, le_of_lt hr.2⟩
    · have hz : densityRate (ubar u q) x r = 0 := (hslab.2.2.2 x r hx (hinside hr)).2.2.2.2
      rw [hz, norm_zero, Set.indicator_of_notMem hx]
  · apply Filter.Eventually.of_forall
    intro x r hr
    exact h_T003.2.2.2.2.1 x r (hpos hr)

theorem T007 (n : ℕ) (m : ℕ) (u : Space n × Set.Ioi (0 : ℝ) → Value m) (q : Value m) (h_T006 : ∀ t₀ : ℝ, 0 < t₀ →
 ∃ b : Space n → ℝ,
 (Set.Ioo (t₀-t₀/4) (t₀+t₀/4)) ∈ 𝓝 t₀ ∧ (Set.Ioo (t₀-t₀/4) (t₀+t₀/4)) ⊆ Set.Ioi (0 : ℝ) ∧
 (∀ᶠ r in 𝓝 t₀, AEStronglyMeasurable (fun x => density (ubar u q) x r) volume) ∧
 Integrable (fun x => density (ubar u q) x t₀) ∧
 AEStronglyMeasurable (fun x => densityRate (ubar u q) x t₀) volume ∧
 (∀ᵐ x ∂volume, ∀ r ∈ (Set.Ioo (t₀-t₀/4) (t₀+t₀/4)), ‖densityRate (ubar u q) x r‖ ≤ b x) ∧
 Integrable b ∧
 (∀ᵐ x ∂volume, ∀ r ∈ (Set.Ioo (t₀-t₀/4) (t₀+t₀/4)), HasDerivAt (fun a => density (ubar u q) x a) (densityRate (ubar u q) x r) r)) :
    ∀ t₀ : ℝ, 0 < t₀ → HasDerivAt (energy (ubar u q)) (∫ x, densityRate (ubar u q) x t₀) t₀ := by
  intro t₀ ht₀
  rcases h_T006 t₀ ht₀ with ⟨b, hs, hpos, hmeas, hint, hrate, hbound, hb, hderiv⟩
  change HasDerivAt (fun r => ∫ x, density (ubar u q) x r)
    (∫ x, densityRate (ubar u q) x t₀) t₀
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (F := fun r (x : Space n) => density (ubar u q) x r)
    (F' := fun r (x : Space n) => densityRate (ubar u q) x r)
    (bound := b) hs hmeas hint hrate hbound hb hderiv).2

theorem T008 (n : ℕ) (m : ℕ) (u : Space n × Set.Ioi (0 : ℝ) → Value m) (q : Value m) (h_H004 : UnitValued (ubar u q)) (h_T003 : FirstCalculus (ubar u q) ∧ SecondCalculus (ubar u q) ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => density (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => densityRate (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
(∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (fun r => density (ubar u q) x r) (densityRate (ubar u q) x t) t) ∧
(∀ (j : Fin n) (x : Space n) (t : ℝ), 0 < t → ∀ k : Fin m,
 fderiv ℝ (fun y => (ubar u q) (y,t) k) x (Pi.single j 1) = spatial (ubar u q) j x t k ∧
 fderiv ℝ (fun y => velocity (ubar u q) y t k) x (Pi.single j 1) = mixed (ubar u q) j x t k ∧
 fderiv ℝ (fun y => spatial (ubar u q) j y t k) x (Pi.single j 1) = spatialSecond (ubar u q) j x t k) ∧
(∀ (x : Space n) (t : Set.Ioi (0 : ℝ)), (ubar u q) (x,t) = u (x,t)) ∧
(∀ (x : Space n) (t : ℝ), t ≤ 0 → (ubar u q) (x,t) = q)) :
    ∀ (x : Space n) (t : ℝ), 0 < t →
 dot ((ubar u q) (x,t)) (velocity (ubar u q) x t) = 0 ∧
 dot (velocity (ubar u q) x t) ((ubar u q) (x,t)) = 0 := by
  intro x t ht
  have hd (k : Fin m) :
      HasDerivAt (fun r => (ubar u q) (x, r) k)
        (velocity (ubar u q) x t k) t :=
    h_T003.1.2.2.2.1 x t ht k
  have hs : HasDerivAt
      (fun r => ∑ k : Fin m, (ubar u q) (x, r) k * (ubar u q) (x, r) k)
      (∑ k : Fin m, (velocity (ubar u q) x t k * (ubar u q) (x, t) k +
        (ubar u q) (x, t) k * velocity (ubar u q) x t k)) t := by
    exact HasDerivAt.fun_sum (fun k _ => (hd k).mul (hd k))
  have heq :
      (fun r => ∑ k : Fin m, (ubar u q) (x, r) k * (ubar u q) (x, r) k)
        =ᶠ[𝓝 t] (fun _ => (1 : ℝ)) := by
    filter_upwards [eventually_gt_nhds ht] with r hr
    exact h_H004 x r hr
  have hz : HasDerivAt
      (fun r => ∑ k : Fin m, (ubar u q) (x, r) k * (ubar u q) (x, r) k)
      0 t :=
    (hasDerivAt_const t (1 : ℝ)).congr_of_eventuallyEq heq
  have hsum := hs.unique hz
  have htwo : 2 * dot ((ubar u q) (x, t)) (velocity (ubar u q) x t) = 0 := by
    dsimp [dot]
    rw [Finset.mul_sum]
    convert hsum using 1
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hdot : dot ((ubar u q) (x, t)) (velocity (ubar u q) x t) = 0 := by
    linarith
  refine ⟨hdot, ?_⟩
  simpa only [dot, mul_comm] using hdot

theorem T009 (n : ℕ) (m : ℕ) (u : Space n × Set.Ioi (0 : ℝ) → Value m) (q : Value m) (h_H005 : Normal (ubar u q)) (h_T008 : ∀ (x : Space n) (t : ℝ), 0 < t →
 dot ((ubar u q) (x,t)) (velocity (ubar u q) x t) = 0 ∧
 dot (velocity (ubar u q) x t) ((ubar u q) (x,t)) = 0) (h_T003 : FirstCalculus (ubar u q) ∧ SecondCalculus (ubar u q) ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => density (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => densityRate (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
(∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (fun r => density (ubar u q) x r) (densityRate (ubar u q) x t) t) ∧
(∀ (j : Fin n) (x : Space n) (t : ℝ), 0 < t → ∀ k : Fin m,
 fderiv ℝ (fun y => (ubar u q) (y,t) k) x (Pi.single j 1) = spatial (ubar u q) j x t k ∧
 fderiv ℝ (fun y => velocity (ubar u q) y t k) x (Pi.single j 1) = mixed (ubar u q) j x t k ∧
 fderiv ℝ (fun y => spatial (ubar u q) j y t k) x (Pi.single j 1) = spatialSecond (ubar u q) j x t k) ∧
(∀ (x : Space n) (t : Set.Ioi (0 : ℝ)), (ubar u q) (x,t) = u (x,t)) ∧
(∀ (x : Space n) (t : ℝ), t ≤ 0 → (ubar u q) (x,t) = q)) :
    ∀ (x : Space n) (t : ℝ), 0 < t →
 dot ((ubar u q) (x,t)) (velocity (ubar u q) x t) = 0 ∧
 dot (velocity (ubar u q) x t) ((ubar u q) (x,t)) = 0 ∧
 dot (velocity (ubar u q) x t) (acceleration (ubar u q) x t - laplacian (ubar u q) x t) = 0 := by
  intro x t ht
  obtain ⟨hUV, hVU⟩ := h_T008 x t ht
  refine ⟨hUV, hVU, ?_⟩
  obtain ⟨a, ha⟩ := h_H005 x t ht
  rw [ha]
  change (∑ k, velocity (ubar u q) x t k * (a * (ubar u q) (x, t) k)) = 0
  calc
    (∑ k, velocity (ubar u q) x t k * (a * (ubar u q) (x, t) k)) =
        a * (∑ k, velocity (ubar u q) x t k * (ubar u q) (x, t) k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = 0 := by change a * dot (velocity (ubar u q) x t) ((ubar u q) (x,t)) = 0; rw [hVU, mul_zero]

namespace Local_T010
theorem yui_aux_0001 (n : ℕ) (m : ℕ) (u : Space n × Set.Ioi (0 : ℝ) → Value m) (q : Value m) (h_T003 : FirstCalculus (ubar u q) ∧ SecondCalculus (ubar u q) ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => density (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => densityRate (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
(∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (fun r => density (ubar u q) x r) (densityRate (ubar u q) x t) t) ∧
(∀ (j : Fin n) (x : Space n) (t : ℝ), 0 < t → ∀ k : Fin m,
 fderiv ℝ (fun y => (ubar u q) (y,t) k) x (Pi.single j 1) = spatial (ubar u q) j x t k ∧
 fderiv ℝ (fun y => velocity (ubar u q) y t k) x (Pi.single j 1) = mixed (ubar u q) j x t k ∧
 fderiv ℝ (fun y => spatial (ubar u q) j y t k) x (Pi.single j 1) = spatialSecond (ubar u q) j x t k) ∧
(∀ (x : Space n) (t : Set.Ioi (0 : ℝ)), (ubar u q) (x,t) = u (x,t)) ∧
(∀ (x : Space n) (t : ℝ), t ≤ 0 → (ubar u q) (x,t) = q)) (h_T005 : (∀ t₀ : ℝ, 0 < t₀ → ∃ C : Set (Space n),
 SlabVanishing (ubar u q) q t₀ C ∧
 ∀ r ∈ Set.Ioo (t₀/2) (3*t₀/2),
 ∀ h ∈ Submodule.span ℝ (sections (ubar u q) r), SupportedSection C h) ∧
(∀ t : ℝ, 0 < t → Integrable (fun x => density (ubar u q) x t))) : yui_aux_type% "∀ (t : ℝ), 0 < t → ∀ h ∈ sections (ubar u q) t, Integrable h" := by
  intro t ht h hh
  obtain ⟨C, hC, hs⟩ := h_T005.1 t ht
  have hmem : t ∈ Set.Ioo (t / 2) (3 * t / 2) := by constructor <;> linarith
  exact (hs t hmem h (Submodule.subset_span hh)).2.2.2

theorem yui_aux_0002 (n : ℕ) (m : ℕ) (u : Space n × Set.Ioi (0 : ℝ) → Value m) (q : Value m) (h_T003 : FirstCalculus (ubar u q) ∧ SecondCalculus (ubar u q) ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => density (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => densityRate (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
(∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (fun r => density (ubar u q) x r) (densityRate (ubar u q) x t) t) ∧
(∀ (j : Fin n) (x : Space n) (t : ℝ), 0 < t → ∀ k : Fin m,
 fderiv ℝ (fun y => (ubar u q) (y,t) k) x (Pi.single j 1) = spatial (ubar u q) j x t k ∧
 fderiv ℝ (fun y => velocity (ubar u q) y t k) x (Pi.single j 1) = mixed (ubar u q) j x t k ∧
 fderiv ℝ (fun y => spatial (ubar u q) j y t k) x (Pi.single j 1) = spatialSecond (ubar u q) j x t k) ∧
(∀ (x : Space n) (t : Set.Ioi (0 : ℝ)), (ubar u q) (x,t) = u (x,t)) ∧
(∀ (x : Space n) (t : ℝ), t ≤ 0 → (ubar u q) (x,t) = q)) (h_T005 : (∀ t₀ : ℝ, 0 < t₀ → ∃ C : Set (Space n),
 SlabVanishing (ubar u q) q t₀ C ∧
 ∀ r ∈ Set.Ioo (t₀/2) (3*t₀/2),
 ∀ h ∈ Submodule.span ℝ (sections (ubar u q) r), SupportedSection C h) ∧
(∀ t : ℝ, 0 < t → Integrable (fun x => density (ubar u q) x t))) : yui_aux_type% "∀ (t : ℝ), 0 < t → ∀ (j : Fin n) (k : Fin m),\n Integrable (fun x => velocity (ubar u q) x t k * spatialSecond (ubar u q) j x t k) ∧\n Integrable (fun x => mixed (ubar u q) j x t k * spatial (ubar u q) j x t k) ∧\n Integrable (fun x => velocity (ubar u q) x t k * spatial (ubar u q) j x t k)" := by
  intro t ht j k
  have hi := @yui_aux_0001 n m u q h_T003 h_T005 t ht
  constructor
  · apply hi
    simp only [sections, Set.mem_setOf_eq]
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨j, k, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩)))
  constructor
  · apply hi
    simp only [sections, Set.mem_setOf_eq]
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨j, k, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))⟩)))
  · apply hi
    simp only [sections, Set.mem_setOf_eq]
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨j, k, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))⟩)))

theorem yui_aux_0003 (n : ℕ) (m : ℕ) (u : Space n × Set.Ioi (0 : ℝ) → Value m) (q : Value m) (h_T003 : FirstCalculus (ubar u q) ∧ SecondCalculus (ubar u q) ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => density (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => densityRate (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
(∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (fun r => density (ubar u q) x r) (densityRate (ubar u q) x t) t) ∧
(∀ (j : Fin n) (x : Space n) (t : ℝ), 0 < t → ∀ k : Fin m,
 fderiv ℝ (fun y => (ubar u q) (y,t) k) x (Pi.single j 1) = spatial (ubar u q) j x t k ∧
 fderiv ℝ (fun y => velocity (ubar u q) y t k) x (Pi.single j 1) = mixed (ubar u q) j x t k ∧
 fderiv ℝ (fun y => spatial (ubar u q) j y t k) x (Pi.single j 1) = spatialSecond (ubar u q) j x t k) ∧
(∀ (x : Space n) (t : Set.Ioi (0 : ℝ)), (ubar u q) (x,t) = u (x,t)) ∧
(∀ (x : Space n) (t : ℝ), t ≤ 0 → (ubar u q) (x,t) = q)) (h_T005 : (∀ t₀ : ℝ, 0 < t₀ → ∃ C : Set (Space n),
 SlabVanishing (ubar u q) q t₀ C ∧
 ∀ r ∈ Set.Ioo (t₀/2) (3*t₀/2),
 ∀ h ∈ Submodule.span ℝ (sections (ubar u q) r), SupportedSection C h) ∧
(∀ t : ℝ, 0 < t → Integrable (fun x => density (ubar u q) x t))) : yui_aux_type% "∀ (t : ℝ), 0 < t → ∀ (j : Fin n) (k : Fin m),\n (∫ x, velocity (ubar u q) x t k * spatialSecond (ubar u q) j x t k) =\n -(∫ x, mixed (ubar u q) j x t k * spatial (ubar u q) j x t k)" := by
  intro t ht j k
  have hi := @yui_aux_0002 n m u q h_T003 h_T005 t ht j k
  have hd := h_T003.2.1.2.2.2.2.2
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) (f := fun x => velocity (ubar u q) x t k)
    (g := fun x => spatial (ubar u q) j x t k) (v := Pi.single j 1)
    hi.2.1 hi.1 hi.2.2
    (fun x _ => (hd j x t ht k).1.differentiableAt)
    (fun x _ => (hd j x t ht k).2.differentiableAt)

theorem yui_aux_0004 (n : ℕ) (m : ℕ) (u : Space n × Set.Ioi (0 : ℝ) → Value m) (q : Value m) (h_T003 : FirstCalculus (ubar u q) ∧ SecondCalculus (ubar u q) ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => density (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => densityRate (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
(∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (fun r => density (ubar u q) x r) (densityRate (ubar u q) x t) t) ∧
(∀ (j : Fin n) (x : Space n) (t : ℝ), 0 < t → ∀ k : Fin m,
 fderiv ℝ (fun y => (ubar u q) (y,t) k) x (Pi.single j 1) = spatial (ubar u q) j x t k ∧
 fderiv ℝ (fun y => velocity (ubar u q) y t k) x (Pi.single j 1) = mixed (ubar u q) j x t k ∧
 fderiv ℝ (fun y => spatial (ubar u q) j y t k) x (Pi.single j 1) = spatialSecond (ubar u q) j x t k) ∧
(∀ (x : Space n) (t : Set.Ioi (0 : ℝ)), (ubar u q) (x,t) = u (x,t)) ∧
(∀ (x : Space n) (t : ℝ), t ≤ 0 → (ubar u q) (x,t) = q)) (h_T005 : (∀ t₀ : ℝ, 0 < t₀ → ∃ C : Set (Space n),
 SlabVanishing (ubar u q) q t₀ C ∧
 ∀ r ∈ Set.Ioo (t₀/2) (3*t₀/2),
 ∀ h ∈ Submodule.span ℝ (sections (ubar u q) r), SupportedSection C h) ∧
(∀ t : ℝ, 0 < t → Integrable (fun x => density (ubar u q) x t))) : yui_aux_type% "∀ f : Fin m → ℝ, (∑ k, - f k) = -(∑ k, f k)" := by
  intro f
  simp only [Finset.sum_neg_distrib]

end Local_T010
open Local_T010 in
theorem T010 (n : ℕ) (m : ℕ) (u : Space n × Set.Ioi (0 : ℝ) → Value m) (q : Value m) (h_T003 : FirstCalculus (ubar u q) ∧ SecondCalculus (ubar u q) ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => density (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => densityRate (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
(∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (fun r => density (ubar u q) x r) (densityRate (ubar u q) x t) t) ∧
(∀ (j : Fin n) (x : Space n) (t : ℝ), 0 < t → ∀ k : Fin m,
 fderiv ℝ (fun y => (ubar u q) (y,t) k) x (Pi.single j 1) = spatial (ubar u q) j x t k ∧
 fderiv ℝ (fun y => velocity (ubar u q) y t k) x (Pi.single j 1) = mixed (ubar u q) j x t k ∧
 fderiv ℝ (fun y => spatial (ubar u q) j y t k) x (Pi.single j 1) = spatialSecond (ubar u q) j x t k) ∧
(∀ (x : Space n) (t : Set.Ioi (0 : ℝ)), (ubar u q) (x,t) = u (x,t)) ∧
(∀ (x : Space n) (t : ℝ), t ≤ 0 → (ubar u q) (x,t) = q)) (h_T005 : (∀ t₀ : ℝ, 0 < t₀ → ∃ C : Set (Space n),
 SlabVanishing (ubar u q) q t₀ C ∧
 ∀ r ∈ Set.Ioo (t₀/2) (3*t₀/2),
 ∀ h ∈ Submodule.span ℝ (sections (ubar u q) r), SupportedSection C h) ∧
(∀ t : ℝ, 0 < t → Integrable (fun x => density (ubar u q) x t))) :
    ∀ t₀ : ℝ, 0 < t₀ → ∀ j : Fin n,
 (∫ x, dot (spatial (ubar u q) j x t₀) (mixed (ubar u q) j x t₀)) =
   -(∫ x, dot (velocity (ubar u q) x t₀) (spatialSecond (ubar u q) j x t₀)) ∧
 Integrable (fun x => dot (spatial (ubar u q) j x t₀) (mixed (ubar u q) j x t₀)) ∧
 Integrable (fun x => dot (velocity (ubar u q) x t₀) (spatialSecond (ubar u q) j x t₀)) ∧
 (∀ k : Fin m,
 Integrable (fun x => velocity (ubar u q) x t₀ k * spatialSecond (ubar u q) j x t₀ k) ∧
 Integrable (fun x => mixed (ubar u q) j x t₀ k * spatial (ubar u q) j x t₀ k) ∧
 Integrable (fun x => velocity (ubar u q) x t₀ k * spatial (ubar u q) j x t₀ k)) := by
  intro t ht j
  have hi := @yui_aux_0002 n m u q h_T003 h_T005 t ht j
  have hid := @yui_aux_0003 n m u q h_T003 h_T005 t ht j
  have hip : ∀ k : Fin m, Integrable (fun x => spatial (ubar u q) j x t k * mixed (ubar u q) j x t k) := by
    intro k
    simpa only [mul_comm] using (hi k).2.1
  constructor
  · have hs : (∫ x, dot (velocity (ubar u q) x t) (spatialSecond (ubar u q) j x t)) =
        -(∫ x, dot (mixed (ubar u q) j x t) (spatial (ubar u q) j x t)) := by
      unfold dot
      rw [integral_finsetSum Finset.univ (fun k _ => (hi k).1),
          integral_finsetSum Finset.univ (fun k _ => (hi k).2.1)]
      simp_rw [hid]
      exact @yui_aux_0004 n m u q h_T003 h_T005 (fun k => ∫ x, mixed (ubar u q) j x t k * spatial (ubar u q) j x t k)
    have hs' : (∫ x, dot (velocity (ubar u q) x t) (spatialSecond (ubar u q) j x t)) =
        -(∫ x, dot (spatial (ubar u q) j x t) (mixed (ubar u q) j x t)) := by
      simpa only [dot, mul_comm] using hs
    linarith
  constructor
  · unfold dot
    exact integrable_finsetSum Finset.univ (fun k _ => hip k)
  constructor
  · unfold dot
    exact integrable_finsetSum Finset.univ (fun k _ => (hi k).1)
  · exact hi

namespace Local_T011
theorem yui_aux_0001 (n : ℕ) (m : ℕ) (u : Space n × Set.Ioi (0 : ℝ) → Value m) (q : Value m) (h_T003 : FirstCalculus (ubar u q) ∧ SecondCalculus (ubar u q) ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => density (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => densityRate (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
(∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (fun r => density (ubar u q) x r) (densityRate (ubar u q) x t) t) ∧
(∀ (j : Fin n) (x : Space n) (t : ℝ), 0 < t → ∀ k : Fin m,
 fderiv ℝ (fun y => (ubar u q) (y,t) k) x (Pi.single j 1) = spatial (ubar u q) j x t k ∧
 fderiv ℝ (fun y => velocity (ubar u q) y t k) x (Pi.single j 1) = mixed (ubar u q) j x t k ∧
 fderiv ℝ (fun y => spatial (ubar u q) j y t k) x (Pi.single j 1) = spatialSecond (ubar u q) j x t k) ∧
(∀ (x : Space n) (t : Set.Ioi (0 : ℝ)), (ubar u q) (x,t) = u (x,t)) ∧
(∀ (x : Space n) (t : ℝ), t ≤ 0 → (ubar u q) (x,t) = q)) (h_T005 : (∀ t₀ : ℝ, 0 < t₀ → ∃ C : Set (Space n),
 SlabVanishing (ubar u q) q t₀ C ∧
 ∀ r ∈ Set.Ioo (t₀/2) (3*t₀/2),
 ∀ h ∈ Submodule.span ℝ (sections (ubar u q) r), SupportedSection C h) ∧
(∀ t : ℝ, 0 < t → Integrable (fun x => density (ubar u q) x t))) (h_T007 : ∀ t₀ : ℝ, 0 < t₀ → HasDerivAt (energy (ubar u q)) (∫ x, densityRate (ubar u q) x t₀) t₀) (h_T009 : ∀ (x : Space n) (t : ℝ), 0 < t →
 dot ((ubar u q) (x,t)) (velocity (ubar u q) x t) = 0 ∧
 dot (velocity (ubar u q) x t) ((ubar u q) (x,t)) = 0 ∧
 dot (velocity (ubar u q) x t) (acceleration (ubar u q) x t - laplacian (ubar u q) x t) = 0) (h_T010 : ∀ t₀ : ℝ, 0 < t₀ → ∀ j : Fin n,
 (∫ x, dot (spatial (ubar u q) j x t₀) (mixed (ubar u q) j x t₀)) =
   -(∫ x, dot (velocity (ubar u q) x t₀) (spatialSecond (ubar u q) j x t₀)) ∧
 Integrable (fun x => dot (spatial (ubar u q) j x t₀) (mixed (ubar u q) j x t₀)) ∧
 Integrable (fun x => dot (velocity (ubar u q) x t₀) (spatialSecond (ubar u q) j x t₀)) ∧
 (∀ k : Fin m,
 Integrable (fun x => velocity (ubar u q) x t₀ k * spatialSecond (ubar u q) j x t₀ k) ∧
 Integrable (fun x => mixed (ubar u q) j x t₀ k * spatial (ubar u q) j x t₀ k) ∧
 Integrable (fun x => velocity (ubar u q) x t₀ k * spatial (ubar u q) j x t₀ k))) : yui_aux_type% "∀ (a b : Value m) (s : Fin n → Value m), dot a (b - ∑ j, s j) = dot a b - ∑ j, dot a (s j)" := by
  intro a b s
  simp only [dot, Pi.sub_apply, Finset.sum_apply, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
  rw [Finset.sum_comm]

theorem yui_aux_0002 (n : ℕ) (m : ℕ) (u : Space n × Set.Ioi (0 : ℝ) → Value m) (q : Value m) (h_T003 : FirstCalculus (ubar u q) ∧ SecondCalculus (ubar u q) ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => density (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => densityRate (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
(∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (fun r => density (ubar u q) x r) (densityRate (ubar u q) x t) t) ∧
(∀ (j : Fin n) (x : Space n) (t : ℝ), 0 < t → ∀ k : Fin m,
 fderiv ℝ (fun y => (ubar u q) (y,t) k) x (Pi.single j 1) = spatial (ubar u q) j x t k ∧
 fderiv ℝ (fun y => velocity (ubar u q) y t k) x (Pi.single j 1) = mixed (ubar u q) j x t k ∧
 fderiv ℝ (fun y => spatial (ubar u q) j y t k) x (Pi.single j 1) = spatialSecond (ubar u q) j x t k) ∧
(∀ (x : Space n) (t : Set.Ioi (0 : ℝ)), (ubar u q) (x,t) = u (x,t)) ∧
(∀ (x : Space n) (t : ℝ), t ≤ 0 → (ubar u q) (x,t) = q)) (h_T005 : (∀ t₀ : ℝ, 0 < t₀ → ∃ C : Set (Space n),
 SlabVanishing (ubar u q) q t₀ C ∧
 ∀ r ∈ Set.Ioo (t₀/2) (3*t₀/2),
 ∀ h ∈ Submodule.span ℝ (sections (ubar u q) r), SupportedSection C h) ∧
(∀ t : ℝ, 0 < t → Integrable (fun x => density (ubar u q) x t))) (h_T007 : ∀ t₀ : ℝ, 0 < t₀ → HasDerivAt (energy (ubar u q)) (∫ x, densityRate (ubar u q) x t₀) t₀) (h_T009 : ∀ (x : Space n) (t : ℝ), 0 < t →
 dot ((ubar u q) (x,t)) (velocity (ubar u q) x t) = 0 ∧
 dot (velocity (ubar u q) x t) ((ubar u q) (x,t)) = 0 ∧
 dot (velocity (ubar u q) x t) (acceleration (ubar u q) x t - laplacian (ubar u q) x t) = 0) (h_T010 : ∀ t₀ : ℝ, 0 < t₀ → ∀ j : Fin n,
 (∫ x, dot (spatial (ubar u q) j x t₀) (mixed (ubar u q) j x t₀)) =
   -(∫ x, dot (velocity (ubar u q) x t₀) (spatialSecond (ubar u q) j x t₀)) ∧
 Integrable (fun x => dot (spatial (ubar u q) j x t₀) (mixed (ubar u q) j x t₀)) ∧
 Integrable (fun x => dot (velocity (ubar u q) x t₀) (spatialSecond (ubar u q) j x t₀)) ∧
 (∀ k : Fin m,
 Integrable (fun x => velocity (ubar u q) x t₀ k * spatialSecond (ubar u q) j x t₀ k) ∧
 Integrable (fun x => mixed (ubar u q) j x t₀ k * spatial (ubar u q) j x t₀ k) ∧
 Integrable (fun x => velocity (ubar u q) x t₀ k * spatial (ubar u q) j x t₀ k))) : yui_aux_type% "∀ t : ℝ, 0 < t → Integrable (fun x => dot (velocity (ubar u q) x t) (acceleration (ubar u q) x t))" := by
  intro t ht
  obtain ⟨C, hC, hsec⟩ := h_T005.1 t ht
  have htmem : t ∈ Set.Ioo (t / 2) (3 * t / 2) := by constructor <;> linarith
  have hmem : (fun x => dot (velocity (ubar u q) x t) (acceleration (ubar u q) x t)) ∈ sections (ubar u q) t := by
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  exact (hsec t htmem _ (Submodule.subset_span hmem)).2.2.2

end Local_T011
open Local_T011 in
theorem T011 (n : ℕ) (m : ℕ) (u : Space n × Set.Ioi (0 : ℝ) → Value m) (q : Value m) (h_T003 : FirstCalculus (ubar u q) ∧ SecondCalculus (ubar u q) ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => density (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => densityRate (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
(∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (fun r => density (ubar u q) x r) (densityRate (ubar u q) x t) t) ∧
(∀ (j : Fin n) (x : Space n) (t : ℝ), 0 < t → ∀ k : Fin m,
 fderiv ℝ (fun y => (ubar u q) (y,t) k) x (Pi.single j 1) = spatial (ubar u q) j x t k ∧
 fderiv ℝ (fun y => velocity (ubar u q) y t k) x (Pi.single j 1) = mixed (ubar u q) j x t k ∧
 fderiv ℝ (fun y => spatial (ubar u q) j y t k) x (Pi.single j 1) = spatialSecond (ubar u q) j x t k) ∧
(∀ (x : Space n) (t : Set.Ioi (0 : ℝ)), (ubar u q) (x,t) = u (x,t)) ∧
(∀ (x : Space n) (t : ℝ), t ≤ 0 → (ubar u q) (x,t) = q)) (h_T005 : (∀ t₀ : ℝ, 0 < t₀ → ∃ C : Set (Space n),
 SlabVanishing (ubar u q) q t₀ C ∧
 ∀ r ∈ Set.Ioo (t₀/2) (3*t₀/2),
 ∀ h ∈ Submodule.span ℝ (sections (ubar u q) r), SupportedSection C h) ∧
(∀ t : ℝ, 0 < t → Integrable (fun x => density (ubar u q) x t))) (h_T007 : ∀ t₀ : ℝ, 0 < t₀ → HasDerivAt (energy (ubar u q)) (∫ x, densityRate (ubar u q) x t₀) t₀) (h_T009 : ∀ (x : Space n) (t : ℝ), 0 < t →
 dot ((ubar u q) (x,t)) (velocity (ubar u q) x t) = 0 ∧
 dot (velocity (ubar u q) x t) ((ubar u q) (x,t)) = 0 ∧
 dot (velocity (ubar u q) x t) (acceleration (ubar u q) x t - laplacian (ubar u q) x t) = 0) (h_T010 : ∀ t₀ : ℝ, 0 < t₀ → ∀ j : Fin n,
 (∫ x, dot (spatial (ubar u q) j x t₀) (mixed (ubar u q) j x t₀)) =
   -(∫ x, dot (velocity (ubar u q) x t₀) (spatialSecond (ubar u q) j x t₀)) ∧
 Integrable (fun x => dot (spatial (ubar u q) j x t₀) (mixed (ubar u q) j x t₀)) ∧
 Integrable (fun x => dot (velocity (ubar u q) x t₀) (spatialSecond (ubar u q) j x t₀)) ∧
 (∀ k : Fin m,
 Integrable (fun x => velocity (ubar u q) x t₀ k * spatialSecond (ubar u q) j x t₀ k) ∧
 Integrable (fun x => mixed (ubar u q) j x t₀ k * spatial (ubar u q) j x t₀ k) ∧
 Integrable (fun x => velocity (ubar u q) x t₀ k * spatial (ubar u q) j x t₀ k))) :
    ∀ t : ℝ, 0 < t → HasDerivAt (energy (ubar u q)) 0 t := by
  classical
  intro t ht
  let v := ubar u q
  let f : Space n → ℝ := fun x => dot (velocity v x t) (acceleration v x t)
  let g : Fin n → Space n → ℝ := fun j x => dot (spatial v j x t) (mixed v j x t)
  let s : Fin n → Space n → ℝ := fun j x => dot (velocity v x t) (spatialSecond v j x t)
  have hf : Integrable f := @yui_aux_0002 n m u q h_T003 h_T005 h_T007 h_T009 h_T010 t ht
  have hg : ∀ j, Integrable (g j) := fun j => (h_T010 t ht j).2.1
  have hs : ∀ j, Integrable (s j) := fun j => (h_T010 t ht j).2.2.1
  have hgsum : Integrable (fun x => ∑ j, g j x) :=
    integrable_finsetSum Finset.univ (fun j _ => hg j)
  have hssum : Integrable (fun x => ∑ j, s j x) :=
    integrable_finsetSum Finset.univ (fun j _ => hs j)
  have hparts : ∀ j, (∫ x, g j x) = -(∫ x, s j x) :=
    fun j => (h_T010 t ht j).1
  have halg : ∀ x, dot (velocity v x t) (acceleration v x t - laplacian v x t) =
      f x - ∑ j, s j x := by
    intro x
    exact @yui_aux_0001 n m u q h_T003 h_T005 h_T007 h_T009 h_T010
      (velocity v x t) (acceleration v x t) (fun j => spatialSecond v j x t)
  have hzero : (∫ x, densityRate v x t) = 0 := by
    calc
      (∫ x, densityRate v x t) =
          2 * (∫ x, f x) + 2 * ∑ j, ∫ x, g j x := by
        change (∫ x, 2 * f x + 2 * ∑ j, g j x) = _
        rw [integral_add (hf.const_mul 2) (hgsum.const_mul 2),
          integral_const_mul, integral_const_mul,
          integral_finsetSum Finset.univ (fun j _ => hg j)]
      _ = 2 * (∫ x, f x) - 2 * ∑ j, ∫ x, s j x := by
        simp_rw [hparts]
        rw [Finset.sum_neg_distrib]
        ring
      _ = 2 * (∫ x, f x - ∑ j, s j x) := by
        rw [integral_sub hf hssum,
          integral_finsetSum Finset.univ (fun j _ => hs j)]
        ring
      _ = 2 * (∫ x, dot (velocity v x t)
          (acceleration v x t - laplacian v x t)) := by
        congr 1
        exact integral_congr_ae (Filter.Eventually.of_forall (fun x => (halg x).symm))
      _ = 0 := by
        have hz : (fun x => dot (velocity v x t)
            (acceleration v x t - laplacian v x t)) = (fun _ : Space n => (0 : ℝ)) :=
          funext (fun x => (h_T009 x t ht).2.2)
        rw [hz]
        simp
  have hd := h_T007 t ht
  rw [hzero] at hd
  exact hd

theorem T012 (n : ℕ) (m : ℕ) (u : Space n × Set.Ioi (0 : ℝ) → Value m) (q : Value m) (h_T003 : FirstCalculus (ubar u q) ∧ SecondCalculus (ubar u q) ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => density (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => densityRate (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
(∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (fun r => density (ubar u q) x r) (densityRate (ubar u q) x t) t) ∧
(∀ (j : Fin n) (x : Space n) (t : ℝ), 0 < t → ∀ k : Fin m,
 fderiv ℝ (fun y => (ubar u q) (y,t) k) x (Pi.single j 1) = spatial (ubar u q) j x t k ∧
 fderiv ℝ (fun y => velocity (ubar u q) y t k) x (Pi.single j 1) = mixed (ubar u q) j x t k ∧
 fderiv ℝ (fun y => spatial (ubar u q) j y t k) x (Pi.single j 1) = spatialSecond (ubar u q) j x t k) ∧
(∀ (x : Space n) (t : Set.Ioi (0 : ℝ)), (ubar u q) (x,t) = u (x,t)) ∧
(∀ (x : Space n) (t : ℝ), t ≤ 0 → (ubar u q) (x,t) = q)) (h_T005 : (∀ t₀ : ℝ, 0 < t₀ → ∃ C : Set (Space n),
 SlabVanishing (ubar u q) q t₀ C ∧
 ∀ r ∈ Set.Ioo (t₀/2) (3*t₀/2),
 ∀ h ∈ Submodule.span ℝ (sections (ubar u q) r), SupportedSection C h) ∧
(∀ t : ℝ, 0 < t → Integrable (fun x => density (ubar u q) x t))) (h_T011 : ∀ t : ℝ, 0 < t → HasDerivAt (energy (ubar u q)) 0 t) :
    ∀ t : ℝ, 0 < t → Integrable (fun x => density (ubar u q) x t) ∧ DifferentiableAt ℝ (energy (ubar u q)) t ∧ deriv (energy (ubar u q)) t = 0 := by
  intro t ht
  exact ⟨h_T005.2 t ht, (h_T011 t ht).differentiableAt, (h_T011 t ht).deriv⟩

set_option Elab.async false in
theorem P (n : ℕ) (m : ℕ) (u : Space n × Set.Ioi (0 : ℝ) → Value m) (q : Value m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : Smooth (ubar u q)) (h_H003 : normSq q = 1) (h_H004 : UnitValued (ubar u q)) (h_H005 : Normal (ubar u q)) (h_H006 : CompactPerturbation (ubar u q) q) :
    ∀ t : ℝ, 0 < t → Integrable (fun x => density (ubar u q) x t) ∧ DifferentiableAt ℝ (energy (ubar u q)) t ∧ deriv (energy (ubar u q)) t = 0 := by
  have h_T001 : FirstCalculus (ubar u q) := @T001 n m u q h_H001 h_H002
  have h_T002 : SecondCalculus (ubar u q) := @T002 n m u q h_T001
  have h_T003 : FirstCalculus (ubar u q) ∧ SecondCalculus (ubar u q) ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => density (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
ContDiffOn ℝ ∞ (fun p : Space n × ℝ => densityRate (ubar u q) p.1 p.2) {p | 0 < p.2} ∧
(∀ (x : Space n) (t : ℝ), 0 < t → HasDerivAt (fun r => density (ubar u q) x r) (densityRate (ubar u q) x t) t) ∧
(∀ (j : Fin n) (x : Space n) (t : ℝ), 0 < t → ∀ k : Fin m,
 fderiv ℝ (fun y => (ubar u q) (y,t) k) x (Pi.single j 1) = spatial (ubar u q) j x t k ∧
 fderiv ℝ (fun y => velocity (ubar u q) y t k) x (Pi.single j 1) = mixed (ubar u q) j x t k ∧
 fderiv ℝ (fun y => spatial (ubar u q) j y t k) x (Pi.single j 1) = spatialSecond (ubar u q) j x t k) ∧
(∀ (x : Space n) (t : Set.Ioi (0 : ℝ)), (ubar u q) (x,t) = u (x,t)) ∧
(∀ (x : Space n) (t : ℝ), t ≤ 0 → (ubar u q) (x,t) = q) := @T003 n m u q h_T001 h_T002
  have h_T004 : ∀ t₀ : ℝ, 0 < t₀ → ∃ C : Set (Space n), SlabVanishing (ubar u q) q t₀ C := @T004 n m u q h_H006 h_T003
  have h_T005 : (∀ t₀ : ℝ, 0 < t₀ → ∃ C : Set (Space n),
 SlabVanishing (ubar u q) q t₀ C ∧
 ∀ r ∈ Set.Ioo (t₀/2) (3*t₀/2),
 ∀ h ∈ Submodule.span ℝ (sections (ubar u q) r), SupportedSection C h) ∧
(∀ t : ℝ, 0 < t → Integrable (fun x => density (ubar u q) x t)) := @T005 n m u q h_T003 h_T004
  have h_T006 : ∀ t₀ : ℝ, 0 < t₀ →
 ∃ b : Space n → ℝ,
 (Set.Ioo (t₀-t₀/4) (t₀+t₀/4)) ∈ 𝓝 t₀ ∧ (Set.Ioo (t₀-t₀/4) (t₀+t₀/4)) ⊆ Set.Ioi (0 : ℝ) ∧
 (∀ᶠ r in 𝓝 t₀, AEStronglyMeasurable (fun x => density (ubar u q) x r) volume) ∧
 Integrable (fun x => density (ubar u q) x t₀) ∧
 AEStronglyMeasurable (fun x => densityRate (ubar u q) x t₀) volume ∧
 (∀ᵐ x ∂volume, ∀ r ∈ (Set.Ioo (t₀-t₀/4) (t₀+t₀/4)), ‖densityRate (ubar u q) x r‖ ≤ b x) ∧
 Integrable b ∧
 (∀ᵐ x ∂volume, ∀ r ∈ (Set.Ioo (t₀-t₀/4) (t₀+t₀/4)), HasDerivAt (fun a => density (ubar u q) x a) (densityRate (ubar u q) x r) r) := @T006 n m u q h_T003 h_T005
  have h_T007 : ∀ t₀ : ℝ, 0 < t₀ → HasDerivAt (energy (ubar u q)) (∫ x, densityRate (ubar u q) x t₀) t₀ := @T007 n m u q h_T006
  have h_T008 : ∀ (x : Space n) (t : ℝ), 0 < t →
 dot ((ubar u q) (x,t)) (velocity (ubar u q) x t) = 0 ∧
 dot (velocity (ubar u q) x t) ((ubar u q) (x,t)) = 0 := @T008 n m u q h_H004 h_T003
  have h_T009 : ∀ (x : Space n) (t : ℝ), 0 < t →
 dot ((ubar u q) (x,t)) (velocity (ubar u q) x t) = 0 ∧
 dot (velocity (ubar u q) x t) ((ubar u q) (x,t)) = 0 ∧
 dot (velocity (ubar u q) x t) (acceleration (ubar u q) x t - laplacian (ubar u q) x t) = 0 := @T009 n m u q h_H005 h_T008 h_T003
  have h_T010 : ∀ t₀ : ℝ, 0 < t₀ → ∀ j : Fin n,
 (∫ x, dot (spatial (ubar u q) j x t₀) (mixed (ubar u q) j x t₀)) =
   -(∫ x, dot (velocity (ubar u q) x t₀) (spatialSecond (ubar u q) j x t₀)) ∧
 Integrable (fun x => dot (spatial (ubar u q) j x t₀) (mixed (ubar u q) j x t₀)) ∧
 Integrable (fun x => dot (velocity (ubar u q) x t₀) (spatialSecond (ubar u q) j x t₀)) ∧
 (∀ k : Fin m,
 Integrable (fun x => velocity (ubar u q) x t₀ k * spatialSecond (ubar u q) j x t₀ k) ∧
 Integrable (fun x => mixed (ubar u q) j x t₀ k * spatial (ubar u q) j x t₀ k) ∧
 Integrable (fun x => velocity (ubar u q) x t₀ k * spatial (ubar u q) j x t₀ k)) := @T010 n m u q h_T003 h_T005
  have h_T011 : ∀ t : ℝ, 0 < t → HasDerivAt (energy (ubar u q)) 0 t := @T011 n m u q h_T003 h_T005 h_T007 h_T009 h_T010
  have h_T012 : ∀ t : ℝ, 0 < t → Integrable (fun x => density (ubar u q) x t) ∧ DifferentiableAt ℝ (energy (ubar u q)) t ∧ deriv (energy (ubar u q)) t = 0 := @T012 n m u q h_T003 h_T005 h_T011
  exact h_T012

#check @P
#print axioms P

end Translation

namespace AuditBExport
set_option autoImplicit false
set_option Elab.async false in
theorem P (n : ℕ) (m : ℕ) (u : Space n × Set.Ioi (0 : ℝ) → Value m) (q : Value m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : Smooth (ubar u q)) (h_H003 : normSq q = 1) (h_H004 : UnitValued (ubar u q)) (h_H005 : Normal (ubar u q)) (h_H006 : CompactPerturbation (ubar u q) q) : ∀ t : ℝ, 0 < t → Integrable (fun x => density (ubar u q) x t) ∧ DifferentiableAt ℝ (energy (ubar u q)) t ∧ deriv (energy (ubar u q)) t = 0 := by
  exact @Translation.P n m u q h_H001 h_H002 h_H003 h_H004 h_H005 h_H006

#check @P
#print axioms P
end AuditBExport


namespace YuiBasis
set_option autoImplicit false
set_option Elab.async false in
theorem B001 : ∀ (n : ℕ) (f : (Fin n → ℝ) → ℝ), Continuous f → HasCompactSupport f → Integrable f := by
  intro n f hf hc
  exact hf.integrable_of_hasCompactSupport hc
set_option Elab.async false in
theorem B002 : ∀ (n : ℕ) (F F' : ℝ → (Fin n → ℝ) → ℝ)
  (b : (Fin n → ℝ) → ℝ) (t₀ : ℝ) (s : Set ℝ),
  s ∈ 𝓝 t₀ →
  (∀ᶠ t in 𝓝 t₀, AEStronglyMeasurable (F t) volume) →
  Integrable (F t₀) →
  AEStronglyMeasurable (F' t₀) volume →
  (∀ᵐ x ∂volume, ∀ t ∈ s, ‖F' t x‖ ≤ b x) →
  Integrable b →
  (∀ᵐ x ∂volume, ∀ t ∈ s, HasDerivAt (fun r => F r x) (F' t x) t) →
  Integrable (F' t₀) ∧
    HasDerivAt (fun t => ∫ x, F t x) (∫ x, F' t₀ x) t₀ := by
  intro n F F' b t₀ s hs hm hi hm' hb hbi hd
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hm hi hm' hb hbi hd
set_option Elab.async false in
theorem B003 : ∀ (n : ℕ) (f g : (Fin n → ℝ) → ℝ) (v : Fin n → ℝ),
  Integrable (fun x => fderiv ℝ f x v * g x) →
  Integrable (fun x => f x * fderiv ℝ g x v) →
  Integrable (fun x => f x * g x) →
  (∀ x ∈ tsupport g, DifferentiableAt ℝ f x) →
  (∀ x ∈ tsupport f, DifferentiableAt ℝ g x) →
  (∫ x, f x * fderiv ℝ g x v) = -(∫ x, fderiv ℝ f x v * g x) := by
  intro n f g v h1 h2 h3 hf hg
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h1 h2 h3 hf hg
set_option Elab.async false in
theorem B004 : ∀ (f g : ℝ → ℝ) (f' g' t : ℝ), HasDerivAt f f' t → HasDerivAt g g' t →
  HasDerivAt (fun r => f r * g r) (f' * g t + f t * g') t := by
  intro f g f' g' t hf hg
  exact hf.mul hg
set_option Elab.async false in
theorem B005 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (x : E),
  ContDiffAt ℝ 2 f x →
  ∀ v w : E, fderiv ℝ (fderiv ℝ f) x v w = fderiv ℝ (fderiv ℝ f) x w v := by
  intro E F _ _ _ _ f x hf v w
  exact hf.isSymmSndFDerivAt (by simp) v w
set_option Elab.async false in
theorem B006 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (U : Set E),
  IsOpen U → ContDiffOn ℝ ∞ f U → ContDiffOn ℝ ∞ (fderiv ℝ f) U := by
  intro E F _ _ _ _ f U hU hf
  exact hf.fderiv_of_isOpen hU (by simp)
set_option Elab.async false in
theorem B007 : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (c : F) (x : E),
  (f =ᶠ[𝓝 x] fun _ => c) → fderiv ℝ f x = 0 := by
  intro E F _ _ _ _ f c x h
  rw [h.fderiv_eq]
  simp
set_option Elab.async false in
theorem B008 : ∀ (n : ℕ) (K : Set ((Fin n → ℝ) × ℝ)) (f : ((Fin n → ℝ) × ℝ) → ℝ),
  IsCompact K → ContinuousOn f K → ∃ B : ℝ, ∀ p ∈ K, ‖f p‖ ≤ B := by
  intro n K f hK hf
  exact hK.exists_bound_of_continuousOn hf
set_option Elab.async false in
theorem B009 : ∀ (n : ℕ) (K : Set (Fin n → ℝ)) (B : ℝ),
  IsCompact K → Integrable (K.indicator (fun _ => B)) := by
  intro n K B hK
  rw [integrable_indicator_iff hK.measurableSet]
  exact integrableOn_const hK.measure_ne_top

end YuiBasis

namespace YuiClosed
set_option autoImplicit false
set_option Elab.async false in
theorem P (n : ℕ) (m : ℕ) (u : Space n × Set.Ioi (0 : ℝ) → Value m) (q : Value m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : Smooth (ubar u q)) (h_H003 : normSq q = 1) (h_H004 : UnitValued (ubar u q)) (h_H005 : Normal (ubar u q)) (h_H006 : CompactPerturbation (ubar u q) q) : ∀ t : ℝ, 0 < t → Integrable (fun x => density (ubar u q) x t) ∧ DifferentiableAt ℝ (energy (ubar u q)) t ∧ deriv (energy (ubar u q)) t = 0 := by
  exact @AuditBExport.P n m u q h_H001 h_H002 h_H003 h_H004 h_H005 h_H006

end YuiClosed

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
  if selector.startsWith "value:" then
    let .defnInfo decl ← getConstInfo (nameOf parts) | throwError "Expected a defined proposition"
    return decl.value
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
    let checks : Array (String × String × String × Array String) := #[("P", "decl:YuiClosed.P", "∀ (n : ℕ) (m : ℕ) (u : Space n × Set.Ioi (0 : ℝ) → Value m) (q : Value m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : Smooth (ubar u q)) (h_H003 : normSq q = 1) (h_H004 : UnitValued (ubar u q)) (h_H005 : Normal (ubar u q)) (h_H006 : CompactPerturbation (ubar u q) q), ∀ t : ℝ, 0 < t → Integrable (fun x => density (ubar u q) x t) ∧ DifferentiableAt ℝ (energy (ubar u q)) t ∧ deriv (energy (ubar u q)) t = 0", #["YuiClosed", "P"])]
    let mut comparisons : Array Json := #[]
    let mut frozenComparisons : Array Json := #[]
    let mut roots : Array Name := #[`YuiClosed.P]
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

#nl2lean_audit_probe
end NL2LeanAuditProbe
