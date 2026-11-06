import Mathlib
open scoped BigOperators ContDiff Topology
open MeasureTheory
namespace WaveMap
abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)
def timeDomain (n : ℕ) : Set (Space n × ℝ) := {p | 0 < p.2}
noncomputable def dt {n m : ℕ} (u : Space n → ℝ → Space m) (x : Space n) (t : ℝ) : Space m :=
  deriv (u x) t
noncomputable def dtt {n m : ℕ} (u : Space n → ℝ → Space m) (x : Space n) (t : ℝ) : Space m :=
  deriv (fun r => dt u x r) t
noncomputable def dx {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Space n → F) (j : Fin n) (x : Space n) : F :=
  fderiv ℝ f x (EuclideanSpace.single j 1)
noncomputable def du {n m : ℕ} (u : Space n → ℝ → Space m) (j : Fin n) (x : Space n) (t : ℝ) : Space m :=
  dx (fun y => u y t) j x
noncomputable def duu {n m : ℕ} (u : Space n → ℝ → Space m) (j : Fin n) (x : Space n) (t : ℝ) : Space m :=
  dx (fun y => du u j y t) j x
noncomputable def dut {n m : ℕ} (u : Space n → ℝ → Space m) (j : Fin n) (x : Space n) (t : ℝ) : Space m :=
  dx (fun y => dt u y t) j x
noncomputable def lap {n m : ℕ} (u : Space n → ℝ → Space m) (x : Space n) (t : ℝ) : Space m :=
  ∑ j, duu u j x t
noncomputable def density {n m : ℕ} (u : Space n → ℝ → Space m) (x : Space n) (t : ℝ) : ℝ :=
  ‖dt u x t‖ ^ 2 + ∑ j, ‖du u j x t‖ ^ 2
noncomputable def densityT {n m : ℕ} (u : Space n → ℝ → Space m) (x : Space n) (t : ℝ) : ℝ :=
  deriv (density u x) t
noncomputable def energy {n m : ℕ} (u : Space n → ℝ → Space m) (t : ℝ) : ℝ :=
  ∫ x, density u x t
noncomputable def flux {n m : ℕ} (u : Space n → ℝ → Space m) (j : Fin n) (t : ℝ) (x : Space n) : ℝ :=
  inner ℝ (dt u x t) (du u j x t)
def box {n : ℕ} (R : ℝ) : Set (Space n) := {x | ∀ j, x j ∈ Set.Icc (-R) R}
def openBox {n : ℕ} (R : ℝ) : Set (Space n) := {x | ∀ j, x j ∈ Set.Ioo (-R) R}
def sectionGood {n : ℕ} (f : Space n → ℝ) (C : Set (Space n)) (R : ℝ) : Prop :=
  Continuous f ∧ (∃ B : ℝ, ∀ x ∈ box (n := n) R, |f x| ≤ B) ∧
  (∀ x ∉ C, f x = 0) ∧ Integrable f
end WaveMap

open WaveMap

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem yui_aux_0001 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_H006 : ∀ (s t : ℝ), 0 < s → s < t → ∃ C : Set (Space n), IsCompact C ∧ ∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc s t → u x r = q) : yui_aux_type% "∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : Space n → ℝ → F), ContDiffOn ℝ ∞ (Function.uncurry f) (timeDomain n) → ContDiffOn ℝ ∞ (fun p : Space n × ℝ => deriv (f p.1) p.2) (timeDomain n) ∧ ∀ j : Fin n, ContDiffOn ℝ ∞ (fun p : Space n × ℝ => dx (fun y => f y p.2) j p.1) (timeDomain n)" := by
  intro F _ _ f hf
  have ho : IsOpen (timeDomain n) := isOpen_lt continuous_const continuous_snd
  have hat (x : Space n) (t : ℝ) (ht : 0 < t) :
      ContDiffAt ℝ ∞ (Function.uncurry f) (x,t) :=
    (hf (x,t) ht).contDiffAt (ho.mem_nhds ht)
  constructor
  · intro p hp
    apply ContDiffAt.contDiffWithinAt
    have hh : ContDiffAt ℝ ∞ (fun z : (Space n × ℝ) × ℝ => f z.1.1 z.2) (p, p.2) :=
      (hat p.1 p.2 hp).comp (p,p.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    have hd : ContDiffAt ℝ ∞ (fun z : Space n × ℝ => fderiv ℝ (f z.1) z.2) p :=
      hh.fderiv contDiffAt_snd (by simp)
    simpa only [deriv] using hd.clm_apply (contDiffAt_const (c := (1 : ℝ)))
  · intro j p hp
    apply ContDiffAt.contDiffWithinAt
    have hh : ContDiffAt ℝ ∞ (fun z : (Space n × ℝ) × Space n => f z.2 z.1.2) (p, p.1) :=
      (hat p.1 p.2 hp).comp (p,p.1) (contDiffAt_snd.prodMk contDiffAt_fst.snd)
    have hd : ContDiffAt ℝ ∞ (fun z : Space n × ℝ => fderiv ℝ (fun y => f y z.2) z.1) p :=
      hh.fderiv contDiffAt_fst (by simp)
    exact hd.clm_apply contDiffAt_const

theorem yui_aux_0002 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_H006 : ∀ (s t : ℝ), 0 < s → s < t → ∃ C : Set (Space n), IsCompact C ∧ ∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc s t → u x r = q) : yui_aux_type% "∀ (f : Fin n → Space n × ℝ → ℝ), (∀ j, ContDiffOn ℝ ∞ (f j) (timeDomain n)) → ContDiffOn ℝ ∞ (fun p => ∑ j, f j p) (timeDomain n)" := by
  intro f hf
  exact ContDiffOn.sum (fun j _ => hf j)

theorem yui_aux_0003 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_H006 : ∀ (s t : ℝ), 0 < s → s < t → ∃ C : Set (Space n), IsCompact C ∧ ∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc s t → u x r = q) : yui_aux_type% "∀ (f : Space n × ℝ → Space m), ContDiffOn ℝ ∞ f (timeDomain n) → ContDiffOn ℝ ∞ (fun p => ‖f p‖ ^ 2) (timeDomain n)" := by
  intro f hf
  have h : ContDiffOn ℝ ∞ (fun p => inner ℝ (f p) (f p)) (timeDomain n) := hf.inner ℝ hf
  simpa only [real_inner_self_eq_norm_sq] using h

theorem yui_aux_0004 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_H006 : ∀ (s t : ℝ), 0 < s → s < t → ∃ C : Set (Space n), IsCompact C ∧ ∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc s t → u x r = q) : yui_aux_type% "∀ r : ℝ, 0 < r →\nContinuous (fun x => density u x r) ∧\nContinuous (fun x => densityT u x r) ∧\nContinuous (fun x => inner ℝ (dt u x r) (dtt u x r)) ∧\n∀ j : Fin n, Continuous (flux u j r) ∧\nContinuous (fun x => inner ℝ (dut u j x r) (du u j x r)) ∧\nContinuous (fun x => inner ℝ (dt u x r) (duu u j x r)) ∧\nContinuous (fun x => dx (flux u j r) j x)" := by
  have ht : ContDiffOn ℝ ∞ (Function.uncurry (dt u)) (timeDomain n) :=
    (yui_aux_0001 n m u q h_H001 h_H002 h_H006 u h_H002).1
  have htt : ContDiffOn ℝ ∞ (Function.uncurry (dtt u)) (timeDomain n) :=
    (yui_aux_0001 n m u q h_H001 h_H002 h_H006 (dt u) ht).1
  have hx (j : Fin n) : ContDiffOn ℝ ∞ (Function.uncurry (du u j)) (timeDomain n) :=
    (yui_aux_0001 n m u q h_H001 h_H002 h_H006 u h_H002).2 j
  have hxt (j : Fin n) : ContDiffOn ℝ ∞ (Function.uncurry (dut u j)) (timeDomain n) :=
    (yui_aux_0001 n m u q h_H001 h_H002 h_H006 (dt u) ht).2 j
  have hxx (j : Fin n) : ContDiffOn ℝ ∞ (Function.uncurry (duu u j)) (timeDomain n) :=
    (yui_aux_0001 n m u q h_H001 h_H002 h_H006 (du u j) (hx j)).2 j
  have he : ContDiffOn ℝ ∞ (Function.uncurry (density u)) (timeDomain n) := by
    exact (yui_aux_0003 n m u q h_H001 h_H002 h_H006 _ ht).add
      (yui_aux_0002 n m u q h_H001 h_H002 h_H006 _ (fun j =>
        yui_aux_0003 n m u q h_H001 h_H002 h_H006 _ (hx j)))
  have het : ContDiffOn ℝ ∞ (Function.uncurry (densityT u)) (timeDomain n) :=
    (yui_aux_0001 n m u q h_H001 h_H002 h_H006 (density u) he).1
  have hf (j : Fin n) : ContDiffOn ℝ ∞ (fun p : Space n × ℝ => flux u j p.2 p.1) (timeDomain n) :=
    ht.inner ℝ (hx j)
  have hfx (j : Fin n) : ContDiffOn ℝ ∞ (fun p : Space n × ℝ => dx (flux u j p.2) j p.1) (timeDomain n) :=
    (yui_aux_0001 n m u q h_H001 h_H002 h_H006 (fun x t => flux u j t x) (hf j)).2 j
  intro r hr
  have sec (f : Space n × ℝ → ℝ) (h : ContDiffOn ℝ ∞ f (timeDomain n)) :
      Continuous (fun x => f (x,r)) :=
    h.continuousOn.comp_continuous (continuous_id.prodMk continuous_const) (fun x => hr)
  refine ⟨sec _ he, sec _ het, sec _ (ht.inner ℝ htt), ?_⟩
  intro j
  exact ⟨sec _ (hf j), sec _ ((hxt j).inner ℝ (hx j)),
    sec _ (ht.inner ℝ (hxx j)), sec _ (hfx j)⟩

theorem yui_aux_0005 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_H006 : ∀ (s t : ℝ), 0 < s → s < t → ∃ C : Set (Space n), IsCompact C ∧ ∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc s t → u x r = q) : yui_aux_type% "∀ R : ℝ, volume ((@WithLp.ofLp 2 (Fin n → ℝ)) ⁻¹' (Set.Icc (fun _ : Fin n => -R) (fun _ : Fin n => R))) = volume (Set.Icc (fun _ : Fin n => -R) (fun _ : Fin n => R))" := by
  intro R
  exact (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage measurableSet_Icc.nullMeasurableSet

theorem yui_aux_0006 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_H006 : ∀ (s t : ℝ), 0 < s → s < t → ∃ C : Set (Space n), IsCompact C ∧ ∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc s t → u x r = q) : yui_aux_type% "∀ R : ℝ, 0 < R → IsCompact (box (n := n) R) ∧\nvolume (box (n := n) R) = ENNReal.ofReal ((2 * R) ^ n) ∧ volume (box (n := n) R) < ⊤" := by
  intro R hR
  let B : Set (Fin n → ℝ) := Set.Icc (fun _ => -R) (fun _ => R)
  have him : WithLp.toLp 2 '' B = box (n := n) R := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact fun j => ⟨hy.1 j, hy.2 j⟩
    · intro hx
      exact ⟨WithLp.ofLp x, ⟨fun j => (hx j).1, fun j => (hx j).2⟩, rfl⟩
  have hc : IsCompact (box (n := n) R) := by
    rw [← him]
    exact isCompact_Icc.image (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ))
  have hv : volume (box (n := n) R) = ENNReal.ofReal ((2 * R) ^ n) := by
    have hp : WithLp.ofLp ⁻¹' B = box (n := n) R := by
      ext x
      exact ⟨fun h j => ⟨h.1 j, h.2 j⟩, fun h => ⟨fun j => (h j).1, fun j => (h j).2⟩⟩
    rw [← hp, yui_aux_0005 n m u q h_H001 h_H002 h_H006 R]
    simp only [B, Real.volume_Icc_pi, sub_neg_eq_add, ← two_mul, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    exact (ENNReal.ofReal_pow (by positivity) _).symm
  exact ⟨hc, hv, hv ▸ ENNReal.ofReal_lt_top⟩

theorem yui_aux_0007 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_H006 : ∀ (s t : ℝ), 0 < s → s < t → ∃ C : Set (Space n), IsCompact C ∧ ∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc s t → u x r = q) : yui_aux_type% "∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (c : F) (x : Space n), fderiv ℝ (fun _ : Space n => c) x = 0" := by
  intro F _ _ c x
  simp

theorem yui_aux_0008 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_H006 : ∀ (s t : ℝ), 0 < s → s < t → ∃ C : Set (Space n), IsCompact C ∧ ∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc s t → u x r = q) : yui_aux_type% "∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]\n(f : Space n → ℝ → F) (c : F) (S : Set (Space n × ℝ)),\nIsOpen S → Set.EqOn (Function.uncurry f) (fun _ => c) S →\n(∀ p ∈ S, deriv (f p.1) p.2 = 0) ∧\n(∀ j : Fin n, ∀ p ∈ S, dx (fun y => f y p.2) j p.1 = 0)" := by
  intro F _ _ f c S hS hf
  constructor
  · intro p hp
    have he : f p.1 =ᶠ[𝓝 p.2] (fun _ => c) := by
      have ht : Filter.Tendsto (fun r : ℝ => (p.1,r)) (𝓝 p.2) (𝓝 p) :=
        (continuous_const.prodMk continuous_id).continuousAt
      exact (ht.eventually (hS.mem_nhds hp)).mono (fun r hr => hf hr)
    simpa only [deriv_const] using he.deriv_eq
  · intro j p hp
    have he : (fun y => f y p.2) =ᶠ[𝓝 p.1] (fun _ => c) := by
      have ht : Filter.Tendsto (fun y : Space n => (y,p.2)) (𝓝 p.1) (𝓝 p) :=
        (continuous_id.prodMk continuous_const).continuousAt
      exact (ht.eventually (hS.mem_nhds hp)).mono (fun y hy => hf hy)
    unfold dx
    rw [he.fderiv_eq, yui_aux_0007 n m u q h_H001 h_H002 h_H006 c p.1]
    rfl

theorem yui_aux_0009 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_H006 : ∀ (s t : ℝ), 0 < s → s < t → ∃ C : Set (Space n), IsCompact C ∧ ∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc s t → u x r = q) : yui_aux_type% "∀ (S : Set (Space n × ℝ)), IsOpen S →\nSet.EqOn (Function.uncurry u) (fun _ => q) S →\n∀ p ∈ S, Function.uncurry u =ᶠ[𝓝 p] (fun _ => q)" := by
  intro S hS hu p hp
  exact Filter.eventually_of_mem (hS.mem_nhds hp) (fun z hz => hu hz)

theorem yui_aux_0010 (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_H006 : ∀ (s t : ℝ), 0 < s → s < t → ∃ C : Set (Space n), IsCompact C ∧ ∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc s t → u x r = q) : yui_aux_type% "∀ (S : Set (Space n × ℝ)), IsOpen S →\nSet.EqOn (Function.uncurry u) (fun _ => q) S →\n∀ (k : ℕ) (p : Space n × ℝ), 0 < k → p ∈ S →\niteratedFDeriv ℝ k (Function.uncurry u) p = 0" := by
  intro S hS hu k p hk hp
  have he : Function.uncurry u =ᶠ[𝓝 p] (fun _ => q) :=
    yui_aux_0009 n m u q h_H001 h_H002 h_H006 S hS hu p hp
  have hd := (he.iteratedFDeriv ℝ k).eq_of_nhds
  rw [hd, iteratedFDeriv_const_of_ne (Nat.ne_of_gt hk)]
  rfl

theorem checked (n : ℕ) (m : ℕ) (u : WaveMap.Space n → ℝ → WaveMap.Space m) (q : WaveMap.Space m) (h_H001 : 1 ≤ n ∧ 1 ≤ m) (h_H002 : ContDiffOn ℝ ∞ (Function.uncurry u) (timeDomain n)) (h_H006 : ∀ (s t : ℝ), 0 < s → s < t → ∃ C : Set (Space n), IsCompact C ∧ ∀ (x : Space n) (r : ℝ), x ∉ C → r ∈ Set.Icc s t → u x r = q) : yui_aux_type% "∀ (S : Set (Space n × ℝ)), IsOpen S →\nSet.EqOn (Function.uncurry u) (fun _ => q) S →\n∀ p ∈ S, density u p.1 p.2 = 0 ∧ densityT u p.1 p.2 = 0 ∧\ninner ℝ (dt u p.1 p.2) (dtt u p.1 p.2) = 0 ∧\n∀ j : Fin n, flux u j p.2 p.1 = 0 ∧\ninner ℝ (dut u j p.1 p.2) (du u j p.1 p.2) = 0 ∧\ninner ℝ (dt u p.1 p.2) (duu u j p.1 p.2) = 0 ∧\ndx (flux u j p.2) j p.1 = 0" := by
  intro S hS hu
  have hpart := yui_aux_0008 n m u q h_H001 h_H002 h_H006 u q S hS hu
  have ht (p : Space n × ℝ) (hp : p ∈ S) : dt u p.1 p.2 = 0 := hpart.1 p hp
  have hx (j : Fin n) (p : Space n × ℝ) (hp : p ∈ S) : du u j p.1 p.2 = 0 := hpart.2 j p hp
  have he : Set.EqOn (Function.uncurry (density u)) (fun _ => (0 : ℝ)) S := by
    intro p hp
    simp [Function.uncurry, density, ht p hp, fun j => hx j p hp]
  have hf (j : Fin n) : Set.EqOn (Function.uncurry (fun x t => flux u j t x)) (fun _ => (0 : ℝ)) S := by
    intro p hp
    simp [Function.uncurry, flux, ht p hp]
  have het := (yui_aux_0008 n m u q h_H001 h_H002 h_H006 (density u) 0 S hS he).1
  have hfx (j : Fin n) :=
    (yui_aux_0008 n m u q h_H001 h_H002 h_H006 (fun x t => flux u j t x) 0 S hS (hf j)).2 j
  intro p hp
  refine ⟨he hp, het p hp, ?_, ?_⟩
  · simp [ht p hp]
  · intro j
    exact ⟨hf j hp, by simp [hx j p hp], by simp [ht p hp], hfx j p hp⟩
#check @checked
#print axioms checked
end YuiAuxiliary
