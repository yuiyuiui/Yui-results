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

#check @T002
#print axioms T002

end Translation
