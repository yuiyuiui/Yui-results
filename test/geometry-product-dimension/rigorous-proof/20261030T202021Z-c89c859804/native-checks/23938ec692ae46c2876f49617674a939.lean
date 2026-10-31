import Mathlib
abbrev GPEucl (k : ℕ) := EuclideanSpace ℝ (Fin k)
def GPI : Set ℝ := Set.Icc 0 1
def GPappend {k : ℕ} (x : GPEucl k) (t : ℝ) : GPEucl (k + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x i) t)
def GPhead {k : ℕ} (z : GPEucl (k + 1)) : GPEucl k :=
  WithLp.toLp 2 (fun i : Fin k => z i.castSucc)
def GPproduct {k : ℕ} (A : Set (GPEucl k)) : Set (GPEucl (k + 1)) :=
  {z | GPhead z ∈ A ∧ z (Fin.last k) ∈ GPI}
def GPcover {X : Type*} [PseudoEMetricSpace X]
    (A : Set X) (δ : ℝ) (U : ℕ → Set X) : Prop :=
  A ⊆ ⋃ i, U i ∧ ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ
noncomputable def GPcost {X : Type*} [PseudoEMetricSpace X]
    (s : ℝ) (U : ℕ → Set X) : ENNReal :=
  ∑' i, (Metric.ediam (U i)) ^ s
noncomputable def GPcontent {X : Type*} [PseudoEMetricSpace X]
    (s δ : ℝ) (A : Set X) : ENNReal :=
  ⨅ (U : ℕ → Set X) (_ : GPcover A δ U), GPcost s U
noncomputable def GPmass {X : Type*} [PseudoEMetricSpace X]
    (s : ℝ) (A : Set X) : ENNReal :=
  ⨆ (δ : ℝ) (_ : 0 < δ), GPcontent s δ A

namespace Translation
set_option autoImplicit false

theorem T001 (n : ℕ) (E : Set (GPEucl n))  :
    (∀ (k : ℕ) (x : GPEucl k) (t : ℝ),
    GPhead (GPappend x t) = x ∧ (GPappend x t) (Fin.last k) = t) ∧
  (∀ (k : ℕ) (z : GPEucl (k + 1)), GPappend (GPhead z) (z (Fin.last k)) = z) ∧
  (∀ (k : ℕ) (x y : GPEucl k) (t u : ℝ),
    dist (GPappend x t) (GPappend y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ (k : ℕ) (z w : GPEucl (k + 1)),
    dist (GPhead z) (GPhead w) ≤ dist z w ∧
    |z (Fin.last k) - w (Fin.last k)| ≤ dist z w) := by
  have hinv : ∀ (k : ℕ) (z : GPEucl (k + 1)),
      GPappend (GPhead z) (z (Fin.last k)) = z := by
    intro k z
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [GPappend]
    · simp [GPappend, GPhead]
  have hsq : ∀ (k : ℕ) (x y : GPEucl k) (t u : ℝ),
      dist (GPappend x t) (GPappend y u) ^ 2 = dist x y ^ 2 + |t - u| ^ 2 := by
    intro k x y t u
    rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_castSucc]
    simp only [GPappend, PiLp.toLp_apply, Fin.snoc_castSucc, Fin.snoc_last]
    rw [← EuclideanSpace.dist_sq_eq, Real.dist_eq]
  refine ⟨?_, hinv, ?_, ?_⟩
  · intro k x t
    constructor
    · ext i
      simp [GPhead, GPappend]
    · simp [GPappend]
  · intro k x y t u
    calc
      dist (GPappend x t) (GPappend y u) =
          Real.sqrt (dist (GPappend x t) (GPappend y u) ^ 2) :=
        (Real.sqrt_sq dist_nonneg).symm
      _ = Real.sqrt (dist x y ^ 2 + |t - u| ^ 2) := by rw [hsq]
  · intro k z w
    have h : dist z w ^ 2 =
        dist (GPhead z) (GPhead w) ^ 2 + |z (Fin.last k) - w (Fin.last k)| ^ 2 := by
      simpa only [hinv] using hsq k (GPhead z) (GPhead w) (z (Fin.last k)) (w (Fin.last k))
    constructor
    · nlinarith [dist_nonneg (x := z) (y := w), dist_nonneg (x := GPhead z) (y := GPhead w),
        sq_nonneg (z (Fin.last k) - w (Fin.last k))]
    · nlinarith [dist_nonneg (x := z) (y := w),
        abs_nonneg (z (Fin.last k) - w (Fin.last k)),
        sq_nonneg (dist (GPhead z) (GPhead w))]

#check @T001
#print axioms T001

end Translation
