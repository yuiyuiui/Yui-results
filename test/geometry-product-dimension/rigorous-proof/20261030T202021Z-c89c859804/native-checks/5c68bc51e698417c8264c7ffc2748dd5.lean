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

theorem T019 (n : ℕ) (E : Set (GPEucl n)) (h_H001 : E.Nonempty) (h_T001 : (∀ (k : ℕ) (x : GPEucl k) (t : ℝ),
    GPhead (GPappend x t) = x ∧ (GPappend x t) (Fin.last k) = t) ∧
  (∀ (k : ℕ) (z : GPEucl (k + 1)), GPappend (GPhead z) (z (Fin.last k)) = z) ∧
  (∀ (k : ℕ) (x y : GPEucl k) (t u : ℝ),
    dist (GPappend x t) (GPappend y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ (k : ℕ) (z w : GPEucl (k + 1)),
    dist (GPhead z) (GPhead w) ≤ dist z w ∧
    |z (Fin.last k) - w (Fin.last k)| ≤ dist z w)) (h_T017 : dimH GPI = 1 ∧
  (∀ s : ℝ, 0 < s → s < 1 → GPmass s GPI = ⊤) ∧
  (∀ (k : ℕ) (A : Set (GPEucl k)) (e : GPI → GPEucl k),
    (∀ t, e t ∈ A) →
    (∀ t u, dist (e t) (e u) = |(t : ℝ) - (u : ℝ)|) →
    (1 : ENNReal) ≤ dimH A ∧
    ∀ (s δ : ℝ), 0 < s → 0 < δ →
      GPcontent s δ GPI ≤ GPcontent s δ A)) :
    dimH E = 0 → dimH E + 1 ≤ dimH (GPproduct E) := by
  intro hdim
  obtain ⟨x₀, hx₀⟩ := h_H001
  let e : GPI → GPEucl (n + 1) := fun t => GPappend x₀ (t : ℝ)
  have he_mem : ∀ t, e t ∈ GPproduct E := by
    intro t
    change GPhead (GPappend x₀ (t : ℝ)) ∈ E ∧
      (GPappend x₀ (t : ℝ)) (Fin.last n) ∈ GPI
    rw [(h_T001.1 n x₀ (t : ℝ)).1, (h_T001.1 n x₀ (t : ℝ)).2]
    exact ⟨hx₀, t.property⟩
  have he_dist : ∀ t u, dist (e t) (e u) = |(t : ℝ) - (u : ℝ)| := by
    intro t u
    change dist (GPappend x₀ (t : ℝ)) (GPappend x₀ (u : ℝ)) = _
    rw [h_T001.2.2.1 n x₀ x₀ (t : ℝ) (u : ℝ), dist_self]
    simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add,
      Real.sqrt_sq_eq_abs, abs_abs]
  have hbound : (1 : ENNReal) ≤ dimH (GPproduct E) :=
    (h_T017.2.2 (n + 1) (GPproduct E) e he_mem he_dist).1
  simpa only [hdim, zero_add] using hbound

#check @T019
#print axioms T019

end Translation
