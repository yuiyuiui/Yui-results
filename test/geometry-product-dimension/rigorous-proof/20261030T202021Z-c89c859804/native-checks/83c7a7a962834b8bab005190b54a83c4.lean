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

theorem T015 (n : ℕ) (E : Set (GPEucl n)) (h_T006 : ∀ (B : Set ℝ) (ρ η : ℝ), B.Nonempty → 0 ≤ ρ →
  (∀ b ∈ B, ∀ b' ∈ B, |b - b'| ≤ ρ) → 0 < η →
  BddAbove B ∧ BddBelow B ∧ IsLUB B (sSup B) ∧ IsGLB B (sInf B) ∧
  sSup B - sInf B ≤ ρ ∧
  B ⊆ Set.Ioo (sInf B - η / 2) (sSup B + η / 2) ∧
  (sInf B - η / 2 < sSup B + η / 2) ∧
  ((sSup B + η / 2) - (sInf B - η / 2) ≤ ρ + η)) :
    ∀ (δ : ℝ) (U : ℕ → Set ℝ), 0 < δ →
  GPcover GPI δ U → (1 : ENNReal) ≤ ∑' i, Metric.ediam (U i) := by
  classical
  intro δ U hδ hU
  have hfin (i : ℕ) : Metric.ediam (U i) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hU.2 i)
  have hdiam (i : ℕ) : ENNReal.ofReal (Metric.diam (U i)) = Metric.ediam (U i) :=
    ENNReal.ofReal_toReal (hfin i)
  have hpair (i : ℕ) : ∀ b ∈ U i, ∀ b' ∈ U i, |b - b'| ≤ Metric.diam (U i) := by
    intro b hb b' hb'
    simpa only [Real.dist_eq] using Metric.dist_le_diam_of_mem' (hfin i) hb hb'
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  have hεreal : 0 < (ε : ℝ) := hε
  let η : ℕ → ℝ := fun i => (ε : ℝ) / 2 / 2 ^ i
  have hη (i : ℕ) : 0 < η i := by dsimp [η]; positivity
  have hsumη : (∑' i, ENNReal.ofReal (η i)) = (ε : ENNReal) := by
    dsimp [η]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity)
      (summable_geometric_two' (ε : ℝ)), tsum_geometric_two']
    simp
  let J : ℕ → Set ℝ := fun i =>
    if (U i).Nonempty then
      Set.Ioo (sInf (U i) - η i / 2) (sSup (U i) + η i / 2)
    else ∅
  have hJ (i : ℕ) : U i ⊆ J i ∧
      MeasureTheory.volume (J i) ≤ Metric.ediam (U i) + ENNReal.ofReal (η i) := by
    by_cases hi : (U i).Nonempty
    · obtain ⟨_, _, _, _, _, hsub, _, hlen⟩ :=
        h_T006 (U i) (Metric.diam (U i)) (η i) hi Metric.diam_nonneg (hpair i) (hη i)
      have hJi : J i = Set.Ioo (sInf (U i) - η i / 2) (sSup (U i) + η i / 2) := by
        simp only [J, if_pos hi]
      rw [hJi]
      refine ⟨hsub, ?_⟩
      rw [Real.volume_Ioo]
      calc
        ENNReal.ofReal (sSup (U i) + η i / 2 - (sInf (U i) - η i / 2))
            ≤ ENNReal.ofReal (Metric.diam (U i) + η i) := ENNReal.ofReal_le_ofReal hlen
        _ = Metric.ediam (U i) + ENNReal.ofReal (η i) := by
          rw [ENNReal.ofReal_add Metric.diam_nonneg (hη i).le, hdiam i]
    · have hempty : U i = ∅ := Set.not_nonempty_iff_eq_empty.mp hi
      simp [J, hi, hempty]
  have hcov : GPI ⊆ ⋃ i, J i := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hU.1 hx)
    exact Set.mem_iUnion.mpr ⟨i, (hJ i).1 hi⟩
  calc
    (1 : ENNReal) = MeasureTheory.volume GPI := by
      simp [GPI, Real.volume_Icc]
    _ ≤ MeasureTheory.volume (⋃ i, J i) := MeasureTheory.measure_mono hcov
    _ ≤ ∑' i, MeasureTheory.volume (J i) := MeasureTheory.measure_iUnion_le J
    _ ≤ ∑' i, (Metric.ediam (U i) + ENNReal.ofReal (η i)) :=
      ENNReal.tsum_le_tsum (fun i => (hJ i).2)
    _ = (∑' i, Metric.ediam (U i)) + ε := by rw [ENNReal.tsum_add, hsumη]

#check @T015
#print axioms T015

end Translation
