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

theorem T011 (n : ℕ) (E : Set (GPEucl n)) (h_T001 : (∀ (k : ℕ) (x : GPEucl k) (t : ℝ),
    GPhead (GPappend x t) = x ∧ (GPappend x t) (Fin.last k) = t) ∧
  (∀ (k : ℕ) (z : GPEucl (k + 1)), GPappend (GPhead z) (z (Fin.last k)) = z) ∧
  (∀ (k : ℕ) (x y : GPEucl k) (t u : ℝ),
    dist (GPappend x t) (GPappend y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ (k : ℕ) (z w : GPEucl (k + 1)),
    dist (GPhead z) (GPhead w) ≤ dist z w ∧
    |z (Fin.last k) - w (Fin.last k)| ≤ dist z w)) (h_T006 : ∀ (B : Set ℝ) (ρ η : ℝ), B.Nonempty → 0 ≤ ρ →
  (∀ b ∈ B, ∀ b' ∈ B, |b - b'| ≤ ρ) → 0 < η →
  BddAbove B ∧ BddBelow B ∧ IsLUB B (sSup B) ∧ IsGLB B (sInf B) ∧
  sSup B - sInf B ≤ ρ ∧
  B ⊆ Set.Ioo (sInf B - η / 2) (sSup B + η / 2) ∧
  (sInf B - η / 2 < sSup B + η / 2) ∧
  ((sSup B + η / 2) - (sInf B - η / 2) ≤ ρ + η)) :
    ∀ (s δ ε : ℝ) (V : ℕ → Set (GPEucl (n + 1))),
  0 < s → 0 < δ → 0 < ε → GPcover (GPproduct E) δ V →
  (∀ i, Metric.ediam (GPhead '' V i) ≤ Metric.ediam (V i)) ∧
  ∃ a b : ℕ → ℝ, ∀ i, (V i).Nonempty →
    a i < b i ∧
    (∀ z ∈ V i, z (Fin.last n) ∈ Set.Ioo (a i) (b i)) ∧
    b i - a i ≤ (Metric.ediam (V i)).toReal +
      ε * (2 : ℝ) ^ (-(i : ℝ) - 1) /
        (1 + (Metric.ediam (V i)).toReal ^ s) := by
  classical
  intro s δ ε V hs hδ hε hV
  have hfin (i : ℕ) : Metric.ediam (V i) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hV.2 i)
  have hdist (i : ℕ) (z w : GPEucl (n + 1)) (hz : z ∈ V i) (hw : w ∈ V i) :
      dist z w ≤ (Metric.ediam (V i)).toReal := by
    rw [dist_edist]
    exact ENNReal.toReal_mono (hfin i) (Metric.edist_le_ediam_of_mem hz hw)
  constructor
  · intro i
    apply Metric.ediam_image_le_iff.mpr
    intro z hz w hw
    have hc : edist (GPhead z) (GPhead w) ≤ edist z w := by
      rw [edist_dist, edist_dist]
      exact ENNReal.ofReal_le_ofReal ((h_T001.2.2.2 n z w).1)
    exact hc.trans (Metric.edist_le_ediam_of_mem hz hw)
  · let ρ : ℕ → ℝ := fun i => (Metric.ediam (V i)).toReal
    let η : ℕ → ℝ := fun i => ε * (2 : ℝ) ^ (-(i : ℝ) - 1) / (1 + ρ i ^ s)
    have hη (i : ℕ) : 0 < η i := by
      have hp : 0 ≤ ρ i ^ s := Real.rpow_nonneg ENNReal.toReal_nonneg s
      exact div_pos (mul_pos hε (Real.rpow_pos_of_pos (by norm_num) _)) (by linarith)
    have intervals : ∀ i, ∃ a b : ℝ, (V i).Nonempty →
        a < b ∧ (∀ z ∈ V i, z (Fin.last n) ∈ Set.Ioo a b) ∧ b - a ≤ ρ i + η i := by
      intro i
      by_cases hi : (V i).Nonempty
      · let B : Set ℝ := (fun z : GPEucl (n + 1) => z (Fin.last n)) '' V i
        have hB : B.Nonempty := hi.image _
        have hpair : ∀ b ∈ B, ∀ b' ∈ B, |b - b'| ≤ ρ i := by
          rintro b ⟨z, hz, rfl⟩ b' ⟨w, hw, rfl⟩
          exact ((h_T001.2.2.2 n z w).2).trans (hdist i z w hz hw)
        rcases h_T006 B (ρ i) (η i) hB ENNReal.toReal_nonneg hpair (hη i) with
          ⟨_, _, _, _, _, hsub, hlt, hlen⟩
        refine ⟨sInf B - η i / 2, sSup B + η i / 2, fun _ => ⟨hlt, ?_, hlen⟩⟩
        intro z hz
        exact hsub ⟨z, hz, rfl⟩
      · exact ⟨0, 0, fun h => (hi h).elim⟩
    choose a b hab using intervals
    exact ⟨a, b, hab⟩

#check @T011
#print axioms T011

end Translation
