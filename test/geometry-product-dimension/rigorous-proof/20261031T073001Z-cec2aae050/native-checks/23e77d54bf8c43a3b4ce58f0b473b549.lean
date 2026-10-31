import Mathlib
open scoped ENNReal NNReal
namespace GP
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)
def unitInterval : Set ℝ := Set.Icc 0 1
def join {n : ℕ} (x : Space n) (t : ℝ) : Space (n + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x i) t)
def horizontal {n : ℕ} (z : Space (n + 1)) : Space n :=
  WithLp.toLp 2 (fun i => z i.castSucc)
def vertical {n : ℕ} (z : Space (n + 1)) : ℝ := z (Fin.last n)
def cylinder {n : ℕ} (E : Set (Space n)) : Set (Space (n + 1)) :=
  {z | horizontal z ∈ E ∧ vertical z ∈ unitInterval}
def Cover {X : Type*} [EMetricSpace X] (A : Set X) (δ : ℝ)
    (U : ℕ → Set X) : Prop :=
  A ⊆ ⋃ i, U i ∧ ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ
noncomputable def cost {X : Type*} [EMetricSpace X] (s : ℝ)
    (U : ℕ → Set X) : ℝ≥0∞ :=
  ∑' i, ⨆ (_ : (U i).Nonempty), (Metric.ediam (U i)) ^ s
noncomputable def content {X : Type*} [EMetricSpace X] (s δ : ℝ)
    (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : Cover A δ U), cost s U
noncomputable def hausdorff {X : Type*} [EMetricSpace X] (s : ℝ)
    (A : Set X) : ℝ≥0∞ :=
  ⨆ (δ : ℝ) (_ : 0 < δ), content s δ A
end GP

namespace Translation
set_option autoImplicit false

theorem T010 (n : ℕ) (E : Set (GP.Space n)) (h_T001 : (∀ (m : ℕ) (A : Set (GP.Space m)), 0 ≤ dimH A ∧
  ∀ (s : ℝ), 0 < s →
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (dimH A < ENNReal.ofReal s → GP.hausdorff s A = 0) ∧
    (ENNReal.ofReal s < dimH A → GP.hausdorff s A = ⊤) ∧
    (GP.hausdorff s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GP.hausdorff s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) ∧ (∀ (A : Set ℝ) (s : ℝ), 0 < s →
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A)) (h_T002 : dimH E < ⊤ ∧ 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧
  (n = 0 → E = Set.univ ∧ (∃ x : GP.Space n, E = {x}) ∧ dimH E = 0) ∧
  ∀ (s δ : ℝ), 0 < s → 0 < δ → GP.content s δ E < ⊤) (h_T009 : ∀ (s δ : ℝ), 0 < s → 0 < δ →
  GP.content s δ E ≤ GP.content (s + 1) δ (GP.cylinder E)) :
    0 < dimH E → dimH E + 1 ≤ dimH (GP.cylinder E) := by
  intro hpos
  have hfin : dimH E ≠ ⊤ := h_T002.1.ne
  let D : ℝ := (dimH E).toReal
  have hD : 0 < D := ENNReal.toReal_pos_iff.2 ⟨hpos, h_T002.1⟩
  have hDcast : ENNReal.ofReal D = dimH E := ENNReal.ofReal_toReal hfin
  have hscale : ∀ (s δ η : ℝ), δ ≤ η → GP.content s η E ≤ GP.content s δ E := by
    intro s δ η hδη
    unfold GP.content
    refine le_iInf fun U => le_iInf fun hU => ?_
    have hUη : GP.Cover E η U :=
      ⟨hU.1, fun i => (hU.2 i).trans (ENNReal.ofReal_le_ofReal hδη)⟩
    exact iInf_le_of_le U (iInf_le_of_le hUη le_rfl)
  have F003 : ∀ s : ℝ, 0 < s → s < D →
      ENNReal.ofReal (s + 1) ≤ dimH (GP.cylinder E) := by
    intro s hs hsD
    have hs_dim : ENNReal.ofReal s < dimH E :=
      (ENNReal.ofReal_lt_iff_lt_toReal hs.le hfin).2 hsD
    have hHs : GP.hausdorff s E = ⊤ :=
      ((h_T001.1 n E).2 s hs).2.2.1 hs_dim
    have F001 : ∀ T : ℝ, 0 < T → ∀ ε : ℝ, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧ ENNReal.ofReal T < GP.content s δ E := by
      intro T hT ε hε
      have hlt : ENNReal.ofReal T < GP.hausdorff s E := by
        rw [hHs]
        exact ENNReal.ofReal_lt_top
      have hex : ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal T < GP.content s δ E := by
        simpa only [GP.hausdorff, lt_iSup_iff, exists_prop] using hlt
      obtain ⟨δ, hδ, hbound⟩ := hex
      refine ⟨min δ ε, lt_min hδ hε, min_le_right _ _, ?_⟩
      exact hbound.trans_le (hscale s (min δ ε) δ (min_le_left _ _))
    have F002 : ∀ T : ℝ, 0 < T →
        ENNReal.ofReal T < GP.hausdorff (s + 1) (GP.cylinder E) := by
      intro T hT
      obtain ⟨δ, hδ, _, hbound⟩ := F001 T hT 1 zero_lt_one
      have hcover : GP.content s δ E ≤ GP.content (s + 1) δ (GP.cylinder E) :=
        h_T009 s δ hs hδ
      have hsup : GP.content (s + 1) δ (GP.cylinder E) ≤
          GP.hausdorff (s + 1) (GP.cylinder E) := by
        unfold GP.hausdorff
        exact le_iSup_of_le δ (le_iSup_of_le hδ le_rfl)
      exact hbound.trans_le (hcover.trans hsup)
    have hHF : GP.hausdorff (s + 1) (GP.cylinder E) = ⊤ := by
      by_contra hQ
      let Q := GP.hausdorff (s + 1) (GP.cylinder E)
      have hp : 0 < Q.toReal + 1 := by positivity
      have hlt : ENNReal.ofReal (Q.toReal + 1) < Q := F002 _ hp
      have hrev : Q < ENNReal.ofReal (Q.toReal + 1) :=
        (ENNReal.lt_ofReal_iff_toReal_lt hQ).2 (by linarith)
      exact lt_asymm hlt hrev
    have hs1 : 0 < s + 1 := by linarith
    exact ((h_T001.1 (n + 1) (GP.cylinder E)).2 (s + 1) hs1).2.2.2.2 hHF
  have hlim : ENNReal.ofReal (D + 1) ≤ dimH (GP.cylinder E) := by
    by_cases hQ : dimH (GP.cylinder E) = ⊤
    · simp [hQ]
    apply (ENNReal.ofReal_le_iff_le_toReal hQ).2
    apply le_of_forall_lt
    intro b hb
    have hm : max 0 (b - 1) < D := max_lt hD (by linarith)
    obtain ⟨s, hs, hsD⟩ := exists_between hm
    have hs0 : 0 < s := lt_of_le_of_lt (le_max_left _ _) hs
    have hbs : b < s + 1 := by
      have : b - 1 < s := lt_of_le_of_lt (le_max_right _ _) hs
      linarith
    exact hbs.trans_le ((ENNReal.ofReal_le_iff_le_toReal hQ).1 (F003 s hs0 hsD))
  simpa only [ENNReal.ofReal_add hD.le (by norm_num : (0 : ℝ) ≤ 1),
    hDcast, ENNReal.ofReal_one] using hlim

#check @T010
#print axioms T010

end Translation
