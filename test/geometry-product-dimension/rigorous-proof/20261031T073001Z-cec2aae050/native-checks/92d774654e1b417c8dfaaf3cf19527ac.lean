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

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem checked (n : ℕ) (E : Set (GP.Space n)) (h_T002 : dimH E < ⊤ ∧ 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧
  (n = 0 → E = Set.univ ∧ (∃ x : GP.Space n, E = {x}) ∧ dimH E = 0) ∧
  ∀ (s δ : ℝ), 0 < s → 0 < δ → GP.content s δ E < ⊤) : yui_aux_type% "∀ (s δ : ℝ), 0 < s → 0 < δ →\n  ∀ (V : ℕ → Set (GP.Space (n+1))), GP.Cover (GP.cylinder E) δ V →\n  LipschitzWith 1 (@GP.horizontal n) →\n  ∀ J : ℕ → Set ℝ, (∀ i, GP.vertical '' V i ⊆ J i) →\n  ∀ t ∈ GP.unitInterval, GP.content s δ E ≤\n    ∑' i, (J i).indicator (fun _ => (Metric.ediam (V i)) ^ s) t" := by
  classical
  intro s δ hs hδ V hV hh J hJ t ht
  let W : ℕ → Set (GP.Space n) := fun i =>
    if t ∈ J i then GP.horizontal '' (V i) else ∅
  have hd (i : ℕ) : Metric.ediam (GP.horizontal '' V i) ≤ Metric.ediam (V i) := by
    simpa only [ENNReal.coe_one, one_mul] using hh.ediam_image_le (V i)
  have hW : GP.Cover E δ W := by
    constructor
    · intro x hx
      have hz : GP.join x t ∈ GP.cylinder E := by
        change GP.horizontal (GP.join x t) ∈ E ∧ GP.vertical (GP.join x t) ∈ GP.unitInterval
        simpa [GP.horizontal, GP.vertical, GP.join] using And.intro hx ht
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hV.1 hz)
      have hti : t ∈ J i := by
        apply hJ i
        exact ⟨GP.join x t, hi, by simp [GP.vertical, GP.join]⟩
      apply Set.mem_iUnion.mpr
      refine ⟨i, ?_⟩
      simp only [W, if_pos hti]
      exact ⟨GP.join x t, hi, by simp [GP.horizontal, GP.join]⟩
    · intro i
      dsimp [W]
      split_ifs
      · exact (hd i).trans (hV.2 i)
      · simp
  have hc : GP.content s δ E ≤ GP.cost s W := by
    exact iInf_le_of_le W (iInf_le_of_le hW le_rfl)
  apply hc.trans
  unfold GP.cost
  apply ENNReal.tsum_le_tsum
  intro i
  by_cases hti : t ∈ J i
  · simp only [Set.indicator_of_mem hti]
    apply iSup_le
    intro hne
    apply ENNReal.rpow_le_rpow _ hs.le
    simpa only [W, if_pos hti] using hd i
  · simp [W, hti, Set.indicator_of_notMem hti]
#check @checked
#print axioms checked
end YuiAuxiliary
