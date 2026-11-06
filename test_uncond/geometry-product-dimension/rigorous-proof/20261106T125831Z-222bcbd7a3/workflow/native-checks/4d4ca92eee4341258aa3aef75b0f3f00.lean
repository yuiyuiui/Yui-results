import Mathlib
open scoped ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric
namespace YuiBasis
noncomputable def Content {X : Type*} [EMetricSpace X]
    (s : ℝ) (δ : ℝ≥0∞) (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i) (_ : ∀ i, Metric.ediam (U i) ≤ δ),
    ∑' i, ⨆ (_ : (U i).Nonempty), Metric.ediam (U i) ^ s
abbrev Ambient (n : ℕ) := EuclideanSpace ℝ (Fin n)
def unitInterval : Set ℝ := Set.Icc 0 1
noncomputable def appendCoord (n : ℕ) (p : Ambient n × ℝ) : Ambient (n + 1) :=
  WithLp.toLp 2 (Fin.lastCases p.2 (fun i => p.1 i))
end YuiBasis

open YuiBasis
namespace YuiPlan
noncomputable def H {X : Type*} [MetricSpace X] (s : ℝ) (A : Set X) : ℝ≥0∞ :=
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  hausdorffMeasure s A
noncomputable def C {X : Type*} [MetricSpace X] (s δ : ℝ) (A : Set X) : ℝ≥0∞ :=
  YuiBasis.Content s (ENNReal.ofReal δ) A
end YuiPlan
open YuiPlan
namespace YuiPortTypes
abbrev T003.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n)) : Prop :=
  ∀ (X : Type u) [MetricSpace X] (A : Set X) (s : ℝ), 0 < s →
  (∀ δ : ℝ, 0 < δ →
    C s δ A = ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)
      (_ : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ), ∑' i, Metric.ediam (U i) ^ s) ∧
  (∀ δ₁ δ₂ : ℝ, 0 < δ₁ → δ₁ ≤ δ₂ → C s δ₂ A ≤ C s δ₁ A) ∧
  H s A = ⨆ (δ : ℝ) (_ : 0 < δ), C s δ A
end YuiPortTypes

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace Translation
set_option autoImplicit false

section
universe u
namespace Local_T004
theorem yui_aux_0001 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T003 : @YuiPortTypes.T003.{u} n E) : yui_aux_type% "∀ (s d r e : ℝ), 0 ≤ s → 0 ≤ d → d < r → 0 < e → ∃ a : ℝ, d < a ∧ a < r ∧ a ^ s < d ^ s + e" := by
  intro s d r e hs hd hdr he
  have hc : ContinuousAt (fun x : ℝ => x ^ s) d := (Real.continuous_rpow_const hs).continuousAt
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hc e he
  let η : ℝ := min δ (r - d) / 2
  have hη : 0 < η := half_pos (lt_min hδ (sub_pos.mpr hdr))
  have hηδ : η < δ := lt_of_le_of_lt (div_le_div_of_nonneg_right (min_le_left δ (r-d)) (by norm_num : (0:ℝ) ≤ 2)) (by linarith)
  have hηr : η < r - d := lt_of_le_of_lt (div_le_div_of_nonneg_right (min_le_right δ (r-d)) (by norm_num : (0:ℝ) ≤ 2)) (by linarith)
  refine ⟨d + η, by linarith, by linarith, ?_⟩
  have hdist : dist (d + η) d < δ := by rw [Real.dist_eq]; simpa [abs_of_pos hη] using hηδ
  have hp := hclose hdist
  rw [Real.dist_eq] at hp
  have := (abs_lt.mp hp).2
  linarith

theorem yui_aux_0002 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T003 : @YuiPortTypes.T003.{u} n E) : yui_aux_type% "∀ ε : ℝ, 0 < ε → (∀ i : ℕ, 0 < ε / 8 * ((1 : ℝ) / 2) ^ i) ∧ (∑' i : ℕ, ENNReal.ofReal (ε / 8 * ((1 : ℝ) / 2) ^ i)) = ENNReal.ofReal (ε / 4)" := by
  intro ε hε
  constructor
  · intro i
    positivity
  · rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) (summable_geometric_two.mul_left (ε / 8)), tsum_mul_left, tsum_geometric_two]
    congr 1
    ring

theorem yui_aux_0003 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T003 : @YuiPortTypes.T003.{u} n E) : yui_aux_type% "∀ (X : Type u) [MetricSpace X] (A : Set X) (s r ε : ℝ), 0 < s → H s A = 0 → 0 < r → 0 < ε → ∃ U : ℕ → Set X, (A ⊆ ⋃ i, U i) ∧ (∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal (r / 2)) ∧ (∑' i, Metric.ediam (U i) ^ s) < ENNReal.ofReal (ε / 4)" := by
  intro X instX A s r ε hs hH hr hε
  have hnorm := h_T003 X A s hs
  have hc : C s (r / 2) A = 0 := by
    apply le_antisymm _ zero_le
    calc
      C s (r / 2) A ≤ ⨆ (δ : ℝ) (_ : 0 < δ), C s δ A := le_iSup_of_le (r / 2) (le_iSup_of_le (half_pos hr) le_rfl)
      _ = 0 := hnorm.2.2.symm.trans hH
  have hlt : C s (r / 2) A < ENNReal.ofReal (ε / 4) := by
    rw [hc]
    exact ENNReal.ofReal_pos.mpr (by linarith)
  rw [hnorm.1 (r / 2) (half_pos hr)] at hlt
  simpa only [iInf_lt_iff, exists_prop] using hlt

theorem yui_aux_0004 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T003 : @YuiPortTypes.T003.{u} n E) : yui_aux_type% "∀ (z : ℝ≥0∞) (r s : ℝ), 0 < r → 0 ≤ s → z ≤ ENNReal.ofReal (r / 2) → 0 ≤ z.toReal ∧ z.toReal < r ∧ ENNReal.ofReal z.toReal = z ∧ z ^ s = ENNReal.ofReal (z.toReal ^ s)" := by
  intro z r s hr hs hz
  have hfin : z ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hz
  have hd : z.toReal ≤ r / 2 := ENNReal.toReal_le_of_le_ofReal (by linarith) hz
  have heq : ENNReal.ofReal z.toReal = z := ENNReal.ofReal_toReal hfin
  refine ⟨ENNReal.toReal_nonneg, by linarith, heq, ?_⟩
  calc
    z ^ s = ENNReal.ofReal z.toReal ^ s := congrArg (fun x : ℝ≥0∞ => x ^ s) heq.symm
    _ = ENNReal.ofReal (z.toReal ^ s) := ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hs

end Local_T004
open Local_T004 in
theorem T004 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T003 : @YuiPortTypes.T003.{u} n E) :
    ∀ (X : Type u) [MetricSpace X] (A : Set X) (s : ℝ), 0 < s →
  (∀ δ : ℝ, 0 < δ →
    C s δ A = ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)
      (_ : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ), ∑' i, Metric.ediam (U i) ^ s) ∧
  (∀ δ₁ δ₂ : ℝ, 0 < δ₁ → δ₁ ≤ δ₂ → C s δ₂ A ≤ C s δ₁ A) ∧
  (H s A = ⨆ (δ : ℝ) (_ : 0 < δ), C s δ A) ∧
  (H s A = 0 → ∀ r ε : ℝ, 0 < r → 0 < ε →
    ∃ (U : ℕ → Set X) (a : ℕ → ℝ),
      (A ⊆ ⋃ i, U i) ∧ (∀ i, 0 < a i ∧ a i ≤ r) ∧
      (∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal (a i)) ∧
      (∑' i, ENNReal.ofReal ((a i) ^ s)) < ENNReal.ofReal ε) := by
  classical
  intro X instX A s hs
  have hnorm := h_T003 X A s hs
  refine ⟨hnorm.1, hnorm.2.1, hnorm.2.2, ?_⟩
  intro hH r ε hr hε
  obtain ⟨U, hcover, hdiam, hcost⟩ :=
    yui_aux_0003 n E h_T003 X A s r ε hs hH hr hε
  let d : ℕ → ℝ := fun i => (Metric.ediam (U i)).toReal
  let e : ℕ → ℝ := fun i => ε / 8 * ((1 : ℝ) / 2) ^ i
  have hgeom := yui_aux_0002 n E h_T003 ε hε
  have hd : ∀ i, 0 ≤ d i ∧ d i < r ∧
      ENNReal.ofReal (d i) = Metric.ediam (U i) ∧
      Metric.ediam (U i) ^ s = ENNReal.ofReal ((d i) ^ s) := by
    intro i
    exact yui_aux_0004 n E h_T003 (Metric.ediam (U i)) r s hr hs.le (hdiam i)
  have hex : ∀ i, ∃ a : ℝ, d i < a ∧ a < r ∧ a ^ s < (d i) ^ s + e i := by
    intro i
    exact yui_aux_0001 n E h_T003 s (d i) r (e i) hs.le (hd i).1 (hd i).2.1 (hgeom.1 i)
  choose a ha using hex
  refine ⟨U, a, hcover, ?_, ?_, ?_⟩
  · intro i
    exact ⟨lt_of_le_of_lt (hd i).1 (ha i).1, (ha i).2.1.le⟩
  · intro i
    rw [← (hd i).2.2.1]
    exact ENNReal.ofReal_le_ofReal (ha i).1.le
  · have hterm : ∀ i, ENNReal.ofReal ((a i) ^ s) ≤
        Metric.ediam (U i) ^ s + ENNReal.ofReal (e i) := by
      intro i
      calc
        ENNReal.ofReal ((a i) ^ s) ≤ ENNReal.ofReal ((d i) ^ s + e i) :=
          ENNReal.ofReal_le_ofReal (ha i).2.2.le
        _ = ENNReal.ofReal ((d i) ^ s) + ENNReal.ofReal (e i) :=
          ENNReal.ofReal_add (Real.rpow_nonneg (hd i).1 s) (hgeom.1 i).le
        _ = Metric.ediam (U i) ^ s + ENNReal.ofReal (e i) := by rw [(hd i).2.2.2]
    have heSum : (∑' i, ENNReal.ofReal (e i)) = ENNReal.ofReal (ε / 4) := hgeom.2
    calc
      (∑' i, ENNReal.ofReal ((a i) ^ s)) ≤
          ∑' i, (Metric.ediam (U i) ^ s + ENNReal.ofReal (e i)) :=
        ENNReal.tsum_le_tsum hterm
      _ = (∑' i, Metric.ediam (U i) ^ s) + ENNReal.ofReal (ε / 4) := by
        rw [ENNReal.tsum_add, heSum]
      _ < ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) :=
        ENNReal.add_lt_add_right ENNReal.ofReal_ne_top hcost
      _ = ENNReal.ofReal (ε / 2) := by
        rw [← ENNReal.ofReal_add (by linarith : 0 ≤ ε / 4) (by linarith : 0 ≤ ε / 4)]
        congr 1
        ring
      _ < ENNReal.ofReal ε := (ENNReal.ofReal_lt_ofReal_iff hε).mpr (by linarith)

end
#check @T004
#print axioms T004

end Translation
