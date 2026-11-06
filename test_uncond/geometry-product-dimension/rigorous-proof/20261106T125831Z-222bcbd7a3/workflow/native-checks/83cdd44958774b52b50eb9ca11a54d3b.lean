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
abbrev T004.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n)) : Prop :=
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
      (∑' i, ENNReal.ofReal ((a i) ^ s)) < ENNReal.ofReal ε)
abbrev T005.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n)) : Prop :=
  ∀ (X : Type u) [MetricSpace X] (V : ℕ → Set (X × ℝ)) (δ : ℝ), 0 < δ →
  (∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ) →
  ∃ J : ℕ → Set ℝ,
    (∀ i, Prod.snd '' (V i) ⊆ J i) ∧
    (∀ i, IsClosed (J i)) ∧
    (∀ i, volume (J i) ≤ Metric.ediam (V i))
abbrev T006.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n)) : Prop :=
  ∀ (X : Type u) [MetricSpace X] (A : Set X) (s : ℝ), 0 < s →
  (∀ δ : ℝ, 0 < δ → C s δ A ≤ C (s + 1) δ (A ×ˢ YuiBasis.unitInterval)) ∧
  H s A ≤ H (s + 1) (A ×ˢ YuiBasis.unitInterval)
abbrev T007.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n)) : Prop :=
  ∀ (X : Type u) [MetricSpace X] (A : Set X) (q : ℝ), 0 < q → H q A = 0 →
  ∀ δ ε : ℝ, 0 < δ → 0 < ε →
    ∃ V : ℕ → Set (X × ℝ), (A ×ˢ YuiBasis.unitInterval ⊆ ⋃ i, V i) ∧
      (∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ) ∧
      (∑' i, Metric.ediam (V i) ^ (q + 1)) < ENNReal.ofReal (2 * ε)
abbrev T008.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n)) : Prop :=
  ∀ (X : Type u) [MetricSpace X] (A : Set X) (q : ℝ), 0 < q → H q A = 0 →
  H (q + 1) (A ×ˢ YuiBasis.unitInterval) = 0 ∧
  (∀ δ ε : ℝ, 0 < δ → 0 < ε →
    ∃ V : ℕ → Set (X × ℝ), (A ×ˢ YuiBasis.unitInterval ⊆ ⋃ i, V i) ∧
      (∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ) ∧
      (∑' i, Metric.ediam (V i) ^ (q + 1)) < ENNReal.ofReal (2 * ε))
abbrev T009.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n)) : Prop :=
  ∀ (X : Type u) [MetricSpace X] (A : Set X), A.Nonempty → 1 ≤ dimH (A ×ˢ YuiBasis.unitInterval)
abbrev T010.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n)) : Prop :=
  ∀ (X : Type u) [MetricSpace X] (A : Set X), A.Nonempty → dimH A ≠ ⊤ →
  dimH (A ×ˢ YuiBasis.unitInterval) ≠ ⊤ ∧
  dimH (A ×ˢ YuiBasis.unitInterval) ≤ dimH A + 1 ∧
  1 ≤ dimH (A ×ˢ YuiBasis.unitInterval)
abbrev T011.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n)) : Prop :=
  ∀ (X : Type u) [MetricSpace X] (A : Set X), A.Nonempty → dimH A ≠ ⊤ →
  dimH (A ×ˢ YuiBasis.unitInterval) = dimH A + 1 ∧ dimH (A ×ˢ YuiBasis.unitInterval) ≠ ⊤
abbrev T013 (n : ℕ) (E : Set (YuiBasis.Ambient n)) : Prop :=
  Function.Bijective (appendCoord n) ∧
  (∀ p p' : Ambient n × ℝ,
    dist p p' ≤ dist (appendCoord n p) (appendCoord n p') ∧
    dist (appendCoord n p) (appendCoord n p') ≤ Real.sqrt 2 * dist p p') ∧
  LipschitzWith (Real.toNNReal (Real.sqrt 2)) (appendCoord n) ∧
  AntilipschitzWith 1 (appendCoord n) ∧
  ∀ S : Set (Ambient n × ℝ), dimH (appendCoord n '' S) = dimH S
end YuiPortTypes

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace Translation
set_option autoImplicit false

theorem T001 (n : ℕ) (E : Set (YuiBasis.Ambient n))  :
    (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞)) ∧ dimH E ≠ ⊤ := by
  refine ⟨⟨bot_le, ?_⟩, Real.dimH_ne_top E⟩
  calc
    dimH E ≤ dimH (Set.univ : Set (Ambient n)) := dimH_mono (Set.subset_univ E)
    _ = (Module.finrank ℝ (Ambient n) : ℝ≥0∞) := Real.dimH_univ_eq_finrank (Ambient n)
    _ = (n : ℝ≥0∞) := by rw [finrank_euclideanSpace_fin]

section
universe u
namespace Local_T003
theorem yui_aux_0001 (n : ℕ) (E : Set (YuiBasis.Ambient n)) : yui_aux_type% "∀ (X : Type u) [MetricSpace X] (s : ℝ), 0 < s → ∀ B : Set X, (⨆ (_ : B.Nonempty), Metric.ediam B ^ s) = Metric.ediam B ^ s" := by
  intro X _ s hs B
  by_cases hB : B.Nonempty
  · simp [hB]
  · have hE : B = ∅ := Set.not_nonempty_iff_eq_empty.mp hB
    simp [hE, ENNReal.zero_rpow_of_pos hs]

theorem yui_aux_0002 (n : ℕ) (E : Set (YuiBasis.Ambient n)) : yui_aux_type% "∀ (X : Type u) [MetricSpace X] (A : Set X) (s : ℝ) (r₁ r₂ : ℝ≥0∞), r₁ ≤ r₂ → YuiBasis.Content s r₂ A ≤ YuiBasis.Content s r₁ A" := by
  intro X _ A s r₁ r₂ hr
  unfold YuiBasis.Content
  refine le_iInf fun U => le_iInf fun hU => le_iInf fun hd => ?_
  exact iInf_le_of_le U (iInf_le_of_le hU (iInf_le_of_le (fun i => (hd i).trans hr) le_rfl))

theorem yui_aux_0003 (n : ℕ) (E : Set (YuiBasis.Ambient n)) : yui_aux_type% "∀ r : ℝ≥0∞, 0 < r → ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ ≤ r" := by
  intro r hr
  by_cases ht : r = ∞
  · exact ⟨1, zero_lt_one, by simp [ht]⟩
  · refine ⟨r.toReal / 2, half_pos (ENNReal.toReal_pos (ne_of_gt hr) ht), ?_⟩
    have hhalf : r.toReal / 2 ≤ r.toReal := by linarith [ENNReal.toReal_nonneg (a := r)]
    calc
      ENNReal.ofReal (r.toReal / 2) ≤ ENNReal.ofReal r.toReal := ENNReal.ofReal_le_ofReal hhalf
      _ = r := ENNReal.ofReal_toReal ht

end Local_T003
open Local_T003 in
theorem T003 (n : ℕ) (E : Set (YuiBasis.Ambient n))  :
    ∀ (X : Type u) [MetricSpace X] (A : Set X) (s : ℝ), 0 < s →
  (∀ δ : ℝ, 0 < δ →
    C s δ A = ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)
      (_ : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ), ∑' i, Metric.ediam (U i) ^ s) ∧
  (∀ δ₁ δ₂ : ℝ, 0 < δ₁ → δ₁ ≤ δ₂ → C s δ₂ A ≤ C s δ₁ A) ∧
  H s A = ⨆ (δ : ℝ) (_ : 0 < δ), C s δ A := by
  intro X inst A s hs
  have hcost := @yui_aux_0001 n E X inst s hs
  have hmono := @yui_aux_0002 n E X inst A s
  refine ⟨?_, ?_, ?_⟩
  · intro δ hδ
    unfold C YuiBasis.Content
    simp_rw [hcost]
  · intro δ₁ δ₂ hδ₁ hδ
    exact hmono (ENNReal.ofReal δ₁) (ENNReal.ofReal δ₂) (ENNReal.ofReal_le_ofReal hδ)
  · have hH : H s A = ⨆ (r : ℝ≥0∞) (_ : 0 < r), YuiBasis.Content s r A := by
      letI : MeasurableSpace X := borel X
      letI : BorelSpace X := ⟨rfl⟩
      exact hausdorffMeasure_apply s A
    rw [hH]
    apply le_antisymm
    · refine iSup₂_le fun r hr => ?_
      rcases @yui_aux_0003 n E r hr with ⟨δ, hδ, hδr⟩
      calc
        YuiBasis.Content s r A ≤ C s δ A := hmono (ENNReal.ofReal δ) r hδr
        _ ≤ ⨆ (δ : ℝ) (_ : 0 < δ), C s δ A := le_iSup₂_of_le δ hδ le_rfl
    · refine iSup₂_le fun δ hδ => ?_
      exact le_iSup₂_of_le (ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδ) le_rfl

end
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
section
universe u
theorem T005 (n : ℕ) (E : Set (YuiBasis.Ambient n))  :
    ∀ (X : Type u) [MetricSpace X] (V : ℕ → Set (X × ℝ)) (δ : ℝ), 0 < δ →
  (∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ) →
  ∃ J : ℕ → Set ℝ,
    (∀ i, Prod.snd '' (V i) ⊆ J i) ∧
    (∀ i, IsClosed (J i)) ∧
    (∀ i, volume (J i) ≤ Metric.ediam (V i)) := by
  classical
  intro X inst V δ hδ hV
  have hproj (i : ℕ) :
      Metric.ediam (Prod.snd '' V i) ≤ Metric.ediam (V i) := by
    simpa using
      (LipschitzWith.prod_snd : LipschitzWith 1 (@Prod.snd X ℝ)).ediam_image_le (V i)
  have hbounded (i : ℕ) : Bornology.IsBounded (Prod.snd '' V i) :=
    Metric.isBounded_iff_ediam_ne_top.mpr
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((hproj i).trans (hV i)))
  have hex (i : ℕ) : ∃ J : Set ℝ,
      Prod.snd '' V i ⊆ J ∧ IsClosed J ∧ volume J ≤ Metric.ediam (V i) := by
    by_cases hi : (Prod.snd '' V i).Nonempty
    · refine ⟨Set.Icc (sInf (Prod.snd '' V i)) (sSup (Prod.snd '' V i)),
        (hbounded i).subset_Icc_sInf_sSup, isClosed_Icc, ?_⟩
      rw [Real.volume_Icc, ← Real.ediam_eq (hbounded i)]
      exact hproj i
    · refine ⟨∅, ?_, isClosed_empty, ?_⟩
      · simp only [Set.not_nonempty_iff_eq_empty] at hi
        simp [hi]
      · simp
  choose J hJ using hex
  exact ⟨J, fun i => (hJ i).1, fun i => (hJ i).2.1, fun i => (hJ i).2.2⟩

end
section
universe u
namespace Local_T006
theorem yui_aux_0001 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T004 : @YuiPortTypes.T004.{u} n E) (h_T005 : @YuiPortTypes.T005.{u} n E) : yui_aux_type% "∀ (X : Type u) [MetricSpace X] (A : Set X) (s δ : ℝ), 0 < s → 0 < δ → ∀ (W : ℕ → Set X), (A ⊆ ⋃ i, W i) → (∀ i, Metric.ediam (W i) ≤ ENNReal.ofReal δ) → C s δ A ≤ ∑' i, Metric.ediam (W i) ^ s" := by
  intro X _ A s δ hs hδ W hc hd
  rw [(h_T004 X A s hs).1 δ hδ]
  exact iInf_le_of_le W (iInf_le_of_le hc (iInf_le_of_le hd (le_refl (∑' i, Metric.ediam (W i) ^ s))))

theorem yui_aux_0002 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T004 : @YuiPortTypes.T004.{u} n E) (h_T005 : @YuiPortTypes.T005.{u} n E) : yui_aux_type% "∀ (X : Type u) [MetricSpace X] (A : Set X) (s δ : ℝ), 0 < s → 0 < δ → ∀ (V : ℕ → Set (X × ℝ)), (A ×ˢ YuiBasis.unitInterval ⊆ ⋃ i, V i) → (∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ) → ∀ (J : ℕ → Set ℝ), (∀ i, Prod.snd '' (V i) ⊆ J i) → ∀ t ∈ YuiBasis.unitInterval, C s δ A ≤ ∑' i, (J i).indicator (fun _ : ℝ => Metric.ediam (V i) ^ s) t" := by
  classical
  intro X _ A s δ hs hδ V hcover hdiam J hJ t ht
  let W : ℕ → Set X := fun i => if t ∈ J i then Prod.fst '' V i else ∅
  have hp (i : ℕ) : Metric.ediam (Prod.fst '' V i) ≤ Metric.ediam (V i) := by
    simpa using (LipschitzWith.prod_fst : LipschitzWith 1 (@Prod.fst X ℝ)).ediam_image_le (V i)
  have hw (i : ℕ) : Metric.ediam (W i) ≤ Metric.ediam (V i) := by
    dsimp [W]
    split_ifs
    · exact hp i
    · simp
  have hc : A ⊆ ⋃ i, W i := by
    intro x hx
    have hxt : (x,t) ∈ A ×ˢ YuiBasis.unitInterval := ⟨hx, ht⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hxt)
    have hti : t ∈ J i := hJ i ⟨(x,t), hi, rfl⟩
    exact Set.mem_iUnion.mpr ⟨i, by simpa [W, hti] using (show x ∈ Prod.fst '' V i from ⟨(x,t), hi, rfl⟩)⟩
  refine (yui_aux_0001 n E h_T004 h_T005 X A s δ hs hδ W hc (fun i => (hw i).trans (hdiam i))).trans ?_
  apply ENNReal.tsum_le_tsum
  intro i
  by_cases hti : t ∈ J i
  · simpa [Set.indicator_of_mem hti] using ENNReal.rpow_le_rpow (hw i) hs.le
  · simp [W, hti, ENNReal.zero_rpow_of_pos hs]

theorem yui_aux_0003 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T004 : @YuiPortTypes.T004.{u} n E) (h_T005 : @YuiPortTypes.T005.{u} n E) : yui_aux_type% "∀ (d : ℝ≥0∞) (s : ℝ), 0 < s → d ^ s * d = d ^ (s + 1)" := by
  intro d s hs
  by_cases hd : d = 0
  · simp [hd, ENNReal.zero_rpow_of_pos hs, ENNReal.zero_rpow_of_pos (add_pos hs zero_lt_one)]
  · rw [ENNReal.rpow_add_of_nonneg s 1 hs.le zero_le_one, ENNReal.rpow_one]

theorem yui_aux_0004 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T004 : @YuiPortTypes.T004.{u} n E) (h_T005 : @YuiPortTypes.T005.{u} n E) : yui_aux_type% "∀ c : ℝ≥0∞, (∫⁻ t : ℝ, YuiBasis.unitInterval.indicator (fun _ => c) t) = c" := by
  intro c
  have hmeas : MeasurableSet YuiBasis.unitInterval := measurableSet_Icc
  have hI : volume YuiBasis.unitInterval = 1 := by simp [YuiBasis.unitInterval, Real.volume_Icc]
  rw [lintegral_indicator_const (μ := volume) hmeas c, hI, mul_one]

theorem yui_aux_0005 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T004 : @YuiPortTypes.T004.{u} n E) (h_T005 : @YuiPortTypes.T005.{u} n E) : yui_aux_type% "∀ (c : ℝ≥0∞) (d : ℕ → ℝ≥0∞) (s : ℝ) (J : ℕ → Set ℝ), 0 < s → (∀ i, IsClosed (J i)) → (∀ i, volume (J i) ≤ d i) → (∀ t ∈ YuiBasis.unitInterval, c ≤ ∑' i, (J i).indicator (fun _ : ℝ => d i ^ s) t) → c ≤ ∑' i, d i ^ (s+1)" := by
  classical
  intro c d s J hs hclosed hvol hslice
  let g : ℕ → ℝ → ℝ≥0∞ := fun i => (J i ∩ YuiBasis.unitInterval).indicator (fun _ => d i ^ s)
  have hm (i : ℕ) : Measurable (g i) :=
    measurable_const.indicator ((hclosed i).measurableSet.inter measurableSet_Icc)
  have hpoint : ∀ t : ℝ, YuiBasis.unitInterval.indicator (fun _ => c) t ≤ ∑' i, g i t := by
    intro t
    by_cases ht : t ∈ YuiBasis.unitInterval
    · have heq (i : ℕ) : g i t = (J i).indicator (fun _ : ℝ => d i ^ s) t := by
        by_cases hj : t ∈ J i <;> simp [g, ht, hj]
      simpa only [Set.indicator_of_mem ht, heq] using hslice t ht
    · simp [Set.indicator_of_notMem ht]
  calc
    c = ∫⁻ t : ℝ, YuiBasis.unitInterval.indicator (fun _ => c) t := (yui_aux_0004 n E h_T004 h_T005 c).symm
    _ ≤ ∫⁻ t : ℝ, ∑' i, g i t := lintegral_mono hpoint
    _ = ∑' i, ∫⁻ t : ℝ, g i t := lintegral_tsum (fun i => (hm i).aemeasurable)
    _ ≤ ∑' i, d i ^ (s+1) := by
      apply ENNReal.tsum_le_tsum
      intro i
      rw [show (∫⁻ t : ℝ, g i t) = d i ^ s * volume (J i ∩ YuiBasis.unitInterval) from
        lintegral_indicator_const ((hclosed i).measurableSet.inter measurableSet_Icc) _]
      calc
        _ ≤ d i ^ s * volume (J i) := mul_le_mul_left' (measure_mono Set.inter_subset_left) _
        _ ≤ d i ^ s * d i := mul_le_mul_left' (hvol i) _
        _ = d i ^ (s+1) := yui_aux_0003 n E h_T004 h_T005 (d i) s hs

end Local_T006
open Local_T006 in
theorem T006 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T004 : @YuiPortTypes.T004.{u} n E) (h_T005 : @YuiPortTypes.T005.{u} n E) :
    ∀ (X : Type u) [MetricSpace X] (A : Set X) (s : ℝ), 0 < s →
  (∀ δ : ℝ, 0 < δ → C s δ A ≤ C (s + 1) δ (A ×ˢ YuiBasis.unitInterval)) ∧
  H s A ≤ H (s + 1) (A ×ˢ YuiBasis.unitInterval) := by
  classical
  intro X _ A s hs
  have hs1 : 0 < s + 1 := add_pos hs zero_lt_one
  have hscale : ∀ δ : ℝ, 0 < δ → C s δ A ≤ C (s + 1) δ (A ×ˢ YuiBasis.unitInterval) := by
    intro δ hδ
    rw [(h_T004 (X × ℝ) (A ×ˢ YuiBasis.unitInterval) (s+1) hs1).1 δ hδ]
    refine le_iInf fun V => le_iInf fun hcover => le_iInf fun hdiam => ?_
    obtain ⟨J, hJ, hclosed, hvol⟩ := h_T005 X V δ hδ hdiam
    exact yui_aux_0005 n E h_T004 h_T005 (C s δ A) (fun i => Metric.ediam (V i)) s J hs hclosed hvol
      (yui_aux_0002 n E h_T004 h_T005 X A s δ hs hδ V hcover hdiam J hJ)
  refine ⟨hscale, ?_⟩
  rw [(h_T004 X A s hs).2.2.1,
    (h_T004 (X × ℝ) (A ×ˢ YuiBasis.unitInterval) (s+1) hs1).2.2.1]
  exact iSup_mono fun δ => iSup_mono fun hδ => hscale δ hδ

end
section
universe u
namespace Local_T007
theorem yui_aux_0001 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T004 : @YuiPortTypes.T004.{u} n E) : yui_aux_type% "∀ (N : ℕ), 0 < N → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ j : Fin N, t ∈ Set.Icc ((j : ℝ) / N) (((j : ℝ) + 1) / N)" := by
  intro N hN t ht
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  by_cases ht1 : t = 1
  · refine ⟨⟨N - 1, Nat.sub_lt hN (by omega)⟩, ?_⟩
    have hc : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
    simp only [Fin.val_mk, ht1, Set.mem_Icc]
    rw [hc]
    constructor
    · apply (div_le_iff₀ hn).mpr
      linarith
    · apply (le_div_iff₀ hn).mpr
      linarith
  · have htt : t < 1 := lt_of_le_of_ne ht.2 ht1
    have hnon : 0 ≤ t * N := mul_nonneg ht.1 hn.le
    have hj : ⌊t * N⌋₊ < N := (Nat.floor_lt hnon).mpr (by nlinarith)
    refine ⟨⟨⌊t * N⌋₊, hj⟩, ?_⟩
    change (⌊t * N⌋₊ : ℝ) / N ≤ t ∧ t ≤ ((⌊t * N⌋₊ : ℝ) + 1) / N
    exact ⟨(div_le_iff₀ hn).mpr (Nat.floor_le hnon),
      (le_div_iff₀ hn).mpr (Nat.lt_floor_add_one _).le⟩

theorem yui_aux_0002 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T004 : @YuiPortTypes.T004.{u} n E) : yui_aux_type% "∀ (a : ℝ), 0 < a → a ≤ 1 → let N := ⌈1 / a⌉₊; 0 < N ∧ 1 / (N : ℝ) ≤ a ∧ (N : ℝ) * a ≤ 2" := by
  intro a ha ha1
  dsimp
  have hN : 0 < ⌈1 / a⌉₊ := Nat.ceil_pos.mpr (by positivity)
  have hNr : (0 : ℝ) < ⌈1 / a⌉₊ := by exact_mod_cast hN
  have hlo : 1 / a ≤ (⌈1 / a⌉₊ : ℝ) := Nat.le_ceil _
  have hhi : (⌈1 / a⌉₊ : ℝ) < 1 / a + 1 := Nat.ceil_lt_add_one (by positivity)
  refine ⟨hN, ?_, ?_⟩
  · apply (div_le_iff₀ hNr).mpr
    have := (div_le_iff₀ ha).mp hlo
    nlinarith
  · have hh := mul_lt_mul_of_pos_right hhi ha
    have he : (1 / a + 1) * a = 1 + a := by field_simp
    rw [he] at hh
    linarith

theorem yui_aux_0003 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T004 : @YuiPortTypes.T004.{u} n E) : yui_aux_type% "∀ (X : Type u) [MetricSpace X] (U : Set X) (a : ℝ) (N : ℕ), 0 < N → Metric.ediam U ≤ ENNReal.ofReal a → 1 / (N : ℝ) ≤ a → ∀ j : Fin N, Metric.ediam (U ×ˢ Set.Icc ((j : ℝ) / N) (((j : ℝ) + 1) / N)) ≤ ENNReal.ofReal a" := by
  intro X inst U a N hN hU hNa j
  apply Metric.ediam_le_iff.mpr
  intro x hx y hy
  rw [Prod.edist_eq]
  apply max_le
  · exact Metric.edist_le_of_ediam_le hx.1 hy.1 hU
  · have hJ : Metric.ediam (Set.Icc ((j : ℝ) / N) (((j : ℝ) + 1) / N)) ≤ ENNReal.ofReal a := by
      rw [Real.ediam_Icc]
      apply ENNReal.ofReal_le_ofReal
      convert hNa using 1 <;> ring
    exact Metric.edist_le_of_ediam_le hx.2 hy.2 hJ

theorem yui_aux_0004 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T004 : @YuiPortTypes.T004.{u} n E) : yui_aux_type% "∀ (N : ℕ) (b : ℝ), 0 ≤ b → (∑' j : Fin N, ENNReal.ofReal b) = ENNReal.ofReal ((N : ℝ) * b)" := by
  intro N b hb
  simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg N)]
  simp

theorem yui_aux_0005 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T004 : @YuiPortTypes.T004.{u} n E) : yui_aux_type% "∀ (N : ℕ) (a q : ℝ) (c : Fin N → ℝ≥0∞), 0 < a → 0 < q → (N : ℝ) * a ≤ 2 → (∀ j, c j ≤ ENNReal.ofReal a) → (∑' j, (c j) ^ (q + 1)) ≤ 2 * ENNReal.ofReal (a ^ q)" := by
  intro N a q c ha hq hNa hc
  have hp : 0 ≤ q + 1 := by linarith
  calc
    (∑' j, c j ^ (q + 1)) ≤ ∑' j : Fin N, ENNReal.ofReal (a ^ (q + 1)) := by
      apply ENNReal.tsum_le_tsum
      intro j
      rw [← ENNReal.ofReal_rpow_of_pos ha]
      exact ENNReal.rpow_le_rpow (hc j) hp
    _ = ENNReal.ofReal ((N : ℝ) * a ^ (q + 1)) :=
      @yui_aux_0004 n E h_T004 N _ (Real.rpow_nonneg ha.le _)
    _ ≤ ENNReal.ofReal (2 * a ^ q) := by
      apply ENNReal.ofReal_le_ofReal
      rw [Real.rpow_add_one ha.ne']
      nlinarith [mul_le_mul_of_nonneg_right hNa (Real.rpow_nonneg ha.le q)]
    _ = 2 * ENNReal.ofReal (a ^ q) := by rw [ENNReal.ofReal_mul (by norm_num)]; norm_num

theorem yui_aux_0006 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T004 : @YuiPortTypes.T004.{u} n E) : yui_aux_type% "∀ (b c : ℝ≥0∞), b < c → (2 : ℝ≥0∞) * b < 2 * c" := by
  intro b c hbc
  simpa only [mul_comm] using
    (ENNReal.mul_lt_mul_left (a := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) hbc)

end Local_T007
open Local_T007 in
theorem T007 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T004 : @YuiPortTypes.T004.{u} n E) :
    ∀ (X : Type u) [MetricSpace X] (A : Set X) (q : ℝ), 0 < q → H q A = 0 →
  ∀ δ ε : ℝ, 0 < δ → 0 < ε →
    ∃ V : ℕ → Set (X × ℝ), (A ×ˢ YuiBasis.unitInterval ⊆ ⋃ i, V i) ∧
      (∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ) ∧
      (∑' i, Metric.ediam (V i) ^ (q + 1)) < ENNReal.ofReal (2 * ε) := by
  classical
  intro X instX A q hq hqzero δ ε hδ hε
  have F001 := (h_T004 X A q hq).2.2.2 hqzero (min 1 δ) ε
    (lt_min zero_lt_one hδ) hε
  rcases F001 with ⟨U, a, hcover, ha, hdiam, hsum⟩
  let N : ℕ → ℕ := fun i => ⌈1 / a i⌉₊
  have hN : ∀ i, 0 < N i ∧ 1 / (N i : ℝ) ≤ a i ∧ (N i : ℝ) * a i ≤ 2 := by
    intro i
    exact @yui_aux_0002 n E h_T004 (a i) (ha i).1 ((ha i).2.trans (min_le_left _ _))
  let T := (i : ℕ) × Fin (N i)
  let P : T → Set (X × ℝ) := fun k =>
    U k.1 ×ˢ Set.Icc ((k.2 : ℝ) / N k.1) (((k.2 : ℝ) + 1) / N k.1)
  have hPd : ∀ k : T, Metric.ediam (P k) ≤ ENNReal.ofReal (a k.1) := by
    intro k
    exact @yui_aux_0003 n E h_T004 X instX (U k.1) (a k.1) (N k.1)
      (hN k.1).1 (hdiam k.1) (hN k.1).2.1 k.2
  have hPc : A ×ˢ YuiBasis.unitInterval ⊆ ⋃ k : T, P k := by
    intro x hx
    rcases Set.mem_iUnion.mp (hcover hx.1) with ⟨i, hi⟩
    obtain ⟨j, hj⟩ := @yui_aux_0001 n E h_T004 (N i) (hN i).1 x.2 hx.2
    exact Set.mem_iUnion.mpr ⟨⟨i, j⟩, hi, hj⟩
  have hPs : (∑' k : T, Metric.ediam (P k) ^ (q + 1)) ≤
      2 * ∑' i, ENNReal.ofReal ((a i) ^ q) := by
    rw [ENNReal.tsum_sigma']
    calc
      (∑' (i : ℕ) (j : Fin (N i)), Metric.ediam (P ⟨i,j⟩) ^ (q + 1)) ≤
          ∑' i, 2 * ENNReal.ofReal ((a i) ^ q) := by
        apply ENNReal.tsum_le_tsum
        intro i
        exact @yui_aux_0005 n E h_T004 (N i) (a i) q
          (fun j => Metric.ediam (P ⟨i,j⟩)) (ha i).1 hq (hN i).2.2
          (fun j => hPd ⟨i,j⟩)
      _ = _ := ENNReal.tsum_mul_left
  letI : Encodable T := Encodable.ofCountable T
  let V : ℕ → Set (X × ℝ) := fun m => ⋃ k ∈ Encodable.decode₂ T m, P k
  refine ⟨V, ?_, ?_, ?_⟩
  · change A ×ˢ YuiBasis.unitInterval ⊆ ⋃ m, ⋃ k ∈ Encodable.decode₂ T m, P k
    rw [Encodable.iUnion_decode₂]
    exact hPc
  · intro m
    dsimp only [V]
    rw [Metric.ediam_iUnion_mem_option]
    apply iSup₂_le
    intro k hk
    exact (hPd k).trans (ENNReal.ofReal_le_ofReal
      ((ha k.1).2.trans (min_le_right _ _)))
  · have hp : 0 < q + 1 := by linarith
    have hzero : (fun S : Set (X × ℝ) => Metric.ediam S ^ (q + 1)) ∅ = 0 := by
      simp [ENNReal.zero_rpow_of_pos hp]
    have hreindex : (∑' m, Metric.ediam (V m) ^ (q + 1)) =
        ∑' k : T, Metric.ediam (P k) ^ (q + 1) :=
      tsum_iUnion_decode₂ (fun S : Set (X × ℝ) => Metric.ediam S ^ (q + 1)) hzero P
    rw [hreindex]
    calc
      (∑' k : T, Metric.ediam (P k) ^ (q + 1)) ≤
          2 * ∑' i, ENNReal.ofReal ((a i) ^ q) := hPs
      _ < 2 * ENNReal.ofReal ε :=
        @yui_aux_0006 n E h_T004 _ _ hsum
      _ = ENNReal.ofReal (2 * ε) := by
        rw [ENNReal.ofReal_mul (by norm_num)]
        norm_num

end
section
universe u
namespace Local_T008
theorem yui_aux_0001 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T004 : @YuiPortTypes.T004.{u} n E) (h_T007 : @YuiPortTypes.T007.{u} n E) : yui_aux_type% "∀ z : ℝ≥0∞, (∀ ε : ℝ, 0 < ε → z ≤ ENNReal.ofReal (2 * ε)) → z = 0" := by
  intro z hz
  apply le_antisymm _ zero_le
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  have hεreal : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  have hhalf : 0 < (ε : ℝ) / 2 := by positivity
  have hconvert : ENNReal.ofReal (2 * ((ε : ℝ) / 2)) = (ε : ℝ≥0∞) := by
    rw [show 2 * ((ε : ℝ) / 2) = (ε : ℝ) by ring]
    exact ENNReal.ofReal_coe_nnreal
  simpa only [zero_add, hconvert] using hz ((ε : ℝ) / 2) hhalf

theorem yui_aux_0002 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T004 : @YuiPortTypes.T004.{u} n E) (h_T007 : @YuiPortTypes.T007.{u} n E) : yui_aux_type% "∀ (X : Type u) [MetricSpace X] (A : Set X) (s δ : ℝ) (V : ℕ → Set X), A ⊆ ⋃ i, V i → (∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ) → (⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i) (_ : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ), ∑' i, Metric.ediam (U i) ^ s) ≤ ∑' i, Metric.ediam (V i) ^ s" := by
  intro X instX A s δ V hcov hdiam
  apply iInf_le_of_le V
  apply iInf_le_of_le hcov
  apply iInf_le_of_le hdiam
  exact le_rfl

end Local_T008
open Local_T008 in
theorem T008 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T004 : @YuiPortTypes.T004.{u} n E) (h_T007 : @YuiPortTypes.T007.{u} n E) :
    ∀ (X : Type u) [MetricSpace X] (A : Set X) (q : ℝ), 0 < q → H q A = 0 →
  H (q + 1) (A ×ˢ YuiBasis.unitInterval) = 0 ∧
  (∀ δ ε : ℝ, 0 < δ → 0 < ε →
    ∃ V : ℕ → Set (X × ℝ), (A ×ˢ YuiBasis.unitInterval ⊆ ⋃ i, V i) ∧
      (∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ) ∧
      (∑' i, Metric.ediam (V i) ^ (q + 1)) < ENNReal.ofReal (2 * ε)) := by
  intro X instX A q hq hqzero
  have hcover := h_T007 X A q hq hqzero
  have hcontent := h_T004 (X × ℝ) (A ×ˢ YuiBasis.unitInterval) (q + 1) (add_pos hq zero_lt_one)
  have hzero : ∀ δ : ℝ, 0 < δ → C (q + 1) δ (A ×ˢ YuiBasis.unitInterval) = 0 := by
    intro δ hδ
    apply (@yui_aux_0001 n E h_T004 h_T007)
    intro ε hε
    obtain ⟨V, hVcover, hVdiam, hVcost⟩ := hcover δ ε hδ hε
    rw [hcontent.1 δ hδ]
    exact (@yui_aux_0002 n E h_T004 h_T007 (X × ℝ) inferInstance
      (A ×ˢ YuiBasis.unitInterval) (q + 1) δ V hVcover hVdiam).trans hVcost.le
  constructor
  · rw [hcontent.2.2.1]
    apply le_antisymm _ zero_le
    refine iSup_le fun δ => iSup_le fun hδ => ?_
    rw [hzero δ hδ]
  · exact hcover

end
theorem T002 (n : ℕ) (E : Set (YuiBasis.Ambient n))  :
    dimH YuiBasis.unitInterval = 1 := by
  have hdim : dimH (segment ℝ (0 : ℝ) 1) = 1 :=
    Real.dimH_segment (by norm_num)
  have hsegment : segment ℝ (0 : ℝ) 1 = Set.Icc 0 1 :=
    segment_eq_Icc (by norm_num)
  simpa only [hsegment, YuiBasis.unitInterval] using hdim

section
universe u
theorem T009 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T002 : dimH YuiBasis.unitInterval = 1) :
    ∀ (X : Type u) [MetricSpace X] (A : Set X), A.Nonempty → 1 ≤ dimH (A ×ˢ YuiBasis.unitInterval) := by
  intro X _ A hA
  rcases hA with ⟨x₀, hx₀⟩
  let f : ℝ → X × ℝ := fun t => (x₀, t)
  have hf : Isometry f := by
    apply Isometry.of_dist_eq
    intro t u
    simp [f, Prod.dist_eq, dist_nonneg]
  have hdim : dimH (f '' YuiBasis.unitInterval) = dimH YuiBasis.unitInterval :=
    le_antisymm (hf.lipschitz.dimH_image_le _) (hf.antilipschitz.le_dimH_image _)
  have hsub : f '' YuiBasis.unitInterval ⊆ A ×ˢ YuiBasis.unitInterval := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨hx₀, ht⟩
  calc
    1 = dimH (f '' YuiBasis.unitInterval) := (hdim.trans h_T002).symm
    _ ≤ dimH (A ×ˢ YuiBasis.unitInterval) := dimH_mono hsub

end
section
universe u
namespace Local_T010
theorem yui_aux_0001 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T008 : @YuiPortTypes.T008.{u} n E) (h_T009 : @YuiPortTypes.T009.{u} n E) : yui_aux_type% "∀ (X : Type u) [MetricSpace X] (A : Set X) (q : ℝ), dimH A ≠ ⊤ → (dimH A).toReal < q → dimH (A ×ˢ YuiBasis.unitInterval) ≤ ENNReal.ofReal (q + 1)" := by
  intro X instX A q hfin hq
  have hqpos : 0 < q := lt_of_le_of_lt ENNReal.toReal_nonneg hq
  let d : ℝ≥0 := ⟨q, hqpos.le⟩
  have hd : (d : ℝ≥0∞) = ENNReal.ofReal q := (ENNReal.ofReal_eq_coe_nnreal hqpos.le).symm
  have hlt : dimH A < (d : ℝ≥0∞) := by
    rw [hd, ← ENNReal.ofReal_toReal hfin]
    exact (ENNReal.ofReal_lt_ofReal_iff hqpos).2 hq
  have hz : H q A = 0 := by
    letI : MeasurableSpace X := borel X
    letI : BorelSpace X := ⟨rfl⟩
    exact hausdorffMeasure_of_dimH_lt (s := A) (d := d) hlt
  have hgz : H (q + 1) (A ×ˢ YuiBasis.unitInterval) = 0 := (h_T008 X A q hqpos hz).1
  have hq1 : 0 ≤ q + 1 := by linarith
  let e : ℝ≥0 := ⟨q + 1, hq1⟩
  have he : (e : ℝ≥0∞) = ENNReal.ofReal (q + 1) := (ENNReal.ofReal_eq_coe_nnreal hq1).symm
  rw [← he]
  letI : MeasurableSpace (X × ℝ) := borel (X × ℝ)
  letI : BorelSpace (X × ℝ) := ⟨rfl⟩
  apply dimH_le_of_hausdorffMeasure_ne_top (s := A ×ˢ YuiBasis.unitInterval) (d := e)
  change H (q + 1) (A ×ˢ YuiBasis.unitInterval) ≠ ⊤
  rw [hgz]
  exact ENNReal.zero_ne_top

end Local_T010
open Local_T010 in
theorem T010 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T008 : @YuiPortTypes.T008.{u} n E) (h_T009 : @YuiPortTypes.T009.{u} n E) :
    ∀ (X : Type u) [MetricSpace X] (A : Set X), A.Nonempty → dimH A ≠ ⊤ →
  dimH (A ×ˢ YuiBasis.unitInterval) ≠ ⊤ ∧
  dimH (A ×ˢ YuiBasis.unitInterval) ≤ dimH A + 1 ∧
  1 ≤ dimH (A ×ˢ YuiBasis.unitInterval) := by
  intro X instX A hA hAfin
  let D : ℝ := (dimH A).toReal
  let G : Set (X × ℝ) := A ×ˢ YuiBasis.unitInterval
  have hDnonneg : 0 ≤ D := ENNReal.toReal_nonneg
  have hD : ENNReal.ofReal D = dimH A := ENNReal.ofReal_toReal hAfin
  have hb : ∀ q : ℝ, D < q → dimH G ≤ ENNReal.ofReal (q + 1) := by
    intro q hq
    exact yui_aux_0001 n E h_T008 h_T009 X A q hAfin hq
  have hq0 : D < D + 1 := by linarith
  have hGfin : dimH G ≠ ⊤ := ne_of_lt (lt_of_le_of_lt (hb (D + 1) hq0) ENNReal.ofReal_lt_top)
  let T : ℝ := (dimH G).toReal
  have hTnonneg : 0 ≤ T := ENNReal.toReal_nonneg
  have hT : ENNReal.ofReal T = dimH G := ENNReal.ofReal_toReal hGfin
  have hsharp : T ≤ D + 1 := by
    by_contra hn
    have hgt : D + 1 < T := lt_of_not_ge hn
    let qmid : ℝ := D + (T - D - 1) / 2
    have hmid : D < qmid := by dsimp [qmid]; linarith
    have hmidpos : 0 ≤ qmid + 1 := by linarith
    have hmidlt : qmid + 1 < T := by dsimp [qmid]; linarith
    have hbound : dimH G ≤ ENNReal.ofReal (qmid + 1) := hb qmid hmid
    have hreal : T ≤ qmid + 1 := by
      have hc := (ENNReal.toReal_le_toReal hGfin ENNReal.ofReal_ne_top).2 hbound
      simpa only [ENNReal.toReal_ofReal hmidpos] using hc
    linarith
  have hupper : dimH G ≤ dimH A + 1 := by
    rw [← hT, ← hD, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add hDnonneg (by norm_num : (0 : ℝ) ≤ 1)]
    exact ENNReal.ofReal_le_ofReal hsharp
  exact ⟨hGfin, hupper, h_T009 X A hA⟩

end
section
universe u
namespace Local_T011
theorem yui_aux_0001 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T006 : @YuiPortTypes.T006.{u} n E) (h_T010 : @YuiPortTypes.T010.{u} n E) : yui_aux_type% "∀ (X : Type u) [MetricSpace X] (A : Set X) (s : ℝ) (hs : 0 ≤ s), ENNReal.ofReal s < dimH A → H s A = ⊤" := by
  intro X instX A s hs hc
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  let d : ℝ≥0 := ⟨s, hs⟩
  have hcoe : (d : ℝ≥0∞) = ENNReal.ofReal s := ENNReal.coe_nnreal_eq d
  have hd : (d : ℝ≥0∞) < dimH A := by rw [hcoe]; exact hc
  have hm := hausdorffMeasure_of_lt_dimH (s := A) hd
  change hausdorffMeasure s A = ⊤
  exact hm

theorem yui_aux_0002 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T006 : @YuiPortTypes.T006.{u} n E) (h_T010 : @YuiPortTypes.T010.{u} n E) : yui_aux_type% "∀ (X : Type u) [MetricSpace X] (A : Set X) (s : ℝ), 0 ≤ s → H s A = ⊤ → ENNReal.ofReal s ≤ dimH A" := by
  intro X instX A s hs hm
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  let d : ℝ≥0 := ⟨s, hs⟩
  have hcoe : (d : ℝ≥0∞) = ENNReal.ofReal s := ENNReal.coe_nnreal_eq d
  have hm' : hausdorffMeasure (d : ℝ) A = ⊤ := hm
  have hd : (d : ℝ≥0∞) ≤ dimH A := le_dimH_of_hausdorffMeasure_eq_top hm'
  rw [hcoe] at hd
  exact hd

theorem yui_aux_0003 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T006 : @YuiPortTypes.T006.{u} n E) (h_T010 : @YuiPortTypes.T010.{u} n E) : yui_aux_type% "∀ a : ℝ≥0∞, a ≠ ⊤ → (a + 1).toReal = a.toReal + 1" := by
  intro a ha
  have hone : (1 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hadd : (a + 1).toReal = a.toReal + (1 : ℝ≥0∞).toReal :=
    ENNReal.toReal_add (a := a) (b := 1) ha hone
  simpa only [ENNReal.toReal_one] using hadd

end Local_T011
open Local_T011 in
theorem T011 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T006 : @YuiPortTypes.T006.{u} n E) (h_T010 : @YuiPortTypes.T010.{u} n E) :
    ∀ (X : Type u) [MetricSpace X] (A : Set X), A.Nonempty → dimH A ≠ ⊤ →
  dimH (A ×ˢ YuiBasis.unitInterval) = dimH A + 1 ∧ dimH (A ×ˢ YuiBasis.unitInterval) ≠ ⊤ := by
  intro X instX A hA hfinite
  obtain ⟨hGfinite, hupper, hone⟩ := h_T010 X A hA hfinite
  let D : ℝ := (dimH A).toReal
  let T : ℝ := (dimH (A ×ˢ YuiBasis.unitInterval)).toReal
  have hDnonneg : 0 ≤ D := ENNReal.toReal_nonneg
  have hTone : 1 ≤ T := by
    have h := ENNReal.toReal_mono hGfinite hone
    simpa only [ENNReal.toReal_one] using h
  have hupperR : T ≤ D + 1 := by
    have hsum : dimH A + 1 ≠ ⊤ := by simp [hfinite]
    have h := ENNReal.toReal_mono hsum hupper
    rw [@yui_aux_0003 n E h_T006 h_T010 (dimH A) hfinite] at h
    exact h
  have hbelow : ∀ s : ℝ, 0 < s → s < D → s + 1 ≤ T := by
    intro s hs hsD
    have hc : ENNReal.ofReal s < dimH A :=
      (ENNReal.ofReal_lt_iff_lt_toReal hs.le hfinite).2 hsD
    have hmA : H s A = ⊤ :=
      @yui_aux_0001 n E h_T006 h_T010 X instX A s hs.le hc
    have hmG : H (s + 1) (A ×ˢ YuiBasis.unitInterval) = ⊤ := by
      apply top_unique
      rw [← hmA]
      exact (h_T006 X A s hs).2
    have hd : ENNReal.ofReal (s + 1) ≤ dimH (A ×ˢ YuiBasis.unitInterval) :=
      @yui_aux_0002 n E h_T006 h_T010 (X × ℝ) inferInstance
        (A ×ˢ YuiBasis.unitInterval) (s + 1) (by linarith) hmG
    exact (ENNReal.ofReal_le_iff_le_toReal hGfinite).1 hd
  have hlowerR : D + 1 ≤ T := by
    rcases eq_or_lt_of_le hDnonneg with hzero | hpos
    · linarith
    · by_contra hnot
      have hlt : T < D + 1 := lt_of_not_ge hnot
      let smid : ℝ := (max 0 (T - 1) + D) / 2
      have hmD : max 0 (T - 1) < D := max_lt hpos (by linarith)
      have hms : max 0 (T - 1) < smid := by dsimp [smid]; linarith
      have hsD : smid < D := by dsimp [smid]; linarith
      have hspos : 0 < smid := lt_of_le_of_lt (le_max_left _ _) hms
      have hTs : T < smid + 1 := by
        have hm := le_max_right (0 : ℝ) (T - 1)
        linarith
      have hcontra := hbelow smid hspos hsD
      linarith
  have heqR : T = D + 1 := le_antisymm hupperR hlowerR
  have hconvD : ENNReal.ofReal D = dimH A := ENNReal.ofReal_toReal hfinite
  have hconvT : ENNReal.ofReal T = dimH (A ×ˢ YuiBasis.unitInterval) :=
    ENNReal.ofReal_toReal hGfinite
  constructor
  · calc
      dimH (A ×ˢ YuiBasis.unitInterval) = ENNReal.ofReal T := hconvT.symm
      _ = ENNReal.ofReal (D + 1) := congrArg ENNReal.ofReal heqR
      _ = ENNReal.ofReal D + ENNReal.ofReal 1 := ENNReal.ofReal_add hDnonneg (by norm_num)
      _ = dimH A + 1 := by rw [hconvD]; norm_num
  · exact hGfinite

end
namespace Local_T012
theorem yui_aux_0001 (n : ℕ) (E : Set (YuiBasis.Ambient n)) : yui_aux_type% "Function.Bijective (appendCoord n)" := by
  let g : Ambient (n + 1) → Ambient n × ℝ :=
    fun y => (WithLp.toLp 2 (fun i : Fin n => y i.castSucc), y (Fin.last n))
  have hleft : ∀ p : Ambient n × ℝ, g (appendCoord n p) = p := by
    intro p
    apply Prod.ext
    · apply PiLp.ext
      intro i
      simp [g, appendCoord]
    · simp [g, appendCoord]
  have hright : ∀ y : Ambient (n + 1), appendCoord n (g y) = y := by
    intro y
    apply PiLp.ext
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [g, appendCoord]
    · simp [g, appendCoord]
  constructor
  · intro p q h
    calc
      p = g (appendCoord n p) := (hleft p).symm
      _ = g (appendCoord n q) := congrArg g h
      _ = q := hleft q
  · intro y
    exact ⟨g y, hright y⟩

theorem yui_aux_0002 (n : ℕ) (E : Set (YuiBasis.Ambient n)) : yui_aux_type% "∀ p q : Ambient n × ℝ, dist (appendCoord n p) (appendCoord n q) ^ 2 = dist p.1 q.1 ^ 2 + dist p.2 q.2 ^ 2" := by
  intro p q
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_castSucc, EuclideanSpace.dist_sq_eq]
  simp [appendCoord]

theorem yui_aux_0003 (n : ℕ) (E : Set (YuiBasis.Ambient n)) : yui_aux_type% "∀ p q : Ambient n × ℝ, dist p q ≤ dist (appendCoord n p) (appendCoord n q) ∧ dist (appendCoord n p) (appendCoord n q) ≤ Real.sqrt 2 * dist p q" := by
  intro p q
  have hid := @yui_aux_0002 n E p q
  have ha : 0 ≤ dist p.1 q.1 := dist_nonneg
  have hb : 0 ≤ dist p.2 q.2 := dist_nonneg
  have hd : 0 ≤ dist (appendCoord n p) (appendCoord n q) := dist_nonneg
  have hm : 0 ≤ dist p q := dist_nonneg
  have ham : dist p.1 q.1 ≤ dist p q := by
    rw [Prod.dist_eq]
    exact le_max_left _ _
  have hbm : dist p.2 q.2 ≤ dist p q := by
    rw [Prod.dist_eq]
    exact le_max_right _ _
  have ha2 : dist p.1 q.1 ^ 2 ≤ dist p q ^ 2 :=
    (sq_le_sq₀ ha hm).2 ham
  have hb2 : dist p.2 q.2 ^ 2 ≤ dist p q ^ 2 :=
    (sq_le_sq₀ hb hm).2 hbm
  constructor
  · rw [Prod.dist_eq]
    apply max_le
    · apply (sq_le_sq₀ ha hd).1
      nlinarith [sq_nonneg (dist p.2 q.2)]
    · apply (sq_le_sq₀ hb hd).1
      nlinarith [sq_nonneg (dist p.1 q.1)]
  · have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    apply (sq_le_sq₀ hd (mul_nonneg hs hm)).1
    calc
      dist (appendCoord n p) (appendCoord n q) ^ 2
          = dist p.1 q.1 ^ 2 + dist p.2 q.2 ^ 2 := hid
      _ ≤ 2 * dist p q ^ 2 := by linarith
      _ = (Real.sqrt 2 * dist p q) ^ 2 := by rw [mul_pow, hs2]

end Local_T012
open Local_T012 in
theorem T012 (n : ℕ) (E : Set (YuiBasis.Ambient n))  :
    Function.Bijective (appendCoord n) ∧
  (∀ p p' : Ambient n × ℝ,
    dist p p' ≤ dist (appendCoord n p) (appendCoord n p') ∧
    dist (appendCoord n p) (appendCoord n p') ≤ Real.sqrt 2 * dist p p') ∧
  LipschitzWith (Real.toNNReal (Real.sqrt 2)) (appendCoord n) ∧
  AntilipschitzWith 1 (appendCoord n) := by
  have hbounds := @yui_aux_0003 n E
  have hcoe : (Real.toNNReal (Real.sqrt 2) : ℝ) = Real.sqrt 2 :=
    Real.coe_toNNReal (Real.sqrt 2) (Real.sqrt_nonneg 2)
  refine ⟨@yui_aux_0001 n E, hbounds, ?_, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro p q
    rw [hcoe]
    exact (hbounds p q).2
  · apply AntilipschitzWith.of_le_mul_dist
    intro p q
    simpa only [NNReal.coe_one, one_mul] using (hbounds p q).1

theorem T013 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_T012 : Function.Bijective (appendCoord n) ∧
  (∀ p p' : Ambient n × ℝ,
    dist p p' ≤ dist (appendCoord n p) (appendCoord n p') ∧
    dist (appendCoord n p) (appendCoord n p') ≤ Real.sqrt 2 * dist p p') ∧
  LipschitzWith (Real.toNNReal (Real.sqrt 2)) (appendCoord n) ∧
  AntilipschitzWith 1 (appendCoord n)) :
    Function.Bijective (appendCoord n) ∧
  (∀ p p' : Ambient n × ℝ,
    dist p p' ≤ dist (appendCoord n p) (appendCoord n p') ∧
    dist (appendCoord n p) (appendCoord n p') ≤ Real.sqrt 2 * dist p p') ∧
  LipschitzWith (Real.toNNReal (Real.sqrt 2)) (appendCoord n) ∧
  AntilipschitzWith 1 (appendCoord n) ∧
  ∀ S : Set (Ambient n × ℝ), dimH (appendCoord n '' S) = dimH S := by
  rcases h_T012 with ⟨hbij, hdist, hlip, hanti⟩
  refine ⟨hbij, hdist, hlip, hanti, ?_⟩
  intro S
  exact le_antisymm (hlip.dimH_image_le S) (hanti.le_dimH_image S)

theorem T014 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_H001 : E.Nonempty) (h_T001 : (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞)) ∧ dimH E ≠ ⊤) (h_T011 : @YuiPortTypes.T011.{0} n E) (h_T013 : @YuiPortTypes.T013 n E) :
    dimH (appendCoord n '' (E ×ˢ YuiBasis.unitInterval)) = dimH E + 1 ∧
  dimH E ≠ ⊤ ∧ dimH (appendCoord n '' (E ×ˢ YuiBasis.unitInterval)) ≠ ⊤ := by
  have hprod : dimH (E ×ˢ YuiBasis.unitInterval) = dimH E + 1 ∧
      dimH (E ×ˢ YuiBasis.unitInterval) ≠ ⊤ :=
    h_T011 (YuiBasis.Ambient n) E h_H001 h_T001.2
  have himage : dimH (appendCoord n '' (E ×ˢ YuiBasis.unitInterval)) =
      dimH (E ×ˢ YuiBasis.unitInterval) :=
    h_T013.2.2.2.2 (E ×ˢ YuiBasis.unitInterval)
  refine ⟨himage.trans hprod.1, h_T001.2, ?_⟩
  rw [himage]
  exact hprod.2

private theorem __connected_T001 (n : ℕ) (E : Set (YuiBasis.Ambient n))  :
    (0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞)) ∧ dimH E ≠ ⊤ := by
  exact @T001 n E

private theorem __connected_T003.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n))  :
    ∀ (X : Type u) [MetricSpace X] (A : Set X) (s : ℝ), 0 < s →
  (∀ δ : ℝ, 0 < δ →
    C s δ A = ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)
      (_ : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ), ∑' i, Metric.ediam (U i) ^ s) ∧
  (∀ δ₁ δ₂ : ℝ, 0 < δ₁ → δ₁ ≤ δ₂ → C s δ₂ A ≤ C s δ₁ A) ∧
  H s A = ⨆ (δ : ℝ) (_ : 0 < δ), C s δ A := by
  exact @T003 n E

private theorem __connected_T004.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n))  :
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
  exact @T004 n E (@__connected_T003.{u} n E)

private theorem __connected_T005.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n))  :
    ∀ (X : Type u) [MetricSpace X] (V : ℕ → Set (X × ℝ)) (δ : ℝ), 0 < δ →
  (∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ) →
  ∃ J : ℕ → Set ℝ,
    (∀ i, Prod.snd '' (V i) ⊆ J i) ∧
    (∀ i, IsClosed (J i)) ∧
    (∀ i, volume (J i) ≤ Metric.ediam (V i)) := by
  exact @T005 n E

private theorem __connected_T006.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n))  :
    ∀ (X : Type u) [MetricSpace X] (A : Set X) (s : ℝ), 0 < s →
  (∀ δ : ℝ, 0 < δ → C s δ A ≤ C (s + 1) δ (A ×ˢ YuiBasis.unitInterval)) ∧
  H s A ≤ H (s + 1) (A ×ˢ YuiBasis.unitInterval) := by
  exact @T006 n E (@__connected_T004.{u} n E) (@__connected_T005.{u} n E)

private theorem __connected_T007.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n))  :
    ∀ (X : Type u) [MetricSpace X] (A : Set X) (q : ℝ), 0 < q → H q A = 0 →
  ∀ δ ε : ℝ, 0 < δ → 0 < ε →
    ∃ V : ℕ → Set (X × ℝ), (A ×ˢ YuiBasis.unitInterval ⊆ ⋃ i, V i) ∧
      (∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ) ∧
      (∑' i, Metric.ediam (V i) ^ (q + 1)) < ENNReal.ofReal (2 * ε) := by
  exact @T007 n E (@__connected_T004.{u} n E)

private theorem __connected_T008.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n))  :
    ∀ (X : Type u) [MetricSpace X] (A : Set X) (q : ℝ), 0 < q → H q A = 0 →
  H (q + 1) (A ×ˢ YuiBasis.unitInterval) = 0 ∧
  (∀ δ ε : ℝ, 0 < δ → 0 < ε →
    ∃ V : ℕ → Set (X × ℝ), (A ×ˢ YuiBasis.unitInterval ⊆ ⋃ i, V i) ∧
      (∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ) ∧
      (∑' i, Metric.ediam (V i) ^ (q + 1)) < ENNReal.ofReal (2 * ε)) := by
  exact @T008 n E (@__connected_T004.{u} n E) (@__connected_T007.{u} n E)

private theorem __connected_T002 (n : ℕ) (E : Set (YuiBasis.Ambient n))  :
    dimH YuiBasis.unitInterval = 1 := by
  exact @T002 n E

private theorem __connected_T009.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n))  :
    ∀ (X : Type u) [MetricSpace X] (A : Set X), A.Nonempty → 1 ≤ dimH (A ×ˢ YuiBasis.unitInterval) := by
  exact @T009 n E (@__connected_T002 n E)

private theorem __connected_T010.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n))  :
    ∀ (X : Type u) [MetricSpace X] (A : Set X), A.Nonempty → dimH A ≠ ⊤ →
  dimH (A ×ˢ YuiBasis.unitInterval) ≠ ⊤ ∧
  dimH (A ×ˢ YuiBasis.unitInterval) ≤ dimH A + 1 ∧
  1 ≤ dimH (A ×ˢ YuiBasis.unitInterval) := by
  exact @T010 n E (@__connected_T008.{u} n E) (@__connected_T009.{u} n E)

private theorem __connected_T011.{u} (n : ℕ) (E : Set (YuiBasis.Ambient n))  :
    ∀ (X : Type u) [MetricSpace X] (A : Set X), A.Nonempty → dimH A ≠ ⊤ →
  dimH (A ×ˢ YuiBasis.unitInterval) = dimH A + 1 ∧ dimH (A ×ˢ YuiBasis.unitInterval) ≠ ⊤ := by
  exact @T011 n E (@__connected_T006.{u} n E) (@__connected_T010.{u} n E)

private theorem __connected_T012 (n : ℕ) (E : Set (YuiBasis.Ambient n))  :
    Function.Bijective (appendCoord n) ∧
  (∀ p p' : Ambient n × ℝ,
    dist p p' ≤ dist (appendCoord n p) (appendCoord n p') ∧
    dist (appendCoord n p) (appendCoord n p') ≤ Real.sqrt 2 * dist p p') ∧
  LipschitzWith (Real.toNNReal (Real.sqrt 2)) (appendCoord n) ∧
  AntilipschitzWith 1 (appendCoord n) := by
  exact @T012 n E

private theorem __connected_T013 (n : ℕ) (E : Set (YuiBasis.Ambient n))  :
    Function.Bijective (appendCoord n) ∧
  (∀ p p' : Ambient n × ℝ,
    dist p p' ≤ dist (appendCoord n p) (appendCoord n p') ∧
    dist (appendCoord n p) (appendCoord n p') ≤ Real.sqrt 2 * dist p p') ∧
  LipschitzWith (Real.toNNReal (Real.sqrt 2)) (appendCoord n) ∧
  AntilipschitzWith 1 (appendCoord n) ∧
  ∀ S : Set (Ambient n × ℝ), dimH (appendCoord n '' S) = dimH S := by
  exact @T013 n E (@__connected_T012 n E)

private theorem __connected_T014 (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_H001 : E.Nonempty) :
    dimH (appendCoord n '' (E ×ˢ YuiBasis.unitInterval)) = dimH E + 1 ∧
  dimH E ≠ ⊤ ∧ dimH (appendCoord n '' (E ×ˢ YuiBasis.unitInterval)) ≠ ⊤ := by
  exact @T014 n E h_H001 (@__connected_T001 n E) (@__connected_T011.{0} n E) (@__connected_T013 n E)

theorem P (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_H001 : E.Nonempty) (h_H002 : IsCompact E) : dimH (appendCoord n '' (E ×ˢ YuiBasis.unitInterval)) = dimH E + 1 ∧
  dimH E ≠ ⊤ ∧ dimH (appendCoord n '' (E ×ˢ YuiBasis.unitInterval)) ≠ ⊤ := by
  exact @__connected_T014 n E h_H001

#check @P
#print axioms P

end Translation

namespace AuditBExport
set_option autoImplicit false
set_option Elab.async false in
theorem P (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_H001 : E.Nonempty) (h_H002 : IsCompact E) : dimH (appendCoord n '' (E ×ˢ YuiBasis.unitInterval)) = dimH E + 1 ∧
  dimH E ≠ ⊤ ∧ dimH (appendCoord n '' (E ×ˢ YuiBasis.unitInterval)) ≠ ⊤ := by
  exact @Translation.P n E h_H001 h_H002

#check @P
#print axioms P
end AuditBExport


namespace YuiBasis
set_option autoImplicit false
set_option Elab.async false in
theorem B001 : ∀ (X : Type*) [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (s : ℝ) (A : Set X),
  hausdorffMeasure s A = ⨆ (δ : ℝ≥0∞) (_ : 0 < δ), YuiBasis.Content s δ A := by
  intro X _ _ _ s A
  exact hausdorffMeasure_apply s A
set_option Elab.async false in
theorem B002 : ∀ (X : Type*) [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (A : Set X) (d : ℝ≥0),
  ((d : ℝ≥0∞) < dimH A → hausdorffMeasure (d : ℝ) A = ⊤) ∧
  (dimH A < (d : ℝ≥0∞) → hausdorffMeasure (d : ℝ) A = 0) ∧
  (hausdorffMeasure (d : ℝ) A ≠ ⊤ → dimH A ≤ (d : ℝ≥0∞)) ∧
  (hausdorffMeasure (d : ℝ) A = ⊤ → (d : ℝ≥0∞) ≤ dimH A) := by
  intro X _ _ _ A d
  exact ⟨hausdorffMeasure_of_lt_dimH, hausdorffMeasure_of_dimH_lt,
    dimH_le_of_hausdorffMeasure_ne_top, le_dimH_of_hausdorffMeasure_eq_top⟩
set_option Elab.async false in
theorem B003 : ∀ (X Y : Type*) [EMetricSpace X] [EMetricSpace Y] (K L : ℝ≥0) (f : X → Y)
  (hf : LipschitzWith K f) (hg : AntilipschitzWith L f) (A : Set X),
  (dimH (f '' A) ≤ dimH A ∧ dimH A ≤ dimH (f '' A)) ∧
  (∀ B : Set X, A ⊆ B → dimH A ≤ dimH B) := by
  intro X Y _ _ K L f hf hg A
  exact ⟨⟨hf.dimH_image_le A, hg.le_dimH_image A⟩, fun B h => dimH_mono h⟩
set_option Elab.async false in
theorem B004 : ∀ (n : ℕ) (A : Set (YuiBasis.Ambient n)), dimH A ≤ (n : ℝ≥0∞) ∧ dimH A ≠ ⊤ := by
  intro n A
  constructor
  · calc
      dimH A ≤ dimH (Set.univ : Set (YuiBasis.Ambient n)) := dimH_mono (Set.subset_univ A)
      _ = (n : ℝ≥0∞) := by rw [Real.dimH_univ_eq_finrank]; simp [YuiBasis.Ambient]
  · exact Real.dimH_ne_top A
set_option Elab.async false in
theorem B005 : dimH (Set.Icc (0 : ℝ) 1) = 1 := by
  simpa only [segment_eq_Icc (by norm_num : (0 : ℝ) ≤ 1)] using
    (Real.dimH_segment (by norm_num : (0 : ℝ) ≠ 1))
set_option Elab.async false in
theorem B006 : ∀ (X : Type*) [MeasurableSpace X] (μ : Measure X) (f : ℕ → X → ℝ≥0∞),
  (∀ i, AEMeasurable (f i) μ) →
  (∫⁻ x, ∑' i, f i x ∂μ) = ∑' i, ∫⁻ x, f i x ∂μ := by
  intro X _ μ f hf
  exact lintegral_tsum hf
set_option Elab.async false in
theorem B007 : ∀ (X : Type*) [MeasurableSpace X] (μ : Measure X) (S : Set X),
  MeasurableSet S → ∀ c : ℝ≥0∞,
  (∫⁻ x, S.indicator (fun _ => c) x ∂μ) = c * μ S := by
  intro X _ μ S hS c
  exact lintegral_indicator_const hS c
set_option Elab.async false in
theorem B008 : ∀ (X : Type*) [MeasurableSpace X] (μ : Measure X),
  (∀ f g : X → ℝ≥0∞, (∀ x, f x ≤ g x) →
    (∫⁻ x, f x ∂μ) ≤ ∫⁻ x, g x ∂μ) ∧
  (∀ c : ℝ≥0∞, (∫⁻ _x : X, c ∂μ) = c * μ Set.univ) := by
  intro X _ μ
  exact ⟨fun f g h => lintegral_mono h, fun c => lintegral_const c⟩
set_option Elab.async false in
theorem B009 : (∀ B : Set ℝ, Bornology.IsBounded B →
  B ⊆ Set.Icc (sInf B) (sSup B) ∧
  volume (Set.Icc (sInf B) (sSup B)) = Metric.ediam B) ∧
  (∀ a b : ℝ, volume (Set.Icc a b) = ENNReal.ofReal (b - a)) ∧
  volume (Set.Icc (0 : ℝ) 1) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro B hB
    exact ⟨hB.subset_Icc_sInf_sSup, Real.volume_Icc.trans (Real.ediam_eq hB).symm⟩
  · intro a b
    exact Real.volume_Icc
  · simp
set_option Elab.async false in
theorem B010 : ∀ q : ℝ, 0 ≤ q → Continuous (fun x : ℝ => x ^ q) := by
  intro q hq
  exact Real.continuous_rpow_const hq
set_option Elab.async false in
theorem B011 : ∀ (X Y : Type*) [EMetricSpace X] [EMetricSpace Y] (K : ℝ≥0) (f : X → Y),
  LipschitzWith K f → ∀ A : Set X,
  Metric.ediam (f '' A) ≤ (K : ℝ≥0∞) * Metric.ediam A := by
  intro X Y _ _ K f hf A
  exact hf.ediam_image_le A

end YuiBasis

namespace YuiClosed
set_option autoImplicit false
/- Instantiate only universes that disappear when checked E proofs replace
   premises. Public levels are inferred from the actual arguments/target.
   This elaborator builds an ordinary application, checked by Lean's kernel;
   it adds no theorem, axiom or proof dependency. -/
open Lean Elab Term in
elab "yui_basis_declared_levels%" : term => do
  return toExpr (← getLevelNames)

-- Capture only the header's explicitly declared levels, before P introduces
-- auto-generated Type* names. Those names can shift after E is removed.
private def yuiBasisDeclaredLevels : List Lean.Name := yui_basis_declared_levels%

open Lean Meta Elab Term in
elab "yui_basis_export%" "(" args:term,* ")" : term <= expectedType => do
  let info ← getConstInfo `AuditBExport.P
  let used ← forallTelescope info.type fun xs body => do
    let mut retained := #[]
    let omitted : Array String := #[]
    for x in xs do
      let decl ← getFVarLocalDecl x
      if !omitted.contains decl.userName.toString then
        retained := retained.push x
    return (collectLevelParams {} (← mkForallFVars retained body)).params
  let levels ← info.levelParams.mapM fun name =>
    if !used.contains name then pure Level.zero
    -- A named public level retains its name, including max/imax expressions
    -- that cannot be uniquely reconstructed from fresh metavariables. Type*
    -- introduces fresh local levels; infer those from the actual arguments.
    else if yuiBasisDeclaredLevels.contains name then pure (Level.param name)
    else mkFreshLevelMVar
  elabAppArgs (mkConst `AuditBExport.P levels) #[] (args.getElems.map Arg.stx)
    expectedType (explicit := true) (ellipsis := false)

set_option Elab.async false in
theorem P (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_H001 : E.Nonempty) (h_H002 : IsCompact E) : dimH (appendCoord n '' (E ×ˢ YuiBasis.unitInterval)) = dimH E + 1 ∧
  dimH E ≠ ⊤ ∧ dimH (appendCoord n '' (E ×ˢ YuiBasis.unitInterval)) ≠ ⊤ := by
  exact yui_basis_export%(n, E, h_H001, h_H002)

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
    let checks : Array (String × String × String × Array String) := #[("P", "decl:YuiClosed.P", "∀ (n : ℕ) (E : Set (YuiBasis.Ambient n)) (h_H001 : E.Nonempty) (h_H002 : IsCompact E), dimH (appendCoord n '' (E ×ˢ YuiBasis.unitInterval)) = dimH E + 1 ∧\n  dimH E ≠ ⊤ ∧ dimH (appendCoord n '' (E ×ˢ YuiBasis.unitInterval)) ≠ ⊤", #["YuiClosed", "P"])]
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
