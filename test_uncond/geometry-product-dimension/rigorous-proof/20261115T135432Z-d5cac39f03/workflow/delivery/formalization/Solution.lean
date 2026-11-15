import Mathlib
open Set MeasureTheory
open scoped ENNReal NNReal
noncomputable section

abbrev YuiRn (n : ℕ) := EuclideanSpace ℝ (Fin n)

def YuiContent {X : Type*} [EMetricSpace X] (a : ℝ) (r : ℝ≥0∞) (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i) (_ : ∀ i, Metric.ediam (U i) ≤ r),
    ∑' i, (Metric.ediam (U i)) ^ a

def YuiJoinEquiv (n : ℕ) : (YuiRn n × ℝ) ≃L[ℝ] YuiRn (n + 1) :=
  (((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).prodCongr
      (ContinuousLinearEquiv.refl ℝ ℝ)).trans
    (ContinuousLinearEquiv.prodComm ℝ (Fin n → ℝ) ℝ)).trans
    ((Fin.consEquivL ℝ (fun _ : Fin (n + 1) => ℝ)).trans
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 1) => ℝ)).symm)

def YuiI : Set ℝ := Set.Icc 0 1

def YuiFmax (n : ℕ) (A : Set (YuiRn n)) : Set (YuiRn n × ℝ) :=
  A ×ˢ YuiI

def YuiFeuc (n : ℕ) (A : Set (YuiRn n)) : Set (YuiRn (n + 1)) :=
  YuiJoinEquiv n '' YuiFmax n A

def YuiLast (n : ℕ) (z : YuiRn (n + 1)) : YuiRn (n + 1) :=
  WithLp.toLp 2 (fun j => z (finRotate (n + 1) j))

def YuiFeucLast (n : ℕ) (A : Set (YuiRn n)) : Set (YuiRn (n + 1)) :=
  YuiLast n '' YuiFeuc n A
namespace YuiPortTypes
abbrev E003 : Prop :=
  ∀ {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (A : Set X) (d : ℝ≥0),
 (dimH A < (d : ℝ≥0∞) → MeasureTheory.Measure.hausdorffMeasure (d : ℝ) A = 0) ∧
 ((d : ℝ≥0∞) < dimH A → MeasureTheory.Measure.hausdorffMeasure (d : ℝ) A = ⊤) ∧
 (MeasureTheory.Measure.hausdorffMeasure (d : ℝ) A ≠ ⊤ → dimH A ≤ (d : ℝ≥0∞)) ∧
 (MeasureTheory.Measure.hausdorffMeasure (d : ℝ) A = ⊤ → (d : ℝ≥0∞) ≤ dimH A)
abbrev E008 : Prop :=
  ∀ {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
 [NormedAddCommGroup W] [NormedSpace ℝ W] (e : V ≃L[ℝ] W) (S : Set V),
 dimH (e '' S) = dimH S
abbrev M006 : Prop :=
  ∀ {X : Type*} [EMetricSpace X] {s t : Set X}, s ⊆ t → dimH s ≤ dimH t
abbrev M007 : Prop :=
  ∀ {X Y : Type*} [EMetricSpace X] [EMetricSpace Y] {f : X → Y},
 Isometry f → ∀ s : Set X, dimH (f '' s) = dimH s
end YuiPortTypes

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace Translation
set_option autoImplicit false

theorem T001 (n : ℕ) (E : Set (YuiRn n)) (h_H001 : E.Nonempty ∧ IsCompact E) (h_E004 : ∀ (n : ℕ) (E : Set (YuiRn n)), dimH E < ⊤) :
    ∃ D : ℝ, 0 ≤ D ∧ dimH E = ENNReal.ofReal D := by
  refine ⟨(dimH E).toReal, ENNReal.toReal_nonneg, ?_⟩
  exact (ENNReal.ofReal_toReal (ne_of_lt (h_E004 n E))).symm

namespace Local_T002
theorem yui_aux_0001 (n : ℕ) (E : Set (YuiRn n)) (h_H001 : E.Nonempty ∧ IsCompact E) (h_E003 : @YuiPortTypes.E003.{0}) (h_E010 : ∀ {X : Type} [MetricSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
 (A : Set X) (q : ℝ), 0 < q → MeasureTheory.Measure.hausdorffMeasure q A = 0 →
 MeasureTheory.Measure.hausdorffMeasure (q + 1) (A ×ˢ Set.Icc (0 : ℝ) 1) = 0) : yui_aux_type% "∀ d : NNReal, (d : ENNReal) = ENNReal.ofReal (d : ℝ)" := by
  intro d
  exact ENNReal.coe_nnreal_eq d

theorem yui_aux_0002 (n : ℕ) (E : Set (YuiRn n)) (h_H001 : E.Nonempty ∧ IsCompact E) (h_E003 : @YuiPortTypes.E003.{0}) (h_E010 : ∀ {X : Type} [MetricSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
 (A : Set X) (q : ℝ), 0 < q → MeasureTheory.Measure.hausdorffMeasure q A = 0 →
 MeasureTheory.Measure.hausdorffMeasure (q + 1) (A ×ˢ Set.Icc (0 : ℝ) 1) = 0) : yui_aux_type% "∀ (d : NNReal) (a : ℝ), (d : ℝ) = a → ∀ A : Set (YuiRn n × ℝ), MeasureTheory.Measure.hausdorffMeasure a A = 0 → MeasureTheory.Measure.hausdorffMeasure (d : ℝ) A ≠ ⊤" := by
  intro d a heq A hz
  rw [heq, hz]
  exact ENNReal.zero_ne_top

end Local_T002
open Local_T002 in
theorem T002 (n : ℕ) (E : Set (YuiRn n)) (h_H001 : E.Nonempty ∧ IsCompact E) (h_E003 : @YuiPortTypes.E003.{0}) (h_E010 : ∀ {X : Type} [MetricSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
 (A : Set X) (q : ℝ), 0 < q → MeasureTheory.Measure.hausdorffMeasure q A = 0 →
 MeasureTheory.Measure.hausdorffMeasure (q + 1) (A ×ˢ Set.Icc (0 : ℝ) 1) = 0) :
    ∀ D : ℝ, 0 ≤ D → dimH E = ENNReal.ofReal D → ∀ q : ℝ, D < q → dimH (YuiFmax n E) ≤ ENNReal.ofReal (q + 1) := by
  intro D hD hdim q hDq
  have hq : 0 < q := lt_of_le_of_lt hD hDq
  have hq1 : 0 < q + 1 := add_pos hq zero_lt_one
  let d : NNReal := ⟨q, hq.le⟩
  let d1 : NNReal := ⟨q + 1, hq1.le⟩
  have hd : (d : ENNReal) = ENNReal.ofReal q :=
    @yui_aux_0001 n E h_H001 h_E003 h_E010 d
  have hd1 : (d1 : ENNReal) = ENNReal.ofReal (q + 1) :=
    @yui_aux_0001 n E h_H001 h_E003 h_E010 d1
  have hlt : dimH E < (d : ENNReal) := by
    rw [hd, hdim]
    exact (ENNReal.ofReal_lt_ofReal_iff hq).2 hDq
  have hz : MeasureTheory.Measure.hausdorffMeasure q E = 0 :=
    (h_E003 E d).1 hlt
  have hp : MeasureTheory.Measure.hausdorffMeasure (q + 1) (YuiFmax n E) = 0 := by
    exact h_E010 E q hq hz
  have hnot : MeasureTheory.Measure.hausdorffMeasure (d1 : ℝ) (YuiFmax n E) ≠ ⊤ :=
    @yui_aux_0002 n E h_H001 h_E003 h_E010 d1 (q + 1) rfl (YuiFmax n E) hp
  have hb : dimH (YuiFmax n E) ≤ (d1 : ENNReal) :=
    (h_E003 (YuiFmax n E) d1).2.2.1 hnot
  exact hd1 ▸ hb

theorem T003 (n : ℕ) (E : Set (YuiRn n)) (h_H001 : E.Nonempty ∧ IsCompact E) (h_T001 : ∃ D : ℝ, 0 ≤ D ∧ dimH E = ENNReal.ofReal D) (h_T002 : ∀ D : ℝ, 0 ≤ D → dimH E = ENNReal.ofReal D → ∀ q : ℝ, D < q → dimH (YuiFmax n E) ≤ ENNReal.ofReal (q + 1)) :
    dimH (YuiFmax n E) ≤ dimH E + 1 := by
  rcases h_T001 with ⟨D, hD, hdim⟩
  have hfinite : dimH (YuiFmax n E) < ∞ :=
    lt_of_le_of_lt (h_T002 D hD hdim (D + 1) (by linarith)) ENNReal.ofReal_lt_top
  have hne : dimH (YuiFmax n E) ≠ ∞ := ne_of_lt hfinite
  have hupper : dimH (YuiFmax n E) ≤ ENNReal.ofReal (D + 1) := by
    by_contra h
    have hstrict : ENNReal.ofReal (D + 1) < dimH (YuiFmax n E) := lt_of_not_ge h
    have hr : D + 1 < (dimH (YuiFmax n E)).toReal :=
      (ENNReal.ofReal_lt_iff_lt_toReal (by linarith) hne).mp hstrict
    let qstar : ℝ := (D + (dimH (YuiFmax n E)).toReal - 1) / 2
    have hDq : D < qstar := by dsimp [qstar]; linarith
    have hq : qstar + 1 < (dimH (YuiFmax n E)).toReal := by dsimp [qstar]; linarith
    have hqnonneg : 0 ≤ qstar + 1 := by linarith
    have hlt : ENNReal.ofReal (qstar + 1) < dimH (YuiFmax n E) :=
      (ENNReal.ofReal_lt_iff_lt_toReal hqnonneg hne).mpr hq
    exact (not_lt_of_ge (h_T002 D hD hdim qstar hDq)) hlt
  rw [ENNReal.ofReal_add hD (by norm_num), ENNReal.ofReal_one, ← hdim] at hupper
  exact hupper

namespace Local_T004
theorem yui_aux_0001 (n : ℕ) (E : Set (YuiRn n)) (h_H001 : E.Nonempty ∧ IsCompact E) (h_E003 : @YuiPortTypes.E003.{0}) (h_E020 : ∀ {X : Type} [MetricSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
 (A : Set X) (s : ℝ), 0 < s →
 MeasureTheory.Measure.hausdorffMeasure s A ≤
 MeasureTheory.Measure.hausdorffMeasure (s + 1) (A ×ˢ Set.Icc (0 : ℝ) 1)) : yui_aux_type% "∀ (s : Real) (hs : 0 ≤ s), ((NNReal.mk s hs : NNReal) : ENNReal) = ENNReal.ofReal s" := by
  intro s hs
  exact ENNReal.coe_nnreal_eq (NNReal.mk s hs)

end Local_T004
open Local_T004 in
theorem T004 (n : ℕ) (E : Set (YuiRn n)) (h_H001 : E.Nonempty ∧ IsCompact E) (h_E003 : @YuiPortTypes.E003.{0}) (h_E020 : ∀ {X : Type} [MetricSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
 (A : Set X) (s : ℝ), 0 < s →
 MeasureTheory.Measure.hausdorffMeasure s A ≤
 MeasureTheory.Measure.hausdorffMeasure (s + 1) (A ×ˢ Set.Icc (0 : ℝ) 1)) :
    ∀ D : ℝ, 0 ≤ D → dimH E = ENNReal.ofReal D → ∀ s : ℝ, 0 < s → s < D → ENNReal.ofReal (s + 1) ≤ dimH (YuiFmax n E) := by
  intro D hD hdim s hs hsD
  have hDpos : 0 < D := lt_trans hs hsD
  have hsconv : ((NNReal.mk s (le_of_lt hs) : NNReal) : ENNReal) = ENNReal.ofReal s :=
    yui_aux_0001 n E h_H001 h_E003 h_E020 s (le_of_lt hs)
  have hstrict : ((NNReal.mk s (le_of_lt hs) : NNReal) : ENNReal) < dimH E := by
    rw [hsconv, hdim]
    exact (ENNReal.ofReal_lt_ofReal_iff hDpos).2 hsD
  have hinf : MeasureTheory.Measure.hausdorffMeasure s E = ⊤ :=
    (h_E003 E (NNReal.mk s (le_of_lt hs))).2.1 hstrict
  have htransfer : MeasureTheory.Measure.hausdorffMeasure s E ≤
      MeasureTheory.Measure.hausdorffMeasure (s + 1) (YuiFmax n E) := by
    simpa only [YuiFmax, YuiI] using h_E020 E s hs
  have hprodinf : MeasureTheory.Measure.hausdorffMeasure (s + 1) (YuiFmax n E) = ⊤ :=
    top_unique (hinf ▸ htransfer)
  have hs1 : 0 ≤ s + 1 := le_of_lt (add_pos hs zero_lt_one)
  have hbound : ((NNReal.mk (s + 1) hs1 : NNReal) : ENNReal) ≤ dimH (YuiFmax n E) :=
    (h_E003 (YuiFmax n E) (NNReal.mk (s + 1) hs1)).2.2.2 hprodinf
  rw [yui_aux_0001 n E h_H001 h_E003 h_E020 (s + 1) hs1] at hbound
  exact hbound

theorem T005 (n : ℕ) (E : Set (YuiRn n)) (h_H001 : E.Nonempty ∧ IsCompact E) (h_T001 : ∃ D : ℝ, 0 ≤ D ∧ dimH E = ENNReal.ofReal D) (h_T004 : ∀ D : ℝ, 0 ≤ D → dimH E = ENNReal.ofReal D → ∀ s : ℝ, 0 < s → s < D → ENNReal.ofReal (s + 1) ≤ dimH (YuiFmax n E)) :
    0 < dimH E → dimH E + 1 ≤ dimH (YuiFmax n E) := by
  intro hpos
  obtain ⟨D, hD, hdim⟩ := h_T001
  have hDpos : 0 < D := ENNReal.ofReal_pos.mp (hdim ▸ hpos)
  have hsum : ENNReal.ofReal (D + 1) = dimH E + 1 := by
    rw [ENNReal.ofReal_add hD (by norm_num), ← hdim]
    norm_num
  rw [← hsum]
  by_contra hnot
  have hlt : dimH (YuiFmax n E) < ENNReal.ofReal (D + 1) := lt_of_not_ge hnot
  have hfinite : dimH (YuiFmax n E) ≠ ∞ :=
    (lt_trans hlt ENNReal.ofReal_lt_top).ne
  have hrepr : ENNReal.ofReal (dimH (YuiFmax n E)).toReal = dimH (YuiFmax n E) :=
    ENNReal.ofReal_toReal hfinite
  have ht : (dimH (YuiFmax n E)).toReal < D + 1 := by
    apply (ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < D + 1)).mp
    simpa only [hrepr] using hlt
  let sstar : ℝ := (D + max 0 ((dimH (YuiFmax n E)).toReal - 1)) / 2
  have hm : max 0 ((dimH (YuiFmax n E)).toReal - 1) < D :=
    max_lt hDpos (by linarith)
  have hm0 : 0 ≤ max 0 ((dimH (YuiFmax n E)).toReal - 1) := le_max_left _ _
  have hmt : (dimH (YuiFmax n E)).toReal - 1 ≤ max 0 ((dimH (YuiFmax n E)).toReal - 1) := le_max_right _ _
  have hspos : 0 < sstar := by dsimp [sstar]; linarith
  have hsD : sstar < D := by dsimp [sstar]; linarith
  have hts : (dimH (YuiFmax n E)).toReal < sstar + 1 := by
    dsimp [sstar]
    linarith
  have hstrict : dimH (YuiFmax n E) < ENNReal.ofReal (sstar + 1) := by
    rw [← hrepr]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < sstar + 1)).mpr hts
  exact (not_lt_of_ge (h_T004 D hD hdim sstar hspos hsD)) hstrict

theorem T006 (n : ℕ) (E : Set (YuiRn n)) (h_H001 : E.Nonempty ∧ IsCompact E) (h_E005 : dimH (Set.Icc (0 : ℝ) 1) = 1) (h_M006 : @YuiPortTypes.M006.{0}) (h_M007 : @YuiPortTypes.M007.{0, 0}) :
    dimH E = 0 → dimH E + 1 ≤ dimH (YuiFmax n E) := by
  intro hzero
  obtain ⟨xzero, hxzero⟩ := h_H001.1
  let f : ℝ → YuiRn n × ℝ := fun t => (xzero, t)
  let C : Set (YuiRn n × ℝ) := f '' YuiI
  have hf : Isometry f := by
    apply isometry_iff_dist_eq.mpr
    intro t u
    simp [f, Prod.dist_eq]
  have hC : C ⊆ YuiFmax n E := by
    rintro z ⟨t, ht, rfl⟩
    exact ⟨hxzero, ht⟩
  have hdimC : dimH C = 1 := by
    calc
      dimH C = dimH YuiI := h_M007 hf YuiI
      _ = 1 := h_E005
  have hmono : dimH C ≤ dimH (YuiFmax n E) := h_M006 hC
  simpa only [hzero, zero_add, hdimC] using hmono

theorem T007 (n : ℕ) (E : Set (YuiRn n)) (h_T001 : ∃ D : ℝ, 0 ≤ D ∧ dimH E = ENNReal.ofReal D) (h_T003 : dimH (YuiFmax n E) ≤ dimH E + 1) (h_T005 : 0 < dimH E → dimH E + 1 ≤ dimH (YuiFmax n E)) (h_T006 : dimH E = 0 → dimH E + 1 ≤ dimH (YuiFmax n E)) :
    dimH (YuiFmax n E) = dimH E + 1 := by
  rcases h_T001 with ⟨D, hD, hdim⟩
  apply le_antisymm h_T003
  by_cases hzero : dimH E = 0
  · exact h_T006 hzero
  · exact h_T005 (lt_of_le_of_ne bot_le (Ne.symm hzero))

theorem T008 (n : ℕ) (E : Set (YuiRn n))  :
    (∀ (x : YuiRn n) (t : ℝ), YuiJoinEquiv n (x, t) = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) ∧ Isometry (YuiLast n) ∧ (∀ (x : YuiRn n) (t : ℝ), YuiLast n (YuiJoinEquiv n (x, t)) = WithLp.toLp 2 (Fin.snoc (WithLp.ofLp x) t)) := by
  have hjoin : ∀ (x : YuiRn n) (t : ℝ), YuiJoinEquiv n (x, t) = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) := by
    intros x t
    rfl
  refine ⟨hjoin, ?_, ?_⟩
  · change Isometry (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finRotate (n + 1)).symm)
    exact (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finRotate (n + 1)).symm).isometry
  · intro x t
    rw [hjoin]
    unfold YuiLast
    rw [Fin.snoc_eq_cons_rotate]

theorem T009 (n : ℕ) (E : Set (YuiRn n)) (h_H001 : E.Nonempty ∧ IsCompact E) (h_E008 : @YuiPortTypes.E008.{0, 0}) (h_M007 : @YuiPortTypes.M007.{0, 0}) (h_T008 : (∀ (x : YuiRn n) (t : ℝ), YuiJoinEquiv n (x, t) = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) ∧ Isometry (YuiLast n) ∧ (∀ (x : YuiRn n) (t : ℝ), YuiLast n (YuiJoinEquiv n (x, t)) = WithLp.toLp 2 (Fin.snoc (WithLp.ofLp x) t))) :
    ∀ C : Set (YuiRn n), dimH (YuiFeuc n C) = dimH (YuiFmax n C) ∧ Isometry (YuiLast n) ∧ dimH (YuiFeucLast n C) = dimH (YuiFeuc n C) ∧ (∀ (x : YuiRn n) (t : ℝ), YuiLast n (YuiJoinEquiv n (x, t)) = WithLp.toLp 2 (Fin.snoc (WithLp.ofLp x) t)) := by
  intro C
  refine ⟨?_, h_T008.2.1, ?_, h_T008.2.2⟩
  · change dimH (YuiJoinEquiv n '' YuiFmax n C) = dimH (YuiFmax n C)
    exact h_E008 (YuiJoinEquiv n) (YuiFmax n C)
  · change dimH (YuiLast n '' YuiFeuc n C) = dimH (YuiFeuc n C)
    exact h_M007 h_T008.2.1 (YuiFeuc n C)

theorem T010 (n : ℕ) (E : Set (YuiRn n)) (h_H001 : E.Nonempty ∧ IsCompact E) (h_T007 : dimH (YuiFmax n E) = dimH E + 1) (h_T009 : ∀ C : Set (YuiRn n), dimH (YuiFeuc n C) = dimH (YuiFmax n C) ∧ Isometry (YuiLast n) ∧ dimH (YuiFeucLast n C) = dimH (YuiFeuc n C) ∧ (∀ (x : YuiRn n) (t : ℝ), YuiLast n (YuiJoinEquiv n (x, t)) = WithLp.toLp 2 (Fin.snoc (WithLp.ofLp x) t))) :
    dimH (YuiFeucLast n E) = dimH E + 1 := by
  exact (h_T009 E).2.2.1.trans ((h_T009 E).1.trans h_T007)

end Translation

namespace YuiBasis
set_option autoImplicit false
set_option Elab.async false in
theorem B003 : ∀ {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (A : Set X) (d : ℝ≥0),
 (dimH A < (d : ℝ≥0∞) → MeasureTheory.Measure.hausdorffMeasure (d : ℝ) A = 0) ∧
 ((d : ℝ≥0∞) < dimH A → MeasureTheory.Measure.hausdorffMeasure (d : ℝ) A = ⊤) ∧
 (MeasureTheory.Measure.hausdorffMeasure (d : ℝ) A ≠ ⊤ → dimH A ≤ (d : ℝ≥0∞)) ∧
 (MeasureTheory.Measure.hausdorffMeasure (d : ℝ) A = ⊤ → (d : ℝ≥0∞) ≤ dimH A) := by
  intro X _ _ _ A d
  exact ⟨(fun h => hausdorffMeasure_of_dimH_lt (s := A) (d := d) h),
    (fun h => hausdorffMeasure_of_lt_dimH (s := A) (d := d) h),
    (fun h => dimH_le_of_hausdorffMeasure_ne_top (s := A) (d := d) h),
    (fun h => le_dimH_of_hausdorffMeasure_eq_top (s := A) (d := d) h)⟩
set_option Elab.async false in
theorem B006 : ∀ {X : Type*} [EMetricSpace X] {s t : Set X}, s ⊆ t → dimH s ≤ dimH t := by
  exact @dimH_mono
set_option Elab.async false in
theorem B007 : ∀ {X Y : Type*} [EMetricSpace X] [EMetricSpace Y] {f : X → Y},
 Isometry f → ∀ s : Set X, dimH (f '' s) = dimH s := by
  exact @Isometry.dimH_image
set_option Elab.async false in
theorem B008 : ∀ {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
 [NormedAddCommGroup W] [NormedSpace ℝ W] (e : V ≃L[ℝ] W) (S : Set V),
 dimH (e '' S) = dimH S := by
  intro V W _ _ _ _ e S
  exact ContinuousLinearEquiv.dimH_image (𝕜 := ℝ) e S

end YuiBasis

namespace Translation
set_option autoImplicit false
private theorem __connected_T001 (n : ℕ) (E : Set (YuiRn n)) (h_H001 : E.Nonempty ∧ IsCompact E) (h_E004 : ∀ (n : ℕ) (E : Set (YuiRn n)), dimH E < ⊤) :
    ∃ D : ℝ, 0 ≤ D ∧ dimH E = ENNReal.ofReal D := by
  exact @T001 n E h_H001 h_E004

private theorem __connected_T002 (n : ℕ) (E : Set (YuiRn n)) (h_H001 : E.Nonempty ∧ IsCompact E) (h_E010 : ∀ {X : Type} [MetricSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
 (A : Set X) (q : ℝ), 0 < q → MeasureTheory.Measure.hausdorffMeasure q A = 0 →
 MeasureTheory.Measure.hausdorffMeasure (q + 1) (A ×ˢ Set.Icc (0 : ℝ) 1) = 0) :
    ∀ D : ℝ, 0 ≤ D → dimH E = ENNReal.ofReal D → ∀ q : ℝ, D < q → dimH (YuiFmax n E) ≤ ENNReal.ofReal (q + 1) := by
  exact @T002 n E h_H001 (@YuiBasis.B003.{0}) h_E010

private theorem __connected_T003 (n : ℕ) (E : Set (YuiRn n)) (h_H001 : E.Nonempty ∧ IsCompact E) (h_E004 : ∀ (n : ℕ) (E : Set (YuiRn n)), dimH E < ⊤) (h_E010 : ∀ {X : Type} [MetricSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
 (A : Set X) (q : ℝ), 0 < q → MeasureTheory.Measure.hausdorffMeasure q A = 0 →
 MeasureTheory.Measure.hausdorffMeasure (q + 1) (A ×ˢ Set.Icc (0 : ℝ) 1) = 0) :
    dimH (YuiFmax n E) ≤ dimH E + 1 := by
  exact @T003 n E h_H001 (@__connected_T001 n E h_H001 h_E004) (@__connected_T002 n E h_H001 h_E010)

private theorem __connected_T004 (n : ℕ) (E : Set (YuiRn n)) (h_H001 : E.Nonempty ∧ IsCompact E) (h_E020 : ∀ {X : Type} [MetricSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
 (A : Set X) (s : ℝ), 0 < s →
 MeasureTheory.Measure.hausdorffMeasure s A ≤
 MeasureTheory.Measure.hausdorffMeasure (s + 1) (A ×ˢ Set.Icc (0 : ℝ) 1)) :
    ∀ D : ℝ, 0 ≤ D → dimH E = ENNReal.ofReal D → ∀ s : ℝ, 0 < s → s < D → ENNReal.ofReal (s + 1) ≤ dimH (YuiFmax n E) := by
  exact @T004 n E h_H001 (@YuiBasis.B003.{0}) h_E020

private theorem __connected_T005 (n : ℕ) (E : Set (YuiRn n)) (h_H001 : E.Nonempty ∧ IsCompact E) (h_E004 : ∀ (n : ℕ) (E : Set (YuiRn n)), dimH E < ⊤) (h_E020 : ∀ {X : Type} [MetricSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
 (A : Set X) (s : ℝ), 0 < s →
 MeasureTheory.Measure.hausdorffMeasure s A ≤
 MeasureTheory.Measure.hausdorffMeasure (s + 1) (A ×ˢ Set.Icc (0 : ℝ) 1)) :
    0 < dimH E → dimH E + 1 ≤ dimH (YuiFmax n E) := by
  exact @T005 n E h_H001 (@__connected_T001 n E h_H001 h_E004) (@__connected_T004 n E h_H001 h_E020)

private theorem __connected_T006 (n : ℕ) (E : Set (YuiRn n)) (h_H001 : E.Nonempty ∧ IsCompact E) (h_E005 : dimH (Set.Icc (0 : ℝ) 1) = 1) :
    dimH E = 0 → dimH E + 1 ≤ dimH (YuiFmax n E) := by
  exact @T006 n E h_H001 h_E005 (@YuiBasis.B006.{0}) (@YuiBasis.B007.{0, 0})

private theorem __connected_T007 (n : ℕ) (E : Set (YuiRn n)) (h_H001 : E.Nonempty ∧ IsCompact E) (h_E004 : ∀ (n : ℕ) (E : Set (YuiRn n)), dimH E < ⊤) (h_E005 : dimH (Set.Icc (0 : ℝ) 1) = 1) (h_E010 : ∀ {X : Type} [MetricSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
 (A : Set X) (q : ℝ), 0 < q → MeasureTheory.Measure.hausdorffMeasure q A = 0 →
 MeasureTheory.Measure.hausdorffMeasure (q + 1) (A ×ˢ Set.Icc (0 : ℝ) 1) = 0) (h_E020 : ∀ {X : Type} [MetricSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
 (A : Set X) (s : ℝ), 0 < s →
 MeasureTheory.Measure.hausdorffMeasure s A ≤
 MeasureTheory.Measure.hausdorffMeasure (s + 1) (A ×ˢ Set.Icc (0 : ℝ) 1)) :
    dimH (YuiFmax n E) = dimH E + 1 := by
  exact @T007 n E (@__connected_T001 n E h_H001 h_E004) (@__connected_T003 n E h_H001 h_E004 h_E010) (@__connected_T005 n E h_H001 h_E004 h_E020) (@__connected_T006 n E h_H001 h_E005)

private theorem __connected_T008 (n : ℕ) (E : Set (YuiRn n))  :
    (∀ (x : YuiRn n) (t : ℝ), YuiJoinEquiv n (x, t) = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) ∧ Isometry (YuiLast n) ∧ (∀ (x : YuiRn n) (t : ℝ), YuiLast n (YuiJoinEquiv n (x, t)) = WithLp.toLp 2 (Fin.snoc (WithLp.ofLp x) t)) := by
  exact @T008 n E

private theorem __connected_T009 (n : ℕ) (E : Set (YuiRn n)) (h_H001 : E.Nonempty ∧ IsCompact E) :
    ∀ C : Set (YuiRn n), dimH (YuiFeuc n C) = dimH (YuiFmax n C) ∧ Isometry (YuiLast n) ∧ dimH (YuiFeucLast n C) = dimH (YuiFeuc n C) ∧ (∀ (x : YuiRn n) (t : ℝ), YuiLast n (YuiJoinEquiv n (x, t)) = WithLp.toLp 2 (Fin.snoc (WithLp.ofLp x) t)) := by
  exact @T009 n E h_H001 (@YuiBasis.B008.{0, 0}) (@YuiBasis.B007.{0, 0}) (@__connected_T008 n E)

private theorem __connected_T010 (n : ℕ) (E : Set (YuiRn n)) (h_H001 : E.Nonempty ∧ IsCompact E) (h_E004 : ∀ (n : ℕ) (E : Set (YuiRn n)), dimH E < ⊤) (h_E005 : dimH (Set.Icc (0 : ℝ) 1) = 1) (h_E010 : ∀ {X : Type} [MetricSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
 (A : Set X) (q : ℝ), 0 < q → MeasureTheory.Measure.hausdorffMeasure q A = 0 →
 MeasureTheory.Measure.hausdorffMeasure (q + 1) (A ×ˢ Set.Icc (0 : ℝ) 1) = 0) (h_E020 : ∀ {X : Type} [MetricSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
 (A : Set X) (s : ℝ), 0 < s →
 MeasureTheory.Measure.hausdorffMeasure s A ≤
 MeasureTheory.Measure.hausdorffMeasure (s + 1) (A ×ˢ Set.Icc (0 : ℝ) 1)) :
    dimH (YuiFeucLast n E) = dimH E + 1 := by
  exact @T010 n E h_H001 (@__connected_T007 n E h_H001 h_E004 h_E005 h_E010 h_E020) (@__connected_T009 n E h_H001)

theorem P (n : ℕ) (E : Set (YuiRn n)) (h_H001 : E.Nonempty ∧ IsCompact E) (h_E003 : ∀ {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (A : Set X) (d : ℝ≥0),
 (dimH A < (d : ℝ≥0∞) → MeasureTheory.Measure.hausdorffMeasure (d : ℝ) A = 0) ∧
 ((d : ℝ≥0∞) < dimH A → MeasureTheory.Measure.hausdorffMeasure (d : ℝ) A = ⊤) ∧
 (MeasureTheory.Measure.hausdorffMeasure (d : ℝ) A ≠ ⊤ → dimH A ≤ (d : ℝ≥0∞)) ∧
 (MeasureTheory.Measure.hausdorffMeasure (d : ℝ) A = ⊤ → (d : ℝ≥0∞) ≤ dimH A)) (h_E004 : ∀ (n : ℕ) (E : Set (YuiRn n)), dimH E < ⊤) (h_E005 : dimH (Set.Icc (0 : ℝ) 1) = 1) (h_M006 : ∀ {X : Type*} [EMetricSpace X] {s t : Set X}, s ⊆ t → dimH s ≤ dimH t) (h_M007 : ∀ {X Y : Type*} [EMetricSpace X] [EMetricSpace Y] {f : X → Y},
 Isometry f → ∀ s : Set X, dimH (f '' s) = dimH s) (h_E008 : ∀ {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
 [NormedAddCommGroup W] [NormedSpace ℝ W] (e : V ≃L[ℝ] W) (S : Set V),
 dimH (e '' S) = dimH S) (h_E010 : ∀ {X : Type} [MetricSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
 (A : Set X) (q : ℝ), 0 < q → MeasureTheory.Measure.hausdorffMeasure q A = 0 →
 MeasureTheory.Measure.hausdorffMeasure (q + 1) (A ×ˢ Set.Icc (0 : ℝ) 1) = 0) (h_E020 : ∀ {X : Type} [MetricSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
 (A : Set X) (s : ℝ), 0 < s →
 MeasureTheory.Measure.hausdorffMeasure s A ≤
 MeasureTheory.Measure.hausdorffMeasure (s + 1) (A ×ˢ Set.Icc (0 : ℝ) 1)) : dimH (YuiFeucLast n E) = dimH E + 1 := by
  exact @__connected_T010 n E h_H001 h_E004 h_E005 h_E010 h_E020

#check @P
#print axioms P

end Translation

namespace AuditBExport
set_option autoImplicit false
theorem resolved_M006 (n : ℕ) (E : Set (YuiRn n)) (h_H001 : E.Nonempty ∧ IsCompact E) (h_E003 : ∀ {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (A : Set X) (d : ℝ≥0),
 (dimH A < (d : ℝ≥0∞) → MeasureTheory.Measure.hausdorffMeasure (d : ℝ) A = 0) ∧
 ((d : ℝ≥0∞) < dimH A → MeasureTheory.Measure.hausdorffMeasure (d : ℝ) A = ⊤) ∧
 (MeasureTheory.Measure.hausdorffMeasure (d : ℝ) A ≠ ⊤ → dimH A ≤ (d : ℝ≥0∞)) ∧
 (MeasureTheory.Measure.hausdorffMeasure (d : ℝ) A = ⊤ → (d : ℝ≥0∞) ≤ dimH A)) (h_E004 : ∀ (n : ℕ) (E : Set (YuiRn n)), dimH E < ⊤) (h_E005 : dimH (Set.Icc (0 : ℝ) 1) = 1) (h_E008 : ∀ {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
 [NormedAddCommGroup W] [NormedSpace ℝ W] (e : V ≃L[ℝ] W) (S : Set V),
 dimH (e '' S) = dimH S) (h_E010 : ∀ {X : Type} [MetricSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
 (A : Set X) (q : ℝ), 0 < q → MeasureTheory.Measure.hausdorffMeasure q A = 0 →
 MeasureTheory.Measure.hausdorffMeasure (q + 1) (A ×ˢ Set.Icc (0 : ℝ) 1) = 0) (h_E020 : ∀ {X : Type} [MetricSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
 (A : Set X) (s : ℝ), 0 < s →
 MeasureTheory.Measure.hausdorffMeasure s A ≤
 MeasureTheory.Measure.hausdorffMeasure (s + 1) (A ×ˢ Set.Icc (0 : ℝ) 1)) : ∀ {X : Type*} [EMetricSpace X] {s t : Set X}, s ⊆ t → dimH s ≤ dimH t := by
  exact @dimH_mono

theorem resolved_M007 (n : ℕ) (E : Set (YuiRn n)) (h_H001 : E.Nonempty ∧ IsCompact E) (h_E003 : ∀ {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (A : Set X) (d : ℝ≥0),
 (dimH A < (d : ℝ≥0∞) → MeasureTheory.Measure.hausdorffMeasure (d : ℝ) A = 0) ∧
 ((d : ℝ≥0∞) < dimH A → MeasureTheory.Measure.hausdorffMeasure (d : ℝ) A = ⊤) ∧
 (MeasureTheory.Measure.hausdorffMeasure (d : ℝ) A ≠ ⊤ → dimH A ≤ (d : ℝ≥0∞)) ∧
 (MeasureTheory.Measure.hausdorffMeasure (d : ℝ) A = ⊤ → (d : ℝ≥0∞) ≤ dimH A)) (h_E004 : ∀ (n : ℕ) (E : Set (YuiRn n)), dimH E < ⊤) (h_E005 : dimH (Set.Icc (0 : ℝ) 1) = 1) (h_E008 : ∀ {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
 [NormedAddCommGroup W] [NormedSpace ℝ W] (e : V ≃L[ℝ] W) (S : Set V),
 dimH (e '' S) = dimH S) (h_E010 : ∀ {X : Type} [MetricSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
 (A : Set X) (q : ℝ), 0 < q → MeasureTheory.Measure.hausdorffMeasure q A = 0 →
 MeasureTheory.Measure.hausdorffMeasure (q + 1) (A ×ˢ Set.Icc (0 : ℝ) 1) = 0) (h_E020 : ∀ {X : Type} [MetricSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
 (A : Set X) (s : ℝ), 0 < s →
 MeasureTheory.Measure.hausdorffMeasure s A ≤
 MeasureTheory.Measure.hausdorffMeasure (s + 1) (A ×ˢ Set.Icc (0 : ℝ) 1)) : ∀ {X Y : Type*} [EMetricSpace X] [EMetricSpace Y] {f : X → Y},
 Isometry f → ∀ s : Set X, dimH (f '' s) = dimH s := by
  exact @Isometry.dimH_image

/- Instantiate only universes that disappear when checked E proofs replace
   premises. Public levels are inferred from the actual arguments/target.
   This elaborator builds an ordinary application, checked by Lean's kernel;
   it adds no theorem, axiom or proof dependency. -/
open Lean Elab Term in
elab "yui_assembly_declared_levels%" : term => do
  return toExpr (← getLevelNames)

-- Capture only the header's explicitly declared levels, before P introduces
-- auto-generated Type* names. Those names can shift after E is removed.
private def yuiAssemblyDeclaredLevels : List Lean.Name := yui_assembly_declared_levels%

open Lean Meta Elab Term in
elab "yui_assembly_export%" "(" args:term,* ")" : term <= expectedType => do
  let info ← getConstInfo `Translation.P
  let used ← forallTelescope info.type fun xs body => do
    let mut retained := #[]
    let omitted : Array String := #["h_M006", "h_M007"]
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
    else if yuiAssemblyDeclaredLevels.contains name then pure (Level.param name)
    else mkFreshLevelMVar
  elabAppArgs (mkConst `Translation.P levels) #[] (args.getElems.map Arg.stx)
    expectedType (explicit := true) (ellipsis := false)

set_option Elab.async false in
theorem P (n : ℕ) (E : Set (YuiRn n)) (h_H001 : E.Nonempty ∧ IsCompact E) (h_E003 : ∀ {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (A : Set X) (d : ℝ≥0),
 (dimH A < (d : ℝ≥0∞) → MeasureTheory.Measure.hausdorffMeasure (d : ℝ) A = 0) ∧
 ((d : ℝ≥0∞) < dimH A → MeasureTheory.Measure.hausdorffMeasure (d : ℝ) A = ⊤) ∧
 (MeasureTheory.Measure.hausdorffMeasure (d : ℝ) A ≠ ⊤ → dimH A ≤ (d : ℝ≥0∞)) ∧
 (MeasureTheory.Measure.hausdorffMeasure (d : ℝ) A = ⊤ → (d : ℝ≥0∞) ≤ dimH A)) (h_E004 : ∀ (n : ℕ) (E : Set (YuiRn n)), dimH E < ⊤) (h_E005 : dimH (Set.Icc (0 : ℝ) 1) = 1) (h_E008 : ∀ {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
 [NormedAddCommGroup W] [NormedSpace ℝ W] (e : V ≃L[ℝ] W) (S : Set V),
 dimH (e '' S) = dimH S) (h_E010 : ∀ {X : Type} [MetricSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
 (A : Set X) (q : ℝ), 0 < q → MeasureTheory.Measure.hausdorffMeasure q A = 0 →
 MeasureTheory.Measure.hausdorffMeasure (q + 1) (A ×ˢ Set.Icc (0 : ℝ) 1) = 0) (h_E020 : ∀ {X : Type} [MetricSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
 (A : Set X) (s : ℝ), 0 < s →
 MeasureTheory.Measure.hausdorffMeasure s A ≤
 MeasureTheory.Measure.hausdorffMeasure (s + 1) (A ×ˢ Set.Icc (0 : ℝ) 1)) : dimH (YuiFeucLast n E) = dimH E + 1 := by
  exact yui_assembly_export%(n, E, h_H001, h_E003, h_E004, h_E005, (@resolved_M006 n E h_H001 h_E003 h_E004 h_E005 h_E008 h_E010 h_E020), (@resolved_M007 n E h_H001 h_E003 h_E004 h_E005 h_E008 h_E010 h_E020), h_E008, h_E010, h_E020)

end AuditBExport

open Lean Meta Elab Command in
run_cmd do
  let result ← liftTermElabM do
    let info ← getConstInfo `Translation.P
    forallTelescope info.type fun xs body => do
      let mut retained := #[]
      let omitted : Array String := #["h_M006", "h_M007"]
      for x in xs do
        let decl ← getFVarLocalDecl x
        if !omitted.contains decl.userName.toString then
          retained := retained.push x
      let exported ← mkForallFVars retained body
      let used := (collectLevelParams {} exported).params.toList
      return Json.mkObj [("parameters", toJson (info.levelParams.map Name.toString)),
        ("export_used_parameters", toJson (used.map Name.toString))]
  logInfo m!"YUI_ASSEMBLY_LEVELS_JSON:{result.compress}"


namespace YuiBasis
set_option autoImplicit false
set_option Elab.async false in
theorem B001 : ∀ {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (a : ℝ) (A : Set X),
 MeasureTheory.Measure.hausdorffMeasure a A =
  ⨆ (r : ℝ≥0∞) (_ : 0 < r),
   ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i) (_ : ∀ i, Metric.ediam (U i) ≤ r),
    ∑' i, ⨆ _ : (U i).Nonempty, (Metric.ediam (U i)) ^ a := by
  exact @MeasureTheory.Measure.hausdorffMeasure_apply
set_option Elab.async false in
theorem B002 : ∀ (μ : Measure ℝ) (f : ℕ → ℝ → ℝ≥0∞), (∀ i, AEMeasurable (f i) μ) →
 (∫⁻ t, ∑' i, f i t ∂μ) = ∑' i, ∫⁻ t, f i t ∂μ := by
  intro μ f hf
  exact MeasureTheory.lintegral_tsum (μ := μ) (f := f) hf
set_option Elab.async false in
theorem B004 : ∀ (n : ℕ) (E : Set (YuiRn n)), dimH E < ⊤ := by
  intro n E
  exact Real.dimH_lt_top (E := YuiRn n) E
set_option Elab.async false in
theorem B005 : dimH (Set.Icc (0 : ℝ) 1) = 1 := by
  simpa only [segment_eq_Icc (show (0 : ℝ) ≤ 1 by norm_num)] using
    (Real.dimH_segment (show (0 : ℝ) ≠ 1 by norm_num))
set_option Elab.async false in
theorem B011 : (∀ a b : ℝ, (volume : Measure ℝ) (Set.Icc a b) = ENNReal.ofReal (b - a)) ∧
 (∀ B : Set ℝ, Bornology.IsBounded B → Metric.ediam B = ENNReal.ofReal (sSup B - sInf B)) := by
  constructor
  · intro a b
    exact Real.volume_Icc (a := a) (b := b)
  · intro B hB
    exact Real.ediam_eq (s := B) hB
set_option Elab.async false in
theorem B009 : ∀ {X : Type} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
 (A : Set X) (q : ℝ), 0 < q → MeasureTheory.Measure.hausdorffMeasure q A = 0 →
 ∀ r ε : ℝ, 0 < r → 0 < ε →
 ∃ (U : ℕ → Set X) (a : ℕ → ℝ),
 (A ⊆ ⋃ i, U i) ∧ (∀ i, 0 < a i ∧ a i ≤ r ∧ Metric.ediam (U i) ≤ ENNReal.ofReal (a i)) ∧
 (∑' i, (ENNReal.ofReal (a i)) ^ q) < ENNReal.ofReal ε := by
  have h_H001 : ∀ {X : Type} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (a : ℝ) (A : Set X),
   MeasureTheory.Measure.hausdorffMeasure a A =
    ⨆ (r : ℝ≥0∞) (_ : 0 < r),
     ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i) (_ : ∀ i, Metric.ediam (U i) ≤ r),
      ∑' i, ⨆ _ : (U i).Nonempty, (Metric.ediam (U i)) ^ a := @YuiBasis.B001
  have yui_nested_e86a9b822539f869ae27_0001 (h_H001 : ∀ {X : Type} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (a : ℝ) (A : Set X),
   MeasureTheory.Measure.hausdorffMeasure a A =
    ⨆ (r : ℝ≥0∞) (_ : 0 < r),
     ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i) (_ : ∀ i, Metric.ediam (U i) ≤ r),
      ∑' i, ⨆ _ : (U i).Nonempty, (Metric.ediam (U i)) ^ a) : (∀ {X : Type} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (A : Set X) (q : ℝ), MeasureTheory.Measure.hausdorffMeasure q A = ⨆ (r : ℝ≥0∞) (_ : 0 < r), ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i) (_ : ∀ i, Metric.ediam (U i) ≤ r), ∑' i, ⨆ _ : (U i).Nonempty, (Metric.ediam (U i)) ^ q) := by
    intro X _ _ _ A q
    exact h_H001 q A
  have yui_nested_e86a9b822539f869ae27_0002 (h_H001 : ∀ {X : Type} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (a : ℝ) (A : Set X),
   MeasureTheory.Measure.hausdorffMeasure a A =
    ⨆ (r : ℝ≥0∞) (_ : 0 < r),
     ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i) (_ : ∀ i, Metric.ediam (U i) ≤ r),
      ∑' i, ⨆ _ : (U i).Nonempty, (Metric.ediam (U i)) ^ a) : (∀ {X : Type} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (A : Set X) (q : ℝ), 0 < q → MeasureTheory.Measure.hausdorffMeasure q A = 0 → ∀ r ε : ℝ, 0 < r → 0 < ε → ∃ U : ℕ → Set X, (A ⊆ ⋃ i, U i) ∧ (∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal r) ∧ (∑' i, (Metric.ediam (U i)) ^ q) < ENNReal.ofReal (ε / 2)) := by
    intro X _ _ _ A q hq hzero r ε hr hε
    have hs := yui_nested_e86a9b822539f869ae27_0001 h_H001 A q
    rw [hzero] at hs
    have hi :
        (⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)
          (_ : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal r),
          ∑' i, ⨆ _ : (U i).Nonempty, (Metric.ediam (U i)) ^ q) ≤ 0 := by
      calc
        _ ≤ (⨆ (s : ℝ≥0∞) (_ : 0 < s),
          ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)
            (_ : ∀ i, Metric.ediam (U i) ≤ s),
            ∑' i, ⨆ _ : (U i).Nonempty, (Metric.ediam (U i)) ^ q) :=
          le_iSup₂ (ENNReal.ofReal r) (ENNReal.ofReal_pos.mpr hr)
        _ = 0 := hs.symm
    have hlt : (⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)
          (_ : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal r),
          ∑' i, ⨆ _ : (U i).Nonempty, (Metric.ediam (U i)) ^ q) < ENNReal.ofReal (ε / 2) :=
      hi.trans_lt (ENNReal.ofReal_pos.mpr (by positivity))
    simp only [iInf_lt_iff] at hlt
    obtain ⟨U, hcover, hdiam, hcost⟩ := hlt
    refine ⟨U, hcover, hdiam, ?_⟩
    have heq : ∀ i, (⨆ _ : (U i).Nonempty, (Metric.ediam (U i)) ^ q) =
        (Metric.ediam (U i)) ^ q := by
      intro i
      by_cases h : (U i).Nonempty
      · simp [h]
      · have hu : U i = ∅ := Set.not_nonempty_iff_eq_empty.mp h
        simp [hu, ENNReal.zero_rpow_of_pos hq]
    simpa only [heq] using hcost
  have yui_nested_e86a9b822539f869ae27_0003 (h_H001 : ∀ {X : Type} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (a : ℝ) (A : Set X),
   MeasureTheory.Measure.hausdorffMeasure a A =
    ⨆ (r : ℝ≥0∞) (_ : 0 < r),
     ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i) (_ : ∀ i, Metric.ediam (U i) ≤ r),
      ∑' i, ⨆ _ : (U i).Nonempty, (Metric.ediam (U i)) ^ a) : (∀ ε : ℝ, 0 < ε → (∀ i : ℕ, 0 < (ε / 2) / 2 / 2 ^ i) ∧ (∑' i : ℕ, ENNReal.ofReal ((ε / 2) / 2 / 2 ^ i)) = ENNReal.ofReal (ε / 2)) := by
    intro ε hε
    constructor
    · intro i
      positivity
    · rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) (summable_geometric_two' (ε / 2))]
      rw [tsum_geometric_two']
  have yui_nested_e86a9b822539f869ae27_0004 (h_H001 : ∀ {X : Type} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (a : ℝ) (A : Set X),
   MeasureTheory.Measure.hausdorffMeasure a A =
    ⨆ (r : ℝ≥0∞) (_ : 0 < r),
     ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i) (_ : ∀ i, Metric.ediam (U i) ≤ r),
      ∑' i, ⨆ _ : (U i).Nonempty, (Metric.ediam (U i)) ^ a) : (∀ (D : ℝ≥0∞) (r : ℝ), 0 ≤ r → D ≤ ENNReal.ofReal r → ENNReal.ofReal D.toReal = D ∧ D.toReal ≤ r) := by
    intro D r hr hD
    have hfinite : D ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hD
    exact ⟨ENNReal.ofReal_toReal hfinite, ENNReal.toReal_le_of_le_ofReal hr hD⟩
  have yui_nested_e86a9b822539f869ae27_0005 (h_H001 : ∀ {X : Type} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (a : ℝ) (A : Set X),
   MeasureTheory.Measure.hausdorffMeasure a A =
    ⨆ (r : ℝ≥0∞) (_ : 0 < r),
     ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i) (_ : ∀ i, Metric.ediam (U i) ≤ r),
      ∑' i, ⨆ _ : (U i).Nonempty, (Metric.ediam (U i)) ^ a) : (∀ (D : ℝ≥0∞) (r c : ℝ), 0 ≤ r → D ≤ ENNReal.ofReal r → D ≤ ENNReal.ofReal (max D.toReal c)) := by
    intro D r c hr hD
    have hreal : ENNReal.ofReal D.toReal = D := (yui_nested_e86a9b822539f869ae27_0004 h_H001 D r hr hD).1
    calc
      D = ENNReal.ofReal D.toReal := hreal.symm
      _ ≤ ENNReal.ofReal (max D.toReal c) :=
        ENNReal.ofReal_le_ofReal (le_max_left D.toReal c)
  have yui_nested_e86a9b822539f869ae27_0006 (h_H001 : ∀ {X : Type} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (a : ℝ) (A : Set X),
   MeasureTheory.Measure.hausdorffMeasure a A =
    ⨆ (r : ℝ≥0∞) (_ : 0 < r),
     ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i) (_ : ∀ i, Metric.ediam (U i) ≤ r),
      ∑' i, ⨆ _ : (U i).Nonempty, (Metric.ediam (U i)) ^ a) : (∀ (D : ℝ≥0∞) (r b q : ℝ), 0 < r → 0 < b → 0 < q → D ≤ ENNReal.ofReal r → ∃ a : ℝ, (0 < a ∧ a ≤ r ∧ D ≤ ENNReal.ofReal a) ∧ (ENNReal.ofReal a) ^ q ≤ D ^ q + ENNReal.ofReal b) := by
    intro D r b q hr hb hq hD
    obtain ⟨hreal, hdr⟩ := yui_nested_e86a9b822539f869ae27_0004 h_H001 D r hr.le hD
    let α : ℝ := min r (b ^ q⁻¹)
    have hα : 0 < α := lt_min hr (Real.rpow_pos_of_pos hb _)
    have hαr : α ≤ r := min_le_left _ _
    have hαb : α ^ q ≤ b := by
      calc
        α ^ q ≤ (b ^ q⁻¹) ^ q :=
          Real.rpow_le_rpow hα.le (min_le_right _ _) hq.le
        _ = b := Real.rpow_inv_rpow hb.le hq.ne'
    refine ⟨max D.toReal α, ⟨hα.trans_le (le_max_right _ _),
      max_le hdr hαr, ?_⟩, ?_⟩
    · exact yui_nested_e86a9b822539f869ae27_0005 h_H001 D r α hr.le hD
    · rcases le_total D.toReal α with h | h
      · rw [max_eq_right h, ENNReal.ofReal_rpow_of_nonneg hα.le hq.le]
        exact (ENNReal.ofReal_le_ofReal hαb).trans (le_add_left le_rfl)
      · rw [max_eq_left h, hreal]
        exact le_self_add
  classical
  intro X _ _ _ A q hq hzero r ε hr hε
  obtain ⟨U, hcover, hdiam, hcost⟩ :=
    yui_nested_e86a9b822539f869ae27_0002 h_H001 A q hq hzero r ε hr hε
  obtain ⟨hbpos, hbsum⟩ := yui_nested_e86a9b822539f869ae27_0003 h_H001 ε hε
  have ha : ∀ i : ℕ, ∃ a : ℝ,
      (0 < a ∧ a ≤ r ∧ Metric.ediam (U i) ≤ ENNReal.ofReal a) ∧
      (ENNReal.ofReal a) ^ q ≤ (Metric.ediam (U i)) ^ q +
        ENNReal.ofReal ((ε / 2) / 2 / 2 ^ i) := by
    intro i
    exact yui_nested_e86a9b822539f869ae27_0006 h_H001 (Metric.ediam (U i)) r
      ((ε / 2) / 2 / 2 ^ i) q hr (hbpos i) hq (hdiam i)
  choose a habound hacost using ha
  refine ⟨U, a, hcover, habound, ?_⟩
  calc
    (∑' i, (ENNReal.ofReal (a i)) ^ q)
        ≤ ∑' i, ((Metric.ediam (U i)) ^ q +
            ENNReal.ofReal ((ε / 2) / 2 / 2 ^ i)) :=
      ENNReal.tsum_le_tsum hacost
    _ = (∑' i, (Metric.ediam (U i)) ^ q) + ENNReal.ofReal (ε / 2) := by
      rw [ENNReal.tsum_add, hbsum]
    _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
      ENNReal.add_lt_add_right ENNReal.ofReal_ne_top hcost
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
set_option Elab.async false in
theorem B010 : ∀ {X : Type} [MetricSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
 (A : Set X) (q : ℝ), 0 < q → MeasureTheory.Measure.hausdorffMeasure q A = 0 →
 MeasureTheory.Measure.hausdorffMeasure (q + 1) (A ×ˢ Set.Icc (0 : ℝ) 1) = 0 := by
  have h_H001 : ∀ {X : Type} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (a : ℝ) (A : Set X),
   MeasureTheory.Measure.hausdorffMeasure a A =
    ⨆ (r : ℝ≥0∞) (_ : 0 < r),
     ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i) (_ : ∀ i, Metric.ediam (U i) ≤ r),
      ∑' i, ⨆ _ : (U i).Nonempty, (Metric.ediam (U i)) ^ a := @YuiBasis.B001
  have h_H002 : ∀ {X : Type} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
   (A : Set X) (q : ℝ), 0 < q → MeasureTheory.Measure.hausdorffMeasure q A = 0 →
   ∀ r ε : ℝ, 0 < r → 0 < ε →
   ∃ (U : ℕ → Set X) (a : ℕ → ℝ),
   (A ⊆ ⋃ i, U i) ∧ (∀ i, 0 < a i ∧ a i ≤ r ∧ Metric.ediam (U i) ≤ ENNReal.ofReal (a i)) ∧
   (∑' i, (ENNReal.ofReal (a i)) ^ q) < ENNReal.ofReal ε := @YuiBasis.B009
  have yui_nested_799adb4f153303a223d8_0001 (h_H001 : ∀ {X : Type} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (a : ℝ) (A : Set X),
   MeasureTheory.Measure.hausdorffMeasure a A =
    ⨆ (r : ℝ≥0∞) (_ : 0 < r),
     ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i) (_ : ∀ i, Metric.ediam (U i) ≤ r),
      ∑' i, ⨆ _ : (U i).Nonempty, (Metric.ediam (U i)) ^ a) (h_H002 : ∀ {X : Type} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
   (A : Set X) (q : ℝ), 0 < q → MeasureTheory.Measure.hausdorffMeasure q A = 0 →
   ∀ r ε : ℝ, 0 < r → 0 < ε →
   ∃ (U : ℕ → Set X) (a : ℕ → ℝ),
   (A ⊆ ⋃ i, U i) ∧ (∀ i, 0 < a i ∧ a i ≤ r ∧ Metric.ediam (U i) ≤ ENNReal.ofReal (a i)) ∧
   (∑' i, (ENNReal.ofReal (a i)) ^ q) < ENNReal.ofReal ε) : (∀ (a : ℝ), 0 < a → a ≤ 1 → ∃ N : ℕ, 0 < N ∧ 1 / (N : ℝ) ≤ a ∧ (N : ℝ) * a ≤ 2 ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ j : Fin N, t ∈ Set.Icc ((j : ℝ) / N) (((j : ℝ) + 1) / N)) := by
    intro a ha ha1
    let N : ℕ := ⌈1 / a⌉₊
    have hN : 0 < N := Nat.ceil_pos.mpr (by positivity)
    have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    have hlow : 1 / a ≤ (N : ℝ) := Nat.le_ceil _
    have hupp : (N : ℝ) < 1 / a + 1 := Nat.ceil_lt_add_one (by positivity)
    refine ⟨N, hN, ?_, ?_, ?_⟩
    · apply (div_le_iff₀ hNr).mpr
      have := (div_le_iff₀ ha).mp hlow
      nlinarith
    · have := (mul_lt_mul_of_pos_right hupp ha)
      have hea : (1 / a + 1) * a = 1 + a := by field_simp
      rw [hea] at this
      linarith
    · intro t ht
      by_cases ht1 : t = 1
      · subst t
        refine ⟨⟨N - 1, Nat.sub_lt hN (by omega)⟩, ?_, ?_⟩
        · apply (div_le_iff₀ hNr).mpr
          norm_cast
          omega
        · apply (le_div_iff₀ hNr).mpr
          have he : ((N - 1 : ℕ) : ℝ) + 1 = N := by
            exact_mod_cast Nat.sub_add_cancel hN
          dsimp
          linarith
      · have htlt : t < 1 := lt_of_le_of_ne ht.2 ht1
        have htn : t * (N : ℝ) < N := by nlinarith
        have htn0 : 0 ≤ t * (N : ℝ) := mul_nonneg ht.1 hNr.le
        refine ⟨⟨⌊t * (N : ℝ)⌋₊, (Nat.floor_lt htn0).mpr htn⟩, ?_, ?_⟩
        · exact (div_le_iff₀ hNr).mpr (Nat.floor_le htn0)
        · exact (le_div_iff₀ hNr).mpr (Nat.lt_floor_add_one _).le
  have yui_nested_799adb4f153303a223d8_0002 (h_H001 : ∀ {X : Type} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (a : ℝ) (A : Set X),
   MeasureTheory.Measure.hausdorffMeasure a A =
    ⨆ (r : ℝ≥0∞) (_ : 0 < r),
     ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i) (_ : ∀ i, Metric.ediam (U i) ≤ r),
      ∑' i, ⨆ _ : (U i).Nonempty, (Metric.ediam (U i)) ^ a) (h_H002 : ∀ {X : Type} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
   (A : Set X) (q : ℝ), 0 < q → MeasureTheory.Measure.hausdorffMeasure q A = 0 →
   ∀ r ε : ℝ, 0 < r → 0 < ε →
   ∃ (U : ℕ → Set X) (a : ℕ → ℝ),
   (A ⊆ ⋃ i, U i) ∧ (∀ i, 0 < a i ∧ a i ≤ r ∧ Metric.ediam (U i) ≤ ENNReal.ofReal (a i)) ∧
   (∑' i, (ENNReal.ofReal (a i)) ^ q) < ENNReal.ofReal ε) : (∀ {X : Type} [MetricSpace X] (U : Set X) (a : ℝ) (N : ℕ), 0 < N → Metric.ediam U ≤ ENNReal.ofReal a → 1 / (N : ℝ) ≤ a → ∀ j : Fin N, Metric.ediam (U ×ˢ Set.Icc ((j : ℝ) / N) (((j : ℝ) + 1) / N)) ≤ ENNReal.ofReal a) := by
    intro X _ U a N hN hU hw j
    have hJ : Metric.ediam (Set.Icc ((j : ℝ) / N) (((j : ℝ) + 1) / N)) ≤ ENNReal.ofReal a := by
      rw [Real.ediam_Icc]
      apply ENNReal.ofReal_le_ofReal
      convert hw using 1 <;> ring
    apply Metric.ediam_le
    intro x hx y hy
    rw [Prod.edist_eq]
    exact max_le (Metric.edist_le_of_ediam_le hx.1 hy.1 hU)
      (Metric.edist_le_of_ediam_le hx.2 hy.2 hJ)
  have yui_nested_799adb4f153303a223d8_0003 (h_H001 : ∀ {X : Type} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (a : ℝ) (A : Set X),
   MeasureTheory.Measure.hausdorffMeasure a A =
    ⨆ (r : ℝ≥0∞) (_ : 0 < r),
     ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i) (_ : ∀ i, Metric.ediam (U i) ≤ r),
      ∑' i, ⨆ _ : (U i).Nonempty, (Metric.ediam (U i)) ^ a) (h_H002 : ∀ {X : Type} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
   (A : Set X) (q : ℝ), 0 < q → MeasureTheory.Measure.hausdorffMeasure q A = 0 →
   ∀ r ε : ℝ, 0 < r → 0 < ε →
   ∃ (U : ℕ → Set X) (a : ℕ → ℝ),
   (A ⊆ ⋃ i, U i) ∧ (∀ i, 0 < a i ∧ a i ≤ r ∧ Metric.ediam (U i) ≤ ENNReal.ofReal (a i)) ∧
   (∑' i, (ENNReal.ofReal (a i)) ^ q) < ENNReal.ofReal ε) : (∀ (a q : ℝ) (N : ℕ), 0 < a → (N : ℝ) * a ≤ 2 → (N : ℝ≥0∞) * (ENNReal.ofReal a) ^ (q + 1) ≤ 2 * (ENNReal.ofReal a) ^ q) := by
    intro a q N ha hNa
    have hc : (N : ℝ≥0∞) * ENNReal.ofReal a ≤ 2 := by
      have h := ENNReal.ofReal_le_ofReal hNa
      simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg N), ENNReal.ofReal_natCast,
        ENNReal.ofReal_ofNat] using h
    rw [ENNReal.rpow_add q 1 (ne_of_gt (ENNReal.ofReal_pos.mpr ha)) ENNReal.ofReal_ne_top,
      ENNReal.rpow_one]
    calc
      (N : ℝ≥0∞) * (ENNReal.ofReal a ^ q * ENNReal.ofReal a) =
          ((N : ℝ≥0∞) * ENNReal.ofReal a) * ENNReal.ofReal a ^ q := by ac_rfl
      _ ≤ 2 * ENNReal.ofReal a ^ q := by gcongr
  have yui_nested_799adb4f153303a223d8_0004 (h_H001 : ∀ {X : Type} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (a : ℝ) (A : Set X),
   MeasureTheory.Measure.hausdorffMeasure a A =
    ⨆ (r : ℝ≥0∞) (_ : 0 < r),
     ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i) (_ : ∀ i, Metric.ediam (U i) ≤ r),
      ∑' i, ⨆ _ : (U i).Nonempty, (Metric.ediam (U i)) ^ a) (h_H002 : ∀ {X : Type} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
   (A : Set X) (q : ℝ), 0 < q → MeasureTheory.Measure.hausdorffMeasure q A = 0 →
   ∀ r ε : ℝ, 0 < r → 0 < ε →
   ∃ (U : ℕ → Set X) (a : ℕ → ℝ),
   (A ⊆ ⋃ i, U i) ∧ (∀ i, 0 < a i ∧ a i ≤ r ∧ Metric.ediam (U i) ≤ ENNReal.ofReal (a i)) ∧
   (∑' i, (ENNReal.ofReal (a i)) ^ q) < ENNReal.ofReal ε) : (∀ {X : Type} [MetricSpace X] {ι : Type} [Countable ι] (A : Set X) (p : ℝ) (R : ℝ≥0∞) (V : ι → Set X), A ⊆ ⋃ i, V i → (∀ i, Metric.ediam (V i) ≤ R) → ∃ W : ℕ → Set X, (A ⊆ ⋃ i, W i) ∧ (∀ i, Metric.ediam (W i) ≤ R) ∧ (∑' i, ⨆ _ : (W i).Nonempty, (Metric.ediam (W i)) ^ p) ≤ ∑' i, (Metric.ediam (V i)) ^ p) := by
    intro X _ ι _ A p R V hcov hdiam
    classical
    letI : Encodable ι := Encodable.ofCountable ι
    let W : ℕ → Set X := fun j => ⋃ b ∈ Encodable.decode₂ ι j, V b
    refine ⟨W, ?_, ?_, ?_⟩
    · simpa only [W, Encodable.iUnion_decode₂] using hcov
    · intro j
      dsimp only [W]
      rw [Metric.ediam_iUnion_mem_option]
      exact iSup₂_le fun b _ => hdiam b
    · calc
        (∑' i, ⨆ _ : (W i).Nonempty, (Metric.ediam (W i)) ^ p) =
            ∑' i, ⨆ _ : (V i).Nonempty, (Metric.ediam (V i)) ^ p :=
          tsum_iUnion_decode₂ (fun t : Set X => ⨆ _ : t.Nonempty, Metric.ediam t ^ p)
            (by simp) V
        _ ≤ ∑' i, (Metric.ediam (V i)) ^ p :=
          ENNReal.tsum_le_tsum fun i => iSup_le fun _ => le_rfl
  have yui_nested_799adb4f153303a223d8_0005 (h_H001 : ∀ {X : Type} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (a : ℝ) (A : Set X),
   MeasureTheory.Measure.hausdorffMeasure a A =
    ⨆ (r : ℝ≥0∞) (_ : 0 < r),
     ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i) (_ : ∀ i, Metric.ediam (U i) ≤ r),
      ∑' i, ⨆ _ : (U i).Nonempty, (Metric.ediam (U i)) ^ a) (h_H002 : ∀ {X : Type} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
   (A : Set X) (q : ℝ), 0 < q → MeasureTheory.Measure.hausdorffMeasure q A = 0 →
   ∀ r ε : ℝ, 0 < r → 0 < ε →
   ∃ (U : ℕ → Set X) (a : ℕ → ℝ),
   (A ⊆ ⋃ i, U i) ∧ (∀ i, 0 < a i ∧ a i ≤ r ∧ Metric.ediam (U i) ≤ ENNReal.ofReal (a i)) ∧
   (∑' i, (ENNReal.ofReal (a i)) ^ q) < ENNReal.ofReal ε) : (∀ {X : Type} [MetricSpace X] (A : Set X) (q r : ℝ) (U : ℕ → Set X) (a : ℕ → ℝ), 0 < q → r ≤ 1 → (A ⊆ ⋃ i, U i) → (∀ i, 0 < a i ∧ a i ≤ r ∧ Metric.ediam (U i) ≤ ENNReal.ofReal (a i)) → ∃ W : ℕ → Set (X × ℝ), (A ×ˢ Set.Icc (0 : ℝ) 1 ⊆ ⋃ k, W k) ∧ (∀ k, Metric.ediam (W k) ≤ ENNReal.ofReal r) ∧ (∑' k, ⨆ _ : (W k).Nonempty, Metric.ediam (W k) ^ (q + 1)) ≤ 2 * ∑' i, ENNReal.ofReal (a i) ^ q) := by
    intro X _ A q r U a hq hr hcov ha
    classical
    choose N hN hw hNa hcover using fun i =>
      yui_nested_799adb4f153303a223d8_0001 h_H001 h_H002 (a i) (ha i).1 ((ha i).2.1.trans hr)
    let ι := Σ i : ℕ, Fin (N i)
    let V : ι → Set (X × ℝ) := fun k =>
      U k.1 ×ˢ Set.Icc ((k.2 : ℝ) / N k.1) (((k.2 : ℝ) + 1) / N k.1)
    have hd : ∀ k : ι, Metric.ediam (V k) ≤ ENNReal.ofReal (a k.1) := by
      intro k
      exact yui_nested_799adb4f153303a223d8_0002 h_H001 h_H002 (U k.1) (a k.1) (N k.1)
        (hN k.1) (ha k.1).2.2 (hw k.1) k.2
    have hc : A ×ˢ Set.Icc (0 : ℝ) 1 ⊆ ⋃ k, V k := by
      intro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hx.1)
      obtain ⟨j, hj⟩ := hcover i x.2 hx.2
      exact Set.mem_iUnion.mpr ⟨⟨i, j⟩, hi, hj⟩
    have hs : (∑' k : ι, Metric.ediam (V k) ^ (q + 1)) ≤
        2 * ∑' i, ENNReal.ofReal (a i) ^ q := by
      calc
        (∑' k : ι, Metric.ediam (V k) ^ (q + 1)) ≤
            ∑' k : ι, ENNReal.ofReal (a k.1) ^ (q + 1) :=
          ENNReal.tsum_le_tsum fun k => ENNReal.rpow_le_rpow (hd k) (by linarith)
        _ = ∑' i, (N i : ℝ≥0∞) * ENNReal.ofReal (a i) ^ (q + 1) := by
          rw [ENNReal.tsum_sigma']
          simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
        _ ≤ ∑' i, 2 * ENNReal.ofReal (a i) ^ q :=
          ENNReal.tsum_le_tsum fun i => yui_nested_799adb4f153303a223d8_0003 h_H001 h_H002 (a i) q (N i)
            (ha i).1 (hNa i)
        _ = 2 * ∑' i, ENNReal.ofReal (a i) ^ q := ENNReal.tsum_mul_left
    obtain ⟨W, hWcov, hWdiam, hWcost⟩ := yui_nested_799adb4f153303a223d8_0004 h_H001 h_H002
      (A ×ˢ Set.Icc (0 : ℝ) 1) (q + 1) (ENNReal.ofReal r) V hc
      (fun k => (hd k).trans (ENNReal.ofReal_le_ofReal (ha k.1).2.1))
    exact ⟨W, hWcov, hWdiam, hWcost.trans hs⟩
  have yui_nested_799adb4f153303a223d8_0006 (h_H001 : ∀ {X : Type} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (a : ℝ) (A : Set X),
   MeasureTheory.Measure.hausdorffMeasure a A =
    ⨆ (r : ℝ≥0∞) (_ : 0 < r),
     ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i) (_ : ∀ i, Metric.ediam (U i) ≤ r),
      ∑' i, ⨆ _ : (U i).Nonempty, (Metric.ediam (U i)) ^ a) (h_H002 : ∀ {X : Type} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
   (A : Set X) (q : ℝ), 0 < q → MeasureTheory.Measure.hausdorffMeasure q A = 0 →
   ∀ r ε : ℝ, 0 < r → 0 < ε →
   ∃ (U : ℕ → Set X) (a : ℕ → ℝ),
   (A ⊆ ⋃ i, U i) ∧ (∀ i, 0 < a i ∧ a i ≤ r ∧ Metric.ediam (U i) ≤ ENNReal.ofReal (a i)) ∧
   (∑' i, (ENNReal.ofReal (a i)) ^ q) < ENNReal.ofReal ε) : (∀ {X : Type} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (A : Set X) (q : ℝ), MeasureTheory.Measure.hausdorffMeasure q A = ⨆ (r : ℝ≥0∞) (_ : 0 < r), ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i) (_ : ∀ i, Metric.ediam (U i) ≤ r), ∑' i, ⨆ _ : (U i).Nonempty, Metric.ediam (U i) ^ q) := by
    intro X _ _ _ A q
    exact h_H001 q A
  have yui_nested_799adb4f153303a223d8_0007 (h_H001 : ∀ {X : Type} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (a : ℝ) (A : Set X),
   MeasureTheory.Measure.hausdorffMeasure a A =
    ⨆ (r : ℝ≥0∞) (_ : 0 < r),
     ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i) (_ : ∀ i, Metric.ediam (U i) ≤ r),
      ∑' i, ⨆ _ : (U i).Nonempty, (Metric.ediam (U i)) ^ a) (h_H002 : ∀ {X : Type} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
   (A : Set X) (q : ℝ), 0 < q → MeasureTheory.Measure.hausdorffMeasure q A = 0 →
   ∀ r ε : ℝ, 0 < r → 0 < ε →
   ∃ (U : ℕ → Set X) (a : ℕ → ℝ),
   (A ⊆ ⋃ i, U i) ∧ (∀ i, 0 < a i ∧ a i ≤ r ∧ Metric.ediam (U i) ≤ ENNReal.ofReal (a i)) ∧
   (∑' i, (ENNReal.ofReal (a i)) ^ q) < ENNReal.ofReal ε) : (∀ {X : Type} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (A : Set X) (q : ℝ), 0 < q → MeasureTheory.Measure.hausdorffMeasure q A = 0 → ∀ r ε : ℝ, 0 < r → 0 < ε → ∃ (U : ℕ → Set X) (a : ℕ → ℝ), (A ⊆ ⋃ i, U i) ∧ (∀ i, 0 < a i ∧ a i ≤ r ∧ Metric.ediam (U i) ≤ ENNReal.ofReal (a i)) ∧ (∑' i, ENNReal.ofReal (a i) ^ q) < ENNReal.ofReal ε) := by
    intro X _ _ _ A q hq hz r ε hr he
    exact h_H002 A q hq hz r ε hr he
  have yui_nested_799adb4f153303a223d8_0008 (h_H001 : ∀ {X : Type} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (a : ℝ) (A : Set X),
   MeasureTheory.Measure.hausdorffMeasure a A =
    ⨆ (r : ℝ≥0∞) (_ : 0 < r),
     ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i) (_ : ∀ i, Metric.ediam (U i) ≤ r),
      ∑' i, ⨆ _ : (U i).Nonempty, (Metric.ediam (U i)) ^ a) (h_H002 : ∀ {X : Type} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
   (A : Set X) (q : ℝ), 0 < q → MeasureTheory.Measure.hausdorffMeasure q A = 0 →
   ∀ r ε : ℝ, 0 < r → 0 < ε →
   ∃ (U : ℕ → Set X) (a : ℕ → ℝ),
   (A ⊆ ⋃ i, U i) ∧ (∀ i, 0 < a i ∧ a i ≤ r ∧ Metric.ediam (U i) ≤ ENNReal.ofReal (a i)) ∧
   (∑' i, (ENNReal.ofReal (a i)) ^ q) < ENNReal.ofReal ε) : (∀ ε : ℝ≥0, (2 : ℝ≥0∞) * ENNReal.ofReal ((ε : ℝ) / 2) = (ε : ℝ≥0∞)) := by
    intro ε
    calc
      (2 : ℝ≥0∞) * ENNReal.ofReal ((ε : ℝ) / 2) =
          ENNReal.ofReal (2 * ((ε : ℝ) / 2)) := by
        rw [ENNReal.ofReal_mul (by norm_num)]
        norm_num
      _ = (ε : ℝ≥0∞) := by
        rw [show (2 : ℝ) * ((ε : ℝ) / 2) = (ε : ℝ) by ring]
        exact ENNReal.ofReal_coe_nnreal
  have yui_nested_799adb4f153303a223d8_0009 (h_H001 : ∀ {X : Type} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (a : ℝ) (A : Set X),
   MeasureTheory.Measure.hausdorffMeasure a A =
    ⨆ (r : ℝ≥0∞) (_ : 0 < r),
     ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i) (_ : ∀ i, Metric.ediam (U i) ≤ r),
      ∑' i, ⨆ _ : (U i).Nonempty, (Metric.ediam (U i)) ^ a) (h_H002 : ∀ {X : Type} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
   (A : Set X) (q : ℝ), 0 < q → MeasureTheory.Measure.hausdorffMeasure q A = 0 →
   ∀ r ε : ℝ, 0 < r → 0 < ε →
   ∃ (U : ℕ → Set X) (a : ℕ → ℝ),
   (A ⊆ ⋃ i, U i) ∧ (∀ i, 0 < a i ∧ a i ≤ r ∧ Metric.ediam (U i) ≤ ENNReal.ofReal (a i)) ∧
   (∑' i, (ENNReal.ofReal (a i)) ^ q) < ENNReal.ofReal ε) : (∀ {X : Type} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (A : Set X) (q : ℝ), 0 < q → MeasureTheory.Measure.hausdorffMeasure q A = 0 → ∀ R : ℝ≥0∞, 0 < R → (⨅ (V : ℕ → Set (X × ℝ)) (_ : A ×ˢ Set.Icc (0 : ℝ) 1 ⊆ ⋃ i, V i) (_ : ∀ i, Metric.ediam (V i) ≤ R), ∑' i, ⨆ _ : (V i).Nonempty, Metric.ediam (V i) ^ (q + 1)) = 0) := by
    classical
    intro X _ _ _ A q hq hzero R hR
    apply le_antisymm ?_ zero_le
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    simp only [zero_add]
    obtain ⟨s, hs0, hspos, hsR⟩ := ENNReal.lt_iff_exists_real_btwn.mp hR
    let r : ℝ := min s 1
    have hr : 0 < r := lt_min (ENNReal.ofReal_pos.mp hspos) zero_lt_one
    have hr1 : r ≤ 1 := min_le_right _ _
    have hrR : ENNReal.ofReal r ≤ R :=
      (ENNReal.ofReal_le_ofReal (min_le_left _ _)).trans hsR.le
    have he : 0 < (ε : ℝ) := hε
    obtain ⟨U, a, hcov, ha, hcost⟩ :=
      yui_nested_799adb4f153303a223d8_0007 h_H001 h_H002 A q hq hzero r ((ε : ℝ) / 2) hr (by positivity)
    obtain ⟨W, hWcov, hWdiam, hWcost⟩ :=
      yui_nested_799adb4f153303a223d8_0005 h_H001 h_H002 A q r U a hq hr1 hcov ha
    calc
      (⨅ (V : ℕ → Set (X × ℝ)) (_ : A ×ˢ Set.Icc (0 : ℝ) 1 ⊆ ⋃ i, V i)
          (_ : ∀ i, Metric.ediam (V i) ≤ R),
          ∑' i, ⨆ _ : (V i).Nonempty, Metric.ediam (V i) ^ (q + 1)) ≤
          ∑' i, ⨆ _ : (W i).Nonempty, Metric.ediam (W i) ^ (q + 1) :=
        iInf_le_of_le W (iInf_le_of_le hWcov
          (iInf_le_of_le (fun i => (hWdiam i).trans hrR) le_rfl))
      _ ≤ 2 * ∑' i, ENNReal.ofReal (a i) ^ q := hWcost
      _ ≤ 2 * ENNReal.ofReal ((ε : ℝ) / 2) := by gcongr
      _ = (ε : ℝ≥0∞) := yui_nested_799adb4f153303a223d8_0008 h_H001 h_H002 ε
  classical
  intro X _ _ _ _ A q hq hz
  apply le_antisymm ?_ zero_le
  rw [h_H001]
  exact iSup₂_le fun R hR => le_of_eq
    (yui_nested_799adb4f153303a223d8_0009 h_H001 h_H002 A q hq hz R hR)
set_option Elab.async false in
theorem B019 : ∀ {X : Type} [MetricSpace X] (A : Set X) (s : ℝ) (r : ℝ≥0∞),
 0 < s → 0 < r → r ≠ ⊤ →
 ∀ V : ℕ → Set (X × ℝ), (A ×ˢ Set.Icc (0 : ℝ) 1 ⊆ ⋃ i, V i) →
 (∀ i, Metric.ediam (V i) ≤ r) →
 YuiContent s r A ≤ ∑' i, (Metric.ediam (V i)) ^ (s + 1) := by
  have h_H001 : ∀ (μ : Measure ℝ) (f : ℕ → ℝ → ℝ≥0∞), (∀ i, AEMeasurable (f i) μ) →
   (∫⁻ t, ∑' i, f i t ∂μ) = ∑' i, ∫⁻ t, f i t ∂μ := @YuiBasis.B002
  have h_H002 : (∀ a b : ℝ, (volume : Measure ℝ) (Set.Icc a b) = ENNReal.ofReal (b - a)) ∧
   (∀ B : Set ℝ, Bornology.IsBounded B → Metric.ediam B = ENNReal.ofReal (sSup B - sInf B)) := @YuiBasis.B011
  have yui_nested_ab04f0ca374a82dd4506_0001 (h_H001 : ∀ (μ : Measure ℝ) (f : ℕ → ℝ → ℝ≥0∞), (∀ i, AEMeasurable (f i) μ) →
   (∫⁻ t, ∑' i, f i t ∂μ) = ∑' i, ∫⁻ t, f i t ∂μ) (h_H002 : (∀ a b : ℝ, (volume : Measure ℝ) (Set.Icc a b) = ENNReal.ofReal (b - a)) ∧
   (∀ B : Set ℝ, Bornology.IsBounded B → Metric.ediam B = ENNReal.ofReal (sSup B - sInf B))) : (∀ B : Set ℝ, Bornology.IsBounded B → ∃ J : Set ℝ, MeasurableSet J ∧ B ⊆ J ∧ (volume : Measure ℝ) J = Metric.ediam B) := by
    intro B hB
    by_cases h : B.Nonempty
    · refine ⟨Set.Icc (sInf B) (sSup B), measurableSet_Icc, ?_, ?_⟩
      · intro t ht
        exact ⟨csInf_le hB.bddBelow ht, le_csSup hB.bddAbove ht⟩
      · rw [h_H002.1, h_H002.2 B hB]
    · have hE : B = ∅ := Set.not_nonempty_iff_eq_empty.mp h
      subst B
      exact ⟨∅, MeasurableSet.empty, Set.Subset.rfl, by simp⟩
  have yui_nested_ab04f0ca374a82dd4506_0002 (h_H001 : ∀ (μ : Measure ℝ) (f : ℕ → ℝ → ℝ≥0∞), (∀ i, AEMeasurable (f i) μ) →
   (∫⁻ t, ∑' i, f i t ∂μ) = ∑' i, ∫⁻ t, f i t ∂μ) (h_H002 : (∀ a b : ℝ, (volume : Measure ℝ) (Set.Icc a b) = ENNReal.ofReal (b - a)) ∧
   (∀ B : Set ℝ, Bornology.IsBounded B → Metric.ediam B = ENNReal.ofReal (sSup B - sInf B))) : (∀ {X : Type} [MetricSpace X] (V : Set (X × ℝ)), Metric.ediam (Prod.fst '' V) ≤ Metric.ediam V ∧ Metric.ediam (Prod.snd '' V) ≤ Metric.ediam V) := by
    intro X inst V
    constructor
    · simpa only [ENNReal.coe_one, one_mul] using (LipschitzWith.prod_fst.ediam_image_le V)
    · simpa only [ENNReal.coe_one, one_mul] using (LipschitzWith.prod_snd.ediam_image_le V)
  have yui_nested_ab04f0ca374a82dd4506_0003 (h_H001 : ∀ (μ : Measure ℝ) (f : ℕ → ℝ → ℝ≥0∞), (∀ i, AEMeasurable (f i) μ) →
   (∫⁻ t, ∑' i, f i t ∂μ) = ∑' i, ∫⁻ t, f i t ∂μ) (h_H002 : (∀ a b : ℝ, (volume : Measure ℝ) (Set.Icc a b) = ENNReal.ofReal (b - a)) ∧
   (∀ B : Set ℝ, Bornology.IsBounded B → Metric.ediam B = ENNReal.ofReal (sSup B - sInf B))) : (∀ {X : Type} (A : Set X) (V : ℕ → Set (X × ℝ)), (A ×ˢ Set.Icc (0 : ℝ) 1 ⊆ ⋃ i, V i) → ∀ x ∈ A, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ i, (x,t) ∈ V i) := by
    intro X A V hcover x hx t ht
    have hp : (x,t) ∈ A ×ˢ Set.Icc (0 : ℝ) 1 := ⟨hx, ht⟩
    exact Set.mem_iUnion.mp (hcover hp)
  have yui_nested_ab04f0ca374a82dd4506_0004 (h_H001 : ∀ (μ : Measure ℝ) (f : ℕ → ℝ → ℝ≥0∞), (∀ i, AEMeasurable (f i) μ) →
   (∫⁻ t, ∑' i, f i t ∂μ) = ∑' i, ∫⁻ t, f i t ∂μ) (h_H002 : (∀ a b : ℝ, (volume : Measure ℝ) (Set.Icc a b) = ENNReal.ofReal (b - a)) ∧
   (∀ B : Set ℝ, Bornology.IsBounded B → Metric.ediam B = ENNReal.ofReal (sSup B - sInf B))) : (∀ {X : Type} [MetricSpace X] (A : Set X) (s : ℝ) (r : ℝ≥0∞), 0 < s → ∀ (V : ℕ → Set (X × ℝ)) (J : ℕ → Set ℝ), (A ×ˢ Set.Icc (0 : ℝ) 1 ⊆ ⋃ i, V i) → (∀ i, Metric.ediam (V i) ≤ r) → (∀ i, Prod.snd '' V i ⊆ J i) → ∀ t ∈ Set.Icc (0 : ℝ) 1, YuiContent s r A ≤ ∑' i, (J i).indicator (fun _ : ℝ => (Metric.ediam (V i)) ^ s) t) := by
    classical
    intro X inst A s r hs V J hcover hd hJ t ht
    let W : ℕ → Set X := fun i => if t ∈ J i then Prod.fst '' V i else ∅
    have hW : A ⊆ ⋃ i, W i := by
      intro x hx
      rcases yui_nested_ab04f0ca374a82dd4506_0003 h_H001 h_H002 A V hcover x hx t ht with ⟨i, hi⟩
      have hti : t ∈ J i := hJ i ⟨(x,t), hi, rfl⟩
      exact Set.mem_iUnion.mpr ⟨i, by simpa [W, hti] using (Set.mem_image_of_mem Prod.fst hi)⟩
    have hWd : ∀ i, Metric.ediam (W i) ≤ r := by
      intro i
      dsimp [W]
      split_ifs
      · exact ((yui_nested_ab04f0ca374a82dd4506_0002 h_H001 h_H002 (V i)).1).trans (hd i)
      · simp
    refine le_trans (iInf_le_of_le W (iInf_le_of_le hW (iInf_le_of_le hWd le_rfl))) ?_
    apply ENNReal.tsum_le_tsum
    intro i
    by_cases hti : t ∈ J i
    · simpa [W, hti, Set.indicator_of_mem] using ENNReal.rpow_le_rpow (yui_nested_ab04f0ca374a82dd4506_0002 h_H001 h_H002 (V i)).1 hs.le
    · simp [W, hti, ENNReal.zero_rpow_of_pos hs]
  have yui_nested_ab04f0ca374a82dd4506_0005 (h_H001 : ∀ (μ : Measure ℝ) (f : ℕ → ℝ → ℝ≥0∞), (∀ i, AEMeasurable (f i) μ) →
   (∫⁻ t, ∑' i, f i t ∂μ) = ∑' i, ∫⁻ t, f i t ∂μ) (h_H002 : (∀ a b : ℝ, (volume : Measure ℝ) (Set.Icc a b) = ENNReal.ofReal (b - a)) ∧
   (∀ B : Set ℝ, Bornology.IsBounded B → Metric.ediam B = ENNReal.ofReal (sSup B - sInf B))) : (∀ a b c : ℝ≥0∞, b ≤ c → a * b ≤ a * c) := by
    intro a b c h
    exact mul_le_mul_right h a
  classical
  intro X inst A s r hs hr hrfin V hcover hd
  have hb : ∀ i, Bornology.IsBounded (Prod.snd '' V i) := by
    intro i
    apply Metric.isBounded_iff_ediam_ne_top.mpr
    exact ne_top_of_le_ne_top hrfin (((yui_nested_ab04f0ca374a82dd4506_0002 h_H001 h_H002 (V i)).2).trans (hd i))
  choose J hJm hJsub hJvol using fun i => yui_nested_ab04f0ca374a82dd4506_0001 h_H001 h_H002 (Prod.snd '' V i) (hb i)
  let ν : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)
  let f : ℕ → ℝ → ℝ≥0∞ := fun i => (J i).indicator (fun _ => (Metric.ediam (V i)) ^ s)
  have hfm : ∀ i, Measurable (f i) := fun i => measurable_const.indicator (hJm i)
  have hν : ν Set.univ = 1 := by
    dsimp [ν]
    rw [Measure.restrict_apply_univ, h_H002.1]
    norm_num
  have hνJ : ∀ i, ν (J i) ≤ Metric.ediam (V i) := by
    intro i
    calc
      ν (J i) ≤ (volume : Measure ℝ) (J i) := by
        dsimp [ν]
        rw [Measure.restrict_apply (hJm i)]
        exact measure_mono Set.inter_subset_left
      _ = Metric.ediam (Prod.snd '' V i) := hJvol i
      _ ≤ Metric.ediam (V i) := (yui_nested_ab04f0ca374a82dd4506_0002 h_H001 h_H002 (V i)).2
  calc
    YuiContent s r A = ∫⁻ _ : ℝ, YuiContent s r A ∂ν := by
      rw [lintegral_const, hν, mul_one]
    _ ≤ ∫⁻ t, ∑' i, f i t ∂ν := by
      apply lintegral_mono_ae
      exact (ae_restrict_mem measurableSet_Icc).mono (fun t ht => yui_nested_ab04f0ca374a82dd4506_0004 h_H001 h_H002 A s r hs V J hcover hd hJsub t ht)
    _ = ∑' i, ∫⁻ t, f i t ∂ν := h_H001 ν f (fun i => (hfm i).aemeasurable)
    _ ≤ ∑' i, (Metric.ediam (V i)) ^ (s + 1) := by
      apply ENNReal.tsum_le_tsum
      intro i
      change (∫⁻ t, (J i).indicator (fun _ : ℝ => (Metric.ediam (V i)) ^ s) t ∂ν) ≤ _
      rw [lintegral_indicator_const (hJm i)]
      calc
        (Metric.ediam (V i)) ^ s * ν (J i) ≤ (Metric.ediam (V i)) ^ s * Metric.ediam (V i) := yui_nested_ab04f0ca374a82dd4506_0005 h_H001 h_H002 _ _ _ (hνJ i)
        _ = (Metric.ediam (V i)) ^ (s + 1) := by
          rw [ENNReal.rpow_add_of_add_pos (ne_top_of_le_ne_top hrfin (hd i)) s 1 (by linarith), ENNReal.rpow_one]
set_option Elab.async false in
theorem B020 : ∀ {X : Type} [MetricSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
 (A : Set X) (s : ℝ), 0 < s →
 MeasureTheory.Measure.hausdorffMeasure s A ≤
 MeasureTheory.Measure.hausdorffMeasure (s + 1) (A ×ˢ Set.Icc (0 : ℝ) 1) := by
  classical
  have hformula :
      ∀ {Y : Type} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
        (a : ℝ) (S : Set Y), 0 < a →
        MeasureTheory.Measure.hausdorffMeasure a S =
          ⨆ (r : ℝ≥0∞) (_ : 0 < r), YuiContent a r S := by
    intro Y _ _ _ a S ha
    have hcost (T : Set Y) :
        (⨆ _ : T.Nonempty, (Metric.ediam T) ^ a) = (Metric.ediam T) ^ a := by
      by_cases h : T.Nonempty
      · simp [h]
      · rw [Set.not_nonempty_iff_eq_empty.mp h]
        simp [ENNReal.zero_rpow_of_pos ha]
    have h := YuiBasis.B001 a S
    simp only [hcost] at h
    exact h
  have hmono :
      ∀ {Y : Type} [MetricSpace Y] (a : ℝ) (S : Set Y) {r t : ℝ≥0∞},
        r ≤ t → YuiContent a t S ≤ YuiContent a r S := by
    intro Y _ a S r t hrt
    unfold YuiContent
    refine le_iInf fun U => le_iInf fun hU => le_iInf fun hdU => ?_
    exact iInf_le_of_le U (iInf_le_of_le hU
      (iInf_le_of_le (fun i => (hdU i).trans hrt) le_rfl))
  have hcontent :
      ∀ {Y : Type} [MetricSpace Y] (S : Set Y) (s : ℝ) (r : ℝ≥0∞),
        0 < s → 0 < r → r ≠ ⊤ →
        YuiContent s r S ≤ YuiContent (s + 1) r (S ×ˢ Set.Icc (0 : ℝ) 1) := by
    intro Y _ S s r hs hr hrt
    change YuiContent s r S ≤
      ⨅ (V : ℕ → Set (Y × ℝ)) (_ : S ×ˢ Set.Icc (0 : ℝ) 1 ⊆ ⋃ i, V i)
        (_ : ∀ i, Metric.ediam (V i) ≤ r), ∑' i, (Metric.ediam (V i)) ^ (s + 1)
    refine le_iInf fun V => le_iInf fun hV => le_iInf fun hdV => ?_
    exact YuiBasis.B019 S s r hs hr hrt V hV hdV
  intro X _ _ _ _ A s hs
  have hs1 : 0 < s + 1 := by linarith
  rw [hformula s A hs, hformula (s + 1) (A ×ˢ Set.Icc (0 : ℝ) 1) hs1]
  refine iSup_le fun r => iSup_le fun hr => ?_
  by_cases hrt : r = ⊤
  · subst r
    exact (hmono s A (r := 1) (t := ⊤) le_top).trans
      ((hcontent A s 1 hs zero_lt_one (by norm_num)).trans
        (le_iSup_of_le 1 (le_iSup_of_le zero_lt_one le_rfl)))
  · exact (hcontent A s r hs hr hrt).trans
      (le_iSup_of_le r (le_iSup_of_le hr le_rfl))

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
    let omitted : Array String := #["h_E003", "h_E004", "h_E005", "h_E008", "h_E010", "h_E020"]
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
theorem P (n : ℕ) (E : Set (YuiRn n)) (h_H001 : E.Nonempty ∧ IsCompact E) : dimH (YuiFeucLast n E) = dimH E + 1 := by
  exact yui_basis_export%(n, E, h_H001, (@YuiBasis.B003), (@YuiBasis.B004), (@YuiBasis.B005), (@YuiBasis.B008), (@YuiBasis.B010), (@YuiBasis.B020))

end YuiClosed
