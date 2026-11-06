import Mathlib
open scoped ENNReal NNReal Topology
open Set MeasureTheory
namespace BasisObjects
abbrev Rn (n : ℕ) := EuclideanSpace ℝ (Fin n)
noncomputable def content {X : Type*} [EMetricSpace X]
    (s : ℝ) (r : ℝ≥0∞) (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)
    (_ : ∀ i, Metric.ediam (U i) ≤ r),
      ∑' i, ⨆ (_ : (U i).Nonempty), (Metric.ediam (U i)) ^ s
def euclideanLift (n : ℕ) : Rn n × ℝ → WithLp 2 (Rn n × ℝ) :=
  WithLp.toLp 2
end BasisObjects

namespace IntervalProduct
abbrev Rn := BasisObjects.Rn
def I : Set ℝ := Set.Icc 0 1
def F (n : ℕ) (E : Set (Rn n)) : Set (Rn n × ℝ) := E ×ˢ I
def j (n : ℕ) (p : WithLp 2 (Rn n × ℝ)) : Rn (n + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => p.fst i) p.snd)
def unj (n : ℕ) (v : Rn (n + 1)) : WithLp 2 (Rn n × ℝ) :=
  WithLp.toLp 2 (WithLp.toLp 2 (fun i : Fin n => v i.castSucc), v (Fin.last n))
def G (n : ℕ) (E : Set (Rn n)) : Set (Rn (n + 1)) :=
  j n '' (BasisObjects.euclideanLift n '' F n E)
noncomputable def H {X : Type*} [MetricSpace X] (a : ℝ) (A : Set X) : ℝ≥0∞ :=
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  MeasureTheory.Measure.hausdorffMeasure a A
noncomputable def cost {ι X : Type*} [MetricSpace X] (a : ℝ) (U : ι → Set X) : ℝ≥0∞ :=
  ∑' i, ⨆ (_ : (U i).Nonempty), (Metric.ediam (U i)) ^ a
noncomputable def realCost {ι X : Type*} [MetricSpace X] (a : ℝ) (U : ι → Set X) : ℝ≥0∞ :=
  ∑' i, (ENNReal.ofReal (Metric.diam (U i))) ^ a
def Cover {X : Type*} [MetricSpace X] (δ : ℝ) (A : Set X) (U : ℕ → Set X) : Prop :=
  A ⊆ ⋃ i, U i ∧ ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ
def RealCover {X : Type*} [MetricSpace X] (δ : ℝ) (A : Set X) (U : ℕ → Set X) : Prop :=
  A ⊆ ⋃ i, U i ∧ (∀ i, Bornology.IsBounded (U i)) ∧ ∀ i, Metric.diam (U i) ≤ δ
end IntervalProduct
open IntervalProduct

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace Translation
set_option autoImplicit false

namespace Local_T001
theorem yui_aux_0001 (n : ℕ) (E : Set (BasisObjects.Rn n)) : yui_aux_type% "∀ (X : Type*) [MetricSpace X] (S : Set X) (δ : ℝ), 0 < δ → (Metric.ediam S ≤ ENNReal.ofReal δ ↔ Bornology.IsBounded S ∧ Metric.diam S ≤ δ)" := by
  intro X _ S δ hδ
  constructor
  · intro h
    have hf : Metric.ediam S ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
    exact ⟨Metric.isBounded_iff_ediam_ne_top.mpr hf, ENNReal.toReal_le_of_le_ofReal hδ.le h⟩
  · rintro ⟨hb, hd⟩
    have he : ENNReal.ofReal (Metric.diam S) = Metric.ediam S := ENNReal.ofReal_toReal hb.ediam_ne_top
    rw [← he]
    exact ENNReal.ofReal_le_ofReal hd

theorem yui_aux_0002 (n : ℕ) (E : Set (BasisObjects.Rn n)) : yui_aux_type% "∀ (X : Type*) [MetricSpace X] (ι : Type*) (a : ℝ), 0 < a → ∀ U : ι → Set X, (∀ i, Bornology.IsBounded (U i)) → cost a U = realCost a U" := by
  intro X _ ι a ha U hb
  classical
  unfold cost realCost
  apply tsum_congr
  intro i
  have he : ENNReal.ofReal (Metric.diam (U i)) = Metric.ediam (U i) := ENNReal.ofReal_toReal (hb i).ediam_ne_top
  rw [he]
  by_cases hn : (U i).Nonempty
  · simp [hn]
  · have hz : U i = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    simp [hz, ENNReal.zero_rpow_of_pos ha]

theorem yui_aux_0003 (n : ℕ) (E : Set (BasisObjects.Rn n)) : yui_aux_type% "∀ (X : Type*) [MetricSpace X] (A : Set X) (a : ℝ), (∀ r s : ℝ≥0∞, r ≤ s → BasisObjects.content a s A ≤ BasisObjects.content a r A) ∧ (∀ (r : ℝ≥0∞) (U : ℕ → Set X), A ⊆ ⋃ i, U i → (∀ i, Metric.ediam (U i) ≤ r) → BasisObjects.content a r A ≤ cost a U) ∧ (∀ (r b : ℝ≥0∞), (∀ U : ℕ → Set X, A ⊆ ⋃ i, U i → (∀ i, Metric.ediam (U i) ≤ r) → b ≤ cost a U) → b ≤ BasisObjects.content a r A)" := by
  intro X _ A a
  have upper : ∀ (r : ℝ≥0∞) (U : ℕ → Set X), A ⊆ ⋃ i, U i → (∀ i, Metric.ediam (U i) ≤ r) → BasisObjects.content a r A ≤ cost a U := by
    intro r U hc hd
    exact iInf_le_of_le U (iInf_le_of_le hc (iInf_le_of_le hd le_rfl))
  have lower : ∀ (r b : ℝ≥0∞), (∀ U : ℕ → Set X, A ⊆ ⋃ i, U i → (∀ i, Metric.ediam (U i) ≤ r) → b ≤ cost a U) → b ≤ BasisObjects.content a r A := by
    intro r b h
    exact le_iInf fun U => le_iInf fun hc => le_iInf fun hd => h U hc hd
  refine ⟨?_, upper, lower⟩
  intro r s hrs
  apply lower
  intro U hc hd
  exact upper s U hc (fun i => (hd i).trans hrs)

theorem yui_aux_0004 (n : ℕ) (E : Set (BasisObjects.Rn n)) : yui_aux_type% "∀ (X : Type*) [MetricSpace X] (A : Set X) (a : ℝ), 0 < a → ∀ δ : ℝ, 0 < δ → BasisObjects.content a (ENNReal.ofReal δ) A = ⨅ (U : ℕ → Set X) (_ : RealCover δ A U), realCost a U" := by
  intro X _ A a ha δ hδ
  rcases yui_aux_0003 n E X A a with ⟨hm, hu, hl⟩
  apply le_antisymm
  · refine le_iInf fun U => le_iInf fun hc => ?_
    have hd : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ := fun i => (yui_aux_0001 n E X (U i) δ hδ).mpr ⟨hc.2.1 i, hc.2.2 i⟩
    rw [← yui_aux_0002 n E X ℕ a ha U hc.2.1]
    exact hu _ U hc.1 hd
  · apply hl
    intro U hc hd
    have hb : ∀ i, Bornology.IsBounded (U i) ∧ Metric.diam (U i) ≤ δ := fun i => (yui_aux_0001 n E X (U i) δ hδ).mp (hd i)
    have hr : RealCover δ A U := ⟨hc, fun i => (hb i).1, fun i => (hb i).2⟩
    rw [yui_aux_0002 n E X ℕ a ha U (fun i => (hb i).1)]
    exact iInf_le_of_le U (iInf_le_of_le hr le_rfl)

theorem yui_aux_0005 (n : ℕ) (E : Set (BasisObjects.Rn n)) : yui_aux_type% "∀ (X : Type*) (ι : Type*) [Countable ι] (V : ι → Set X), ∃ e : ι ↪ ℕ, ∃ U : ℕ → Set X, (∀ k, U (e k) = V k) ∧ (∀ i, i ∉ Set.range e → U i = ∅) ∧ (⋃ i, U i) = (⋃ k, V k) ∧ (∀ w : Set X → ℝ≥0∞, w ∅ = 0 → (∑' i, w (U i)) = ∑' k, w (V k))" := by
  intro X ι _ V
  classical
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat ι
  let e : ι ↪ ℕ := ⟨f, hf⟩
  let U : ℕ → Set X := fun i => ⋃ k, ⋃ (_ : e k = i), V k
  have he : ∀ k, U (e k) = V k := by
    intro k
    simp [U, e.injective.eq_iff]
  have hz : ∀ i, i ∉ Set.range e → U i = ∅ := by
    intro i hi
    have hne : ∀ k, e k ≠ i := fun k hk => hi ⟨k, hk⟩
    simp [U, hne]
  refine ⟨e, U, he, hz, ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
      rcases Set.mem_iUnion.mp hi with ⟨k, hk⟩
      rcases Set.mem_iUnion.mp hk with ⟨_, hv⟩
      exact Set.mem_iUnion.mpr ⟨k, hv⟩
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨k, hk⟩
      exact Set.mem_iUnion.mpr ⟨e k, by rwa [he]⟩
  · intro w hw
    have hs : Function.support (fun i => w (U i)) ⊆ Set.range e := by
      intro i hi
      by_contra hn
      exact hi (by change w (U i) = 0; rw [hz i hn, hw])
    calc
      (∑' i, w (U i)) = ∑' k, w (U (e k)) := (e.injective.tsum_eq hs).symm
      _ = ∑' k, w (V k) := tsum_congr (fun k => congrArg w (he k))

theorem yui_aux_0006 (n : ℕ) (E : Set (BasisObjects.Rn n)) : yui_aux_type% "∀ (X : Type*) [MetricSpace X] (A : Set X) (a : ℝ), H a A = ⨆ (δ : ℝ) (_ : 0 < δ), BasisObjects.content a (ENNReal.ofReal δ) A" := by
  intro X _ A a
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  have hh : H a A = ⨆ (r : ℝ≥0∞) (_ : 0 < r), BasisObjects.content a r A := MeasureTheory.Measure.hausdorffMeasure_apply a A
  rw [hh]
  have hm := (yui_aux_0003 n E X A a).1
  apply le_antisymm
  · refine iSup_le fun r => iSup_le fun hr => ?_
    by_cases hf : r = ⊤
    · subst r
      exact (hm (ENNReal.ofReal 1) ⊤ le_top).trans (le_iSup₂_of_le (1 : ℝ) zero_lt_one le_rfl)
    · have hp : 0 < r.toReal := ENNReal.toReal_pos (ne_of_gt hr) hf
      exact le_iSup₂_of_le r.toReal hp (by rw [ENNReal.ofReal_toReal hf])
  · refine iSup_le fun δ => iSup_le fun hδ => ?_
    exact le_iSup₂_of_le (ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδ) le_rfl

theorem yui_aux_0007 (n : ℕ) (E : Set (BasisObjects.Rn n)) : yui_aux_type% "∀ (X : Type*) [MetricSpace X] (A : Set X) (a δ : ℝ), 0 < δ → (BasisObjects.content a (ENNReal.ofReal δ) A = 0 ↔ ∀ ε : ℝ, 0 < ε → ∃ U : ℕ → Set X, Cover δ A U ∧ cost a U < ENNReal.ofReal ε)" := by
  intro X _ A a δ hδ
  constructor
  · intro hc ε hε
    have hl : BasisObjects.content a (ENNReal.ofReal δ) A < ENNReal.ofReal ε := by
      rw [hc]
      exact ENNReal.ofReal_pos.mpr hε
    unfold BasisObjects.content at hl
    simp only [iInf_lt_iff] at hl
    rcases hl with ⟨U, hc, hd, hu⟩
    exact ⟨U, ⟨hc, hd⟩, hu⟩
  · intro hc
    by_contra hn
    have hp : 0 < BasisObjects.content a (ENNReal.ofReal δ) A := bot_lt_iff_ne_bot.mpr hn
    obtain ⟨ε, _, hε, hlt⟩ := ENNReal.lt_iff_exists_real_btwn.mp hp
    obtain ⟨U, hU, hcost⟩ := hc ε (ENNReal.ofReal_pos.mp hε)
    have hup : BasisObjects.content a (ENNReal.ofReal δ) A ≤ cost a U := (yui_aux_0003 n E X A a).2.1 _ U hU.1 hU.2
    exact (not_lt_of_ge hup) (hcost.trans hlt)

end Local_T001
open Local_T001 in
theorem T001 (n : ℕ) (E : Set (BasisObjects.Rn n))  :
    ∀ (X : Type*) [MetricSpace X] (A : Set X) (a : ℝ), 0 < a →
  (∀ δ : ℝ, 0 < δ →
    BasisObjects.content a (ENNReal.ofReal δ) A =
      ⨅ (U : ℕ → Set X) (_ : RealCover δ A U), realCost a U) ∧
  (∀ (ι : Type*) [Countable ι] (V : ι → Set X),
    ∃ e : ι ↪ ℕ, ∃ U : ℕ → Set X,
      (∀ k, U (e k) = V k) ∧
      (∀ i, i ∉ Set.range e → U i = ∅) ∧
      (⋃ i, U i) = (⋃ k, V k) ∧
      cost a U = cost a V ∧ realCost a U = realCost a V) ∧
  (∀ δ₁ δ₂ : ℝ, 0 < δ₁ → δ₁ ≤ δ₂ →
    BasisObjects.content a (ENNReal.ofReal δ₂) A ≤
      BasisObjects.content a (ENNReal.ofReal δ₁) A) ∧
  (∀ (δ : ℝ) (U : ℕ → Set X), 0 < δ → Cover δ A U →
    BasisObjects.content a (ENNReal.ofReal δ) A ≤ cost a U) ∧
  (∀ (δ : ℝ) (b : ℝ≥0∞), 0 < δ →
    (∀ U : ℕ → Set X, Cover δ A U → b ≤ cost a U) →
      b ≤ BasisObjects.content a (ENNReal.ofReal δ) A) ∧
  (H a A = ⨆ (δ : ℝ) (_ : 0 < δ), BasisObjects.content a (ENNReal.ofReal δ) A) ∧
  (∀ δ : ℝ, 0 < δ → BasisObjects.content a (ENNReal.ofReal δ) A ≤ H a A) ∧
  (∀ δ : ℝ, 0 < δ →
    (BasisObjects.content a (ENNReal.ofReal δ) A = 0 ↔
      ∀ ε : ℝ, 0 < ε → ∃ U : ℕ → Set X, Cover δ A U ∧ cost a U < ENNReal.ofReal ε)) ∧
  (H a A = 0 ↔
    ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
      ∃ U : ℕ → Set X, Cover δ A U ∧ cost a U < ENNReal.ofReal ε) := by
  intro X inst A a ha
  classical
  rcases yui_aux_0003 n E X A a with ⟨hm, hu, hl⟩
  have hh := yui_aux_0006 n E X A a
  have hle : ∀ δ : ℝ, 0 < δ → BasisObjects.content a (ENNReal.ofReal δ) A ≤ H a A := by
    intro δ hδ
    rw [hh]
    exact le_iSup₂_of_le δ hδ le_rfl
  have hz := yui_aux_0007 n E X A a
  refine ⟨yui_aux_0004 n E X A a ha, ?_, ?_, ?_, ?_, hh, hle, hz, ?_⟩
  · intro ι hι V
    obtain ⟨e, U, he, hempty, hunion, hs⟩ := yui_aux_0005 n E X ι V
    refine ⟨e, U, he, hempty, hunion, ?_, ?_⟩
    · exact hs (fun S => ⨆ (_ : S.Nonempty), (Metric.ediam S) ^ a) (by simp)
    · exact hs (fun S => (ENNReal.ofReal (Metric.diam S)) ^ a) (by simp [ENNReal.zero_rpow_of_pos ha])
  · intro δ₁ δ₂ hδ₁ hδ
    exact hm _ _ (ENNReal.ofReal_le_ofReal hδ)
  · intro δ U hδ hU
    exact hu _ U hU.1 hU.2
  · intro δ b hδ hb
    exact hl _ b (fun U hc hd => hb U ⟨hc, hd⟩)
  · constructor
    · intro hH δ hδ
      apply (hz δ hδ).mp
      apply le_antisymm
      · simpa only [hH] using hle δ hδ
      · exact bot_le
    · intro hc
      rw [hh]
      apply le_antisymm
      · exact iSup_le fun δ => iSup_le fun hδ => le_of_eq ((hz δ hδ).mpr (hc δ hδ))
      · exact bot_le

#check @T001
#print axioms T001

end Translation
