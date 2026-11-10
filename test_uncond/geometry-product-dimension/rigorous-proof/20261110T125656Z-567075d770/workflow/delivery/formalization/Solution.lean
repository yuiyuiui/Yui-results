import Mathlib
open scoped ENNReal NNReal MeasureTheory
open Set MeasureTheory
noncomputable section
namespace ProductInterval
abbrev V (n : ℕ) := EuclideanSpace ℝ (Fin n)
def interval : Set ℝ := Set.Icc 0 1
def appendCoord (n : ℕ) (p : V n × ℝ) : V (n + 1) :=
  (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm
    (Fin.snoc ((EuclideanSpace.equiv (Fin n) ℝ) p.1) p.2)
def euclideanProduct (n : ℕ) (E : Set (V n)) : Set (V (n + 1)) :=
  appendCoord n '' (E ×ˢ interval)
end ProductInterval
namespace ProductInterval
def F (n : ℕ) (E : Set (V n)) : Set (V n × ℝ) := E ×ˢ interval
def D (n : ℕ) (E : Set (V n)) : ℝ := (dimH E).toReal
end ProductInterval

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace Translation
set_option autoImplicit false

theorem T001 (n : ℕ) (E : Set (ProductInterval.V n)) (h_E008 : (∀ (n : ℕ) (E : Set (ProductInterval.V n)), dimH E ≤ (n : ℝ≥0∞)) ∧
 dimH ProductInterval.interval = 1) :
    0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ (n : ℝ≥0∞) < ∞ ∧ dimH ProductInterval.interval = 1 ∧ 0 ≤ ProductInterval.D n E ∧ ProductInterval.D n E ≤ (n : ℝ) ∧ ENNReal.ofReal (ProductInterval.D n E) = dimH E := by
  have hbound : dimH E ≤ (n : ℝ≥0∞) := h_E008.1 n E
  have hn : (n : ℝ≥0∞) < ∞ := ENNReal.natCast_lt_top n
  have hfinite : dimH E ≠ ∞ := ne_of_lt (lt_of_le_of_lt hbound hn)
  have hreal : (dimH E).toReal ≤ (n : ℝ) := by
    simpa only [ENNReal.toReal_natCast] using
      (ENNReal.toReal_mono (ENNReal.natCast_ne_top n) hbound)
  have hinverse : ENNReal.ofReal ((dimH E).toReal) = dimH E :=
    ENNReal.ofReal_toReal hfinite
  exact ⟨bot_le, hbound, hn, h_E008.2, ENNReal.toReal_nonneg, hreal, hinverse⟩

namespace Local_T002
theorem yui_aux_0001 (n : ℕ) (E : Set (ProductInterval.V n)) (h_T001 : 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ (n : ℝ≥0∞) < ∞ ∧ dimH ProductInterval.interval = 1 ∧ 0 ≤ ProductInterval.D n E ∧ ProductInterval.D n E ≤ (n : ℝ) ∧ ENNReal.ofReal (ProductInterval.D n E) = dimH E) (h_M002 : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (A : Set X) (a : ℝ≥0),
(dimH A < (a : ℝ≥0∞) → MeasureTheory.Measure.hausdorffMeasure (a : ℝ) A = 0) ∧
((a : ℝ≥0∞) < dimH A → MeasureTheory.Measure.hausdorffMeasure (a : ℝ) A = ∞) ∧
(MeasureTheory.Measure.hausdorffMeasure (a : ℝ) A = 0 → dimH A ≤ (a : ℝ≥0∞)) ∧
(MeasureTheory.Measure.hausdorffMeasure (a : ℝ) A = ∞ → (a : ℝ≥0∞) ≤ dimH A)) (h_E003 : ∀ (n : ℕ) (E : Set (ProductInterval.V n)) (q : ℝ), 0 < q →
 MeasureTheory.Measure.hausdorffMeasure q E = 0 →
 MeasureTheory.Measure.hausdorffMeasure (q + 1) (E ×ˢ ProductInterval.interval) = 0) : yui_aux_type% "∀ (r : ℝ) (hr : 0 ≤ r), (↑(NNReal.mk r hr) : ℝ≥0∞) = ENNReal.ofReal r" := by
  intro r hr
  exact ENNReal.coe_nnreal_eq (NNReal.mk r hr)

end Local_T002
open Local_T002 in
theorem T002 (n : ℕ) (E : Set (ProductInterval.V n)) (h_T001 : 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ (n : ℝ≥0∞) < ∞ ∧ dimH ProductInterval.interval = 1 ∧ 0 ≤ ProductInterval.D n E ∧ ProductInterval.D n E ≤ (n : ℝ) ∧ ENNReal.ofReal (ProductInterval.D n E) = dimH E) (h_M002 : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (A : Set X) (a : ℝ≥0),
(dimH A < (a : ℝ≥0∞) → MeasureTheory.Measure.hausdorffMeasure (a : ℝ) A = 0) ∧
((a : ℝ≥0∞) < dimH A → MeasureTheory.Measure.hausdorffMeasure (a : ℝ) A = ∞) ∧
(MeasureTheory.Measure.hausdorffMeasure (a : ℝ) A = 0 → dimH A ≤ (a : ℝ≥0∞)) ∧
(MeasureTheory.Measure.hausdorffMeasure (a : ℝ) A = ∞ → (a : ℝ≥0∞) ≤ dimH A)) (h_E003 : ∀ (n : ℕ) (E : Set (ProductInterval.V n)) (q : ℝ), 0 < q →
 MeasureTheory.Measure.hausdorffMeasure q E = 0 →
 MeasureTheory.Measure.hausdorffMeasure (q + 1) (E ×ˢ ProductInterval.interval) = 0) :
    ∀ b : ℝ, ProductInterval.D n E < b → dimH (ProductInterval.F n E) ≤ ENNReal.ofReal (b + 1) := by
  intro b hb
  rcases (id h_T001) with ⟨h_dim_nonneg, h_dim_le, h_n_fin, h_interval, hD, hD_le, hD_eq⟩
  have hb_pos : 0 < b := lt_of_le_of_lt hD hb
  let a : ℝ≥0 := ⟨b, le_of_lt hb_pos⟩
  have ha : (a : ℝ≥0∞) = ENNReal.ofReal b :=
    @yui_aux_0001 n E h_T001 h_M002 h_E003 b (le_of_lt hb_pos)
  have hdim : dimH E < (a : ℝ≥0∞) := by
    rw [ha, ← hD_eq]
    exact (ENNReal.ofReal_lt_ofReal_iff hb_pos).2 hb
  have hz : MeasureTheory.Measure.hausdorffMeasure b E = 0 :=
    (h_M002 (ProductInterval.V n) E a).1 hdim
  have hz_prod : MeasureTheory.Measure.hausdorffMeasure (b + 1) (ProductInterval.F n E) = 0 :=
    h_E003 n E b hb_pos hz
  have hc_nonneg : 0 ≤ b + 1 := by linarith
  let c : ℝ≥0 := ⟨b + 1, hc_nonneg⟩
  have hc : (c : ℝ≥0∞) = ENNReal.ofReal (b + 1) :=
    @yui_aux_0001 n E h_T001 h_M002 h_E003 (b + 1) hc_nonneg
  have hbound : dimH (ProductInterval.F n E) ≤ (c : ℝ≥0∞) :=
    (h_M002 (ProductInterval.V n × ℝ) (ProductInterval.F n E) c).2.2.1 hz_prod
  exact hc ▸ hbound

theorem T003 (n : ℕ) (E : Set (ProductInterval.V n)) (h_T001 : 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ (n : ℝ≥0∞) < ∞ ∧ dimH ProductInterval.interval = 1 ∧ 0 ≤ ProductInterval.D n E ∧ ProductInterval.D n E ≤ (n : ℝ) ∧ ENNReal.ofReal (ProductInterval.D n E) = dimH E) (h_T002 : ∀ b : ℝ, ProductInterval.D n E < b → dimH (ProductInterval.F n E) ≤ ENNReal.ofReal (b + 1)) :
    dimH (ProductInterval.F n E) ≤ dimH E + 1 := by
  rcases h_T001 with ⟨_, _, _, _, hD, _, hD_eq⟩
  have hfinite : dimH (ProductInterval.F n E) < ∞ :=
    lt_of_le_of_lt (h_T002 (ProductInterval.D n E + 1) (by linarith)) ENNReal.ofReal_lt_top
  let T : ℝ := (dimH (ProductInterval.F n E)).toReal
  have hT_nonneg : 0 ≤ T := ENNReal.toReal_nonneg
  have hT_eq : ENNReal.ofReal T = dimH (ProductInterval.F n E) :=
    ENNReal.ofReal_toReal (ne_of_lt hfinite)
  have hbound : ∀ b : ℝ, ProductInterval.D n E < b → T ≤ b + 1 := by
    intro b hb
    have hb_nonneg : 0 ≤ b + 1 := by linarith
    exact ENNReal.toReal_le_of_le_ofReal hb_nonneg (h_T002 b hb)
  have hT_le : T ≤ ProductInterval.D n E + 1 := by
    by_contra h
    have hstrict : ProductInterval.D n E + 1 < T := lt_of_not_ge h
    let u : ℝ := (ProductInterval.D n E + T - 1) / 2
    have hu_lower : ProductInterval.D n E < u := by dsimp [u]; linarith
    have hu_upper : u < T - 1 := by dsimp [u]; linarith
    have hu_bound := hbound u hu_lower
    linarith
  calc
    dimH (ProductInterval.F n E) = ENNReal.ofReal T := hT_eq.symm
    _ ≤ ENNReal.ofReal (ProductInterval.D n E + 1) := ENNReal.ofReal_le_ofReal hT_le
    _ = ENNReal.ofReal (ProductInterval.D n E) + ENNReal.ofReal 1 :=
      ENNReal.ofReal_add hD (by norm_num)
    _ = dimH E + 1 := by rw [hD_eq]; norm_num

namespace Local_T004
theorem yui_aux_0001 (n : ℕ) (E : Set (ProductInterval.V n)) (h_T001 : 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ (n : ℝ≥0∞) < ∞ ∧ dimH ProductInterval.interval = 1 ∧ 0 ≤ ProductInterval.D n E ∧ ProductInterval.D n E ≤ (n : ℝ) ∧ ENNReal.ofReal (ProductInterval.D n E) = dimH E) (h_M002 : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (A : Set X) (a : ℝ≥0),
(dimH A < (a : ℝ≥0∞) → MeasureTheory.Measure.hausdorffMeasure (a : ℝ) A = 0) ∧
((a : ℝ≥0∞) < dimH A → MeasureTheory.Measure.hausdorffMeasure (a : ℝ) A = ∞) ∧
(MeasureTheory.Measure.hausdorffMeasure (a : ℝ) A = 0 → dimH A ≤ (a : ℝ≥0∞)) ∧
(MeasureTheory.Measure.hausdorffMeasure (a : ℝ) A = ∞ → (a : ℝ≥0∞) ≤ dimH A)) (h_E004 : ∀ (n : ℕ) (E : Set (ProductInterval.V n)) (s : ℝ), 0 < s →
 MeasureTheory.Measure.hausdorffMeasure s E ≤
 MeasureTheory.Measure.hausdorffMeasure (s + 1) (E ×ˢ ProductInterval.interval)) : yui_aux_type% "∀ (x : Real) (hx : 0 ≤ x), ENNReal.ofNNReal (NNReal.mk x hx) = ENNReal.ofReal x" := by
  intro x hx
  exact ENNReal.coe_nnreal_eq (NNReal.mk x hx)

end Local_T004
open Local_T004 in
theorem T004 (n : ℕ) (E : Set (ProductInterval.V n)) (h_T001 : 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ (n : ℝ≥0∞) < ∞ ∧ dimH ProductInterval.interval = 1 ∧ 0 ≤ ProductInterval.D n E ∧ ProductInterval.D n E ≤ (n : ℝ) ∧ ENNReal.ofReal (ProductInterval.D n E) = dimH E) (h_M002 : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (A : Set X) (a : ℝ≥0),
(dimH A < (a : ℝ≥0∞) → MeasureTheory.Measure.hausdorffMeasure (a : ℝ) A = 0) ∧
((a : ℝ≥0∞) < dimH A → MeasureTheory.Measure.hausdorffMeasure (a : ℝ) A = ∞) ∧
(MeasureTheory.Measure.hausdorffMeasure (a : ℝ) A = 0 → dimH A ≤ (a : ℝ≥0∞)) ∧
(MeasureTheory.Measure.hausdorffMeasure (a : ℝ) A = ∞ → (a : ℝ≥0∞) ≤ dimH A)) (h_E004 : ∀ (n : ℕ) (E : Set (ProductInterval.V n)) (s : ℝ), 0 < s →
 MeasureTheory.Measure.hausdorffMeasure s E ≤
 MeasureTheory.Measure.hausdorffMeasure (s + 1) (E ×ˢ ProductInterval.interval)) :
    0 < dimH E → 0 < ProductInterval.D n E ∧ ∀ b : ℝ, 0 < b → b < ProductInterval.D n E → ENNReal.ofReal (b + 1) ≤ dimH (ProductInterval.F n E) := by
  intro hpos
  have hconvert := @yui_aux_0001 n E h_T001 h_M002 h_E004
  rcases h_T001 with ⟨_, _, _, _, hDnonneg, _, hDdim⟩
  have hDpos : 0 < ProductInterval.D n E := ENNReal.ofReal_pos.mp (by
    rw [hDdim]
    exact hpos)
  refine ⟨hDpos, ?_⟩
  intro b hb hbD
  have hbnonneg : 0 ≤ b := le_of_lt hb
  have hbconv : ENNReal.ofNNReal (NNReal.mk b hbnonneg) = ENNReal.ofReal b :=
    hconvert b hbnonneg
  have hbcompare : ENNReal.ofNNReal (NNReal.mk b hbnonneg) < dimH E := by
    rw [hbconv, ← hDdim]
    exact (ENNReal.ofReal_lt_ofReal_iff hDpos).2 hbD
  have hmu : MeasureTheory.Measure.hausdorffMeasure b E = ∞ :=
    (h_M002 (ProductInterval.V n) E (NNReal.mk b hbnonneg)).2.1 hbcompare
  have hmuF : MeasureTheory.Measure.hausdorffMeasure (b + 1) (ProductInterval.F n E) = ∞ := by
    apply top_unique
    change ∞ ≤ MeasureTheory.Measure.hausdorffMeasure (b + 1) (E ×ˢ ProductInterval.interval)
    rw [← hmu]
    exact h_E004 n E b hb
  have hb1nonneg : 0 ≤ b + 1 := by linarith
  have hb1conv : ENNReal.ofNNReal (NNReal.mk (b + 1) hb1nonneg) = ENNReal.ofReal (b + 1) :=
    hconvert (b + 1) hb1nonneg
  have hbound : ENNReal.ofNNReal (NNReal.mk (b + 1) hb1nonneg) ≤ dimH (ProductInterval.F n E) :=
    (h_M002 (ProductInterval.V n × ℝ) (ProductInterval.F n E)
      (NNReal.mk (b + 1) hb1nonneg)).2.2.2 hmuF
  rw [hb1conv] at hbound
  exact hbound

namespace Local_T005
theorem yui_aux_0001 (n : ℕ) (E : Set (ProductInterval.V n)) (h_T001 : 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ (n : ℝ≥0∞) < ∞ ∧ dimH ProductInterval.interval = 1 ∧ 0 ≤ ProductInterval.D n E ∧ ProductInterval.D n E ≤ (n : ℝ) ∧ ENNReal.ofReal (ProductInterval.D n E) = dimH E) (h_T004 : 0 < dimH E → 0 < ProductInterval.D n E ∧ ∀ b : ℝ, 0 < b → b < ProductInterval.D n E → ENNReal.ofReal (b + 1) ≤ dimH (ProductInterval.F n E)) : yui_aux_type% "dimH E + 1 = ENNReal.ofReal (ProductInterval.D n E + 1)" := by
  rw [ENNReal.ofReal_add h_T001.2.2.2.2.1 (by norm_num : (0 : ℝ) ≤ 1), h_T001.2.2.2.2.2.2]
  norm_num

end Local_T005
open Local_T005 in
theorem T005 (n : ℕ) (E : Set (ProductInterval.V n)) (h_T001 : 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ (n : ℝ≥0∞) < ∞ ∧ dimH ProductInterval.interval = 1 ∧ 0 ≤ ProductInterval.D n E ∧ ProductInterval.D n E ≤ (n : ℝ) ∧ ENNReal.ofReal (ProductInterval.D n E) = dimH E) (h_T004 : 0 < dimH E → 0 < ProductInterval.D n E ∧ ∀ b : ℝ, 0 < b → b < ProductInterval.D n E → ENNReal.ofReal (b + 1) ≤ dimH (ProductInterval.F n E)) :
    0 < dimH E → dimH E + 1 ≤ dimH (ProductInterval.F n E) := by
  intro hpos
  by_contra hnot
  have hlt : dimH (ProductInterval.F n E) < dimH E + 1 := lt_of_not_ge hnot
  have hendpoint : dimH E + 1 = ENNReal.ofReal (ProductInterval.D n E + 1) :=
    yui_aux_0001 n E h_T001 h_T004
  rw [hendpoint] at hlt
  have hfinite : dimH (ProductInterval.F n E) < ∞ :=
    lt_trans hlt ENNReal.ofReal_lt_top
  let T : ℝ := (dimH (ProductInterval.F n E)).toReal
  have hTnonneg : 0 ≤ T := ENNReal.toReal_nonneg
  have hTeq : ENNReal.ofReal T = dimH (ProductInterval.F n E) :=
    ENNReal.ofReal_toReal (ne_of_lt hfinite)
  obtain ⟨hDpos, hlower⟩ := h_T004 hpos
  have hD1pos : 0 < ProductInterval.D n E + 1 := by linarith
  have hTlt : T < ProductInterval.D n E + 1 := by
    apply (ENNReal.ofReal_lt_ofReal_iff hD1pos).mp
    rwa [hTeq]
  let v : ℝ := max 0 (T - 1)
  let s0 : ℝ := (v + ProductInterval.D n E) / 2
  have hvnonneg : 0 ≤ v := le_max_left _ _
  have hTv : T - 1 ≤ v := le_max_right _ _
  have hvlt : v < ProductInterval.D n E := by
    exact max_lt_iff.mpr ⟨hDpos, by linarith⟩
  have hspos : 0 < s0 := by dsimp [s0]; linarith
  have hslt : s0 < ProductInterval.D n E := by dsimp [s0]; linarith
  have hvs : v < s0 := by dsimp [s0]; linarith
  have hbound : ENNReal.ofReal (s0 + 1) ≤ ENNReal.ofReal T := by
    rw [hTeq]
    exact hlower s0 hspos hslt
  have hrealbound : s0 + 1 ≤ T :=
    (ENNReal.ofReal_le_ofReal_iff hTnonneg).mp hbound
  linarith

theorem T006 (n : ℕ) (E : Set (ProductInterval.V n)) (h_H002 : E.Nonempty) (h_T001 : 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ (n : ℝ≥0∞) < ∞ ∧ dimH ProductInterval.interval = 1 ∧ 0 ≤ ProductInterval.D n E ∧ ProductInterval.D n E ≤ (n : ℝ) ∧ ENNReal.ofReal (ProductInterval.D n E) = dimH E) (h_M012 : ∀ (X : Type) [MetricSpace X] (A B : Set X), A ⊆ B → dimH A ≤ dimH B) (h_M013 : ∀ (X Y : Type) [MetricSpace X] [MetricSpace Y] (f : X → Y), Isometry f →
 ∀ (S : Set X), dimH (f '' S) = dimH S) :
    1 ≤ dimH (ProductInterval.F n E) := by
  rcases h_H002 with ⟨x₀, hx₀⟩
  let f : ℝ → ProductInterval.V n × ℝ := fun t => (x₀, t)
  have hf : Isometry f := by
    apply isometry_iff_dist_eq.mpr
    intro t u
    simp only [f, Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
  have himage : dimH (f '' ProductInterval.interval) = dimH ProductInterval.interval :=
    h_M013 ℝ (ProductInterval.V n × ℝ) f hf ProductInterval.interval
  have hsub : f '' ProductInterval.interval ⊆ ProductInterval.F n E := by
    rintro p ⟨t, ht, rfl⟩
    exact ⟨hx₀, ht⟩
  have hmono : dimH (f '' ProductInterval.interval) ≤ dimH (ProductInterval.F n E) :=
    h_M012 (ProductInterval.V n × ℝ) (f '' ProductInterval.interval)
      (ProductInterval.F n E) hsub
  rw [himage, h_T001.2.2.2.1] at hmono
  exact hmono

theorem T007 (n : ℕ) (E : Set (ProductInterval.V n)) (h_T001 : 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ (n : ℝ≥0∞) < ∞ ∧ dimH ProductInterval.interval = 1 ∧ 0 ≤ ProductInterval.D n E ∧ ProductInterval.D n E ≤ (n : ℝ) ∧ ENNReal.ofReal (ProductInterval.D n E) = dimH E) (h_T005 : 0 < dimH E → dimH E + 1 ≤ dimH (ProductInterval.F n E)) (h_T006 : 1 ≤ dimH (ProductInterval.F n E)) :
    dimH E + 1 ≤ dimH (ProductInterval.F n E) := by
  have hDnonneg : 0 ≤ ProductInterval.D n E := h_T001.2.2.2.2.1
  have hDdim : ENNReal.ofReal (ProductInterval.D n E) = dimH E := h_T001.2.2.2.2.2.2
  have hcases : 0 < ProductInterval.D n E ∨ ProductInterval.D n E = 0 := by
    rcases lt_or_eq_of_le hDnonneg with hpos | hzero
    · exact Or.inl hpos
    · exact Or.inr hzero.symm
  rcases hcases with hpos | hzero
  · apply h_T005
    rw [← hDdim]
    exact ENNReal.ofReal_pos.mpr hpos
  · have hdimzero : dimH E = 0 := by
      rw [← hDdim, hzero]
      simp
    simpa [hdimzero] using h_T006

theorem T008 (n : ℕ) (E : Set (ProductInterval.V n)) (h_T003 : dimH (ProductInterval.F n E) ≤ dimH E + 1) (h_T007 : dimH E + 1 ≤ dimH (ProductInterval.F n E)) :
    dimH (ProductInterval.F n E) = dimH E + 1 := by
  exact le_antisymm h_T003 h_T007

theorem T009 (n : ℕ) (E : Set (ProductInterval.V n)) (h_E005 : ∀ (n : ℕ) (S : Set (ProductInterval.V n × ℝ)),
 dimH (ProductInterval.appendCoord n '' S) = dimH S) :
    dimH (ProductInterval.euclideanProduct n E) = dimH (ProductInterval.F n E) := by
  simpa only [ProductInterval.euclideanProduct, ProductInterval.F] using
    h_E005 n (ProductInterval.F n E)

theorem T010 (n : ℕ) (E : Set (ProductInterval.V n)) (h_T008 : dimH (ProductInterval.F n E) = dimH E + 1) (h_T009 : dimH (ProductInterval.euclideanProduct n E) = dimH (ProductInterval.F n E)) :
    dimH (ProductInterval.euclideanProduct n E) = dimH E + 1 := by
  exact h_T009.trans h_T008

set_option Elab.async false in
theorem P (n : ℕ) (E : Set (ProductInterval.V n)) (h_H001 : IsCompact E) (h_H002 : E.Nonempty) (h_M002 : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (A : Set X) (a : ℝ≥0),
(dimH A < (a : ℝ≥0∞) → MeasureTheory.Measure.hausdorffMeasure (a : ℝ) A = 0) ∧
((a : ℝ≥0∞) < dimH A → MeasureTheory.Measure.hausdorffMeasure (a : ℝ) A = ∞) ∧
(MeasureTheory.Measure.hausdorffMeasure (a : ℝ) A = 0 → dimH A ≤ (a : ℝ≥0∞)) ∧
(MeasureTheory.Measure.hausdorffMeasure (a : ℝ) A = ∞ → (a : ℝ≥0∞) ≤ dimH A)) (h_E003 : ∀ (n : ℕ) (E : Set (ProductInterval.V n)) (q : ℝ), 0 < q →
 MeasureTheory.Measure.hausdorffMeasure q E = 0 →
 MeasureTheory.Measure.hausdorffMeasure (q + 1) (E ×ˢ ProductInterval.interval) = 0) (h_E004 : ∀ (n : ℕ) (E : Set (ProductInterval.V n)) (s : ℝ), 0 < s →
 MeasureTheory.Measure.hausdorffMeasure s E ≤
 MeasureTheory.Measure.hausdorffMeasure (s + 1) (E ×ˢ ProductInterval.interval)) (h_E005 : ∀ (n : ℕ) (S : Set (ProductInterval.V n × ℝ)),
 dimH (ProductInterval.appendCoord n '' S) = dimH S) (h_E008 : (∀ (n : ℕ) (E : Set (ProductInterval.V n)), dimH E ≤ (n : ℝ≥0∞)) ∧
 dimH ProductInterval.interval = 1) (h_M012 : ∀ (X : Type) [MetricSpace X] (A B : Set X), A ⊆ B → dimH A ≤ dimH B) (h_M013 : ∀ (X Y : Type) [MetricSpace X] [MetricSpace Y] (f : X → Y), Isometry f →
 ∀ (S : Set X), dimH (f '' S) = dimH S) :
    dimH (ProductInterval.euclideanProduct n E) = dimH E + 1 := by
  have h_T001 : 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ (n : ℝ≥0∞) < ∞ ∧ dimH ProductInterval.interval = 1 ∧ 0 ≤ ProductInterval.D n E ∧ ProductInterval.D n E ≤ (n : ℝ) ∧ ENNReal.ofReal (ProductInterval.D n E) = dimH E := @T001 n E h_E008
  have h_T002 : ∀ b : ℝ, ProductInterval.D n E < b → dimH (ProductInterval.F n E) ≤ ENNReal.ofReal (b + 1) := @T002 n E h_T001 h_M002 h_E003
  have h_T003 : dimH (ProductInterval.F n E) ≤ dimH E + 1 := @T003 n E h_T001 h_T002
  have h_T004 : 0 < dimH E → 0 < ProductInterval.D n E ∧ ∀ b : ℝ, 0 < b → b < ProductInterval.D n E → ENNReal.ofReal (b + 1) ≤ dimH (ProductInterval.F n E) := @T004 n E h_T001 h_M002 h_E004
  have h_T005 : 0 < dimH E → dimH E + 1 ≤ dimH (ProductInterval.F n E) := @T005 n E h_T001 h_T004
  have h_T006 : 1 ≤ dimH (ProductInterval.F n E) := @T006 n E h_H002 h_T001 h_M012 h_M013
  have h_T007 : dimH E + 1 ≤ dimH (ProductInterval.F n E) := @T007 n E h_T001 h_T005 h_T006
  have h_T008 : dimH (ProductInterval.F n E) = dimH E + 1 := @T008 n E h_T003 h_T007
  have h_T009 : dimH (ProductInterval.euclideanProduct n E) = dimH (ProductInterval.F n E) := @T009 n E h_E005
  have h_T010 : dimH (ProductInterval.euclideanProduct n E) = dimH E + 1 := @T010 n E h_T008 h_T009
  exact h_T010

#check @P
#print axioms P

end Translation

namespace AuditBExport
set_option autoImplicit false
theorem resolved_M002 (n : ℕ) (E : Set (ProductInterval.V n)) (h_H001 : IsCompact E) (h_H002 : E.Nonempty) (h_E003 : ∀ (n : ℕ) (E : Set (ProductInterval.V n)) (q : ℝ), 0 < q →
 MeasureTheory.Measure.hausdorffMeasure q E = 0 →
 MeasureTheory.Measure.hausdorffMeasure (q + 1) (E ×ˢ ProductInterval.interval) = 0) (h_E004 : ∀ (n : ℕ) (E : Set (ProductInterval.V n)) (s : ℝ), 0 < s →
 MeasureTheory.Measure.hausdorffMeasure s E ≤
 MeasureTheory.Measure.hausdorffMeasure (s + 1) (E ×ˢ ProductInterval.interval)) (h_E005 : ∀ (n : ℕ) (S : Set (ProductInterval.V n × ℝ)),
 dimH (ProductInterval.appendCoord n '' S) = dimH S) (h_E008 : (∀ (n : ℕ) (E : Set (ProductInterval.V n)), dimH E ≤ (n : ℝ≥0∞)) ∧
 dimH ProductInterval.interval = 1) : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (A : Set X) (a : ℝ≥0),
(dimH A < (a : ℝ≥0∞) → MeasureTheory.Measure.hausdorffMeasure (a : ℝ) A = 0) ∧
((a : ℝ≥0∞) < dimH A → MeasureTheory.Measure.hausdorffMeasure (a : ℝ) A = ∞) ∧
(MeasureTheory.Measure.hausdorffMeasure (a : ℝ) A = 0 → dimH A ≤ (a : ℝ≥0∞)) ∧
(MeasureTheory.Measure.hausdorffMeasure (a : ℝ) A = ∞ → (a : ℝ≥0∞) ≤ dimH A) := by
  intro X _ _ _ A a
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    exact hausdorffMeasure_of_dimH_lt (s := A) (d := a) h
  · intro h
    exact hausdorffMeasure_of_lt_dimH (s := A) (d := a) h
  · intro h
    apply dimH_le_of_hausdorffMeasure_ne_top (s := A) (d := a)
    rw [h]
    exact ENNReal.zero_ne_top
  · intro h
    exact le_dimH_of_hausdorffMeasure_eq_top (s := A) (d := a) h

theorem resolved_M012 (n : ℕ) (E : Set (ProductInterval.V n)) (h_H001 : IsCompact E) (h_H002 : E.Nonempty) (h_E003 : ∀ (n : ℕ) (E : Set (ProductInterval.V n)) (q : ℝ), 0 < q →
 MeasureTheory.Measure.hausdorffMeasure q E = 0 →
 MeasureTheory.Measure.hausdorffMeasure (q + 1) (E ×ˢ ProductInterval.interval) = 0) (h_E004 : ∀ (n : ℕ) (E : Set (ProductInterval.V n)) (s : ℝ), 0 < s →
 MeasureTheory.Measure.hausdorffMeasure s E ≤
 MeasureTheory.Measure.hausdorffMeasure (s + 1) (E ×ˢ ProductInterval.interval)) (h_E005 : ∀ (n : ℕ) (S : Set (ProductInterval.V n × ℝ)),
 dimH (ProductInterval.appendCoord n '' S) = dimH S) (h_E008 : (∀ (n : ℕ) (E : Set (ProductInterval.V n)), dimH E ≤ (n : ℝ≥0∞)) ∧
 dimH ProductInterval.interval = 1) : ∀ (X : Type) [MetricSpace X] (A B : Set X), A ⊆ B → dimH A ≤ dimH B := by
  intro X _ A B h
  exact dimH_mono h

theorem resolved_M013 (n : ℕ) (E : Set (ProductInterval.V n)) (h_H001 : IsCompact E) (h_H002 : E.Nonempty) (h_E003 : ∀ (n : ℕ) (E : Set (ProductInterval.V n)) (q : ℝ), 0 < q →
 MeasureTheory.Measure.hausdorffMeasure q E = 0 →
 MeasureTheory.Measure.hausdorffMeasure (q + 1) (E ×ˢ ProductInterval.interval) = 0) (h_E004 : ∀ (n : ℕ) (E : Set (ProductInterval.V n)) (s : ℝ), 0 < s →
 MeasureTheory.Measure.hausdorffMeasure s E ≤
 MeasureTheory.Measure.hausdorffMeasure (s + 1) (E ×ˢ ProductInterval.interval)) (h_E005 : ∀ (n : ℕ) (S : Set (ProductInterval.V n × ℝ)),
 dimH (ProductInterval.appendCoord n '' S) = dimH S) (h_E008 : (∀ (n : ℕ) (E : Set (ProductInterval.V n)), dimH E ≤ (n : ℝ≥0∞)) ∧
 dimH ProductInterval.interval = 1) : ∀ (X Y : Type) [MetricSpace X] [MetricSpace Y] (f : X → Y), Isometry f →
 ∀ (S : Set X), dimH (f '' S) = dimH S := by
  intro X Y _ _ f hf S
  exact hf.dimH_image S

set_option Elab.async false in
theorem P (n : ℕ) (E : Set (ProductInterval.V n)) (h_H001 : IsCompact E) (h_H002 : E.Nonempty) (h_E003 : ∀ (n : ℕ) (E : Set (ProductInterval.V n)) (q : ℝ), 0 < q →
 MeasureTheory.Measure.hausdorffMeasure q E = 0 →
 MeasureTheory.Measure.hausdorffMeasure (q + 1) (E ×ˢ ProductInterval.interval) = 0) (h_E004 : ∀ (n : ℕ) (E : Set (ProductInterval.V n)) (s : ℝ), 0 < s →
 MeasureTheory.Measure.hausdorffMeasure s E ≤
 MeasureTheory.Measure.hausdorffMeasure (s + 1) (E ×ˢ ProductInterval.interval)) (h_E005 : ∀ (n : ℕ) (S : Set (ProductInterval.V n × ℝ)),
 dimH (ProductInterval.appendCoord n '' S) = dimH S) (h_E008 : (∀ (n : ℕ) (E : Set (ProductInterval.V n)), dimH E ≤ (n : ℝ≥0∞)) ∧
 dimH ProductInterval.interval = 1) : dimH (ProductInterval.euclideanProduct n E) = dimH E + 1 := by
  exact @Translation.P n E h_H001 h_H002 (@resolved_M002 n E h_H001 h_H002 h_E003 h_E004 h_E005 h_E008) h_E003 h_E004 h_E005 h_E008 (@resolved_M012 n E h_H001 h_H002 h_E003 h_E004 h_E005 h_E008) (@resolved_M013 n E h_H001 h_H002 h_E003 h_E004 h_E005 h_E008)

#check @P
#print axioms P
end AuditBExport


namespace YuiBasis
set_option autoImplicit false
set_option Elab.async false in
theorem B001 : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (a : ℝ) (A : Set X),
MeasureTheory.Measure.hausdorffMeasure a A =
 ⨆ (r : ℝ≥0∞) (_ : 0 < r), ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)
 (_ : ∀ i, Metric.ediam (U i) ≤ r), ∑' i, ⨆ _ : (U i).Nonempty, (Metric.ediam (U i)) ^ a := by
  intro X _ _ _ a A
  exact MeasureTheory.Measure.hausdorffMeasure_apply a A
set_option Elab.async false in
theorem B002 : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (A : Set X) (a : ℝ≥0),
(dimH A < (a : ℝ≥0∞) → MeasureTheory.Measure.hausdorffMeasure (a : ℝ) A = 0) ∧
((a : ℝ≥0∞) < dimH A → MeasureTheory.Measure.hausdorffMeasure (a : ℝ) A = ∞) ∧
(MeasureTheory.Measure.hausdorffMeasure (a : ℝ) A = 0 → dimH A ≤ (a : ℝ≥0∞)) ∧
(MeasureTheory.Measure.hausdorffMeasure (a : ℝ) A = ∞ → (a : ℝ≥0∞) ≤ dimH A) := by
  intro X _ _ _ A a
  refine ⟨fun h => hausdorffMeasure_of_dimH_lt h,
   fun h => hausdorffMeasure_of_lt_dimH h, ?_,
   fun h => le_dimH_of_hausdorffMeasure_eq_top h⟩
  intro h
  exact dimH_le_of_hausdorffMeasure_ne_top (by simpa [h])
set_option Elab.async false in
theorem B003 : ∀ (n : ℕ) (E : Set (ProductInterval.V n)) (q : ℝ), 0 < q →
 MeasureTheory.Measure.hausdorffMeasure q E = 0 →
 MeasureTheory.Measure.hausdorffMeasure (q + 1) (E ×ˢ ProductInterval.interval) = 0 := by
  have h_H001 : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (a : ℝ) (A : Set X),
  MeasureTheory.Measure.hausdorffMeasure a A =
   ⨆ (r : ℝ≥0∞) (_ : 0 < r), ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)
   (_ : ∀ i, Metric.ediam (U i) ≤ r), ∑' i, ⨆ _ : (U i).Nonempty, (Metric.ediam (U i)) ^ a := @YuiBasis.B001
  have yui_nested_0302804ac4c3b00183c3_0001 (h_H001 : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (a : ℝ) (A : Set X),
  MeasureTheory.Measure.hausdorffMeasure a A =
   ⨆ (r : ℝ≥0∞) (_ : 0 < r), ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)
   (_ : ∀ i, Metric.ediam (U i) ≤ r), ∑' i, ⨆ _ : (U i).Nonempty, (Metric.ediam (U i)) ^ a) : (∀ (ε : ℝ≥0), (∑' i : ℕ, ((ε * (1 / 2 : ℝ≥0) ^ (i + 3) : ℝ≥0) : ℝ≥0∞)) = ((ε / 4 : ℝ≥0) : ℝ≥0∞)) := by
    intro ε
    have hg : HasSum (fun i : ℕ => (1 / 2 : ℝ≥0) ^ i) 2 := by
      apply NNReal.hasSum_coe.mp
      simpa using hasSum_geometric_two
    have hf : (fun i : ℕ => ε * (1 / 2 : ℝ≥0) ^ (i + 3)) = (fun i : ℕ => (ε * (1 / 2 : ℝ≥0) ^ 3) * (1 / 2 : ℝ≥0) ^ i) := by
      funext i
      rw [pow_add]
      ring
    have he : (ε * (1 / 2 : ℝ≥0) ^ 3) * 2 = ε / 4 := by norm_num; ring
    have hs : HasSum (fun i : ℕ => ε * (1 / 2 : ℝ≥0) ^ (i + 3)) (ε / 4) := by
      rw [hf, ← he]
      exact hg.mul_left _
    exact ENNReal.tsum_coe_eq hs
  have yui_nested_0302804ac4c3b00183c3_0002 (h_H001 : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (a : ℝ) (A : Set X),
  MeasureTheory.Measure.hausdorffMeasure a A =
   ⨆ (r : ℝ≥0∞) (_ : 0 < r), ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)
   (_ : ∀ i, Metric.ediam (U i) ≤ r), ∑' i, ⨆ _ : (U i).Nonempty, (Metric.ediam (U i)) ^ a) : (∀ (n : ℕ) (E : Set (ProductInterval.V n)) (q : ℝ) (r : ℝ≥0∞), 0 < r → (⨅ (U : ℕ → Set (ProductInterval.V n)) (_ : E ⊆ ⋃ i, U i) (_ : ∀ i, Metric.ediam (U i) ≤ r), ∑' i, ⨆ _ : (U i).Nonempty, Metric.ediam (U i) ^ q) ≤ MeasureTheory.Measure.hausdorffMeasure q E) := by
    intro n E q r hr
    rw [h_H001 (ProductInterval.V n) q E]
    apply le_iSup_of_le r
    apply le_iSup_of_le hr
    exact le_rfl
  have yui_nested_0302804ac4c3b00183c3_0003 (h_H001 : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (a : ℝ) (A : Set X),
  MeasureTheory.Measure.hausdorffMeasure a A =
   ⨆ (r : ℝ≥0∞) (_ : 0 < r), ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)
   (_ : ∀ i, Metric.ediam (U i) ≤ r), ∑' i, ⨆ _ : (U i).Nonempty, (Metric.ediam (U i)) ^ a) : (∀ (n : ℕ) (E : Set (ProductInterval.V n)) (q : ℝ), 0 < q → MeasureTheory.Measure.hausdorffMeasure q E = 0 → ∀ (r ε : ℝ≥0), 0 < r → 0 < ε → ∃ U : ℕ → Set (ProductInterval.V n), E ⊆ ⋃ i, U i ∧ (∀ i, Metric.ediam (U i) ≤ (r : ℝ≥0∞)) ∧ (∑' i, Metric.ediam (U i) ^ q) < (ε : ℝ≥0∞)) := by
    intro n E q hq hE r ε hr hε
    have hz : (⨅ (U : ℕ → Set (ProductInterval.V n)) (_ : E ⊆ ⋃ i, U i) (_ : ∀ i, Metric.ediam (U i) ≤ (r : ℝ≥0∞)), ∑' i, ⨆ _ : (U i).Nonempty, Metric.ediam (U i) ^ q) = 0 := by
      apply le_antisymm _ (zero_le)
      have hh := yui_nested_0302804ac4c3b00183c3_0002 h_H001 n E q (r : ℝ≥0∞) (ENNReal.coe_pos.mpr hr)
      rw [hE] at hh
      exact hh
    have hl : (⨅ (U : ℕ → Set (ProductInterval.V n)) (_ : E ⊆ ⋃ i, U i) (_ : ∀ i, Metric.ediam (U i) ≤ (r : ℝ≥0∞)), ∑' i, ⨆ _ : (U i).Nonempty, Metric.ediam (U i) ^ q) < (ε : ℝ≥0∞) := by
      rw [hz]
      exact ENNReal.coe_pos.mpr hε
    rcases iInf_lt_iff.mp hl with ⟨U, hU⟩
    rcases iInf_lt_iff.mp hU with ⟨hc, hU⟩
    rcases iInf_lt_iff.mp hU with ⟨hd, hU⟩
    refine ⟨U, hc, hd, ?_⟩
    convert hU using 1
    congr 1
    funext i
    by_cases hi : (U i).Nonempty
    · simp [hi]
    · have he : U i = ∅ := Set.not_nonempty_iff_eq_empty.mp hi
      simp [he, ENNReal.zero_rpow_of_pos hq]
  have yui_nested_0302804ac4c3b00183c3_0004 (h_H001 : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (a : ℝ) (A : Set X),
  MeasureTheory.Measure.hausdorffMeasure a A =
   ⨆ (r : ℝ≥0∞) (_ : 0 < r), ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)
   (_ : ∀ i, Metric.ediam (U i) ≤ r), ∑' i, ⨆ _ : (U i).Nonempty, (Metric.ediam (U i)) ^ a) : (∀ (n : ℕ) (E : Set (ProductInterval.V n)) (q : ℝ), 0 < q → MeasureTheory.Measure.hausdorffMeasure q E = 0 → ∀ (r ε : ℝ≥0), 0 < r → 0 < ε → ∃ (U : ℕ → Set (ProductInterval.V n)) (a : ℕ → ℝ≥0), E ⊆ ⋃ i, U i ∧ (∀ i, Metric.ediam (U i) ≤ (a i : ℝ≥0∞)) ∧ (∀ i, 0 < a i ∧ a i ≤ r) ∧ (∑' i, (a i : ℝ≥0∞) ^ q) < (ε : ℝ≥0∞)) := by
    intro n E q hq hE r ε hr hε
    rcases yui_nested_0302804ac4c3b00183c3_0003 h_H001 n E q hq hE r (ε / 2) hr (by positivity) with ⟨U, hc, hd, hs⟩
    let d : ℕ → ℝ≥0 := fun i => (Metric.ediam (U i)).toNNReal
    have hdcoe (i : ℕ) : (d i : ℝ≥0∞) = Metric.ediam (U i) :=
      ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (hd i))
    have hdr (i : ℕ) : d i ≤ r := by
      apply ENNReal.coe_le_coe.mp
      rw [hdcoe]
      exact hd i
    let w : ℕ → ℝ≥0 := fun i => ε * (1 / 2 : ℝ≥0) ^ (i + 3)
    let b : ℕ → ℝ≥0 := fun i => min (r / 2) ((w i) ^ (1 / q))
    let a : ℕ → ℝ≥0 := fun i => max (d i) (b i)
    have hbpos (i : ℕ) : 0 < b i := by
      dsimp [b, w]
      exact lt_min (by positivity) (NNReal.rpow_pos (by positivity))
    have hbr (i : ℕ) : b i ≤ r := (min_le_left _ _).trans (by simp)
    have hbw (i : ℕ) : (b i : ℝ≥0∞) ^ q ≤ (w i : ℝ≥0∞) := by
      rw [← ENNReal.coe_rpow_of_nonneg _ hq.le]
      apply ENNReal.coe_le_coe.mpr
      calc
        b i ^ q ≤ (w i ^ (1 / q)) ^ q := NNReal.rpow_le_rpow (min_le_right _ _) hq.le
        _ = w i := by rw [← NNReal.rpow_mul]; simp [hq.ne']
    have ham (i : ℕ) : (a i : ℝ≥0∞) ^ q ≤ Metric.ediam (U i) ^ q + (w i : ℝ≥0∞) := by
      change ((max (d i) (b i) : ℝ≥0) : ℝ≥0∞) ^ q ≤ _
      rw [ENNReal.coe_max, ENNReal.max_rpow hq.le, hdcoe]
      exact max_le (le_add_right le_rfl) ((hbw i).trans (le_add_left le_rfl))
    refine ⟨U, a, hc, fun i => ?_, fun i => ⟨(hbpos i).trans_le (le_max_right _ _), max_le (hdr i) (hbr i)⟩, ?_⟩
    · rw [← hdcoe]
      exact ENNReal.coe_le_coe.mpr (le_max_left _ _)
    · calc
        (∑' i, (a i : ℝ≥0∞) ^ q) ≤ ∑' i, (Metric.ediam (U i) ^ q + (w i : ℝ≥0∞)) := ENNReal.tsum_le_tsum ham
        _ = (∑' i, Metric.ediam (U i) ^ q) + ((ε / 4 : ℝ≥0) : ℝ≥0∞) := by
          rw [ENNReal.tsum_add, show (∑' i, (w i : ℝ≥0∞)) = ((ε / 4 : ℝ≥0) : ℝ≥0∞) from yui_nested_0302804ac4c3b00183c3_0001 h_H001 ε]
        _ < ((ε / 2 : ℝ≥0) : ℝ≥0∞) + ((ε / 4 : ℝ≥0) : ℝ≥0∞) := ENNReal.add_lt_add_right ENNReal.coe_ne_top hs
        _ < (ε : ℝ≥0∞) := by
          rw [← ENNReal.coe_add, ENNReal.coe_lt_coe]
          have hp : (0 : ℝ) < ε := hε
          exact_mod_cast (show (ε : ℝ) / 2 + (ε : ℝ) / 4 < ε by linarith)
  have yui_nested_0302804ac4c3b00183c3_0005 (h_H001 : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (a : ℝ) (A : Set X),
  MeasureTheory.Measure.hausdorffMeasure a A =
   ⨆ (r : ℝ≥0∞) (_ : 0 < r), ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)
   (_ : ∀ i, Metric.ediam (U i) ≤ r), ∑' i, ⨆ _ : (U i).Nonempty, (Metric.ediam (U i)) ^ a) : (∀ (a : ℝ≥0), 0 < a → a ≤ 1 → ∃ (N : ℕ) (J : Fin N → Set ℝ), 0 < N ∧ ProductInterval.interval ⊆ ⋃ j, J j ∧ (∀ j, Metric.ediam (J j) ≤ (a : ℝ≥0∞)) ∧ (N : ℝ≥0∞) * (a : ℝ≥0∞) ≤ 2) := by
    intro a ha ha1
    let N : ℕ := ⌈(1 / (a : ℝ))⌉₊
    have haR : (0 : ℝ) < a := ha
    have hN : 0 < N := Nat.ceil_pos.mpr (by positivity)
    have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    have hceil : 1 / (a : ℝ) ≤ (N : ℝ) := Nat.le_ceil _
    have hlen : 1 / (N : ℝ) ≤ (a : ℝ) := by
      apply (div_le_iff₀ hNR).mpr
      have h := (div_le_iff₀ haR).mp hceil
      nlinarith
    have hcost : (N : ℝ) * (a : ℝ) ≤ 2 := by
      have h := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 1 / (a : ℝ) by positivity)
      change (N : ℝ) < 1 / (a : ℝ) + 1 at h
      have h' := (mul_lt_mul_of_pos_right h haR)
      have hi : (a : ℝ) ≤ 1 := ha1
      have he : (1 / (a : ℝ) + 1) * (a : ℝ) = 1 + a := by field_simp
      rw [he] at h'
      linarith
    let J : Fin N → Set ℝ := fun j => Set.Icc ((j : ℕ) / (N : ℝ)) (((j : ℕ) + 1) / (N : ℝ))
    refine ⟨N, J, hN, ?_, ?_, ?_⟩
    · intro x hx
      change 0 ≤ x ∧ x ≤ 1 at hx
      by_cases hx1 : x = 1
      · subst x
        refine Set.mem_iUnion.mpr ⟨⟨N - 1, by omega⟩, ?_⟩
        change ((N - 1 : ℕ) : ℝ) / (N : ℝ) ≤ 1 ∧ 1 ≤ (((N - 1 : ℕ) : ℝ) + 1) / (N : ℝ)
        have he : ((N - 1 : ℕ) : ℝ) + 1 = N := by
          exact_mod_cast (Nat.sub_add_cancel (show 1 ≤ N by omega))
        constructor
        · apply (div_le_iff₀ hNR).mpr
          linarith
        · rw [he, div_self hNR.ne']
      · have hxl : x < 1 := lt_of_le_of_ne hx.2 hx1
        have hf : ⌊x * (N : ℝ)⌋₊ < N := (Nat.floor_lt (mul_nonneg hx.1 hNR.le)).mpr (by nlinarith)
        refine Set.mem_iUnion.mpr ⟨⟨⌊x * (N : ℝ)⌋₊, hf⟩, ?_⟩
        change (⌊x * (N : ℝ)⌋₊ : ℝ) / (N : ℝ) ≤ x ∧ x ≤ ((⌊x * (N : ℝ)⌋₊ : ℝ) + 1) / (N : ℝ)
        constructor
        · exact (div_le_iff₀ hNR).mpr (Nat.floor_le (mul_nonneg hx.1 hNR.le))
        · exact (le_div_iff₀ hNR).mpr (Nat.lt_floor_add_one _).le
    · intro j
      dsimp [J]
      rw [Real.ediam_Icc, ENNReal.ofReal_le_coe]
      have he : (((j : ℕ) : ℝ) + 1) / (N : ℝ) - (j : ℕ) / (N : ℝ) = 1 / (N : ℝ) := by ring
      rw [he]
      exact hlen
    · have hh : (N : ℝ≥0) * a ≤ 2 := by exact_mod_cast hcost
      exact_mod_cast hh
  have yui_nested_0302804ac4c3b00183c3_0006 (h_H001 : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (a : ℝ) (A : Set X),
  MeasureTheory.Measure.hausdorffMeasure a A =
   ⨆ (r : ℝ≥0∞) (_ : 0 < r), ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)
   (_ : ∀ i, Metric.ediam (U i) ≤ r), ∑' i, ⨆ _ : (U i).Nonempty, (Metric.ediam (U i)) ^ a) : (∀ (N : ℕ → ℕ) (f : ℕ → ℝ≥0∞), (∑' p : (Σ i : ℕ, Fin (N i)), f p.1) = ∑' i : ℕ, (N i : ℝ≥0∞) * f i) := by
    intro N f
    rw [ENNReal.tsum_sigma' (fun p : (Σ i : ℕ, Fin (N i)) => f p.1)]
    simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have yui_nested_0302804ac4c3b00183c3_0007 (h_H001 : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (a : ℝ) (A : Set X),
  MeasureTheory.Measure.hausdorffMeasure a A =
   ⨆ (r : ℝ≥0∞) (_ : 0 < r), ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)
   (_ : ∀ i, Metric.ediam (U i) ≤ r), ∑' i, ⨆ _ : (U i).Nonempty, (Metric.ediam (U i)) ^ a) : (∀ (X ι : Type) [MetricSpace X] [Encodable ι] (t : ι → Set X) (r : ℝ≥0∞), (∀ p, Metric.ediam (t p) ≤ r) → ∀ k : ℕ, Metric.ediam (⋃ p ∈ Encodable.decode₂ ι k, t p) ≤ r) := by
    intro X ι _ _ t r ht k
    exact Encodable.iUnion_decode₂_cases (f := t) (C := fun s : Set X => Metric.ediam s ≤ r) (by simp) ht
  have yui_nested_0302804ac4c3b00183c3_0008 (h_H001 : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (a : ℝ) (A : Set X),
  MeasureTheory.Measure.hausdorffMeasure a A =
   ⨆ (r : ℝ≥0∞) (_ : 0 < r), ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)
   (_ : ∀ i, Metric.ediam (U i) ≤ r), ∑' i, ⨆ _ : (U i).Nonempty, (Metric.ediam (U i)) ^ a) : (∀ (x y : ℝ≥0∞), x < y → 2 * x < 2 * y) := by
    intro x y hxy
    exact ENNReal.mul_lt_mul_right (a := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) hxy
  have yui_nested_0302804ac4c3b00183c3_0009 (h_H001 : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (a : ℝ) (A : Set X),
  MeasureTheory.Measure.hausdorffMeasure a A =
   ⨆ (r : ℝ≥0∞) (_ : 0 < r), ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)
   (_ : ∀ i, Metric.ediam (U i) ≤ r), ∑' i, ⨆ _ : (U i).Nonempty, (Metric.ediam (U i)) ^ a) : (∀ (n : ℕ) (E : Set (ProductInterval.V n)) (q : ℝ), 0 < q → MeasureTheory.Measure.hausdorffMeasure q E = 0 → ∀ (r ε : ℝ≥0), 0 < r → r ≤ 1 → 0 < ε → ∃ W : ℕ → Set (ProductInterval.V n × ℝ), E ×ˢ ProductInterval.interval ⊆ ⋃ k, W k ∧ (∀ k, Metric.ediam (W k) ≤ (r : ℝ≥0∞)) ∧ (∑' k, Metric.ediam (W k) ^ (q + 1)) < 2 * (ε : ℝ≥0∞)) := by
    classical
    intro n E q hq hE r ε hr hr1 hε
    rcases yui_nested_0302804ac4c3b00183c3_0004 h_H001 n E q hq hE r ε hr hε with ⟨U, a, hc, hd, ha, hs⟩
    have hi (i : ℕ) := yui_nested_0302804ac4c3b00183c3_0005 h_H001 (a i) (ha i).1 ((ha i).2.trans hr1)
    choose N J hN hcJ hdJ hcost using hi
    let ι := Σ i : ℕ, Fin (N i)
    let t : ι → Set (ProductInterval.V n × ℝ) := fun p => U p.1 ×ˢ J p.1 p.2
    have ht (p : ι) : Metric.ediam (t p) ≤ (a p.1 : ℝ≥0∞) := by
      apply Metric.ediam_le
      intro x hx y hy
      rw [Prod.edist_eq]
      exact max_le (Metric.edist_le_of_ediam_le hx.1 hy.1 (hd p.1)) (Metric.edist_le_of_ediam_le hx.2 hy.2 (hdJ p.1 p.2))
    have htc : E ×ˢ ProductInterval.interval ⊆ ⋃ p, t p := by
      intro x hx
      rcases Set.mem_iUnion.mp (hc hx.1) with ⟨i, hi⟩
      rcases Set.mem_iUnion.mp (hcJ i hx.2) with ⟨j, hj⟩
      exact Set.mem_iUnion.mpr ⟨⟨i, j⟩, hi, hj⟩
    have hpc (i : ℕ) : (N i : ℝ≥0∞) * (a i : ℝ≥0∞) ^ (q + 1) ≤ 2 * (a i : ℝ≥0∞) ^ q := by
      rw [ENNReal.rpow_add q 1 (ENNReal.coe_ne_zero.mpr (ha i).1.ne') ENNReal.coe_ne_top, ENNReal.rpow_one]
      calc
        (N i : ℝ≥0∞) * ((a i : ℝ≥0∞) ^ q * (a i : ℝ≥0∞)) =
            ((N i : ℝ≥0∞) * (a i : ℝ≥0∞)) * (a i : ℝ≥0∞) ^ q := by ac_rfl
        _ ≤ 2 * (a i : ℝ≥0∞) ^ q := mul_le_mul_right' (hcost i) _
    have hts : (∑' p : ι, Metric.ediam (t p) ^ (q + 1)) < 2 * (ε : ℝ≥0∞) := by
      calc
        (∑' p : ι, Metric.ediam (t p) ^ (q + 1)) ≤ ∑' p : ι, (a p.1 : ℝ≥0∞) ^ (q + 1) :=
          ENNReal.tsum_le_tsum (fun p => ENNReal.rpow_le_rpow (ht p) (by linarith))
        _ = ∑' i : ℕ, (N i : ℝ≥0∞) * (a i : ℝ≥0∞) ^ (q + 1) := by
          exact yui_nested_0302804ac4c3b00183c3_0006 h_H001 N (fun i => (a i : ℝ≥0∞) ^ (q + 1))
        _ ≤ ∑' i : ℕ, 2 * (a i : ℝ≥0∞) ^ q := ENNReal.tsum_le_tsum hpc
        _ = 2 * ∑' i : ℕ, (a i : ℝ≥0∞) ^ q := ENNReal.tsum_mul_left
        _ < 2 * (ε : ℝ≥0∞) := yui_nested_0302804ac4c3b00183c3_0008 h_H001 _ _ hs
    let W : ℕ → Set (ProductInterval.V n × ℝ) := fun k => ⋃ p ∈ Encodable.decode₂ ι k, t p
    refine ⟨W, ?_, ?_, ?_⟩
    · dsimp [W]
      rw [Encodable.iUnion_decode₂]
      exact htc
    · intro k
      exact yui_nested_0302804ac4c3b00183c3_0007 h_H001 (ProductInterval.V n × ℝ) ι t (r : ℝ≥0∞) (fun p => (ht p).trans (ENNReal.coe_le_coe.mpr (ha p.1).2)) k
    · change (∑' k : ℕ, Metric.ediam (⋃ p ∈ Encodable.decode₂ ι k, t p) ^ (q + 1)) < _
      rw [tsum_iUnion_decode₂ (fun s : Set (ProductInterval.V n × ℝ) => Metric.ediam s ^ (q + 1)) (by simp [ENNReal.zero_rpow_of_pos (show 0 < q + 1 by linarith)]) t]
      exact hts
  have yui_nested_0302804ac4c3b00183c3_0010 (h_H001 : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (a : ℝ) (A : Set X),
  MeasureTheory.Measure.hausdorffMeasure a A =
   ⨆ (r : ℝ≥0∞) (_ : 0 < r), ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)
   (_ : ∀ i, Metric.ediam (U i) ≤ r), ∑' i, ⨆ _ : (U i).Nonempty, (Metric.ediam (U i)) ^ a) : (∀ (n : ℕ) (W : ℕ → Set (ProductInterval.V n × ℝ)) (p : ℝ), (∑' k : ℕ, ⨆ _ : (W k).Nonempty, Metric.ediam (W k) ^ p) ≤ ∑' k : ℕ, Metric.ediam (W k) ^ p) := by
    intro n W p
    apply ENNReal.tsum_le_tsum
    intro k
    exact iSup_le fun _ => le_rfl
  intro n E q hq hE
  apply le_antisymm ?_ zero_le
  rw [h_H001 (ProductInterval.V n × ℝ) (q + 1) (E ×ˢ ProductInterval.interval)]
  refine iSup_le fun R => iSup_le fun hR => ?_
  rcases exists_between hR with ⟨ρ, hρ, hρR⟩
  rcases ENNReal.lt_iff_exists_coe.mp hρR with ⟨s, rfl, hsR⟩
  let r : ℝ≥0 := min s 1
  have hr : 0 < r := lt_min (ENNReal.coe_pos.mp hρ) zero_lt_one
  have hr1 : r ≤ 1 := min_le_right _ _
  have hrR : (r : ℝ≥0∞) ≤ R :=
    (ENNReal.coe_le_coe.mpr (min_le_left _ _)).trans hsR.le
  refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
  simp only [zero_add]
  rcases yui_nested_0302804ac4c3b00183c3_0009 h_H001 n E q hq hE r (δ / 2) hr hr1 (by positivity) with ⟨W, hc, hd, hs⟩
  have he : (2 : ℝ≥0∞) * ((δ / 2 : ℝ≥0) : ℝ≥0∞) = (δ : ℝ≥0∞) := by
    have he' : (2 : ℝ≥0) * (δ / 2) = δ := by ring
    exact_mod_cast he'
  rw [he] at hs
  apply iInf_le_of_le W
  apply iInf_le_of_le hc
  apply iInf_le_of_le (fun k => (hd k).trans hrR)
  exact (yui_nested_0302804ac4c3b00183c3_0010 h_H001 n W (q + 1)).trans hs.le
set_option Elab.async false in
theorem B006 : ∀ (X : Type) [MeasurableSpace X] (μ : MeasureTheory.Measure X) (f : ℕ → X → ℝ≥0∞),
 (∀ i, AEMeasurable (f i) μ) →
 (∫⁻ x, ∑' i, f i x ∂μ) = ∑' i, ∫⁻ x, f i x ∂μ := by
  intro X _ μ f hf
  exact MeasureTheory.lintegral_tsum hf
set_option Elab.async false in
theorem B007 : ∀ (B : Set ℝ), MeasureTheory.volume B ≤ Metric.ediam B := by
  exact Real.volume_le_diam
set_option Elab.async false in
theorem B004 : ∀ (n : ℕ) (E : Set (ProductInterval.V n)) (s : ℝ), 0 < s →
 MeasureTheory.Measure.hausdorffMeasure s E ≤
 MeasureTheory.Measure.hausdorffMeasure (s + 1) (E ×ˢ ProductInterval.interval) := by
  have h_H001 : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (a : ℝ) (A : Set X),
  MeasureTheory.Measure.hausdorffMeasure a A =
   ⨆ (r : ℝ≥0∞) (_ : 0 < r), ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)
   (_ : ∀ i, Metric.ediam (U i) ≤ r), ∑' i, ⨆ _ : (U i).Nonempty, (Metric.ediam (U i)) ^ a := @YuiBasis.B001
  have h_H002 : ∀ (X : Type) [MeasurableSpace X] (μ : MeasureTheory.Measure X) (f : ℕ → X → ℝ≥0∞),
   (∀ i, AEMeasurable (f i) μ) →
   (∫⁻ x, ∑' i, f i x ∂μ) = ∑' i, ∫⁻ x, f i x ∂μ := @YuiBasis.B006
  have h_H003 : ∀ (B : Set ℝ), MeasureTheory.volume B ≤ Metric.ediam B := @YuiBasis.B007
  have yui_nested_877752aa3eab39345043_0001 (h_H001 : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (a : ℝ) (A : Set X),
  MeasureTheory.Measure.hausdorffMeasure a A =
   ⨆ (r : ℝ≥0∞) (_ : 0 < r), ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)
   (_ : ∀ i, Metric.ediam (U i) ≤ r), ∑' i, ⨆ _ : (U i).Nonempty, (Metric.ediam (U i)) ^ a) (h_H002 : ∀ (X : Type) [MeasurableSpace X] (μ : MeasureTheory.Measure X) (f : ℕ → X → ℝ≥0∞),
   (∀ i, AEMeasurable (f i) μ) →
   (∫⁻ x, ∑' i, f i x ∂μ) = ∑' i, ∫⁻ x, f i x ∂μ) (h_H003 : ∀ (B : Set ℝ), MeasureTheory.volume B ≤ Metric.ediam B) : (∀ (n : ℕ) (s : ℝ), 0 < s → ∀ (U : ℕ → Set (ProductInterval.V n × ℝ)), (∫⁻ t in ProductInterval.interval, ∑' i, (closure (Prod.snd '' U i)).indicator (fun _ : ℝ => (Metric.ediam (U i)) ^ s) t) ≤ ∑' i, ⨆ _ : (U i).Nonempty, (Metric.ediam (U i)) ^ (s + 1)) := by
    intro n s hs U
    classical
    let J : ℕ → Set ℝ := fun i => closure (Prod.snd '' U i)
    let f : ℕ → ℝ → ℝ≥0∞ := fun i => (J i).indicator (fun _ => (Metric.ediam (U i)) ^ s)
    have hm (i : ℕ) : Measurable (f i) := measurable_const.indicator isClosed_closure.measurableSet
    change (∫⁻ t, ∑' i, f i t ∂volume.restrict ProductInterval.interval) ≤ _
    rw [h_H002 ℝ (volume.restrict ProductInterval.interval) f (fun i => (hm i).aemeasurable)]
    apply ENNReal.tsum_le_tsum
    intro i
    have hj : volume (J i) ≤ Metric.ediam (U i) := by
      calc
        volume (J i) ≤ Metric.ediam (J i) := h_H003 (J i)
        _ = Metric.ediam (Prod.snd '' U i) := Metric.ediam_closure _
        _ ≤ Metric.ediam (U i) := by simpa using LipschitzWith.prod_snd.ediam_image_le (U i)
    have hi : (∫⁻ t, f i t ∂volume.restrict ProductInterval.interval) ≤ (Metric.ediam (U i)) ^ (s + 1) := by
      calc
        (∫⁻ t, f i t ∂volume.restrict ProductInterval.interval) =
            (Metric.ediam (U i)) ^ s * (volume.restrict ProductInterval.interval) (J i) :=
          lintegral_indicator_const isClosed_closure.measurableSet _
        _ ≤ (Metric.ediam (U i)) ^ s * Metric.ediam (U i) :=
          mul_le_mul_left' ((Measure.restrict_apply_le _ _).trans hj) _
        _ = (Metric.ediam (U i)) ^ (s + 1) := by
          rw [ENNReal.rpow_add_of_nonneg s 1 hs.le (by norm_num), ENNReal.rpow_one]
    by_cases hne : (U i).Nonempty
    · exact hi.trans (le_iSup_of_le hne le_rfl)
    · have he : U i = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      simpa [f, J, he] using hi
  have yui_nested_877752aa3eab39345043_0002 (h_H001 : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (a : ℝ) (A : Set X),
  MeasureTheory.Measure.hausdorffMeasure a A =
   ⨆ (r : ℝ≥0∞) (_ : 0 < r), ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)
   (_ : ∀ i, Metric.ediam (U i) ≤ r), ∑' i, ⨆ _ : (U i).Nonempty, (Metric.ediam (U i)) ^ a) (h_H002 : ∀ (X : Type) [MeasurableSpace X] (μ : MeasureTheory.Measure X) (f : ℕ → X → ℝ≥0∞),
   (∀ i, AEMeasurable (f i) μ) →
   (∫⁻ x, ∑' i, f i x ∂μ) = ∑' i, ∫⁻ x, f i x ∂μ) (h_H003 : ∀ (B : Set ℝ), MeasureTheory.volume B ≤ Metric.ediam B) : (∀ (n : ℕ) (E : Set (ProductInterval.V n)) (U : ℕ → Set (ProductInterval.V n × ℝ)),
  E ×ˢ ProductInterval.interval ⊆ ⋃ i, U i →
  ∀ (x : ProductInterval.V n), x ∈ E → ∀ (t : ℝ), t ∈ ProductInterval.interval → ∃ i, (x,t) ∈ U i) := by
    intro n E U hU x hx t ht
    have hxt : (x,t) ∈ E ×ˢ ProductInterval.interval := ⟨hx,ht⟩
    exact Set.mem_iUnion.mp (hU hxt)
  have yui_nested_877752aa3eab39345043_0003 (h_H001 : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (a : ℝ) (A : Set X),
  MeasureTheory.Measure.hausdorffMeasure a A =
   ⨆ (r : ℝ≥0∞) (_ : 0 < r), ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)
   (_ : ∀ i, Metric.ediam (U i) ≤ r), ∑' i, ⨆ _ : (U i).Nonempty, (Metric.ediam (U i)) ^ a) (h_H002 : ∀ (X : Type) [MeasurableSpace X] (μ : MeasureTheory.Measure X) (f : ℕ → X → ℝ≥0∞),
   (∀ i, AEMeasurable (f i) μ) →
   (∫⁻ x, ∑' i, f i x ∂μ) = ∑' i, ∫⁻ x, f i x ∂μ) (h_H003 : ∀ (B : Set ℝ), MeasureTheory.volume B ≤ Metric.ediam B) : (∀ (n : ℕ) (E : Set (ProductInterval.V n)) (s : ℝ), 0 < s →
  ∀ (r : ℝ≥0∞), 0 < r → r < ⊤ →
  ∀ (U : ℕ → Set (ProductInterval.V n × ℝ)), E ×ˢ ProductInterval.interval ⊆ ⋃ i, U i →
  (∀ i, Metric.ediam (U i) ≤ r) →
  (⨅ (W : ℕ → Set (ProductInterval.V n)) (_ : E ⊆ ⋃ i, W i)
   (_ : ∀ i, Metric.ediam (W i) ≤ r), ∑' i, ⨆ _ : (W i).Nonempty, (Metric.ediam (W i)) ^ s) ≤
  ∑' i, ⨆ _ : (U i).Nonempty, (Metric.ediam (U i)) ^ (s + 1)) := by
    intro n E s hs r hr hrt U hU hd
    classical
    let c : ℝ≥0∞ := ⨅ (W : ℕ → Set (ProductInterval.V n)) (_ : E ⊆ ⋃ i, W i)
     (_ : ∀ i, Metric.ediam (W i) ≤ r), ∑' i, ⨆ _ : (W i).Nonempty, (Metric.ediam (W i)) ^ s
    let J : ℕ → Set ℝ := fun i => closure (Prod.snd '' U i)
    have hp (t : ℝ) (ht : t ∈ ProductInterval.interval) :
        c ≤ ∑' i, (J i).indicator (fun _ : ℝ => (Metric.ediam (U i)) ^ s) t := by
      let W : ℕ → Set (ProductInterval.V n) := fun i => if t ∈ J i then Prod.fst '' U i else ∅
      have hw : E ⊆ ⋃ i, W i := by
        intro x hx
        obtain ⟨i, hi⟩ := @yui_nested_877752aa3eab39345043_0002 h_H001 h_H002 h_H003 n E U hU x hx t ht
        have htj : t ∈ J i := subset_closure ⟨(x, t), hi, rfl⟩
        apply Set.mem_iUnion.mpr
        refine ⟨i, ?_⟩
        simpa only [W, if_pos htj] using (show x ∈ Prod.fst '' U i from ⟨(x, t), hi, rfl⟩)
      have hproj (i : ℕ) : Metric.ediam (Prod.fst '' U i) ≤ Metric.ediam (U i) := by
        simpa using LipschitzWith.prod_fst.ediam_image_le (U i)
      have hwdiam : ∀ i, Metric.ediam (W i) ≤ r := by
        intro i
        by_cases htj : t ∈ J i
        · simpa only [W, if_pos htj] using (hproj i).trans (hd i)
        · simp [W, htj]
      calc
        c ≤ ∑' i, ⨆ _ : (W i).Nonempty, (Metric.ediam (W i)) ^ s :=
          iInf_le_of_le W (iInf_le_of_le hw (iInf_le_of_le hwdiam le_rfl))
        _ ≤ ∑' i, (J i).indicator (fun _ : ℝ => (Metric.ediam (U i)) ^ s) t := by
          apply ENNReal.tsum_le_tsum
          intro i
          by_cases htj : t ∈ J i
          · simp only [W, if_pos htj, Set.indicator_of_mem htj]
            exact iSup_le fun _ => ENNReal.rpow_le_rpow (hproj i) hs.le
          · simp [W, htj]
    have hint : c ≤ ∫⁻ t in ProductInterval.interval,
        ∑' i, (J i).indicator (fun _ : ℝ => (Metric.ediam (U i)) ^ s) t := by
      have hm : (∫⁻ _ : ℝ in ProductInterval.interval, c) = c := by
        simp [ProductInterval.interval, Real.volume_Icc]
      rw [← hm]
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (show MeasurableSet ProductInterval.interval from measurableSet_Icc)] with t ht
      exact hp t ht
    exact hint.trans (@yui_nested_877752aa3eab39345043_0001 h_H001 h_H002 h_H003 n s hs U)
  intro n E s hs
  classical
  let CE : ℝ≥0∞ → ℝ≥0∞ := fun r =>
    ⨅ (W : ℕ → Set (ProductInterval.V n)) (_ : E ⊆ ⋃ i, W i)
      (_ : ∀ i, Metric.ediam (W i) ≤ r),
      ∑' i, ⨆ _ : (W i).Nonempty, (Metric.ediam (W i)) ^ s
  let CP : ℝ≥0∞ → ℝ≥0∞ := fun r =>
    ⨅ (U : ℕ → Set (ProductInterval.V n × ℝ))
      (_ : E ×ˢ ProductInterval.interval ⊆ ⋃ i, U i)
      (_ : ∀ i, Metric.ediam (U i) ≤ r),
      ∑' i, ⨆ _ : (U i).Nonempty, (Metric.ediam (U i)) ^ (s + 1)
  rw [h_H001 (ProductInterval.V n) s E,
      h_H001 (ProductInterval.V n × ℝ) (s + 1) (E ×ˢ ProductInterval.interval)]
  change (⨆ r, ⨆ _ : 0 < r, CE r) ≤ ⨆ r, ⨆ _ : 0 < r, CP r
  apply iSup_le
  intro r
  apply iSup_le
  intro hr
  let q : ℝ≥0∞ := min r 1
  have hq : 0 < q := lt_min hr (by norm_num)
  have hqr : q ≤ r := min_le_left _ _
  have hqt : q < ⊤ := lt_of_le_of_lt (min_le_right r 1) (by simp)
  calc
    CE r ≤ CE q := by
      apply le_iInf
      intro W
      apply le_iInf
      intro hW
      apply le_iInf
      intro hd
      exact iInf_le_of_le W (iInf_le_of_le hW
        (iInf_le_of_le (fun i => (hd i).trans hqr) le_rfl))
    _ ≤ CP q := by
      apply le_iInf
      intro U
      apply le_iInf
      intro hU
      apply le_iInf
      intro hd
      exact @yui_nested_877752aa3eab39345043_0003 h_H001 h_H002 h_H003 n E s hs q hq hqt U hU hd
    _ ≤ ⨆ r, ⨆ _ : 0 < r, CP r :=
      le_iSup_of_le q (le_iSup_of_le hq le_rfl)
set_option Elab.async false in
theorem B009 : ∀ (X Y : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
 (e : X ≃L[ℝ] Y) (S : Set X), dimH (e '' S) = dimH S := by
  intro X Y _ _ _ _ e S
  exact e.dimH_image S
set_option Elab.async false in
theorem B005 : ∀ (n : ℕ) (S : Set (ProductInterval.V n × ℝ)),
 dimH (ProductInterval.appendCoord n '' S) = dimH S := by
  have h_H001 : ∀ (X Y : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
   (e : X ≃L[ℝ] Y) (S : Set X), dimH (e '' S) = dimH S := @YuiBasis.B009
  have yui_nested_a144468a30756955a11d_0001 (h_H001 : ∀ (X Y : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
   (e : X ≃L[ℝ] Y) (S : Set X), dimH (e '' S) = dimH S) : (∀ n : ℕ,
    Function.LeftInverse
      (fun z : ProductInterval.V (n + 1) =>
        ((EuclideanSpace.equiv (Fin n) ℝ).symm
          (Fin.init ((EuclideanSpace.equiv (Fin (n + 1)) ℝ) z)),
         ((EuclideanSpace.equiv (Fin (n + 1)) ℝ) z) (Fin.last n)))
      (ProductInterval.appendCoord n) ∧
    Function.RightInverse
      (fun z : ProductInterval.V (n + 1) =>
        ((EuclideanSpace.equiv (Fin n) ℝ).symm
          (Fin.init ((EuclideanSpace.equiv (Fin (n + 1)) ℝ) z)),
         ((EuclideanSpace.equiv (Fin (n + 1)) ℝ) z) (Fin.last n)))
      (ProductInterval.appendCoord n)) := by
    intro n
    constructor
    · intro p
      apply Prod.ext
      · change (EuclideanSpace.equiv (Fin n) ℝ).symm
          (Fin.init ((EuclideanSpace.equiv (Fin (n + 1)) ℝ)
            ((EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm
              (Fin.snoc ((EuclideanSpace.equiv (Fin n) ℝ) p.1) p.2)))) = p.1
        rw [ContinuousLinearEquiv.apply_symm_apply, Fin.init_snoc,
          ContinuousLinearEquiv.symm_apply_apply]
      · change ((EuclideanSpace.equiv (Fin (n + 1)) ℝ)
          ((EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm
            (Fin.snoc ((EuclideanSpace.equiv (Fin n) ℝ) p.1) p.2))) (Fin.last n) = p.2
        rw [ContinuousLinearEquiv.apply_symm_apply, Fin.snoc_last]
    · intro z
      change (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm
        (Fin.snoc
          ((EuclideanSpace.equiv (Fin n) ℝ)
            ((EuclideanSpace.equiv (Fin n) ℝ).symm
              (Fin.init ((EuclideanSpace.equiv (Fin (n + 1)) ℝ) z))))
          (((EuclideanSpace.equiv (Fin (n + 1)) ℝ) z) (Fin.last n))) = z
      rw [ContinuousLinearEquiv.apply_symm_apply, Fin.snoc_init_self,
        ContinuousLinearEquiv.symm_apply_apply]
  intro n S
  let e : (ProductInterval.V n × ℝ) ≃ₗ[ℝ] ProductInterval.V (n + 1) :=
    { toFun := ProductInterval.appendCoord n
      invFun := fun z =>
        ((EuclideanSpace.equiv (Fin n) ℝ).symm
          (Fin.init ((EuclideanSpace.equiv (Fin (n + 1)) ℝ) z)),
         ((EuclideanSpace.equiv (Fin (n + 1)) ℝ) z) (Fin.last n))
      left_inv := ((@yui_nested_a144468a30756955a11d_0001 h_H001) n).1
      right_inv := ((@yui_nested_a144468a30756955a11d_0001 h_H001) n).2
      map_add' := by
        intro p q
        apply (EuclideanSpace.equiv (Fin (n + 1)) ℝ).injective
        simp only [ProductInterval.appendCoord, map_add,
          ContinuousLinearEquiv.apply_symm_apply]
        ext i
        cases i using Fin.lastCases <;> simp
      map_smul' := by
        intro c p
        apply (EuclideanSpace.equiv (Fin (n + 1)) ℝ).injective
        simp only [ProductInterval.appendCoord, map_smul,
          ContinuousLinearEquiv.apply_symm_apply]
        ext i
        cases i using Fin.lastCases <;> simp }
  exact h_H001 (ProductInterval.V n × ℝ) (ProductInterval.V (n + 1))
    e.toContinuousLinearEquiv S
set_option Elab.async false in
theorem B010 : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X],
 dimH (Set.univ : Set X) = (Module.finrank ℝ X : ℝ≥0∞) := by
  intro X _ _ _
  exact Real.dimH_univ_eq_finrank X
set_option Elab.async false in
theorem B011 : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
 (S : Set X), (interior S).Nonempty → dimH S = (Module.finrank ℝ X : ℝ≥0∞) := by
  intro X _ _ _ S h
  exact Real.dimH_of_nonempty_interior h
set_option Elab.async false in
theorem B012 : ∀ (X : Type) [MetricSpace X] (A B : Set X), A ⊆ B → dimH A ≤ dimH B := by
  intro X _ A B h
  exact dimH_mono h
set_option Elab.async false in
theorem B008 : (∀ (n : ℕ) (E : Set (ProductInterval.V n)), dimH E ≤ (n : ℝ≥0∞)) ∧
 dimH ProductInterval.interval = 1 := by
  have h_H001 : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X],
   dimH (Set.univ : Set X) = (Module.finrank ℝ X : ℝ≥0∞) := @YuiBasis.B010
  have h_H002 : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
   (S : Set X), (interior S).Nonempty → dimH S = (Module.finrank ℝ X : ℝ≥0∞) := @YuiBasis.B011
  have h_H003 : ∀ (X : Type) [MetricSpace X] (A B : Set X), A ⊆ B → dimH A ≤ dimH B := @YuiBasis.B012
  have yui_nested_66b60048a428c354e242_0001 (h_H001 : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X],
   dimH (Set.univ : Set X) = (Module.finrank ℝ X : ℝ≥0∞)) (h_H002 : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
   (S : Set X), (interior S).Nonempty → dimH S = (Module.finrank ℝ X : ℝ≥0∞)) (h_H003 : ∀ (X : Type) [MetricSpace X] (A B : Set X), A ⊆ B → dimH A ≤ dimH B) : (∀ n : ℕ, Module.finrank ℝ (ProductInterval.V n) = n) := by
    intro n
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n
    exact finrank_euclideanSpace_fin
  constructor
  · intro n E
    calc
      dimH E ≤ dimH (Set.univ : Set (ProductInterval.V n)) :=
        h_H003 (ProductInterval.V n) E Set.univ (Set.subset_univ E)
      _ = (Module.finrank ℝ (ProductInterval.V n) : ℝ≥0∞) :=
        h_H001 (ProductInterval.V n)
      _ = (n : ℝ≥0∞) := by
        rw [(@yui_nested_66b60048a428c354e242_0001 h_H001 h_H002 h_H003) n]
  · have hi : (interior ProductInterval.interval).Nonempty := by
      rw [ProductInterval.interval, interior_Icc]
      refine ⟨(1 / 2 : ℝ), ?_⟩
      constructor <;> norm_num
    calc
      dimH ProductInterval.interval = (Module.finrank ℝ ℝ : ℝ≥0∞) :=
        h_H002 ℝ ProductInterval.interval hi
      _ = 1 := by simp
set_option Elab.async false in
theorem B013 : ∀ (X Y : Type) [MetricSpace X] [MetricSpace Y] (f : X → Y), Isometry f →
 ∀ (S : Set X), dimH (f '' S) = dimH S := by
  intro X Y _ _ f hf S
  exact hf.dimH_image S

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
    let omitted : Array String := #["h_E003", "h_E004", "h_E005", "h_E008"]
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
theorem P (n : ℕ) (E : Set (ProductInterval.V n)) (h_H001 : IsCompact E) (h_H002 : E.Nonempty) : dimH (ProductInterval.euclideanProduct n E) = dimH E + 1 := by
  exact yui_basis_export%(n, E, h_H001, h_H002, (@YuiBasis.B003), (@YuiBasis.B004), (@YuiBasis.B005), (@YuiBasis.B008))

end YuiClosed
