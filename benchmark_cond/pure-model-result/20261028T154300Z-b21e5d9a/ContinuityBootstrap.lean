import Proof
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

/-- A genuine first-crossing argument discharges a temporary unit bound.
 The conclusion on each prefix is an actual hypothesis to be instantiated
 by the internally proved restarted stability estimate. -/
theorem continuity_unit_bootstrap {a b D : ℝ} (_hab : a ≤ b)
    (q : ℝ → ℝ) (hq : Continuous q) (hqa : q a < 1) (hD : D < 1)
    (hLocal : ∀ c ∈ Set.Icc a b, (∀ r ∈ Set.Icc a c, q r ≤ 1) → q c ≤ D) :
    ∀ t ∈ Set.Icc a b, q t ≤ D := by
  have hUnit : ∀ t ∈ Set.Icc a b, q t ≤ 1 := by
    by_contra hbad
    push Not at hbad
    obtain ⟨r, hr, hqr⟩ := hbad
    obtain ⟨s, hs, hqs⟩ := intermediate_value_Icc hr.1 hq.continuousOn ⟨hqa.le, hqr.le⟩
    let S : Set ℝ := Set.Icc a b ∩ {t | q t = 1}
    have hScompact : IsCompact S := isCompact_Icc.inter_right (isClosed_eq hq continuous_const)
    have hSnonempty : S.Nonempty := ⟨s, ⟨hs.1, hs.2.trans hr.2⟩, hqs⟩
    obtain ⟨c, hc, hmin⟩ := hScompact.exists_isMinOn hSnonempty continuous_id.continuousOn
    have hcI : c ∈ Set.Icc a b := hc.1
    have hqc : q c = 1 := hc.2
    have hPrefix : ∀ x ∈ Set.Icc a c, q x ≤ 1 := by
      intro x hx
      by_contra hqx
      have hqx' : 1 < q x := lt_of_not_ge hqx
      obtain ⟨y, hy, hqy⟩ := intermediate_value_Icc hx.1 hq.continuousOn ⟨hqa.le, hqx'.le⟩
      have hyS : y ∈ S := ⟨⟨hy.1, hy.2.trans (hx.2.trans hcI.2)⟩, hqy⟩
      have hcy : c ≤ y := hmin hyS
      have hyx : y < x := lt_of_le_of_ne hy.2 (by intro h; rw [h] at hqy; linarith)
      linarith [hx.2]
    have hcD := hLocal c hcI hPrefix
    linarith
  intro t ht
  exact hLocal t ht (fun r hr => hUnit r ⟨hr.1, hr.2.trans ht.2⟩)

end KdV
