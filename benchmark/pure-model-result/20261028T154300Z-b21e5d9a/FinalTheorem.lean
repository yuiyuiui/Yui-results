import RoughDataDensity
noncomputable section
open KdV

/-- Theorem 1, conditional only on the explicitly typed cited source results.
 The stronger companion `uniform_rough_convergence` proves the same conclusion
 for every continuous Sobolev Duhamel solution, before selecting the solution
 obtained by smooth approximation. -/
theorem theorem_1 (externalStep : LiWuStepIdentity)
    (externalStage : LiWuStageEstimate) (externalProduct : LiWuProductEstimate)
    (externalTrilinear : LiWuTrilinearEstimate)
    (externalGalerkin : BITGalerkinEstimate) (externalLimit : BITExistenceLimit)
    (externalHigh : BITHigherRegularity) (externalLow : BITLowRegularity)
    (externalLipschitz : BITWeakerLipschitz) : TheoremOne := by
  intro T hT γ hγ hγ1 R hR
  obtain ⟨C, hC, τ0, hτ0, hConv⟩ := uniform_rough_convergence externalStep externalStage externalProduct
    externalTrilinear externalGalerkin externalLimit externalHigh externalLow externalLipschitz hT hγ hγ1 hR
  refine ⟨C, hC, τ0, hτ0, ?_⟩
  intro f hf hfr hfm hfR u hu
  exact hConv f hf hfr hfm hfR u hu.1

