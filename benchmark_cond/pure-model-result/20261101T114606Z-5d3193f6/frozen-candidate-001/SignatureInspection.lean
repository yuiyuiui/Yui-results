import CompletedProof
set_option pp.universes true
set_option pp.explicit true
#print theorem_1
#print KdV.TheoremOne
#print KdV.ExactSolution
#print KdV.ObtainedBySmoothApproximation
#print KdV.SmoothSolution
#print KdV.KdVSolution
#print KdV.Duhamel
#print KdV.SobolevContinuousOn
#print KdV.LiWuStepIdentity
#print KdV.LiWuStageEstimate
#print KdV.LiWuProductEstimate
#print KdV.LiWuTrilinearEstimate
#print KdV.WeakTimeDerivative
#print KdV.BITGalerkinEstimate
#print KdV.SourceGalerkinODE
#print KdV.BITExistenceLimit
#print KdV.SourceLimitCertificate
#print KdV.SourceConstructedLimit
#print KdV.SourceWeakSolution
#print KdV.SourceNonzeroEquation
#print KdV.HomogeneousEssentiallyBounded
#print KdV.SourceLpConvergence
#print KdV.SourceWeakStarConvergence
#print KdV.BITHigherRegularity
#print KdV.BITLowRegularity
#print KdV.SourceUniqueContinuous
#print KdV.SourceLocalLipschitz
#print KdV.BITWeakerLipschitz
#print BareModelCompletion.LiWuProduct22
#print BareModelCompletion.HistoricalIntegralStageEstimate
#print BareModelCompletion.LiWuProposition34
#print BareModelCompletion.BITTheorems42And43
#print BareModelCompletion.BITLimit43
#print BareModelCompletion.BITNormalForm410
#print BareModelCompletion.LiWuStep52
#print BareModelCompletion.BITTheorem65
#print axioms theorem_1
#print axioms BareModelCompletion.liWuStage72_eq_endpoint
#print axioms BareModelCompletion.stage_to_historical
#print axioms BareModelCompletion.historical_to_stage
#print axioms BareModelCompletion.stage_iff_historical
#print axioms BareModelCompletion.trilinear_to_historical
#print axioms BareModelCompletion.galerkin_to_historical
#print axioms BareModelCompletion.bit42_from_joint
#print axioms BareModelCompletion.limit_to_historical
#print axioms BareModelCompletion.step_to_historical
#print BareModelCompletion.SourceLocalLipschitzAllTimes
#print BareModelCompletion.source_local_lipschitz_iff
#print axioms BareModelCompletion.source_local_lipschitz_iff
#print BareModelCompletion.sqrt_padding_lipschitz
#print BareModelCompletion.pairedSphereLift
#print BareModelCompletion.pairedSphereLift_lipschitz
#print BareModelCompletion.pairedSphereLift_norm
#print axioms BareModelCompletion.sqrt_padding_lipschitz
#print axioms BareModelCompletion.pairedSphereLift_lipschitz
#print axioms BareModelCompletion.pairedSphereLift_norm

#print BareModelCompletion.BITProposition41
#print BareModelCompletion.BITLimit43For
#print BareModelCompletion.BITDependence518
#print BareModelCompletion.BITDependence67Norm
#print BareModelCompletion.BITDependence67
#print BareModelCompletion.BITTheorem51
#print BareModelCompletion.BITTheorem63
#print BareModelCompletion.BITUniqueWeak
#print BareModelCompletion.bitHomSup
#print BareModelCompletion.HistoricalEndpointStageEstimate
#print BareModelCompletion.liWuEta415
#print BareModelCompletion.liWuRemainder61
#print BareModelCompletion.liWuCross410
#print BareModelCompletion.completed_theorem_1
#print BareModelCompletion.completed_exact_solution_exists
#print BareModelCompletion.completed_exact_solution_iff
#print BareModelCompletion.source_galerkin_family
#print BareModelCompletion.galerkin_higher_continuity
#print BareModelCompletion.galerkin_continuity_iff
#print BareModelCompletion.liWuEta415_eq_covariance
#print BareModelCompletion.liWuRemainder61_eq_remainder
#print BareModelCompletion.liWuCross410_eq_frozenCross
#print BareModelCompletion.sourceSphereData_properties
#print BareModelCompletion.sourceSphereData_difference
#print BareModelCompletion.sourceSphereData_L2_converges
#print BareModelCompletion.source_flow_coefficient_limit
#print BareModelCompletion.local_lipschitz_from_spheres
#print BareModelCompletion.high_to_historical
#print BareModelCompletion.low_to_historical
#print BareModelCompletion.bitHomSup_le_iff
#print BareModelCompletion.dependence67_iff
#print axioms BareModelCompletion.completed_theorem_1
#print axioms BareModelCompletion.completed_exact_solution_exists
#print axioms BareModelCompletion.completed_exact_solution_iff
#print axioms BareModelCompletion.local_lipschitz_from_spheres
#print axioms BareModelCompletion.high_to_historical
#print axioms BareModelCompletion.low_to_historical
#print axioms BareModelCompletion.galerkin_continuity_iff
#print axioms BareModelCompletion.dependence67_iff
#print BareModelCompletion.BITStrongLp43
#print BareModelCompletion.LiWuLemma72Grid
#print BareModelCompletion.HistoricalIntegralStageEstimate
#print BareModelCompletion.HistoricalEndpointStageEstimate
#print BareModelCompletion.strongLp43_to_scalar
#print BareModelCompletion.limit43For_to_certificate
#print BareModelCompletion.stage_grid_to_historical
#print BareModelCompletion.source_stage_shift
#print BareModelCompletion.source_stage_power_nonneg
#print axioms BareModelCompletion.strongLp43_to_scalar
#print axioms BareModelCompletion.stage_grid_to_historical
#print axioms BareModelCompletion.source_galerkin_family
#print BareModelCompletion.BITConstructedLimit43
#print BareModelCompletion.BITStrongLp43
#print BareModelCompletion.LiWuStep52Grid
#print BareModelCompletion.source_time_measure_eq
#print BareModelCompletion.CIntegral_congr_ae
#print BareModelCompletion.weakTimeDerivative_congr_ae
#print BareModelCompletion.source_rescaled_norm
#print BareModelCompletion.source_rescaled_memLp_iff
#print BareModelCompletion.source_rescaled_time_norm
#print BareModelCompletion.original_limit_exists
#print BareModelCompletion.original_constructed_weak
#print BareModelCompletion.step_grid_to_historical
#print BareModelCompletion.step_grid_iff_universal
#print KdV.RealValued
#print KdV.MeanZero
#print KdV.InHomSobolev
#print KdV.HomSobolevContinuousOn
#print KdV.InSobolev
#print KdV.Sobolev
#print KdV.hNorm
#print KdV.homogeneousNorm
#print KdV.sourceNorm
#print KdV.sourceStageLower
#print KdV.sourceStagePower
#print KdV.step
#print KdV.quadratic
#print KdV.cubicCorrection
#print KdV.lastBoundary
#print KdV.cubicBoundary
#print KdV.numerical
#print KdV.airy
#print KdV.inverseDerivative
#print KdV.inverseDerivative₂
#print KdV.normalizedMeasure
#print KdV.Torus
#print axioms BareModelCompletion.CIntegral_congr_ae
#print axioms BareModelCompletion.weakTimeDerivative_congr_ae
#print axioms BareModelCompletion.source_rescaled_memLp_iff
#print axioms BareModelCompletion.source_rescaled_time_norm
#print axioms BareModelCompletion.step_grid_iff_universal

#print BareModelCompletion.completed_exact_solution_unique
#print axioms BareModelCompletion.completed_exact_solution_unique

#print BareModelCompletion.BITTheorem65Norm
#print BareModelCompletion.bit65_iff_historical
#print axioms BareModelCompletion.bit65_iff_historical

#print BareModelCompletion.BochnerWeakTimeDerivative
#print BareModelCompletion.weakTimeDerivative_iff_bochner
#print axioms BareModelCompletion.weakTimeDerivative_iff_bochner

#print BareModelCompletion.tripleSumEquiv

#print BareModelCompletion.quadrupleSumEquiv

#print BareModelCompletion.triple_tsum_reindex

#print BareModelCompletion.quadruple_tsum_reindex

#print BareModelCompletion.nonresonant_zero_denominator

#print BareModelCompletion.cubic_zero_input

#print BareModelCompletion.quartic_zero_input

#print KdV.sourceProductExponent

#print KdV.sourceNormalization

#print KdV.weighted

#print KdV.homogeneousWeighted

#print KdV.SobolevContinuousOn

#print KdV.maximumError

#print Memℓp
#print MeasureTheory.MemLp

#print BareModelCompletion.BITGalerkinFamily
#print BareModelCompletion.source_global_galerkin_family
#print axioms BareModelCompletion.source_global_galerkin_family

#print BareModelCompletion.bitB2

#print BareModelCompletion.bitB3

#print BareModelCompletion.bitB14

#print BareModelCompletion.bitB24

#print BareModelCompletion.bitB4

#print BareModelCompletion.bitAresM412

#print BareModelCompletion.original_constructed_energy

#print axioms BareModelCompletion.original_constructed_energy

#print BareModelCompletion.quartic_nonres_domain
#print axioms BareModelCompletion.quartic_nonres_domain

#print BareModelCompletion.BITTheorems42And43AllBounds

#print BareModelCompletion.BITTheorem65AllBounds

#print BareModelCompletion.bit42_43_all_bounds_iff

#print BareModelCompletion.bit65_all_bounds_iff

#print axioms BareModelCompletion.bit42_43_all_bounds_iff
#print axioms BareModelCompletion.bit65_all_bounds_iff
