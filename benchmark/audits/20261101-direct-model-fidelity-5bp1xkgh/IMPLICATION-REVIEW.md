# External-premise implication review after criterion clarification

## Current verdict

**SOURCE-MAPPING-VERIFIED within the inspected nine-literature-premise boundary**, allowing sound specializations and weakened conclusions as explicitly authorized by the user.

The applicable acceptance relation is:

    primary theorem + proved definition/representation bridges
        ==> actual external premise used by Lean.

A converse is not required. This current verdict supersedes the negative full-equivalence gate in REPORT.md for the clarified acceptance criterion. The earlier report remains preserved as a record of a different, unnecessarily strict criterion. Its missing-converse findings are not evidence of an invalid external assumption.

The candidate is unchanged: Proof.lean SHA-256 bf73ff25c1c67c020023ad545649bd2e0444658191c6c0c637b86528ad0b0cd0. All seven frozen input bindings were rechecked unchanged. The prior fresh Lean 4.32.2 / pinned Mathlib clean build and actual signature inspection are reused; no new model, proof construction, or compilation was necessary.

## Classification of every explicit external premise

| Premise | Direction checked | Classification |
|---|---|---|
| E1 LiWuStepIdentity | The source identity is used only for real mean-zero H1 inputs and the actual fixed scheme/remainder. | Valid domain specialization; stronger input requirements, not a new rough-input conclusion. |
| E2 LiWuStageEstimate | Source Lemma 7.2 supplies the same bilinear estimate, complete beta interval, exponent, zero-mean convention and positive losses. The finite final-time scope is explicit. | Source estimate in the local representation; no unsupported weaker-regularity range or stronger rate found. |
| E3 LiWuProductEstimate | Source (2.2)-(2.3) supplies the same four exponent cases. The positive measure factor is retained and normalized conversion is separately proved. | Same product estimate with a checked normalization bridge. |
| E4 LiWuTrilinearEstimate | Both source Proposition 3.4 clauses are retained on intervals of length at most one, using the source derivative exponent 23/14. Right-side permutations leave the operator slots fixed. | Valid bounded-interval restriction and explicit weak-derivative/essential-norm formulation; no stronger time or spatial regularity conclusion found. |
| E5 BITGalerkinEstimate | Theorem 4.2 concludes both the normal-form identity and the uniform estimate. The encoded premise takes only the estimate. | Dropping a conjunct from the conclusion: legitimate weakening. |
| E6 BITExistenceLimit | Theorem 4.3 supplies the limiting solution, convergence, energy and a common bound from Theorem 4.2. The certificate merely existentially retains a common bound after the datum. | Forgetting quantitative bound-dependence information: legitimate weakening, not additional uniformity. |
| E7 BITHigherRegularity | Source Theorem 5.1 / (5.18) supplies continuity, uniqueness, conservation and quantitative Lipschitz solution dependence. The encoded dependence asks only for a neighborhood of each fixed base datum. | Local qualitative consequence of the cited stronger dependence result. |
| E8 BITLowRegularity | Source Theorem 6.3 / (6.7) supplies the corresponding positive low-regularity dependence; the encoded property has the same local restriction. | Local qualitative consequence, with the original 0<s<=1/2 range retained. |
| E9 BITWeakerLipschitz | Theorem 6.5 supplies the same negative-index range, initial L2 sum bound and constants depending on M,theta before T and both data. Continuous-class restrictions and a.e. time bounds do not strengthen the conclusion. | Same source estimate with its solution-class interpretation and separately proved transport/all-time corollary. |

All nine literature inputs are from results actually cited by the supplied natural-language proof.

## Why the previously highlighted cases are safe under this criterion

### Estimate-only conclusion

For E5 the source has the schematic form:

    assumptions -> (normal_form_identity AND norm_estimate).

The external premise retains:

    assumptions -> norm_estimate.

The first proposition implies the second directly. It is unnecessary to reintroduce an unused source conclusion to justify this use.

### Qualitative local dependence

For E7/E8 fix the base datum f, regularity s and final time T. Restrict the other datum g to a positive-radius neighborhood of f; for example radius one bounds its Sobolev norm by norm(f)+1. The cited quantitative solution-map estimates and their a priori bounds supply a common dependence constant on this neighborhood. Restricting the comparison to continuous weak solutions uses the cited uniqueness class. The all-time estimate also implies the a.e.-time estimate used by SourceLocalLipschitz.

This discards quantitative information and comparison data outside the neighborhood. It does not assert C1 regularity, a lower admissible Sobolev threshold, or an unsupported uniform constant independent of the base datum.

### Specializations still require matching objects and conditions

Calling something a specialization is not sufficient. A condition must actually imply the source hypotheses, the source conclusion must imply the used conclusion, and objects, domains, quantifier order and constant dependence must agree through justified bridges. Exchanging stronger regularity for weaker decay, without a proof of the needed implication, would not be accepted by this audit.

## Scope and preservation

No unsupported strengthening or wrong-object substitution was found among these nine premises in the source/definition/signature review. This is a manual source-admissibility assessment under explicit cited literature, not a new Yui Audit B receipt, a machine proof of the literature, or a complete manual audit of every internal Lean proof line.

The target-concordance assessment is unchanged. Neither the original proof nor historical benchmark evidence is edited. This supplement corrects the acceptance interpretation rather than repairing the candidate.

The same versioned Research Cognition receipt is reused: numerical integrator, KdV flow, source versions, representation and normalization are unchanged. The user clarified the implication criterion; no expert card or external candidate was used as proof evidence.

