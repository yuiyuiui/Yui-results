# Yui benchmark endpoint fidelity and source timing review

## Result and scope

Run: /Users/syyui/projects/Yui-results/benchmark/results/20261031T212422Z-533b379994

The final six literature endpoints E001-E006 and the full target P are faithful to the accepted NL0 meanings in the inspected source/definition/signature boundary. No unsupported external-theorem strengthening or wrong-object substitution was found. The existing independent source reviews and final interface-semantic review all record PASS. Current read-only Audit A and final Audit B validation succeeded.

The equivalence objects are the actual mathematical statements used by this run, with their complete definitions, conditions and quantifiers. Sound source clauses/specializations remain permitted under the user's clarified criterion. This is not a claim to have encoded every unused conclusion of every theorem in the cited papers.

This review combines direct inspection with existing independent judgments. It is not a new isolated Yui reviewer run, a full manual review of all internal Lean proof lines, or a machine proof of natural-language/Lean semantic equivalence. Machine Audit B establishes preservation and checked closure of the independently reviewed encoding.

## Frozen evidence

- Final Proof.lean SHA-256: 93d2d1f04878c16f0e84782666c02bf00a7bb228cd6bb729e1e8366dd1a3712b.
- Actual final file: nl0-to-lean/0002/workflow/audit-b/Proof.lean.
- Accepted source: nl0/merged-0001/nl0.json and spec.json.
- Independent Audit A: nl0/merged-0001/audit-a.json; its global role read both primary texts and recorded separate source checks for all six E rows.
- Final semantic authority: nl0-to-lean/0002/interface-review/review.json, SHA-256 e2845fcc24151e1a9c2caf15f2cef2fb4701c764cdc624bfc1a7b02d782250c5.
- Final machine receipt: nl0-to-lean/0002/workflow/audit-b/machine-acceptance.json; actual full E/P and defining header match the frozen authority, with proof integrity passed, no freeze deviation and no source warning.
- Original supplied target PDF SHA-256: 5d6432bf9c097991bf5d853f38e831a539b4f052f0ccf4010bba6e37b54507b6.
- Babin-Ilyin-Titi arXiv:0910.1389v2 primary PDF SHA-256: b6958c0b155bb8463f85900c4beaf75b1cf399382101a720cc39edf82cfac52e.
- Li-Wu 50-page FoCM-3.pdf primary PDF SHA-256: e71452d13d7d54b902c6d79a08bbcd68edab795f0a59366fff14399b98192f9b.

Both primary texts are retained in nl0/merged-0001/external-sources. Source identity, locators, source statements, five-part Audit A source reviews and actual endpoint explanations are collected in the existing EXTERNAL_THEOREM_CORRESPONDENCE.json. That collection is evidence navigation, not an independent verdict by itself.

## Six external endpoints

| E | Actual Lean meaning | Primary counterpart | Assessment |
|---|---|---|---|
| E001 | EFlow, Proof.lean:155 | Babin-Ilyin-Titi exact-flow/Galerkin/limit/regularity suite, Theorems 4.2-4.3,5.1,6.3-6.4 with their defining context | Full nonnegative regularity range, source Fourier equation and real mean-zero homogeneous norms; bound, dependence, conservation, compatibility, smooth approximation and convergence clauses were inspected. No integrator convergence is an input. |
| E002 | EDependence, line 176 | Theorem 6.5/(6.22) | Preserves -1<theta<=0, the sum of the initial L2 norms, and constants depending on the norm bound and theta before the horizon. Physical/twisted estimates agree by the common isometry. |
| E003 | ETri, line 199 | Li-Wu Proposition 3.4/(3.13) | Both dynamic and constant-input bounds; alpha endpoints, genuine weak derivative, essential norms, negative index 23/14, all right-side slots, and source measure normalization are retained. |
| E004 | EStage, line 212 | Li-Wu Lemma 7.2/(7.2)-(7.3) | Mean-zero bilinear stage, all beta endpoints, all three beta0 cases and a sufficiently small positive epsilon are retained. |
| E005 | EProduct, line 220 | Li-Wu (2.2)-(2.3) | Includes sigma=0, both positive-epsilon endpoint cases and the source unnormalized norm. |
| E006 | Endpoint, line 225 | Li-Wu (4.20)-(4.23),(5.2) | The unchanged four-term update, time/frame signs, both endpoints and the exact covariance remainder match the smooth real mean-zero source identity. |

The ETri dynamic constant can be selected independently of alpha: the source alpha=0 case applies to every admissible alpha>=0 input by Sobolev inclusion, while X and the negative derivative norm are unchanged. Thus the earlier constant quantifier does not add an unsupported estimate. The frozen definitions preserve the source right-side permutations without assuming an operator-slot symmetry.

EFlow places a common subsequence before all lower positive sigma. Under the same uniform upper Sobolev bound, convergence at one intermediate index plus interpolation supplies every sigma below the upper order; finite time and the same bounds supply every finite time exponent. This quantifier organization does not require a stronger compactness theorem.

## Source-class check for E001

The broad SourceClass predicate at line 131 uses the integrated source equation and essentially bounded L2, whereas the displayed Theorem 6.4 states uniqueness in the continuous L2 class. This difference was inspected rather than accepted from a PASS label.

The primary text provides more than the isolated displayed Theorem 6.4:

1. Definition 3.1 and Remark 3.1 give the integrated coefficient solution class and absolute continuity of each Fourier coefficient.
2. Remark 3.5 says that every such solution satisfies the second normal form as an L-infinity Hdot0 functional equation.
3. Lemma 7.2 gives B2 smoothing by one derivative, Lemma 7.6 gives B3 smoothing by two, and Lemmas 7.11/7.14 bound the normal-form right side.

These facts give the continuous L2 representative needed for Theorem 6.4. Essential L2 boundedness and continuous coefficients first imply pointwise L2 boundedness by finite-mode limits. The B2 and B3 correction terms are continuous in L2: their output smoothing gives uniform spatial tails, and each fixed output coefficient is continuous by finite-frequency approximation of the source kernels. For example the B3 kernel at fixed output k is proportional, off the excluded resonances, to 1/[a(k-a)(k-b)(k-c)] with a+b+c=k; its squared kernel is summable in the two free input indices, and the product-square sum is bounded by the sixth power of the common L2 bound. This controls coefficient tails uniformly in time. The corrected normal-form path has an L2-bounded derivative and hence is continuous in L2; adding back the two corrections gives continuity of the original path.

Consequently the SourceClass uniqueness interpretation is supported by the primary normal-form context together with the stated continuous-class theorem. It was not justified merely by changing the words of Theorem 6.4. These are source-admissibility deductions; this review does not claim a newly added Lean bridge theorem.

## Target concordance

The final header defines GridError at line 505 and Target at line 513; actual export AuditBExport.P is at line 15811.

The target retains T>0, 0<gamma<=1 and R>0; constants C,tau0 are chosen before every datum in the complete real mean-zero H^gamma ball and every positive L. The step is exactly psi, without a frequency cutoff, with all four Htau terms. GridError asserts the error at every n<=L, including 0 and L, equivalent to the finite maximum in the original statement. Fourier normalization, Sobolev norm, torus period, real/mean-zero conditions and the source-to-target PDE sign change agree with the source.

One syntactic difference is important: Target uses forall L exists u, whereas the paper refers to its fixed exact flow. Exact includes uniqueness against every KSol, and the checked exact-flow construction supplies an exact solution independently of L. Therefore all the selected u for different L coincide on [0,T]. Transporting the grid inequalities along that equality recovers the original single-flow statement; conversely the fixed flow supplies each existential witness. This is not a weaker target through choosing a different solution at each step count.

SmoothApprox is uniform in the stated Sobolev norm and uses genuine C-infinity time regularity. The earlier analytic-top/weak-derivative interface defects were repaired before final freeze; the final header uses the explicit inner-top coercion and a genuine test-function weak derivative.

## Source timing

Canonical native stages were used once each. Copied review/runtime evidence was not double-counted.

| Observable | Count | Recorded seconds |
|---|---:|---:|
| search_external_sources | 4 | 20.215983 |
| read_external_source | 21 | 11.669595 |
| Above retrieval/access tools combined | 25 | 31.885578 |
| Independent global Audit A reads of cached primary text via read_task_input(s) | 43 | about 0.213468 of tool execution |
| Entire global Audit A stage | 1 | 288.581343 |
| Both pre-freeze interface semantic review stages | 2 | 663.881154 |

Initial author retrieval/access activity runs from 2026-11-01 05:27:09.319862 to 05:28:15.474820 Asia/Shanghai, an elapsed span of 66.154958 seconds. Its 22 source tools consume 24.251323 recorded seconds; intervening model/service time and interleaved work are not pure retrieval time.

The auditor additionally performs three external metadata/access calls totaling 7.634255 seconds. Its 43 cached primary-text reads occur between 05:49:22.003818 and 05:49:56.773579. Local read execution is short because it serves already retrieved text; this does not mean the model understood 92 PDF pages in 0.21 seconds.

The 288.58-second global review includes source verification, target/definition/structure review and writing the review. The 663.88-second interface-review total includes both failed and repaired submissions and covers E/P, representation and local plans. Neither is an isolated source-only timer.

**Pure model time spent understanding and checking primary statements is not separately recorded.** Therefore 31.89 seconds is retrieval/access tool execution, not the complete cost of finding, reading and semantically verifying the literature. The original four-hour-nine-minute run is dominated by later local Lean proof work, not these recorded retrieval calls.

## Validation and preservation

Current read-only commands:

    python3 -B RUN/runtime/nl0/scripts/nl0.py check RUN/nl0/merged-0001/nl0.json --spec RUN/nl0/merged-0001/spec.json --audit RUN/nl0/merged-0001/audit-a.json
    python3 -B RUN/runtime/nl02lean/scripts/audit_b.py check RUN/nl0-to-lean/0002/workflow/audit-b --review RUN/nl0-to-lean/0002/workflow/audit-b/machine-acceptance.json

Both exited 0; the first reported a valid current-standard independent Audit A receipt with no unresolved reviews/source warnings, and the second AUDIT-B-PASSED with exact interface consistency and proof integrity. No new model or Lean run was started. Original proof, source, profiles, receipts and costs were not modified.

Research Cognition scientific-computing 0.133.0 and pde-continuum 0.94.0 were selected by caller judgment, unrated. Initial broad cards were not used as theorem evidence; the audit relied on actual primary texts and bound run artifacts. The route receipt is preserved with this report.

