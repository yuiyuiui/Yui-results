# Post hoc source and target correspondence review

## Verdict and scope

**SOURCE-MAPPING-VERIFIED within the inspected source/signature boundary; target concordance verified.** No material target, source or added-assumption mismatch was found in that boundary. This is a separate manual post hoc assessment of the completed direct candidate, not an original benchmark-stage verdict, Yui Audit B receipt, or full audit of all 13,958 proof lines. It does not add proof inputs or feedback to either measured arm.

The source inputs are clauses/specializations of published results, rather than verbatim encodings of every conclusion of each source theorem. In particular E5 retains an estimate clause, E7/E8 retain qualitative local dependence, and E4 uses bounded intervals. These restrictions are disclosed and sufficient for the recorded uses; they do not replace the target by a different numerical method or add its convergence as a premise.

## Frozen candidate and target

Candidate SHA-256: `bf73ff25c1c67c020023ad545649bd2e0444658191c6c0c637b86528ad0b0cd0`.

Theorem 1 in the supplied PDF, p. 2: for positive T and R and 0<gamma<=1, choose positive C and tau0 depending only on T,gamma,R, before every real mean-zero H^gamma datum in the R ball, its stated exact solution and positive integer L. With tau=T/L<=tau0, the maximum L2 error over n=0,...,L is at most C*tau^gamma for the complete fixed unfiltered update.

The frozen source is the supplied local PDF, SHA-256 `5d6432bf9c097991bf5d853f38e831a539b4f052f0ccf4010bba6e37b54507b6`. The paper's definitions on p. 2 and exact-flow convention on p. 3 were checked as part of the target.

## Target crosswalk

| Boundary | Lean location | Assessment |
|---|---|---|
| Period, measure and Sobolev norm | Proof.lean:20-33, 158 | MATCH: Period 2pi, normalized Haar measure and weight (1+k^2)^(s/2); complete weighted l2 realization and dense polynomial image. |
| Reality and zero mean | Proof.lean:240-241 | MATCH: Conjugate Fourier symmetry and zero coefficient. |
| Full fixed scheme | Proof.lean:250-291 | MATCH: Every term of the two corrections, both endpoint differences and all Fourier modes are retained. |
| Constants and quantifiers | Proof.lean:433-439 | MATCH: C,tau0 precede the datum, exact solution and positive integer L; dependence is only T,gamma,R. |
| Convergence target | Proof.lean:427-439 | MATCH: Maximum over range(L+1), exponent gamma, positive T/L, and no logarithmic factor or cutoff. |
| Solution meaning and non-vacuity | Proof.lean:399-425, 13543-13558 | MATCH_WITH_INTERNAL_BRIDGES: Duhamel class plus smooth approximation; equivalence and existence declarations are proved under the same cited external inputs. |
| Distributional physical equation | Proof.lean:13912-13933 | MATCH_WITH_INTERNAL_BRIDGES: The H^-3 identity and H^3 spatial tests give the specified PDE meaning. |
| Only declared final premises | Proof.lean:13946-13957; verification.log | MATCH: Exactly nine explicitly typed source inputs; no extra convergence/stability/target premise appears in the final signature. |

The Fourier Sobolev representation is concrete rather than an arbitrary predicate. The polynomial-density declaration is at line 872. Physical multiplication/Fourier convolution correspondence is at line 5703. The solution-equivalence and existence declarations avoid treating an empty solution class as a target proof. Their full derivations are kernel-covered by the existing compiled candidate; this review inspected their signatures and relevant correspondence definitions, rather than independently replaying every internal proof.

## External source ledger

The nine final source inputs were expanded beyond their names, including the trilinear structure fields and the weak-solution, limit-certificate and dependence predicates. Primary source bytes were retrieved independently of the author's source notes:

- [Li-Wu, 50-page author manuscript](https://www.polyu.edu.hk/ama/profile/byli/FoCM-3.pdf), local `li-wu.pdf`, SHA-256 `e71452d13d7d54b902c6d79a08bbcd68edab795f0a59366fff14399b98192f9b`.
- [Babin-Ilyin-Titi, arXiv:0910.1389v2](https://arxiv.org/pdf/0910.1389v2), local `babin-ilyin-titi.pdf`, SHA-256 `b6958c0b155bb8463f85900c4beaf75b1cf399382101a720cc39edf82cfac52e`.

| Input | Lean line | Original locator | Verdict |
|---|---:|---|---|
| LiWuStepIdentity | 6941 | Li-Wu, PDF pp. 23-25, (4.20)-(4.23), (5.2) | MATCH_AS_USED |
| LiWuStageEstimate | 3767 | Li-Wu, PDF pp. 32-34, Lemma 7.2 and (7.2)-(7.3) | MATCH_AS_USED |
| LiWuProductEstimate | 3750 | Li-Wu, PDF p. 8, (2.2)-(2.3) | MATCH_AS_USED |
| LiWuTrilinearEstimate | 4232 | Li-Wu, PDF pp. 12,14, (3.13), Proposition 3.4 | MATCH_AS_USED |
| BITGalerkinEstimate | 5753 | Babin-Ilyin-Titi v2, PDF pp. 11,13, (4.1)-(4.2), Theorem 4.2/(4.13) | MATCH_ESTIMATE_CLAUSE |
| BITExistenceLimit | 6510 | Babin-Ilyin-Titi v2, PDF p. 14, Theorem 4.3/(4.20)-(4.21) | MATCH_CONSTRUCTION_CLAUSE |
| BITHigherRegularity | 6541 | Babin-Ilyin-Titi v2, PDF pp. 19,21, Theorem 5.1/(5.18) | MATCH_QUALITATIVE_CLAUSES |
| BITLowRegularity | 6551 | Babin-Ilyin-Titi v2, PDF pp. 22,27, Theorem 6.3/(6.7) | MATCH_QUALITATIVE_CLAUSES |
| BITWeakerLipschitz | 6570 | Babin-Ilyin-Titi v2, PDF p. 28, Theorem 6.5/(6.22) | MATCH_AS_USED |

Detailed interface assessments and their precise qualifications are in `external-correspondence.json`. Representation changes are not silently inserted into source hypotheses: `sourceNorm` uses sqrt(2pi), the normalized product/trilinear conversions are project lemmas, and the source PDE reflection/sign transform is proved internally. The target's initial-ball bound is also internal rather than an unjustified monotonicity assumption about a source constant. The original Li-Wu logarithmic convergence theorem is not an input to `theorem_1`.

## Mechanical evidence reused, not rerun

The actual supervisor receipt binds the current source hash and records whole-file compilation. Existing verification expands the root to exactly the nine source inputs and reports only propext, Classical.choice and Quot.sound. The final file imports only Mathlib; its active options adjust heartbeats and do not disable kernel checking. The pinned recorded environment is Lean 4.32.2 / Mathlib commit 905b95818eb32af7874a58b427f50c1711a5e96c.

No new Lean or model session was launched by this review. No fresh clean build or full internal proof audit was performed. Accordingly this report does not grant FULL-RIGOR-CHECK-PASSED or claim Lean proved the cited literature. Its positive conclusion is the requested manual source/target correspondence assessment under the recorded kernel-checked conditional candidate.

## Preservation

The direct candidate and its original execution evidence are unchanged. The former cross-arm runtime comparison was removed during benchmark cleanup. This post hoc review remains separate from measured construction and is not a full internal proof audit.
