# Direct-model source and target fidelity audit

## Verdict

Principal status: **SOURCE-MISMATCH**, specifically **strict full-original-statement concordance not met**.

- The provenance half of the user's external-dependency requirement passes: all nine explicit literature parameters refer to results or identities actually cited in the supplied natural-language proof.
- The requirement that every parameter be a complete equivalent formalization of its original theorem does **not** pass. Some parameters intentionally retain clauses, specializations or qualitative consequences. This is a scope/encoding mismatch under the requested strict criterion, not evidence that the imported clauses are false.
- The target statement is **MATCH_WITH_CHECKED_INTERNAL_BRIDGES**: no changed method, narrower datum class, lost initial-ball uniformity, wrong exponent or omitted grid endpoint was found.
- A fresh pinned build and elaborated root/type/axiom inspection passed. This audit does not claim a complete line-by-line manual review of all internal proofs or a full round-trip audit.

## Frozen artifacts and trust

Audited historical run: /Users/syyui/projects/Yui-results/benchmark/pure-model-result/20261028T154300Z-b21e5d9a

Candidate Proof.lean SHA-256: bf73ff25c1c67c020023ad545649bd2e0444658191c6c0c637b86528ad0b0cd0

Target PDF SHA-256: 5d6432bf9c097991bf5d853f38e831a539b4f052f0ccf4010bba6e37b54507b6

The unchanged candidate was copied to a fresh temporary directory and compiled there with Lean 4.32.2 and Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c. Its source imports only Mathlib. Its root has exactly the nine literature premises listed below; its kernel axiom report contains only propext, Classical.choice and Quot.sound. The source token scan found no sorry, admit, axiom, opaque or unsafe. No dependency or runtime was updated.

The original candidate and its original evidence were not modified. The 2026-10-29 post hoc review is retained as a locator and explicitly did not claim complete original-theorem equivalence. Its candidate hash matches this audit. Its MATCH_AS_USED verdict is not inherited as a pass of the stricter current requirement.

Primary sources checked:

1. Supplied 15-page target PDF, especially pp.2-3,6-8,11 and the bibliography.
2. [Li-Wu, 50-page author manuscript](https://www.polyu.edu.hk/ama/profile/byli/FoCM-3.pdf), SHA-256 e71452d13d7d54b902c6d79a08bbcd68edab795f0a59366fff14399b98192f9b.
3. [Babin-Ilyin-Titi, arXiv:0910.1389v2](https://arxiv.org/pdf/0910.1389v2), SHA-256 b6958c0b155bb8463f85900c4beaf75b1cf399382101a720cc39edf82cfac52e.

Existing independently downloaded primary PDFs were read directly; critical formula pages were rendered and visually inspected. The public primary URLs were also checked. Author correspondence notes were treated as claims to compare against the actual types and primary texts.

## Exact target

For every T>0, 0<gamma<=1 and R>0, choose C>0 and tau0>0 before every real mean-zero datum f in H^gamma with norm <=R, its stipulated exact solution u, and every positive natural L. With tau=T/L<=tau0, the maximum over n=0,...,L of the normalized L2 norm of u(n*tau)-numerical(tau,f,n) is <=C*tau^gamma.

The torus is R/(2*pi*Z); measure is dx/(2*pi); the Fourier character and coefficient signs, weight (1+k^2)^(s/2), and the PDE u_t+u_xxx=partial_x(u^2)/2 agree with the source. The algorithm is the exact unfiltered full-mode update, including all four H_tau terms and both endpoint differences. No logarithmic factor, spatial cutoff, support constraint, or added numerical Sobolev bound appears in the target.

| Boundary | Actual declarations / lines in Proof.lean | Finding |
|---|---|---|
| Concrete Sobolev completion, normalized L2 | InSobolev:48; hNorm:158; normalizedL2Equiv:214; normalized_fourierCoeff:226; polynomialToSobolev_denseRange:872 | Matches the stated completion and Fourier/L2 conventions. |
| Reality and mean zero | RealValued:240; MeanZero:241; reconstructL2_real_iff:5638 | Concrete Fourier conditions, with physical interpretation bridges. |
| Full numerical method | airy:250; inverseDerivative:254; quadratic:261; cubicBoundary:267; lastBoundary:272; cubicCorrection:278; step:285; numerical:289 | All constants, signs, inverse derivatives, projections and endpoint orders match the displayed source method. |
| Domain and norms are used legitimately | step_inSobolev:2966; numerical_inSobolev:2972; normalized_L2_product_coeff:5703 | The raw totalized sequence/norm definitions are accompanied by actual membership and multiplication lemmas. |
| Quantifiers, initial ball and maximum | maximumError:428; TheoremOne:433 | C and tau0 precede all data, solutions and step counts; range(L+1) includes 0 and L. |
| Solution class and non-vacuity | KdVSolution:406; ExactSolution:424; kdv_solution_unique:13149; exactSolution_iff_kdvSolution:13543; exact_solution_exists:13551 | The approximation predicate is proved not to narrow the continuous positive-Sobolev Duhamel solution class under the same cited flow premises; existence is separately established. |
| Physical PDE | kdv_solution_distributional_spatial_tests:13912 | The concrete negative-Sobolev distributional identity and spatial test pairing are proved, rather than assumed as an abstract selector. |
| Root signature | theorem_1:13946; signature-inspection.log | Exactly the nine literature premises, with no additional convergence, stability, numerical regularity or target assumption. |

These are source/definition/signature findings under explicit literature premises. They are not a claim that Lean proved those papers.

## External provenance and strict-equivalence matrix

All nine declarations belong to the two mathematical references used by the supplied proof. Proven Mathlib declarations are distinguished from these nine explicit EXTERNAL parameters.

| ID | Lean declaration (line) | Primary original | Cited in NL PDF | Current finding |
|---|---|---|---|---|
| E1 | KdV.LiWuStepIdentity (6941) | Li-Wu, (4.20)-(4.23), (5.2), PDF pp.23-25 | Target PDF p.8 | SOURCE_IDENTITY_SPECIALIZATION |
| E2 | KdV.LiWuStageEstimate (3767) | Li-Wu, Lemma 7.2 and (7.2)-(7.3), PDF pp.32-34 | Target PDF pp.2,7 | DISPLAYED_ESTIMATE_CORRESPONDENCE |
| E3 | KdV.LiWuProductEstimate (3750) | Li-Wu, (2.2)-(2.3), PDF p.8 | Target PDF p.7 | DISPLAYED_ESTIMATE_CORRESPONDENCE |
| E4 | KdV.LiWuTrilinearEstimate (4232) | Li-Wu, (3.13), Proposition 3.4, PDF pp.12,14 | Target PDF p.6 | BOUNDED_INTERVAL_SOURCE_FORMULATION |
| E5 | KdV.BITGalerkinEstimate (5753) | Babin-Ilyin-Titi, Theorem 4.2, PDF p.13 | Target PDF p.3 | PARTIAL_THEOREM_NOT_FULL_ENCODING |
| E6 | KdV.BITExistenceLimit (6510) | Babin-Ilyin-Titi, Theorem 4.3, PDF pp.14-15 | Target PDF p.3 | CONSTRUCTION_CLAUSES_WITH_BOUND_DEPENDENCE_QUALIFICATION |
| E7 | KdV.BITHigherRegularity (6541) | Babin-Ilyin-Titi, Theorem 5.1 and (5.18), PDF pp.19,21 | Target PDF p.3 | QUANTITATIVE_CONCLUSION_WEAKENED |
| E8 | KdV.BITLowRegularity (6551) | Babin-Ilyin-Titi, Theorem 6.3 and (6.7), PDF pp.22,27 | Target PDF p.3 | QUANTITATIVE_CONCLUSION_WEAKENED |
| E9 | KdV.BITWeakerLipschitz (6570) | Babin-Ilyin-Titi, Theorem 6.5 and (6.22), PDF p.28 | Target PDF p.3 | DISPLAYED_ESTIMATE_CORRESPONDENCE |

### E1: KdV.LiWuStepIdentity

Actual fixed update and covariance remainder agree with the cited identity. The premise is restricted to real mean-zero H1 inputs; it is not an encoding of the source identity in its full rough-input scope.

### E2: KdV.LiWuStageEstimate

Retains the bilinear operator, zero-mean convention, all three lower-endpoint cases, positive epsilon loss, complete beta interval and interpolation exponent. This audit checks the source formula and interpretation, not an independently formalized full-source iff.

### E3: KdV.LiWuProductEstimate

Retains all four gamma cases and positive losses; sourceNorm explicitly preserves unnormalized spatial norms. The normalized corollary is separately proved.

### E4: KdV.LiWuTrilinearEstimate

Retains both dynamic/static clauses, derivative exponent 23/14, essential norms and right-hand-side permutations with operator slots fixed. Uses an explicit interval bound <=1 and a coefficient weak-derivative representation. Full bidirectional equivalence with every bounded-interval source formulation is not supplied.

### E5: KdV.BITGalerkinEstimate

Imports the a priori estimate (4.13) only. The original theorem also concludes that the Galerkin solution solves the second normal-form equation (4.10). That conclusion is absent from this external premise; its omission is expressly disclosed in the source comment.

### E6: KdV.BITExistenceLimit

Retains a fixed lower sigma, subsequence, all finite p>1 strong convergence, weak-star convergence, weak solution and a.e. energy identity. The certificate existentially chooses a common bound after the datum; it does not bind that number to the preceding Theorem 4.2 constant with its complete source dependence. This is not certified as a complete one-to-one theorem encoding.

### E7: KdV.BITHigherRegularity

Continuity, continuous-class uniqueness and energy conservation are retained for constructed limits. SourceLocalLipschitz chooses a neighborhood and constant after the base datum. It omits the source's quantitative all-pair dependence in (5.18), to which Theorem 5.1 explicitly refers.

### E8: KdV.BITLowRegularity

Retains the full 0<s<=1/2 range and constructed-limit continuity/continuous-class uniqueness. Quantitative dependence in (6.7) is replaced by the same qualitative local neighborhood predicate; no full converse is supplied.

### E9: KdV.BITWeakerLipschitz

Retains -1<theta<=0, the sum of initial L2 norms, and positive constants depending on M,theta before T and both flows. The essential-time estimate is lifted to all times by separately proved continuity. The original Theorem 6.4 is not an extra root parameter.


## Decisive strict-equivalence failures

### E5: an estimate clause is not the complete Theorem 4.2

The original Theorem 4.2 has two conclusions: the source Galerkin trajectory satisfies the second normal-form equation (4.10), and it satisfies the uniform-in-truncation estimate (4.13). BITGalerkinEstimate encodes only the second conclusion. The candidate's own preceding comment explicitly excludes the unused identity.

Thus a source-to-estimate specialization is documented. A complete corresponding source proposition and a converse equivalence are not supplied. Do not describe this premise as the entire original theorem.

### E7/E8: quantitative dependence is replaced by a local qualitative predicate

The actual predicate SourceLocalLipschitz at line 6530 has the pattern

    for each fixed base datum f and its flow v:
      exists radius r>0 and C>0,
      for all g with norm(g-f)<r and their continuous weak flows w:
        norm(v-w) <= C * norm(f-g) almost everywhere in time.

The original Theorem 5.1 explicitly invokes (5.18), with the prescribed dependence of constants on the Sobolev norms of the pair and time. Theorem 6.3 explicitly invokes (6.7). The local neighborhood predicate does not retain those complete quantitative statements, and the candidate does not establish their full converses from these local fields.

These fields may be appropriate source consequences for a weaker interface. That is different from satisfying the present full-original-equivalence requirement.

### Other qualifications

E1 is explicitly specialized to H1 inputs. E4 explicitly fixes the interval-length scope. E6 retains a substantial limiting certificate but does not tie its existential bound to the same preceding source constant. None is promoted here to a complete original-statement iff merely because its used conclusion is supported by the source.

## Consequence and remaining obligation

No target mismatch or independent extra mathematical oracle was found in the inspected boundary. The strict external-equivalence gate remains unmet.

To meet that gate, retain complete source-faithful theorem propositions, including quantitative constant dependence and every claimed original conclusion. Derive the desired H1, bounded-interval, estimate-only and qualitative local interfaces as separately proved project corollaries. When claiming an equivalent encoding, provide the actual bidirectional representation/definition bridges.

This audit implements no such changes and performs no new proof or model run. It adds only a separate audit report and evidence. It does not overwrite the historical benchmark's recorded execution or acceptance status.

## Research context receipt

Research Cognition selected scientific-computing 0.133.0 and pde-continuum 0.94.0 by caller judgment; confidence is unrated. Initial context cards concerned other problems and were rejected for substantive use. A bounded discovery returned AIM 518 candidates, but their previews were treated only as navigation and were not used as theorem evidence or transferred proof methods. All substantive decisions above come from the frozen Lean artifact and the primary sources. The versioned route and discovery receipt are retained separately.

