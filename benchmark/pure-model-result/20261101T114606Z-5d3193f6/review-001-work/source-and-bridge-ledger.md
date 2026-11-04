# Original-source completion of Theorem 1

This ledger distinguishes the original published inputs, checked project-specific
consequences, and unchanged historical proof. The new export is
`BareModelCompletion.completed_theorem_1` in CompletedProof.lean. It is conditional
on explicitly typed literature propositions, not on new kernel axioms. Source
correspondence below is the author's primary-text assessment; outside semantic
acceptance is a separate matter.

## Versions and operational provenance

Only the six authorized mathematical inputs were read, together with the pinned
Lean/Mathlib. No agents, skills, memories, other experiment outputs or other
solutions were used. All new construction and compiler repair were performed in
this author session. No additional primary version was retrieved.

| Supplied primary file | Version | SHA-256 |
|---|---|---|
| target.pdf | Kaiwen Jin, *Removing the logarithmic loss in the Li–Wu KdV integrator*, 10 October 2026; 15 pages | 5d6432bf9c097991bf5d853f38e831a539b4f052f0ccf4010bba6e37b54507b6 |
| li-wu.pdf | Buyang Li and Yifei Wu, *An Unfiltered Low-Regularity Integrator for the KdV Equation with Solutions Below H1*; supplied 50-page manuscript, PDF creation metadata 31 January 2025 | e71452d13d7d54b902c6d79a08bbcd68edab795f0a59366fff14399b98192f9b |
| babin-ilyin-titi.pdf | Anatoli V. Babin, Alexei A. Ilyin and Edriss S. Titi, *On the regularization mechanism for the periodic Korteweg–de Vries equation*; arXiv:0910.1389v2, 23 October 2010; 42 pages | b6958c0b155bb8463f85900c4beaf75b1cf399382101a720cc39edf82cfac52e |

The source PDFs' page numbers are used throughout. Extracted texts have explicit
PDF page markers. `source-metadata.json` records metadata, without substituting
metadata for printed version identification. The historical DOI/URL descriptions
in correspondence.md were not treated as certification.

The initial native capability check verified command execution, reads of the
staged files, scratch write/read/removal and Lean 4.32.2 execution. `pdftotext`
was missing; installed PyMuPDF extracted all three PDFs successfully. This did
not block work. The original compiled independently as OriginalProof.olean.

OriginalProof.lean remains byte-for-byte unchanged, with required SHA-256
`bf73ff25c1c67c020023ad545649bd2e0444658191c6c0c637b86528ad0b0cd0`.
The pinned Mathlib commit was checked as
`905b95818eb32af7874a58b427f50c1711a5e96c`. No shared toolchain was modified.

## Final assumption inventory

The complete exported signature has exactly these nine explicit literature
inputs, followed by `KdV.TheoremOne`. There are no implicit external mathematical
parameters, abstract operators, numerical regularity assumptions, stability
estimates or convergence estimates. All source proposition definitions and their
nested fields are printed in SignatureInspection-build.log.

| Root parameter | Lean proposition | Genuine primary statement |
|---|---|---|
| step | LiWuStep52Grid | Li–Wu (5.2), p.25; algebraic (4.20)–(4.23), pp.23–24; original definitions (1.4), (4.10), (4.15), (6.1) |
| stage | LiWuLemma72Grid | Li–Wu Lemma 7.2, pp.32–34, with (7.2)–(7.3), p.32 and the complete grid from §1 |
| product | LiWuProduct22 | Li–Wu (2.2)–(2.3), p.8 |
| trilinear | LiWuProposition34 | Both parts and the right-side permutation clause of Li–Wu Proposition 3.4, p.14; operator (3.13) |
| bit41 | BITProposition41 | BIT Proposition 4.1, p.11, global existence and the full energy identity (4.3) for (4.1)–(4.2) |
| bit43 | BITTheorems42And43 | Full BIT Theorem 4.2, p.13, including (4.10) and (4.13), and Theorem 4.3, pp.14–15, with the same bound |
| bit51 | BITTheorem51 | Full BIT Theorem 5.1, p.19, including quantitative (5.18), p.21 |
| bit63 | BITTheorem63 | Full BIT Theorem 6.3, p.27, with quantitative (6.7) and governing (6.2)–(6.5), p.22 |
| bit65 | BITTheorem65 | Full BIT Theorem 6.5, (6.22), p.28; continuous solution class specified in Theorem 6.4, pp.27–28 |

Proposition 4.1 is needed to supply the family to the original Theorem 4.3. The
latter is a theorem about a given Galerkin family, not just an existential
project certificate. Its addition is part of restoring that original input
quantifier; it does not supply a numerical estimate. Theorems 6.4 and Li–Wu 1.1 are not independent inputs: the former specifies
the C([0,T];Hdot^0) comparison class, and positive-data existence is supplied by
4.3/5.1/6.3; the latter is background and is not used for the numerical estimate.
The source roots contain only published source clauses. None contains a field asserting a historical
local Lipschitz port or any other project-specific bridge.

## Every historical port

All names in this table after the historical column are in
`BareModelCompletion`, unless prefixed otherwise.

| Historical KdV port | Classification | Exact input and checked consequence |
|---|---|---|
| LiWuStepIdentity | NEEDS_BRIDGE | LiWuStep52Grid → step_grid_to_universal → step_to_historical; exported composition step_grid_to_historical |
| LiWuStageEstimate | NEEDS_BRIDGE | LiWuLemma72Grid → stage_grid_to_historical; preserves fixed T while deriving the old arbitrary-step interface |
| LiWuProductEstimate | EQUIVALENT_AS_STATED | LiWuProduct22 is a direct abbreviation; no artificial product bridge |
| LiWuTrilinearEstimate | NEEDS_BRIDGE | LiWuProposition34 → trilinear_to_historical, restricting only the fixed length-bound parameter to the old H≤1 range |
| BITGalerkinEstimate | NEEDS_BRIDGE | BITTheorems42And43 → bit42_from_joint → galerkin_to_historical; extract the estimate from the full theorem including its normal form |
| BITExistenceLimit | NEEDS_BRIDGE | BITProposition41 and BITTheorems42And43 → source_global_galerkin_family, strongLp43_to_scalar, limit43For_to_certificate, limit_to_historical |
| BITHigherRegularity | NEEDS_BRIDGE | BITTheorem51, original construction and BITTheorem65 → high_to_historical; full quantitative dependence is retained at the input |
| BITLowRegularity | NEEDS_BRIDGE | BITTheorem63, original construction/bound and BITTheorem65 → low_to_historical; the source L∞ norm estimate, not a qualitative replacement, is the input |
| BITWeakerLipschitz | EQUIVALENT_AS_STATED | BITTheorem65 directly abbreviates the full historical type, including −1<theta≤0 and constants independent of T |

No old weakened port is an independent final assumption. The only directly
retained old ports are the two classified equivalent. The historical theorem is
applied unchanged to all nine exact or derived ports in CompletedProof.lean.

## Common definitions and source representations

The target torus is AddCircle(2*pi), with probability Haar measure dx/(2*pi),
character exp(ikx), and Fourier coefficient `(2*pi)^(-1) integral f exp(-ikx)`.
`weight s k=(1+k^2)^(s/2)`, `InSobolev` is the actual weighted square-summable
space, and `hNorm` is the square root of that full square sum. The historical
complete-space construction, polynomial density and Fourier reconstruction
identify these with the target's completions, for every real index. Reality is
`f(-k)=conj(f(k))`; mean zero is `f(0)=0`. The historical physical reconstruction
and product theorems identify these conventions with real physical functions,
vanishing normalized integral, Parseval and actual multiplication. No finite
support or pointwise Fourier-series convergence is imposed.

Li–Wu §2.2, p.6, uses the same Fourier coefficient but unnormalized Lebesgue
spatial norm: `sourceNormalization=sqrt(2*pi)` and
`sourceNorm s f=sourceNormalization*hNorm s f`. This is the literal displayed
source formula, including for distributions. `source_rescaled_norm`,
`source_rescaled_memLp_iff` and `source_rescaled_time_norm` check the actual
complete-space norm rescaling and both directions of time-space membership.
The historical normalized_product_estimate, normalized_stage_estimate,
normalized_static_trilinear and normalized_dynamic_trilinear perform the
normalization consequences: one factor of sqrt(2*pi) for bilinear estimates,
two for trilinear estimates. No source normalization is absorbed silently into
an assumed normalized interface.

BIT §3, p.5, uses probability spatial measure and homogeneous mean-zero spaces:
`homogeneousNorm s f^2=sum |k|^(2s)|f(k)|^2`. Its H^s in (3.4) is
`|f(0)|^2+Hdot^s norm^2`, so on this mean-zero class the H^sigma in Theorem 4.3
is exactly Hdot^sigma, not the target's Japanese-bracket norm. The complete
homogeneous space is represented by its weighted L2Seq coordinates;
homogeneousReconstruct_weighted, homogeneousReconstruct_norm and their historical
membership/reality lemmas check the inverse and norm. This is also the
Hilbert-space representation in the strong and weak-star convergence clauses.

Time measure is ordinary Lebesgue measure. `source_time_measure_eq` proves that
open and closed intervals give the same restricted measure. Thus the source's
open-interval L∞ notation and the formal closed-interval essential norms have
identical values and membership classes. `CIntegral_congr_ae` and
`weakTimeDerivative_congr_ae` check representative independence and both
directions of weak-derivative representative change. Continuous representatives
are retained separately wherever the source or target calls for them; endpoints
are never removed from a continuous solution or the target maximum.

The source equation is U_t=U U_x+U_xxx; the target equation is
u_t+u_xxx=(1/2)partial_x(u^2). The historical reflectSign map is
`reflectSign f(k)=-f(-k)`, representing u(t,x)=-U(t,-x). Both directions of the
integrated source/target equations and Airy-frame transformations are checked
historically. `sourceFrame t f=reflectSign(airy(-t) f)`. Norms, reality, zero
mean and L2 distances are preserved. Homogeneous/inhomogeneous continuity
conversions are historical proofs. The internally used loose upper comparison
`hNorm s≤2^s*homogeneousNorm s` for s≥0 changes only an internal constant; both
actual norm definitions remain exactly the original definitions.

## Li–Wu field-by-field map

### Product (2.2)–(2.3)

LiWuProduct22 retains the entire gamma range [0,1], every positive epsilon loss,
all f in H^gamma and g in H^a, product membership in L2 and the bilinear bound.
The four cases of a are 1/2+epsilon at gamma=0; 1/2−gamma on (0,1/2);
epsilon at gamma=1/2; and zero on (1/2,1]. The source's plus/minus convention is
§2.1(vii), p.6. Constants precede both inputs. No source conclusion is dropped.

### Stage Lemma 7.2 and (7.2)–(7.3)

LiWuLemma72Grid keeps T>0, 0<gamma≤1, epsilon>0 and the full beta interval.
The lower endpoint is 2*gamma−3/2 below 1/2, −1/2−epsilon at 1/2, and gamma−1
above 1/2. The power is exactly `(1+gamma−beta)/(1+gamma−beta0)`. Its positive
constant precedes L>0, tau=T/L, n<L, the intermediate time in [n*tau,(n+1)*tau]
and both mean-zero H^gamma inputs. Both H^beta membership and the norm bound are
retained. sourceBilinearStage is the unprojected endpoint formula (7.3).

liWuStage72 is the literal coefficient integral (7.2). The checked
liWuStage72_eq_endpoint uses historical fixed_normal_form and
bilinearStage_eq_source, so the integral and endpoint definitions are proved
equal, not postulated. The auxiliary HistoricalIntegralStageEstimate and
HistoricalEndpointStageEstimate are internal historical-port reformulations,
not independently imported literature statements.

The old port allows an arbitrary tau with (n+1)*tau≤T, rather than only a
complete grid T/L. stage_grid_to_historical proves this consequence without
assuming monotonicity in an unspecified T-dependent constant: choose
L=floor(T/tau), so theta=T/L lies between tau and 2*tau, keep the same T, and
conjugate the start time to zero using source_stage_shift. The power q is
nonnegative throughout the full beta range. The new bound uses C*2^q, before
all old step, time and input quantifiers. No source estimate at a varying final
time is used.

### Trilinear Proposition 3.4

Both dynamic and static fields are retained. alpha ranges over [0,1]. The
condition `|s-s0| ≲ 1` is expressed by an arbitrary fixed finite bound H>0 on
interval length, with its implicit constant allowed to depend on that fixed
bound; it is not silently assigned the numerical value one. Times obey
0≤a≤b and b−a≤H. Dynamic inputs have actual L∞ H^alpha membership, and actual
weak distributional derivatives in L∞ H^(−23/14). BochnerWeakTimeDerivative is an equality of actual H^(-23/14)-valued Bochner
integrals for every smooth compactly supported time test. The checked
weakTimeDerivative_iff_bochner proves BOTH directions of correspondence with the
historical coefficientwise Fourier distribution tests, under exactly the source
MemLp hypotheses. smul_interval_coefficient proves integrability and commutation
with Fourier coordinates. No continuity of the input trajectory is assumed.
Derivative representatives are not arbitrary prescribed a.e. classical derivatives.

The dynamic conclusion includes L2 membership, the C*(b−a)*product X_j term,
and every right-side placement of the negative norm while leaving the operator
slots fixed. X is exactly the source L∞ L2 norm plus the negative derivative
norm. The static field retains all alpha and the exact `(b−a)^alpha` factor.
CIntegral is (3.13): outer P removes output zero, inner P removes k1+k2=0,
and D^(-1) in the third slot removes k3=0. All integer intermediates are retained.
trilinear_to_historical restricts H to the old 0<H≤1 domain and supplies the
proved coefficient/Bochner weak-derivative conversion.

### Algebraic identity (5.2)

LiWuStep52Grid keeps the original gamma in (0,1], T>0, L>0, tau=T/L and n<L,
with every mean-zero H^gamma input to the defined update. It has no stability,
residual or convergence estimate. The formula is exactly f+F^n+A^n−R2^n after
twisting the fixed physical update. liWuStage72 is F^n from (7.2);
liWuCross410 is the full cross integral A^n from (4.10); liWuEta415 keeps the
two exponential factors in the original average (4.15); and liWuRemainder61 is
(6.1), including the negative tau/(18*i*k), the phase, all integer modes, zero
output and exclusion k1+k2=0. No zero-mode or endpoint correction is dropped.

liWuEta415_eq_covariance proves combination of the exponentials;
liWuRemainder61_eq_remainder proves exact covariance-object equality;
liWuCross410_eq_frozenCross proves the stage substitution inside the cross
integral. The step grid/universal quantifier change is proved in both directions
by step_grid_iff_universal: for a given tau,n choose T=(n+1)*tau and L=n+1.
There are no estimate constants in this identity, so that reparameterization
loses no dependence. step_to_historical finally specializes gamma=1, as the
historical port requires. It does not replace the full source with an H1 input.

## BIT field-by-field map

### Proposition 4.1 and Galerkin standing definitions

SourceGalerkinODE is exactly (4.1) with the original positive phase sign,
projection (4.2) on both arguments and output, and initial condition v(0)=f,
including the full stationary tail outside the projection. source_phase_formula
historically checks the phase 3*k*k1*k2. This is an exact-flow construction;
there is no projection in the numerical method.

BITProposition41 retains every real mean-zero Hdot^0 datum, every positive
Galerkin index, existence of a single global trajectory on t≥0 and the full
squared energy identity for every such t. Its continuous Hdot^0 solution class
is specified on every closed [0,T]. The equality with the norm at time zero in
(4.3) is also retained through v(0)=f in SourceGalerkinODE. There is no positive
regularity restriction on this source input.

source_global_galerkin_family constructs the global family needed by Theorem
4.3, including conservation for ALL t≥0 and continuity/equation on EVERY finite
horizon. BITGalerkinFamily retains those global time ranges; they are not
silently replaced by properties only up to the limit horizon T.
galerkin_higher_continuity proves that only finitely many modes move while the
entire rough tail is stationary, so any higher initial regularity persists
continuously. galerkin_continuity_iff proves both directions of the Hdot^s/Hdot^0
Galerkin solution-class correspondence for initial Hdot^s, s≥0. No initial
Fourier-polynomial restriction or numerical regularity is imposed.

### Full Theorems 4.2 and 4.3

BITTheorems42And43 chooses A after s≥0, M0≥0, T>0 and actual initial norm r≥0,
but before all indices, data and flows. Initial Hdot^s norm equals r, not merely
at most r; initial L2 norm is bounded by M0. This is the original quantitative
dependence in (4.13).

The first field retains BOTH conclusions of Theorem 4.2: normal form (4.10)
and the uniform Hdot^s estimate at every time in [0,T]. BITNormalForm410 uses
within-interval derivatives on the closed solution interval. Concrete bitB2,
bitB3, bitB14, bitB24 and bitB4 are respectively (3.16), (3.25), (3.28), (3.29)
and (3.27), with coefficient one half on B4^1, original phases and the original
input/output truncations (4.8), (4.11). Zero denominators contribute zero,
omitting the source's zero-denominator terms. The additional split-mode
condition c+d≠0 is explicitly retained in B4^1 and B4^2: in (3.24)–(3.26) the
differentiated original mode lies in Z\{0}, so this condition survives the
cancellation yielding (3.28). It must not be lost merely because it is absent
from the simplified denominator. quartic_nonres_domain checks that reindexing
of the original nonresonant conditions. Zero input modes vanish
for these mean-zero source arguments. The operators are explicitly extended by
ZERO at output zero, as required by the source's nonzero-mode codomain.
tripleSumEquiv/quadrupleSumEquiv and their tsum reindexing proofs check the exact
integer-sum constraints. nonresonant_zero_denominator, cubic_zero_input and
quartic_zero_input check the omitted-term conventions. The equations concern
nonzero output modes.

Printed conventions are preserved literally: (4.2), p.11, uses |k|≤m, while
(4.12), p.13, uses |k|<m / |k|≥m and the full initial norm. bitAresM412 uses
those printed (4.12) conventions; no proposed correction is silently imported.
The completion does not use the normal-form field to prove an unrelated claim:
galerkin_to_historical extracts the other, estimate conclusion.

The second field retains Theorem 4.3 for s>0. The datum is fixed, a Galerkin
family G is GIVEN with its full global source equation, energy conservation
and continuous solution class on every finite horizon,
and sigma is fixed in (0,s) before selecting the limiting solution/subsequence.
This is universal over given source families, not an existential weakened family
input. BITLimit43For retains: the Definition 3.1 weak solution, actual essential
Hdot^s boundedness, the SAME A from (4.13), a.e. L2 energy conservation, a strictly
increasing subsequence, strong L^p H^sigma convergence for every finite p>1, and
weak-star L∞ Hdot^s convergence.

BITStrongLp43 uses actual complete Hilbert-space-valued representatives, both
curves' L^p membership and convergence of the vector-valued L^p difference to
zero. It is not the historical scalar-norm surrogate. The weak-star clause
SourceWeakStarConvergence retains L∞ vector representatives and testing against
every integrable Hilbert dual function. The source H^sigma equals Hdot^sigma
here by (3.4). Strictly increasing positive Galerkin indices are reindexed by
m+1; no subsequence endpoint or unboundedness condition is lost.

strongLp43_to_scalar proves the historical scalar membership and error-norm
convergence by equality of the actual weighted Hilbert difference norms, a.e.
representative equality and eLpNorm_norm. limit43For_to_certificate then packages
the given family, its proved (4.13) bound, and the original subsequence into the
historical certificate. limit_to_historical supplies that family from Proposition
4.1 and specializes M0 and r to the datum's actual norms. A common bound is not
silently moved after the datum in the source statement.

BITConstructedLimit43, used by the original regularity statements below, retains
the original vector-valued construction. The historical weaker
SourceConstructedLimit is NOT an input to these source statements.

### Full Theorem 5.1, including (5.18)

BITTheorem51.regularity retains s>1/2, T>0, all real mean-zero Hdot^s data and
all original constructed limits, their C([0,T];Hdot^s) regularity, uniqueness
in the Definition 3.1 solution class, and all-time L2 conservation. BITUniqueWeak
uses that source class before the historical continuous comparison restriction.
The primary statement explicitly refers to Definition 3.1; the source's
continuous class is kept separately where it is explicitly imposed, notably
Theorem 6.4/6.5.

BITTheorem51.dependence is the full quantitative BITDependence518. The scalar
parameter functions precede both data and their continuous source flows. It
retains T* in (0,T], C'>0, N=floor(T/T*)+1 and the factor `(C'+1)^N`.
The printed p.21 proof line says T* depends only on
`||w0||_s+||w0||_s` and T (with fixed s); equation (5.18) puts the SUM
`||v0||_s+||w0||_s` in C'. These two printed dependencies are kept separately:
delta is evaluated at twice the second initial norm, while C' is evaluated at
the sum. The repeated w0 in that proof line is not silently replaced by v0.
Both parameter functions are positive at every nonnegative norm parameter,
and delta is at most T. The source's w−v and w0−v0 order is also retained.
On a fixed equal-norm sphere the two norm parameters coincide, which is exactly
what the bridge uses. No local boundedness, monotonicity, or replacement by a
qualitative neighborhood or an assumed ball-uniform constant is imported.

### Full Theorem 6.3, including (6.7)

BITTheorem63.regularity retains the ENTIRE interval 0<s≤1/2, the original
constructed-limit class, continuous Hdot^s regularity and source-class uniqueness.
The all-time energy described in the source proof is also checked as a
consequence by original_constructed_energy, using the original a.e. energy and
continuous norm. Its dependence field is BITDependence67Norm, the literal L∞ norm inequality in
(6.7) at theta=s, as Theorem 6.3's proof specifies. The governing C0 bound (6.3)
is the SUM of the two L∞ Hdot^s norms, not the essential supremum of a pointwise
sum. The choice of n from (6.4) and tau from (6.2)–(6.5) gives constants depending
on s,T,C0 before both flows. The positive tau,C,C' and exact factor
`C'*(2*C+1)^(floor(T/tau)+1)` are retained. Inputs are actual essentially bounded
source Hdot^s flows. The (6.7) conclusion is not replaced by a local map predicate.

bitHomSup_le_iff, homogeneous_essential_sub and
dependence67_iff prove both directions of the literal L∞ norm inequality versus
the a.e. comparison form, including finiteness of the real norm function's
L∞ seminorm. These are checked representation consequences, not new assumptions.

### Consequences for both historical regularity ports

original_limit_exists constructs a limit in the FULL original class from the
original family theorem. The source regularity/uniqueness clauses apply to that
limit. Historical certificates are used only to extract their weak-solution
property; original uniqueness transfers the original regularity and conservation
to the historical representative. homogeneous_continuity_congr checks the
closed-interval transfer. No weakened construction predicate is hidden in the
new original input fields.

The two missing historical local Lipschitz claims require substantive new work.
PaddingHelpers defines a simultaneous lift of weighted cutoff data to a fixed
norm sphere. Its checked properties are: reality and zero mean, exact norm 2R,
unchanged low modes, difference at most three times the original Hdot^s
difference, and convergence of the lifted data in L2 for every s>0.
sqrt_padding_lipschitz controls the two square-root amplitudes; neither unknown
source constants nor their derivatives are bounded by assumption.

local_lipschitz_from_spheres applies the original quantitative estimate on that
single fixed sphere, constructs the lifted source flows from the original
existence and regularity clauses, uses BIT Theorem 6.5 with theta=0 to obtain
coefficient convergence of those flows, and passes to the Hdot^s norm bound using
historical homogeneous_norm_limit. The resulting neighborhood has radius one
and a constant chosen before the nearby datum and flow. For the low-regularity
case, low_fixed_sphere_bound first supplies the common original (4.13)/(4.20)
bound and hence a common C0 for (6.7).

source_local_lipschitz_iff proves both directions between all-time and a.e.
local comparisons for continuous source flows, keeping the same radius and
constant. high_to_historical and low_to_historical assemble all the required
fields, including this derived comparison, source continuity, uniqueness and
the original higher-regularity energy clause. There is no independent local
comparison assumption in the final theorem.

### Full Theorem 6.5

BITTheorem65 retains M≥0, every −1<theta≤0, real mean-zero L2 data with summed
L2 norm at most M, and both continuous weak solutions. Positive C',CM precede T,
both data and flows; their dependence is only on M,theta. The exact essential
norm factor C'*CM^T and the initial Hdot^theta difference are retained. bit65_iff_historical checks BOTH directions between the full literal norm
form BITTheorem65Norm and the retained historical a.e. form, with the SAME
constants and parameter order. Continuity in Hdot^0 supplies actual essential
Hdot^theta membership, including negative theta. Thus the old port is already
strictly equivalent to the complete statement and is reused directly. The historical
source_flow_lipschitz derives all-time endpoint bounds from continuity, and the
historical source/target frame transformation derives target L2 dependence.

## Target correspondence and assembly

The target is Theorem 1, p.2, with ALL §2 standing definitions and equations
(1) and (2). The unchanged quadratic, cubicCorrection, lastBoundary and step
implement every update term, both endpoint differences, the mean term and the
1/(27*tau) correction. Their multipliers, signs, Fourier normalization and every
integer intermediate are unchanged. Neither a filter nor a spectral cutoff is
part of numerical or step.

The actual conclusion KdV.TheoremOne has order
`forall T>0, gamma in (0,1], R>0, exists C>0,tau0>0, forall f in the real
mean-zero H^gamma ball of radius R, forall exact solutions u, forall L>0 with
tau=T/L<=tau0, maximumError<=C*tau^gamma`.
The maximum is the literal Finset.sup' over Finset.range(L+1), including n=0
AND n=L. C and tau0 precede the datum, solution and integer grid. There is no
smooth-data restriction or assumed numerical H^gamma bound.

ExactSolution retains the continuous positive-Sobolev Duhamel solution and the
actual smooth approximation condition. The historical physical reconstruction,
H^(-3)-valued weak PDE and spatial test-pairing theorems give equation (1)
distributionally, including the separately retained initial condition. The new
completed_exact_solution_exists, completed_exact_solution_iff and
completed_exact_solution_unique reuse the checked historical constructions to
show nonvacuity, equivalence with the continuous Duhamel class, and uniqueness
on the entire closed interval, from the exact source inputs. Smooth approximation
therefore does not shrink the target initial-data class or exact solution class.

CompletedProof.lean applies the UNCHANGED theorem_1 to the exact product and
weaker-norm ports and seven derived ports. The historical convergence proof,
bootstrap, density passage, numerical recurrence and target were not re-solved
or edited. The new padding work concerns source-interface consequences only.

## Build, signature and trust inspection

Run `python3 build-all.py` with the provided LEAN_PATH. It invokes the pinned
Lean executable in dependency order on EVERY supplementary module, and also
rebuilds OriginalProof separately. It records commands and exit codes in
build-status.json and full-build.log; each module has its own build log. The
original hash is checked before the build and recorded again after it.

SignatureInspection.lean prints the actual NEW root, all nine source types,
every assumption-bearing source structure and nested weak/constructed-limit/
convergence/dependence predicate, the historical ports, target and solution
predicates, normalization and numerical definitions, and the main bridge types.
In particular, input BITTheorem51/63 refer to BITConstructedLimit43 with genuine
vector-valued convergence; the weaker historical certificate occurs internally
only. The generic helper hypotheses in local_lipschitz_from_spheres are discharged
by actual source clauses in high_to_historical and low_to_historical; they are
not root parameters or structure fields.

The root's #print axioms output contains only propext, Classical.choice and
Quot.sound. The literature propositions are visible free parameters and are
not misrepresented as axioms found by that command. No sorry, admit, sorryAx,
new unproved axiom, unproved opaque constant or unsafe substitute was introduced.
Printing the source types and their nested fields, not just #print axioms,
is the assumption audit.

## Accounting and acceptance

All artifacts here are supplementary author work. The preserved original file
and its fixed hash identify the historical candidate separately. No historical
metrics were available in the allowed inputs, and the outside passive recorder
collects native usage/time for this invocation. No launcher, continuation
controller or independent usage instrumentation was built. Reproducible build
scripts only compile and record exit status.

result.json leaves measured durations and tokens null for the passive recorder
to fill. The combined quantities are historical plus supplementary usage/time;
no unavailable measurements or sums are invented. Author completion and source
correspondence assessment do not constitute outside semantic acceptance.

The auxiliary all-bounds formulations BITTheorems42And43AllBounds and
BITTheorem65AllBounds also include every real upper-bound parameter.
bit42_43_all_bounds_iff and bit65_all_bounds_iff check BOTH directions of the
nonnegative-bound formulation: negative bounds (or a negative actual norm r)
have no admissible datum. This makes the otherwise implicit norm-bound domain
convention explicit; no parameter case is lost by the final root types.

## Final recorded validation

All ten modules in build-status.json completed with exit code zero, including
OriginalProof, every supplementary dependency and SignatureInspection. The final
original SHA-256 matches the required value. root-signature.txt extracts the
actual new declaration signature; root-axioms.txt preserves its actual kernel
axiom report. completion-verification.json records these checks, and
lean-source-hashes.json fixes the built Lean source contents. The code-token scan
after removing nested comments and strings found none of the prohibited proof
substitutes or new axiom/opaque declarations. result.json records author status
complete, with no remaining proof obligations. Measured accounting values remain
null pending the outside passive recorder; the historical-plus-supplementary
sum formulas are recorded there.
