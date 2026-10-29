# Target and checkpoint

This is an **in-progress development**, not a completed formal proof. The exported
declaration `theorem_1` has not yet been constructed. `result.json` records the
remaining obligations. No convergence or stability assertion is being imported
as a hypothesis.

The supplied paper is Kaiwen Jin, *Removing the logarithmic loss in the Li–Wu KdV
integrator*, dated 10 October 2026, 15 pages. Its entire statement, conventions,
Sections 2–4 (including the proof), and the rest of the article were extracted
from the supplied PDF into `paper.txt` and read. The target is Theorem 1, pages
2–3, proved on pages 3–11.

The intended quantifier order is

```
for every T > 0, 0 < γ ≤ 1, R > 0,
there exist C > 0 and τ₀ > 0,
for every real, mean-zero u₀ ∈ H^γ with ‖u₀‖H^γ ≤ R,
for every positive integer L with τ = T/L ≤ τ₀,
max_{0 ≤ n ≤ L} ‖u(nτ) − uⁿ‖L² ≤ C τ^γ.
```

The constants must precede the datum and step count. The exact solution is the
unique real, mean-zero `C([0,T]; H^γ)` distributional solution obtained by smooth
approximation. Restricting the theorem to classical or finitely supported data
would not meet the target.

# Representation currently implemented

`KdV.Torus` is `AddCircle (2 * Real.pi)` and `normalizedMeasure` is Mathlib's
probability Haar measure. It has total mass one. Fourier coefficients are indexed
by all of `ℤ`. `InSobolev s f` means that
`((1+k²)^(s/2) f̂(k))_k` belongs to `ℓ²(ℤ,ℂ)`.
`hNorm s f` is the square root of the sum of the squared absolute values of this
weighted sequence. `hNorm_sq` gives the paper's exact inhomogeneous norm formula.
`Sobolev s` carries the complete norm topology transported by `sobolevIsometry`
from weighted `ℓ²`. The indexed coefficient structure prevents inheriting the weaker pointwise
topology on raw sequences. Its index is a structure parameter, so checking
coefficient projections does not expand the weighted summability predicate. `polynomialToSobolev_denseRange` proves density of
the finite coefficient sequences. Thus this is the prescribed completion of
trigonometric polynomials for every real `s`. The `s=0` reconstruction uses the pinned Mathlib
Fourier Hilbert basis for the normalized torus. That basis uses coefficients
`(2π)⁻¹ ∫₀²π f(x) exp(-ikx) dx`.

`RealValued f` is conjugate symmetry, and `MeanZero f` is `f 0 = 0`.
`product` is the full integer convolution. Every use as a product of Sobolev
distributions will require the appropriate summability proof; Lean's totalized
`tsum` alone does not supply well-definedness. `hNorm` is a Sobolev norm only
after its membership hypothesis is established.

`airy t` has multiplier `exp(i t k³)`, exactly `S_t = exp(-t ∂ₓ³)`.
`inverseDerivative` has multiplier `(ik)⁻¹` away from zero and zero at zero.
`inverseDerivative₂` is its composition with itself. `removeMean` deletes the
zero coefficient. `quadratic` is `F_τ` from equation (2).

`cubicCorrection` contains every term of `H_τ`, in the displayed order:

1. `P[(S_τ D⁻¹f) D⁻¹F_τ(f)] / 3`;
2. `τ (S_τ D⁻¹f) P₀(f²) / 9`;
3. minus `1/54` times the endpoint difference of
   `S_{τ-s} D⁻¹[(S_s D⁻¹f)³]`;
4. minus `1/(27τ)` times the endpoint difference of
   `S_{τ-s} D⁻²[(S_{s-τ} D⁻²F_τ(f))(S_s D⁻¹f)]`.

Each endpoint difference is value at `s=τ` minus value at `s=0`.
`step τ f = S_τ f + F_τ(f) + H_τ(f)` and `numerical` iterates this fixed map,
starting at the original datum. There is no spectral projection in the update.
Mean preservation and Airy norm preservation have elementary proof developments.
The full update is proved to preserve membership in every `H^γ` for
`0≤γ≤1`. The `H¹` convolution algebra estimate is proved using weighted Young
inequalities and the internally proved `H¹` embedding into absolutely summable
coefficients. The bundled update `stepBundled` and each finite iterate
`numericalBundled` are continuous on the full `L²` completion. Their coefficient
representations are proved equal to `step` and `numerical`. Reality preservation is proved for every stage, correction, complete step and
finite iterate. Strong time continuity and joint continuity of the Airy action
are proved for every real Sobolev index. Absolute convergence and the uniform coefficient bound for
the convolution of two `L²` inputs are proved. The inverse derivative is proved
to map `L²` into `H¹` with norm at most `√2` times the original norm.

The full cubic remainder is defined by the exact covariance multiplier and all
integer input frequencies. The two pointwise four-frequency majorants of Lemma 3
are proved. `thirdLargest` uses the maximum of the minima of the four triples,
so ties require no choice of ordering. For decreasing inputs the expression is
proved equal to the third input. The proof of the second majorant gives constant
two and then weakens it to the paper's six. `four_linear` proves the full
infinite nonnegative four-linear sum of Lemma 4, with explicit constant 48;
`four_linear_restricted` includes restriction to any subset. The proof uses an
elementary weighted Cauchy–Schwarz kernel bound in place of the paper's dyadic
summation: `1/N₃` is bounded by the six reciprocal maxima of pairs, each remaining
convolution is bounded by Cauchy–Schwarz, and the matrix kernel
`1/max(m,n)` is bounded on `ℓ²` using weights `m^(-1/2)`. The row bounds are proved
by the pinned Mathlib sum/integral comparisons and elementary power integrals.
Both signs of every nonzero integer are retained. All of this summation argument
is internally proved.

The two covariance bounds of Lemma 2, with their precise constants, and the
interpolated multiplier bound (11) are now internally proved, including exponent
zero. `interactionOutput_bound` constructs the bounded trilinear `L²` output by
Riesz duality and identifies its coefficients with absolutely convergent sums.
`remainder_eq_interactionRemainder` proves the equality of the paper's original
pair-indexed formula with the zero-sum quadruple representation, using a
bijection of their nonzero summands. Thus `mixed_remainder_bound` proves the
full unfiltered estimate (10), with explicit constant
`(48/18) 6^(1-γ) 18^γ`, on the stated mean-zero Sobolev inputs. A separate theorem
for arbitrary inserted modulus-one multipliers has not been exported; the
generic trilinear bound permits such a specialization.

`numerical_state_estimate` proves Corollary 7 for the same exact remainder. It
uses only `f∈L²` for the numerical state and `w∈H^γ` for the exact comparison,
with `‖w‖H^γ≤M` and `δ=‖f-w‖L²≤1`. Its explicit admissible constant is
`remainderConstant γ * M³ + 16*(2*M+1)²`. The proof uses a three-term trilinear
telescoping identity and the exponent-zero estimate. It assumes neither a
numerical `H^γ` bound nor a stability/convergence estimate. It in fact holds for
every positive timestep; the target only needs timesteps at most one.

`cutoff` is a symmetric projection used only for approximation. It is proved to
preserve reality and zero mean, contract the norm in every `H^s`, have finite
support, and converge to the original input in `H^s`. In particular the
approximants stay in the very same initial-data ball.

# Primary-source audit and planned external inputs

The spatial product, bilinear stage and both continuous trilinear estimates now
have explicit formal premise types. The exact step identity and flow results
still need formal premise types, and all source applications need completion. The following
is an audit record, not an independent certification of source correspondence.

## Li–Wu

Buyang Li and Yifei Wu, *An Unfiltered Low-Regularity Integrator for the KdV
Equation with Solutions Below H¹*. The supplied paper specifically cites the
[50-page author manuscript](https://www.polyu.edu.hk/ama/profile/byli/FoCM-3.pdf),
rather than journal pagination; journal DOI `10.1007/s10208-025-09702-0`.
The manuscript is accessible through the web tool. Shell downloads failed with
a DNS error, so no claim is made to have downloaded the PDF locally. The exact
equation (1.4), on manuscript page 4, has been compared with the complete update
above and agrees term by term.

* Proposition 3.4, manuscript page 14, applies to `α∈[0,1]`,
  `s≥s₀≥0` with bounded interval length, and inputs in
  `L∞([s₀,s];H^α)` with time derivatives in `L∞ H^(-23/14)`.
  Its operator is the time integral of
  `S_{-t} P{P[(S_t f₁)(S_t f₂)](S_t D⁻¹f₃)}`.
  Part (1) bounds its `L²` norm by a constant times
  `|s-s₀| ∏ⱼ ‖fⱼ‖X` plus
  `‖f₁‖L∞H^(-23/14) ‖f₂‖L∞L² ‖f₃‖L∞L²`,
  where `‖f‖X=‖f‖L∞L²+‖∂ₜf‖L∞H^(-23/14)`.
  The source explicitly states that the inputs can be permuted **on the right
  hand side**. Part (2), for time-independent inputs, bounds it by a constant
  times `|s-s₀|^α ∏ⱼ ‖fⱼ‖H^α`.
  Both parts and the permutation sentence were verified in the primary text.
* Lemma 7.2, PDF pages 32–34 (statement begins on page 32): for `0<γ≤1`, two `H^γ` inputs,
  `s∈[tₙ,tₙ₊₁]`, and `β∈[β₀(γ),1+γ]`, the bilinear stage
  `Fⁿ[s;v₁,v₂]=(1/2)∫_{tₙ}^s B_t(v₁,v₂)dt` has `H^β` norm at most
  a constant times `τ^((1+γ-β)/(1+γ-β₀)) ‖v₁‖H^γ ‖v₂‖H^γ`.
  Here `β₀=2γ-3/2` below `1/2`, `β₀=-1/2-ε` at `1/2` for a
  fixed positive loss, and `β₀=γ-1` above `1/2`. The source statement
  and all three cases were verified. The supplied paper fixes `ε=1/8`.
* Equations (2.2)–(2.3), manuscript page 8: for `γ∈[0,1]`,
  `‖fg‖L² ≲ ‖f‖H^γ ‖g‖H^{a(γ)}`, with `a(0)=1/2+`,
  `a(γ)=1/2-γ` for `0<γ<1/2`, `a(1/2)=0+`, and `a(γ)=0`
  for `γ>1/2`. These were verified. The present target only needs positive
  `γ`, choosing `a(1/2)=1/8`.
* Equations (4.15), (4.20)–(4.23), (5.2)–(5.4), and (6.1) are cited by the
  supplied paper for the cubic covariance remainder and the exact step identity.
  The covariance definition (4.15), the coefficient formula (6.1), the relation
  `Aⁿ=Hⁿ+R₂ⁿ` in (4.20), the twisted/physical update relation (4.23), and the
  interpolation formulas (5.2)–(5.4) have now been compared in the primary text.
  Their signs, coefficients and both endpoint corrections agree with the supplied
  paper. Their formal encodings and applicability proofs remain unfinished.

The source's unnormalized spatial norms differ from the target's by `√(2π)`.
Absorption into constants still requires explicit correspondence in the formal
premises. Li–Wu's convergence theorem is not an allowed input to this proof.

## Babin–Ilyin–Titi

Anatoli V. Babin, Alexei A. Ilyin, and Edriss S. Titi,
*On the regularization mechanism for the periodic Korteweg–de Vries equation*,
[arXiv:0910.1389v2](https://arxiv.org/pdf/0910.1389v2), 23 October 2010, 42 pages.
This precise version is accessible through the web tool. It treats
`U_t = U U_x + U_xxx` and mean-zero homogeneous Sobolev norms.

* Theorem 4.2, page 13: for `s₀≥0`, initial datum in homogeneous `H^{s₀}`
  with `L²` norm at most `M₀`, solutions of the Galerkin system (4.1) on
  `[0,T]` satisfy a homogeneous `H^{s₀}` bound, uniform in the truncation,
  depending only on `M₀,T,‖v(0)‖H^{s₀},s₀`. Verified.
* Theorem 4.3, page 14: for `s₀>0` and `0<σ<s₀`, a subsequence of those
  Galerkin solutions with the same datum converges strongly in
  `Lᵖ([0,T];H^σ)` for each fixed `1<p<∞` and weak-star in
  `L∞ H^{s₀}` to a solution in the sense of Definition 3.1; it has the
  same uniform bound and conserves its `L²` norm almost everywhere. Verified.
* Definition 3.1, page 6: the twisted coefficients are in `L∞ H⁰` and
  satisfy, for every nonzero `k`, the integrated coefficient equation
  `v_k(t)-v_k(0)=(ik/2)∫₀ᵗ ∑_{k₁+k₂=k} exp(i3kk₁k₂s)v_{k₁}(s)v_{k₂}(s) ds`.
  The source untwists by `Û_k(t)=exp(-ik³t)v_k(t)`. Verified.
* Theorem 5.1, page 19: for `s>1/2` and any finite `T>0`, the solution
  from Theorem 4.3 is unique, continuous into homogeneous `H^s`, Lipschitz
  in its initial datum in the sense of equation (5.18), and conserves the
  `L²` norm at every time. The statement and equation (5.18) were verified.
  That equation bounds the difference on `[0,T]` by
  `(C'(s,T,‖v₀‖H^s+‖w₀‖H^s)+1)^N ‖v₀-w₀‖H^s`,
  with `N=⌊T/T*⌋+1` and `T*` depending only on the displayed parameters.
* Theorem 6.3, page 27: the analogous uniqueness, continuity and Lipschitz
  assertions for `0<s≤1/2`, with Lipschitz dependence as in equation (6.7).
  The complete theorem statement was verified and retained in
  `sources/primary-excerpts-02.json`. Equation (6.7) was subsequently checked and
  retained in `sources/primary-excerpts-05.json`: under (6.5), iteration gives
  `‖v-w‖L∞H^θ ≤ C' (2C(T)+1)^(⌊T/τ⌋+1) ‖v₀-w₀‖H^θ`, where the local step
  and constants depend on the indicated bounds of the two solutions in
  `L∞ H^{θ₀}`. The paper uses Theorem 6.5 at `θ=0` for the uniform `L²`
  dependence, avoiding a need to infer its uniformity from this local formula.
* Theorem 6.4, page 27: for `s=0`, any homogeneous `H⁰` datum and `T>0`
  have a unique continuous homogeneous `H⁰` solution of (3.9), Lipschitz
  in its initial datum. Verified.
* Theorem 6.5, page 28: for `θ∈(-1,0]`, two initial `L²` norms summing
  to at most `M` give
  `‖v-w‖L∞([0,T];H^θ) ≤ C' (C_M)^T ‖v₀-w₀‖H^θ`,
  where `C'` and `C_M` depend only on `M,θ`. Verified, including `θ=0`.

The intended change of variables is `u(t,x)=-U(t,-x)`; on coefficients it
is `û(k)=-Û(-k)`. The supplied paper derives the signs in the equation
and preservation of all the Sobolev norms. These transformations and the
homogeneous-to-inhomogeneous norm comparisons remain internal proof obligations.

# Build and trust

`build.py` invokes only the specified Lean 4.32.2 binary and the existing
Mathlib/precompiled package search paths. The pinned Mathlib commit supplied by
the user is `905b95818eb32af7874a58b427f50c1711a5e96c`.
No environment update is performed. `build.log` is the latest compiler output.
Compilation of a checkpoint does not establish Theorem 1, nor does this audit
constitute independent semantic certification of primary-source fidelity.

# Latest compiler checkpoint

The pinned Lean executable successfully compiled the complete current
`Proof.lean` with output `Proof.olean` after the indexed Sobolev representation
change. The norm transport and continuous full-update definitions are checked
by the kernel, with no skipped checks. This is still a partial development,
and does not establish Theorem 1.

# Encoded external premises and new internal estimates

`LiWuProductEstimate` encodes (2.2)–(2.3) with `0≤γ≤1` and a positive loss
parameter `ε`, retained at `γ=0` and `γ=1/2`. Its constant precedes both inputs.
Membership in the resulting `L²` space and the norm inequality are explicit.
`sourceNorm s f = sqrt(2π) * hNorm s f` retains the primary text's unnormalized
spatial norm. `normalized_product_estimate` proves the normalization conversion;
it does not assume it.

`LiWuStageEstimate` encodes Lemma 7.2 over the entire interval
`β₀(γ,ε)≤β≤1+γ`. It quantifies over a finite horizon, regularity, loss and output
index before its constant, then over timestep, grid index, intermediate time,
and both mean-zero inputs. All timestep and input factors in the source estimate
are retained. The premise uses `sourceBilinearStage`, the *unprojected* endpoint
formula (7.3). `product_airy_zero` and `bilinearStage_eq_source` prove internally
that inserting the mean projection in each boundary value leaves the endpoint
difference unchanged. Thus this representation change is not an extra external
assumption. Restriction to steps contained in a finite horizon allows its constant
to depend on that horizon; no input or step dependence is admitted.

`paper_stage_bounds` derives both bounds (18), using the fixed loss `1/8` and
internally proved exponent comparisons in all three regularity regimes.
`numerical_stage_bounds` derives the pointwise stage bounds used in (20), including
a uniform `H¹` bound, the `H¹` difference bound and the `H^{aγ}`/`L²` smallness.
It takes only `f∈L²`, `w∈H^γ`, `‖w‖≤M`, and `‖f-w‖L²≤1`. Its constant precedes
all timesteps, grid indices and inputs. `bilinearStage_diagonal_sub` proves the
polarization identity used for the perturbation estimate.

`B`, `J`, `CIntegral` and `bilinearStage` are now defined by their full coefficient
formulas. The elementary `L²×L²→H^(-23/14)` bound for `B`, the `H¹` bound for `J`,
and the sharper bound involving `‖D⁻¹f‖L²` are proved. The substitution identity
`J_t(B_t(f,g),h)` and its coefficient integral version (14) are proved, using
`D⁻¹D=P` explicitly. The time-dependent integration-by-parts identity (13) is now proved under
explicit regularity hypotheses. Their verification for the actual trajectories
remains an obligation. `cutoff_gain_bound` and `high_cutoff_bound` prove the low/high
frequency Sobolev estimates used only in the proof; they do not modify the update.

The representation of physical products by convolution coefficients and the
source/target changes of equation are now proved below. The remaining external
premise encodings, exact-flow construction and full distributional correspondence
still require completion and assessment. These conditional lemmas and source audits do not constitute
an independently certified primary-source formalization of Theorem 1.

# Continuous trilinear premise and internal normal forms

`LiWuTrilinearEstimate.dynamic` states Proposition 3.4(1) on bounded intervals,
with `α∈[0,1]`, three `L∞ H^α` inputs, and three `L∞ H^(-23/14)` weak time
derivatives. All essential bounds are `MemLp ... ∞` in the complete normed
Sobolev spaces, with Lebesgue time measure restricted to the interval. The two
endpoints have zero time measure. `WeakTimeDerivative` is defined by integration
against compactly supported smooth test functions in the open interval. An
almost-everywhere classical derivative alone is not substituted for this
hypothesis. `sourceXNorm` is the source's unnormalized `L∞L²` norm plus its
unnormalized negative Sobolev derivative norm. The conclusion includes membership
of the full coefficient integral in `L²`, and the inequality for each designated
negative-norm input, with the operator's input slots fixed.

`LiWuTrilinearEstimate.timeIndependent` states part (2) over the entire range
`0≤α≤1`, for the same full operator on time-independent inputs. The fixed
interval-length bound `H` is quantified before the constant, making the source's
bounded-length convention explicit. `normalized_static_trilinear` proves the
conversion to normalized spatial norms, with factor `sqrt(2π)^2`. The primary
statement, including its permutation clause and time-independent restriction,
was rechecked in the accessible 50-page primary PDF, page 14. The interpretation
of its weak derivative in the formal spaces and its full source correspondence
still require independent semantic assessment.

`J_coefficient_series`, `B_coefficient_series`, `JMode_hasDerivAt` and
`J_fixed_hasDerivAt` prove the normal-form phase differentiation on the full
mean-zero `L²` space. Summable derivative bounds justify differentiation of the
infinite series. `fixed_normal_form` retains both endpoint values.
`RegularFourierPath` records coefficient continuity, coefficient differentiation
on the interval interior, and common square-summable coefficient envelopes for
an input and its derivative. `variable_J_hasDerivAt` proves the time-dependent
phase/product differentiation under those explicit internal hypotheses.
`variable_normal_form` integrates it to obtain exactly (13), again retaining
both endpoints. `regularFourierPath_of_h1_bounds` proves that ordinary uniform
`H¹` bounds on the input and derivative supply the envelope hypotheses.
`B_h1_of_h2` proves the higher regularity used only for justifying these
identities. No higher norm appears in a claimed final convergence bound.

The normal-form lemma is an internal proved implication. Verification of its
regularity hypotheses for the actual smooth exact and numerical interpolation
paths is unfinished, and has not been put into an external premise. The remaining
residual estimates, stability, bootstrap, exact-flow correspondence and density
argument are still necessary before `theorem_1` can be exported.

# Physical reconstruction and source equation correspondence

`reconstructL2_real_iff` proves that coefficient conjugate symmetry is equivalent
to almost-everywhere reality of the reconstructed normalized torus function.
`reconstructL2_integrable`, `reconstructL2_mean` and `reconstructL2_meanZero`
identify the zero coefficient with the actual normalized spatial integral.
`normalized_L2_product_integrable` proves integrability of the physical product
of any two `L²` functions. `normalized_L2_product_coeff` proves its full convolution
formula by Parseval in Mathlib's Fourier Hilbert basis, using a character shift
and conjugation. Thus `reconstructL2_product_coeff` identifies the raw product
used throughout the method and PDE with physical multiplication, including rough
inputs. No pointwise convergence of a Fourier series is assumed.

`reflectSign f k = -f(-k)` preserves the Sobolev norms, reality and zero mean.
`reflectSign_B` proves the change between the source's positive twisted phase
and the target's negative phase. `homogeneousWeight`, `InHomSobolev` and
`homogeneousNorm` encode the source's normalized mean-zero homogeneous norms.
For nonnegative `s`, the proved comparisons are
`homogeneousNorm s f ≤ hNorm s f ≤ 2^s * homogeneousNorm s f`.
The deliberately loose comparison constant depends only on `s`. At order zero
the norms agree exactly. Their norm continuities transfer on the prescribed
closed time interval.

`SourceNonzeroEquation` states the source's integrated coefficient equation only
for nonzero modes, as in Definition 3.1. `SourceNonzeroEquation.all_modes` proves
the zero-mode extension from mean-zero hypotheses. `source_phase_formula`
identifies `B(-t)` with the source's `exp(+i 3kabt)` phase.
`sourceTwisted_to_target` and `targetTwisted_to_source` prove both changes under
reflection. `twist_Duhamel` and `untwist_Duhamel` prove both changes between the
physical Duhamel representation and the target twisted representation. These
are algebraic/integral identities proved internally, without additional solution
premises. `source_solution_to_kdv` and `kdv_solution_to_source` combine the norm,
continuity, reality and equation changes. `sourceFrame_difference_norm` proves
that the source homogeneous `L²` distance is exactly the original physical
`L²` distance. The source existence/uniqueness theorems, smooth-approximation
construction, and complete distributional PDE correspondence remain unfinished.

# Source-flow construction and initial-ball uniformity

`SourceGalerkinODE` is the cited source's (4.1), with the positive phase,
initial data on all modes, and the projection in its exact-flow construction.
This projection is absent from the numerical update. The derivative condition
is on the open time interval and Sobolev continuity includes both endpoints.

`BITGalerkinEstimate` encodes the estimate clause (4.13) of Theorem 4.2,
arXiv:0910.1389v2, page 13. Its constant follows `s,M₀,T,r` and precedes the
datum, flow and Galerkin index. The hypothesis is the equality
`homogeneousNorm s f = r`; no monotonicity in an unspecified source constant
or uniform bound over a norm ball is imported.

`homogeneous_sphere_padding` now proves the uniformity step internally. It
replaces a projected datum's tail with two real, symmetric modes outside the
projection, making the homogeneous norm exactly `R`. The projected trajectory
is unchanged and the original tail is stationary. The fixed-sphere source bound
therefore yields `uniform_source_galerkin_bound` over the entire norm ball.
`homogeneous_L2_time_subsequence` derives almost-everywhere coefficientwise
convergence from strong time convergence, using Mathlib. Finite-frequency norm
limits and continuity then transfer the bound to every time, including endpoints.

`BITExistenceLimit` encodes Theorem 4.3 and its a priori bound: a real weak
solution, essential higher-norm boundedness, almost-everywhere energy equality,
a Galerkin subsequence converging strongly in every finite time `L^p`, `p>1`,
at a fixed `0<σ<s`, and weak-star convergence in the top Sobolev space. Time
norms are actual `MemLp`/`eLpNorm` conditions; weak-star convergence is tested
against every integrable weighted-Hilbert-space dual function. Its bound is
chosen after the datum and does not assume initial-ball uniformity.

`BITHigherRegularity` and `BITLowRegularity` encode Theorems 5.1 and 6.3,
respectively, for the limiting solution constructed by Theorem 4.3. They retain
continuity, uniqueness in the continuous solution class, and local Lipschitz
dependence. The higher-regularity premise also retains energy equality at all
times. `BITL2Wellposedness` records Theorem 6.4, whose primary statement explicitly
specifies uniqueness in `C([0,T]; Hdot^0)`. None of these types assumes uniqueness
among arbitrary essentially bounded weak solutions. `BITWeakerLipschitz` records
the complete range `-1<θ≤0` of Theorem 6.5: the two constants depend only on
`M,θ`, precede time and data, and bound the time-essential-supremum difference by
`C' * CM^T` times the initial weaker norm when the initial L² norms sum to at
most `M`. Continuous solution-class hypotheses are explicit.

`SourceWeakSolution` includes the integrated Fourier equation, real zero-mean
coefficients, and an actual essential time bound. Continuous homogeneous paths
are proved to have such essential bounds; target Sobolev solutions are proved
to satisfy these source weak hypotheses under the frame transformation.
`uniform_source_flow_exists`, `uniform_source_flow_bound`, and
`uniform_kdv_flow_bound` now derive uniform exact-flow bounds with constants
preceding data. `source_flow_lipschitz` upgrades the external almost-everywhere
estimate to all times. `kdv_flow_l2_lipschitz` transports it to physical L²,
including flows with different nonnegative Sobolev orders.

These are explicit conditional source encodings and internally proved
applications, not independent certification of primary-source fidelity.
Theorem 1's interpolation estimates, stability/bootstrap, solution-concept
completion and density passage remain unfinished. The exported declaration
`theorem_1` does not yet exist.

# Continuous interpolation checkpoint

`LiWuStepIdentity` now explicitly records the cited identity (5.2), equivalently
(4.20)–(4.23), specialized to order-one real zero-mean inputs. It states equality
of the full physical update, conjugated into the twisted frame, with the frozen
stage plus cross integral minus the precise covariance remainder already defined.
It does not supply a residual or stability estimate. The source formulas were
accessible and checked; this conditional encoding still requires independent
semantic assessment. The specialization to H¹ is sufficient for the temporary
smooth-data interpolation argument and does not restrict the target data ball.

`frozenCross`, `frozenSquare`, `endpointCorrection`, `localInterpolation`, and
`interpolationRemainder` are the full formulas of Section 4.3. Endpoint agreement
is proved from the identity. `stageTwoBundled`, `frozenCrossBundled`, and
`frozenSquareBundled` represent these same functions in complete Sobolev spaces;
coefficient equality with their Bochner integrals is proved. Coefficient
derivatives follow from the proved phase identity and the fundamental theorem
of calculus. `localInterpolation_regular` verifies all hypotheses of the proved
variable-input normal form for the actual interpolation. Higher norms used for
this justification do not occur in its convergence estimates.

`numerical_stage_square_bound`, `numerical_square_integral_bound`, and
`numerical_endpoint_correction_bound` prove (21), with constants before the
numerical state and step. `numerical_cross_inverse_bound` proves the asymmetric
inverse-derivative cross bound used in (22). `frozenCross_normal_form` proves
(23)'s identity, including justification for the zero initial boundary value.
`continuous_CIntegrand_fixed` and the trilinear additivity lemmas prove the
analytic legitimacy of the forthcoming cubic telescoping argument even for
rough L² inputs. None of these estimates is an external premise.

The complete merged partial development is now 7690 lines and compiled with
the pinned Lean executable; `Proof-build-process.json` records exit code 0 and
`Proof-build.log` is empty. This remains an incomplete development: the remaining
defect bounds, restarted stability, bootstrap and final uniform density passage
have not been established, and `theorem_1` is absent.

# Defect norm checkpoint

The new merged chapters prove all estimates (22)–(24) for the actual one-step
interpolation. `numerical_static_cubic_bound` uses the internally proved three-
term telescoping identity, the cited static estimate at γ on the exact state,
and its order-zero estimate on the three difference terms. This yields
`numerical_cross_bound` and `numerical_defect_l2_bound`, without a numerical
H^γ norm bound. `numerical_cross_inverse_integral_bound` commutes the Fourier
inverse derivative with the integral, and `numerical_defect_negative_bound`
combines it with (21). `negative_hNorm_le_inverse` supplies the mean-zero
negative-norm comparison internally.

`interpolationRemainderDerivative` is the derivative of the actual defect;
`interpolationRemainder_hasDerivAt` proves this coefficientwise. Its continuous
bundled representation gives `interpolationRemainder_regular`.
`numerical_defect_derivative_bound` proves both its inverse-derivative and
negative Sobolev bounds. `numerical_defect_time_bounds` combines these into the
actual essential time norm, proves both required `MemLp` conditions, and derives
the distributional time derivative from the proved regularity. Thus (24) is
available with no hidden regularity or time-norm premise.

`normalized_dynamic_trilinear` transports the full cited estimate to normalized
measure and retains all three choices of the negative-norm input. The normalization
factor is proved to contribute exactly its square to the constant. No residual
or stability bound is imported by this result.

The merged partial file is now 8403 lines and has a successful full pinned build
(exit code 0 in `Proof-build-process.json`, empty `Proof-build.log`). Residual
(26), restarted stability/bootstrap, solution-concept completion and density
remain unfinished; no declaration named `theorem_1` is present.

# Residual checkpoint

`localResidual` and `localResidualDerivative` now encode the exact expressions
in (25)–(26). `localInterpolation_perturbation_identity` proves the differential
identity from bilinearity. `localResidual_hasDerivAt` proves the actual residual
derivative, and `localInterpolation_integral_identity` proves (25)'s integral
identity by the fundamental theorem of calculus. These identities refer to the
previously defined, endpoint-correct interpolation of the specified method.

The dynamic trilinear estimate is applied in `dynamic_constant_pair_bound` and
`numerical_cubic_defect_bound`, retaining all actual time norm, membership and
weak derivative hypotheses. Restriction to a partial final step is proved.
`integral_B_self_bound` and `integral_B_cross_bound` are internally proved
normal-form estimates, retaining both endpoints until the zero initial defect
is substituted. `numerical_residual_bilinear_bounds` supplies all their hypotheses
from the actual interpolation. `numerical_residual_derivative_bound` and
`numerical_residual_bounds` now prove both bounds in (26), with constants before
the numerical state and step count and independent of higher numerical norms.

The merged 9240-line partial development has a successful full pinned build
(exit code 0, empty compiler log). The remaining numerical work is the global
piecewise interpolation, restarted stability estimates (27)–(34), the bootstrap
and the final uniform density argument. The exact-solution-concept completion
also remains necessary. `theorem_1` is still absent.

# Global paths and proof projections checkpoint

`concatenate` joins finitely many step functions. Its continuity theorem uses
proved endpoint matching. `globalInterpolation` applies it to the actual twisted
numerical states: these states retain every mode and are proved to stay in H²
for the temporary regularity argument. `globalInterpolation_grid` identifies
every grid value, including the terminal point, with the specified method.
`globalResidual` joins the cumulative local increments; it is continuous, starts
at zero, and `globalResidual_step_increment` identifies each step increment.

`global_perturbation_integral_identity` proves the restarted perturbation identity
on every subinterval of the numerical time interval. Classical derivatives are
only used in open steps. Mathlib's fundamental theorem off a countable set handles
the grid, so differentiability at grid points is not assumed. The same method
proves `variable_normal_form_grid` and `grid_weakTimeDerivative` for continuous
paths with possibly jumping derivative pieces. The derivative representatives
are proved measurable and integrable by the concatenation tools.

`SupportedIn` and its product/inverse-derivative/Airy rules prove that the
trilinear integral of three inputs supported at frequencies at most m has no
output above 3m. The projection maps are bounded continuous linear maps, contract
Sobolev norms, and commute with the weak time derivative. These projections only
occur in the proof, not in the algorithm. `CIntegral_paths_difference` proves the
moving-input telescoping identity needed for the high-output estimate.

The primary Proposition 3.4 statement was rechecked. The formal trilinear premise
now explicitly includes `0 < H ≤ 1`; all applications use H=1. Thus its
bounded-length hypothesis is visible and no arbitrary-length extension is
assumed. The complete α range and both source conclusions remain encoded.
Details are in `sources/source-check-07.md`.

All 10119 merged lines pass a full build in the pinned environment, with exit
code 0 and an empty compiler log. The numerical high-output estimate, restarted
norm estimates, stability/bootstrap, final density and solution-concept
completion remain necessary; `theorem_1` is not yet declared.

# High-output and actual error normal-form checkpoint

`ProjectionTimeNorm` estimates prove contraction of both components of the actual
X time norm and the precise high-input negative-norm gain.
`one_high_cubic_bound` applies the cited source estimate separately to each
specified high-input term, preserving the weak derivative and essential-bound
hypotheses. `high_output_trilinear_bound` now proves (32), with proof threshold
3m and gain `weight (-pStar) m`. It uses the internally proved support
cancellation and moving-input telescoping, rather than importing a high-output
estimate as a premise.

`extendedTwistedPath` extends the actual H² Duhamel solution constantly outside
its time interval. Its continuity, mean zero, integrated equation, and actual
coefficient derivative are proved. `numericalDerivativeFamily` and
`numericalResidualDerivativeFamily` supply verified derivative families of the
full interpolation. `actual_error_normal_form` applies the proved grid normal
form to the actual exact and numerical trajectories, discharging every internal
ODE callback and retaining both endpoints. `actual_error_integral_identity`
proves (29), and `actual_error_grid_norm` identifies its grid norm with the
physical L² error of the original method.

`restarted_residual_bound` proves (27), including the count of full and partial
increments. `restarted_residual_derivative_time_bound` proves the corresponding
global essential-time derivative bound. These conditional internal results take
a bootstrap error bound on a restarted interval and an exact Hγ bound. The exact
bound is to be instantiated by `uniform_kdv_flow_bound`, which was already proved
from the cited flow results with constants preceding the datum. The bootstrap
condition still has to be discharged by the global first-exit argument; no
stability or convergence estimate has been made an external premise.

The merged partial file has 11241 lines and passes a full pinned build (exit
code 0, empty log). The remaining work includes the full restarted X estimates,
forcing estimate and stability/absorption, global bootstrap, uniform density and
complete solution-concept correspondence. The exported `theorem_1` is absent.


Further checkpoint: the 12031-line merged partial development passes the full
pinned build. The internal `restarted_error_time_bound` proves the small error
X estimate in (28), and `restarted_affine_error_time_bounds` proves the bounded
X estimates for the interpolation (coefficient 1) and midpoint (coefficient
1/2), with actual weak derivatives and essential time memberships. The generic
`dynamic_small_input_bound` keeps operator slots fixed while selecting the
small negative input. `local_residual_forcing_bound` proves the complete-step
and partial-step forcing bound, including the actual endpoint correction.
`grid_integral_bound` proves finite-step accumulation for genuine Bochner
integrals without requiring derivative pieces to agree at grid points. The
actual `restarted_forcing_bound` has also compiled separately and is being
merged. Its bootstrap and exact-flow bound hypotheses are internal hypotheses
still to be discharged by later work, not added external premises. The full
stability/absorption, bootstrap, density, solution-concept correspondence and
export of theorem_1 remain unfinished.


Further checkpoint: the merged 12796-line partial file passes a full pinned
build (exit 0; only unnecessary-sequencing linter warnings). The actual
`restarted_forcing_bound`, `restarted_cubic_bound`,
`restarted_error_integral_bound`, `restarted_error_inequality`,
`absorption_parameters`, and `restarted_stability_bound` are now proved and
merged. They give the quantitative restarted argument through (35), including
retained endpoint terms, both cubic terms, forcing, low-output control, a
frequency threshold chosen before data, and an actual maximum argument. The
temporary unit-error bootstrap remains explicit. `continuity_unit_bootstrap`
has compiled separately and supplies a genuine first-crossing argument; its
application on finitely many blocks is still unfinished. No stability estimate
has been added as an external premise. The final density passage, complete
solution-concept correspondence and export of theorem_1 remain unfinished.


Convergence checkpoint: the 13166-line merged `Proof.lean` passes the full pinned
build (exit code 0; linter warnings only). It now exports the top-level
`theorem_1 : TheoremOne`, with nine explicit cited-result parameters. The
stronger `uniform_rough_convergence` proves the same quantitative conclusion
for every real mean-zero continuous Sobolev Duhamel solution. The first-crossing
argument and fixed-number block induction discharge the error bootstrap.
`uniform_h2_convergence` contains no H² norm in its constants. Density constructs
actual H² flows for Fourier-polynomial approximants using the source existence
results, bounds them uniformly in Hγ using the already proved initial-ball
bound, and passes to rough data by the source L² dependence and full-method L²
continuity at fixed timestep. Approximation cutoffs do not enter the method.
All constants are selected before the original datum and step count.

The checkpoint remains in progress: distributional correspondence and the
canonical smooth-approximation solution-concept correspondence are not yet
fully formalized. The existence of continuous positive Sobolev Duhamel flows is
proved, so the stronger convergence statement is not vacuous. A proof of the
rate for that larger class does not itself certify that every detail of the
paper's exact-solution representation has been independently verified.
