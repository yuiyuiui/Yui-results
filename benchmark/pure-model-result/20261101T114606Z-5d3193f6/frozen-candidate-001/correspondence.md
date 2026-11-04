**Target and status**

`Proof.lean` is a complete conditional formal development. Its top-level exported declaration is `theorem_1 : KdV.TheoremOne`, with nine explicit parameters for cited external results. Those parameters are mathematical propositions, not new axioms. Every internal estimate, existence/approximation construction, stability argument and density step has a Lean proof.

The target is Theorem 1 of the supplied 15-page paper, Kaiwen Jin, *Removing the logarithmic loss in the Li–Wu KdV integrator*, 10 October 2026. The entire supplied article, including the definitions, assumptions and proof, was read; `paper.txt` preserves its extracted text.

The formal conclusion has this order:

```
∀ T > 0, ∀ γ > 0 with γ ≤ 1, ∀ R > 0,
∃ C > 0, ∃ τ₀ > 0,
∀ real mean-zero f ∈ H^γ with ‖f‖H^γ ≤ R,
∀ exact solutions u for f,
∀ L ∈ ℕ with L > 0 and τ = T/L ≤ τ₀,
max { ‖u(nτ) − numerical(τ,f,n)‖L² : n = 0,…,L } ≤ C τ^γ.
```

`maximumError` is the literal `Finset.sup'` over `Finset.range (L+1)`. Both endpoints are included. `uniform_rough_convergence` proves the same estimate for the larger class of all continuous Sobolev Duhamel solutions. Constants precede the datum, solution and step count. No numerical Sobolev bound or desired stability/convergence estimate is a parameter.

**Spaces, measure and Fourier representation**

`Torus = AddCircle (2π)`. `normalizedMeasure` is probability Haar measure, representing `dx/(2π)`. The Fourier character is `exp(ikx)` and the coefficient is `(2π)⁻¹ ∫₀²π f(x)exp(-ikx) dx`.

All integer modes are present. `weight s k = (1+k²)^(s/2)`, `InSobolev s f` is weighted `ℓ²` membership, and `hNorm s f` is the square root of the weighted square sum. `Sobolev s` carries the complete norm topology transported by `sobolevIsometry`. `polynomialToSobolev_denseRange` identifies it with the prescribed completion of trigonometric polynomials, for every real index.

For negative indices, `distributionTest s φ` is a continuous functional on `Sobolev (-s)`. Its action is proved to be

```
∑ k∈ℤ, f̂(k) φ̂(-k),       |⟨f,φ⟩| ≤ ‖f‖H^(-s) ‖φ‖H^s.
```

This is a bilinear distribution/test pairing; it intentionally has no Hilbert-space conjugation. On functions it is the zero coefficient of the full product. `normalized_L2_product_coeff` proves that convolution is the Fourier representation of actual normalized physical multiplication, including for two rough L² inputs. No pointwise Fourier-series convergence is assumed.

`RealValued f` means `f(-k)=conj(f(k))`, proved equivalent to almost-everywhere reality of `reconstructL2 f`. `MeanZero f` means `f(0)=0`, proved equivalent to vanishing normalized integral. Parseval and the L² reconstruction are proved using the pinned Mathlib Fourier Hilbert basis.

**The complete fixed method**

`airy t` has multiplier `exp(itk³)`, so it is `S_t=exp(-t∂ₓ³)`. `inverseDerivative` is `(ik)⁻¹` off zero and zero at zero. `inverseDerivative₂` is its square. `mean` is `P₀` and `removeMean` is `P=I-P₀`. `product` is convolution over every integer input mode.

The definitions `quadratic`, `cubicCorrection`, `step`, and `numerical` implement exactly

\[
F_τ(f)=\tfrac16P[(S_τD^{-1}f)^2]-\tfrac16S_τP[(D^{-1}f)^2],
\]

\[
\begin{aligned}
H_τ(f)={}&\tfrac13P[(S_τD^{-1}f)D^{-1}F_τ(f)]
 +\tfrac τ9(S_τD^{-1}f)P_0(f^2)\\
&-\tfrac1{54}[S_{τ-s}D^{-1}((S_sD^{-1}f)^3)]_{s=0}^{s=τ}\\
&-\tfrac1{27τ}[S_{τ-s}D^{-2}((S_{s-τ}D^{-2}F_τ(f))(S_sD^{-1}f))]_{s=0}^{s=τ}.
\end{aligned}
\]

Each bracket is its value at `s=τ` minus its value at zero. The recurrence starts at the original datum and uses `S_τ f+F_τ(f)+H_τ(f)`. The full update preserves L² membership, the required positive Sobolev membership, reality and mean zero. Its bundled map and every finite iterate are continuous on L².

There is no filter or spatial cutoff in this recurrence. Symmetric cutoffs appear only in proved approximation and frequency-decomposition lemmas. All products retain their full intermediates.

**Exact solution and distributional equation**

`KdVSolution γ T f u` requires real mean-zero `C([0,T];H^γ)` regularity, the initial condition, and, for every integer mode and every time in the closed interval, the Duhamel identity

\[
\widehat u(t,k)=e^{itk^3}\widehat f(k)
 +\frac12\int_0^t e^{i(t-s)k^3}(ik)\widehat{u(s)^2}(k)\,ds.
\]

`SmoothSolution` additionally requires every spatial Sobolev regularity and every finite time differentiability order on the closed interval. `ObtainedBySmoothApproximation` requires actual such solutions, convergence of their data in H^γ, and uniform-in-time L² convergence of the flows. `ExactSolution` combines this condition with `KdVSolution`.

These are not vacuous or additional smooth-data restrictions:

- `positive_kdv_flow_exists` constructs continuous positive Sobolev flows from the cited source results.
- `all_sobolev_flow_exists` transfers higher spatial regularity by uniqueness.
- `all_regular_coefficient_contDiffOn` proves time smoothness from the actual autonomous KdV equation in the Sobolev scale, including one-sided endpoint regularity.
- `smooth_kdv_flow_exists` constructs the smooth approximating flows.
- `kdv_solution_smooth_approximation` proves the required convergence, using polynomial approximants and the cited L² flow dependence.
- `exactSolution_iff_kdvSolution` and `exact_solution_exists` prove equivalence with the continuous positive Sobolev Duhamel class and existence for every admissible datum. `kdv_solution_unique` proves uniqueness in that class.

`physicalRHS f = -∂ₓ³f + (1/2)∂ₓ(f²)`. `physicalRoughField` realizes it as a continuous map `H⁰ → H⁻³`. `kdv_solution_sobolev_distributional` proves the actual Bochner identity

\[
\int_0^T φ'(t)u(t)\,dt=-\int_0^T φ(t)\bigl(-∂_x^3u(t)+\tfrac12∂_x(u(t)^2)\bigr)\,dt
\quad\text{in }H^{-3}
\]

for every compactly supported smooth time test function in `(0,T)`. `kdv_solution_distributional_spatial_tests` proves its pairing with every H³ spatial test function, hence with smooth periodic spatial tests. The distribution/test pairing and physical product correspondence above supply the spatial distribution representation. This is equation (1) distributionally, with the separately retained initial condition.

**External premise types and primary sources**

The types in `Proof.lean` are the authoritative complete formal hypotheses and conclusions for the cited clauses/specializations used here. All essential primary texts were accessible and inspected. Source text inspection and the following correspondence are a manual assessment; they are not independent certification. See `warn.json`.

Li–Wu: Buyang Li and Yifei Wu, *An Unfiltered Low-Regularity Integrator for the KdV Equation with Solutions Below H¹*, the cited [50-page author manuscript](https://www.polyu.edu.hk/ama/profile/byli/FoCM-3.pdf), DOI [10.1007/s10208-025-09702-0](https://doi.org/10.1007/s10208-025-09702-0). The manuscript version, rather than journal pagination, is used.

1. `LiWuProductEstimate`: (2.2)–(2.3), manuscript page 8. For `0≤γ≤1`, every loss `ε>0`, and all inputs in H^γ and H^{a(γ,ε)}, the product belongs to L² and satisfies the bilinear norm bound. Here `a=1/2+ε` at zero, `a=1/2-γ` strictly between zero and one half, `a=ε` at one half, and `a=0` above one half. The constant precedes both inputs.
2. `LiWuStageEstimate`: Lemma 7.2 and (7.3), PDF pages 32–34. For `T>0`, `0<γ≤1`, `ε>0`, and `β₀≤β≤1+γ`, its constant precedes all positive steps, grid indices, intermediate times and mean-zero H^γ inputs. The output belongs to H^β, with factor `τ^((1+γ-β)/(1+γ-β₀))`. The three lower endpoints are `2γ-3/2`, `-1/2-ε`, and `γ-1`, respectively below, at, and above one half. The formal premise uses the source's unprojected endpoint stage. `bilinearStage_eq_source` proves its equality with the projected endpoint difference used internally.
3. `LiWuTrilinearEstimate`: both parts of Proposition 3.4, manuscript page 14. For `0<H≤1`, `0≤α≤1`, and `0≤a≤b` with `b-a≤H`, the dynamic statement requires actual essential H^α bounds and actual weak H^(-23/14) derivatives for all three inputs. It concludes L² membership of the full cubic time integral and the bound

   `C(b-a)∏X_j + C‖f_i‖L∞H^(-23/14) ∏_{j≠i}‖f_j‖L∞L²`,

   for each chosen `i`, leaving operator slots fixed. `X_j` is the L∞L² norm plus the essential negative derivative norm. The static statement retains the full range `0≤α≤1` and the factor `(b-a)^α∏‖f_j‖H^α`. Constants precede the interval and inputs. Every application uses `H=1`. The source permutation is on the bound's right side; no operator permutation is assumed.
4. `LiWuStepIdentity`: the algebraic identity from (4.20)–(4.23), equivalently (5.2), specialized to real mean-zero H¹ inputs. For every positive τ and grid index, the twisted complete update equals `f + bilinearStage + frozenCross - remainder`. The remainder is the exact covariance formula (4.15), (6.1), already defined independently. This premise contains no residual, stability or convergence bound. The full physical update (1.4) and both endpoint corrections were compared term by term with the supplied paper.

Li–Wu's spatial norms are unnormalized. `sourceNorm = κ*hNorm`, `κ=√(2π)`, explicitly retains that convention. The proved conversions contribute κ for bilinear estimates and κ² for trilinear estimates. Their logarithmic convergence theorem is never a premise.

Babin–Ilyin–Titi: Anatoli V. Babin, Alexei A. Ilyin and Edriss S. Titi, *On the regularization mechanism for the periodic Korteweg–de Vries equation*, [arXiv:0910.1389v2](https://arxiv.org/pdf/0910.1389v2), 23 October 2010, 42 pages. The source uses normalized measure and mean-zero homogeneous spaces. `SourceWeakSolution` retains Definition 3.1's integrated nonzero-mode equation and an actual essential Hdot⁰ bound.

5. `BITGalerkinEstimate`: the estimate clause (4.13) of Theorem 4.2, PDF page 13. For `s≥0`, `M₀≥0`, `T>0`, and actual initial norm `r≥0`, a constant is chosen before the positive Galerkin index, real datum and continuous Galerkin flow. Hypotheses include initial Hdot^s norm **equal to** r and initial L² norm at most M₀. The conclusion bounds Hdot^s at all times. Equation (4.1) initializes the full datum; modes outside the source projection are stationary, exactly as `SourceGalerkinODE` specifies. No initial-ball uniformity or monotonicity of an unspecified source constant is assumed.
6. `BITExistenceLimit`: Theorem 4.3, PDF page 14. For `s>0`, `T>0`, real mean-zero Hdot^s data and a fixed `0<σ<s`, there is a limiting weak solution, essentially bounded in Hdot^s, with the almost-everywhere L² energy identity. Its certificate includes the source Galerkin family, a strictly increasing subsequence, strong L^p-time Hdot^σ convergence for every finite `p>1`, and weak-star L∞ Hdot^s convergence tested against every integrable Hilbert-space dual function. The common bound follows the datum; it is not silently uniform on the initial ball.
7. `BITHigherRegularity`: Theorem 5.1, PDF page 19, with dependence described in (5.18). For `s>1/2`, `T>0`, real Hdot^s data and the constructed limiting solution, it retains continuous Hdot^s regularity, uniqueness in the continuous solution class, local Lipschitz dependence, and all-time L² conservation. `SourceLocalLipschitz` spells out a positive initial-data neighborhood, a positive constant preceding all nearby real data and continuous weak flows, and the almost-everywhere time inequality. The local solution-map formulation is used for this qualitative source conclusion; no bound uniform on an initial ball is inferred from it.
8. `BITLowRegularity`: Theorem 6.3, PDF page 27. It retains the analogous constructed-limit continuity, continuous-class uniqueness and local Lipschitz conclusion for the entire range `0<s≤1/2`, with dependence described through (6.7).
9. `BITWeakerLipschitz`: Theorem 6.5, (6.22), PDF page 28. For `M≥0` and `-1<θ≤0`, positive constants `C′, C_M` precede T, both real mean-zero L² data and both continuous weak flows. Initial L² norms must sum to at most M. The essential-time Hdot^θ difference is at most `C′ C_M^T` times the initial Hdot^θ difference. The full θ range is encoded; the proof uses θ=0 and upgrades the estimate to all times by continuity.

`BITL2Wellposedness` also records the continuous-class Theorem 6.4 but is not a parameter of `theorem_1`; positive-regularity existence and Theorem 6.5 suffice here. No uniqueness among arbitrary L∞ Hdot⁰ weak solutions is assumed. Primary statements, including the full-tail Galerkin convention and the dependence clauses, are recorded in `sources/primary-excerpts-01.json` through `-06.json` and `sources/source-check-07.md`, `-08.md`.

The source equation is `U_t=U U_x+U_xxx`. The proved transformation is `u(t,x)=-U(t,-x)`, coefficient map `reflectSign f(k)=-f(-k)`, together with the respective Airy frames. It preserves norms, reality, mean zero and L² distances. Source/target integrated equations and both frame changes are proved in both directions. Auxiliary norm comparison uses the valid loose bound `‖f‖H^s≤2^s‖f‖Hdot^s` for nonnegative s; the target's exact H^s norm itself is unchanged.

**Internal convergence proof**

The covariance estimates, two four-frequency majorants, infinite four-linear summation and mixed remainder estimate are internal proofs. The summation uses a proved Schur/Hardy kernel bound in place of the paper's dyadic summation. Corollary 7's numerical-state estimate follows by trilinear telescoping and its L² endpoint.

The complete continuous interpolation has the exact numerical endpoints. Its actual coefficient derivatives, weak derivatives and residual are proved. Both normal-form endpoints are retained after restarting. The defect, residual, forcing and low/high estimates are derived for those paths. A numerical H^γ bound is never required.

The source fixed-actual-norm bound becomes an initial-ball bound by the proved sphere-padding construction, passage through strong time convergence and finite-frequency limits, followed by continuity. `uniform_kdv_flow_bound` chooses its bound before the datum.

`restarted_stability_bound` proves (35) with proof parameters chosen uniformly. `continuity_unit_bootstrap` and `grid_block_bootstrap` discharge the temporary unit-error hypothesis. `uniform_h2_convergence` proves the maximum-grid estimate using only the common exact H^γ bound. `uniform_rough_convergence` then uses norm-contracting polynomial approximants, actual H² flows, uniform L² flow dependence and continuity of every finite iterate of the full numerical map. The timestep is fixed only during this limiting argument; the constants were chosen earlier.

**Build and trust boundary**

The final `Proof.lean` imports only `Mathlib`; it does not import auxiliary checkpoints. Build command: `python3 build.py Proof.lean -o Proof.olean`. `build.py` supplies the existing pinned library search paths and invokes `/Users/syyui/.elan/toolchains/leanprover--lean4---v4.32.2/bin/lean`. No `lake update` or environment change was performed. The Mathlib commit was checked as `905b95818eb32af7874a58b427f50c1711a5e96c`.

`Proof-build-process.json`, `Proof-build.log`, `Audit-build.log`, and `build-verification.json` record verification. The axiom audit of `theorem_1` and the main analytic/correspondence declarations reports only `propext`, `Classical.choice`, and `Quot.sound`. There are no `sorry`, `admit`, `axiom`, or `unsafe` tokens in `Proof.lean`.

This is a conditional formal proof with manually checked primary-source correspondence. It is a completed candidate for independent semantic assessment, not an independently certified primary-source formalization. `warn.json` retains that distinction. Historical progress notes are preserved separately in `checkpoint-history.md`.
