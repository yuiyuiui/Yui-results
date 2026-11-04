# Acceptance feedback for candidate 001

The independent candidate evaluation is complete and NOT_ACCEPTED. All ten modules rebuilt and the original hash remained unchanged. The unmet requirements below are evaluation feedback, not mathematical construction hints. The original full task remains unchanged.

## S8 — FAIL

Original-equivalent source input: BareModelCompletion.BITTheorem63

regularity retains 0<s<=1/2, constructed limits, continuity and weak uniqueness. dependence is BITDependence67Norm (:344), whose governing bound is fixed to bitHomSup s T v + bitHomSup s T w <= C0, with Hdot^s essential membership. The source permits theta0=0 for 0<s<1/2 and theta0>0 at s=1/2. Thus the submitted constant/step choices may depend on a higher Sobolev flow bound where the primary result depends on an Hdot^0 bound. The literal factor C-prime*(2C+1)^(floor(T/tau)+1) does not preserve this quantitative dependence by itself. dependence67_iff changes only norm versus a.e. form; it does not prove recovery of the original theta0 dependence.

Required evidence: Restore the complete original quantitative dependence, including the governing lower-norm bounds; keep any sufficient specialization internal as a proved consequence. Supply a checked substantive equivalence if retaining a reformulation.

Evidence locations: BIT p.27 Theorem 6.3, p.22 (6.2)–(6.7), p.23 (6.8), p.26 Theorem 6.1; /Users/syyui/projects/Yui-results/benchmark/pure-model-supplement/20261101T114606Z-5d3193f6/work/OriginalExternals.lean:355

## H8 — FAIL

Exact-original input coverage for KdV.BITLowRegularity

The proof is closed from the submitted input, but that input specializes the governing source dependence. Exact-original-input coverage is therefore unresolved; compilation of low_to_historical does not certify it.

Required evidence: Provide coverage from a full original-equivalent low-regularity source input, with the original quantitative dependence intact.

Evidence locations: /Users/syyui/projects/Yui-results/benchmark/pure-model-supplement/20261101T114606Z-5d3193f6/work/RegularityBridges.lean:172

## T4 — UNVERIFIED

Substantive two-way correspondence with the paper distributional solution convention

The actual declarations prove KdVSolution implies the coefficient, H^-3-valued and spatially tested distributional PDE. completed_exact_solution_iff proves equivalence with KdVSolution, which itself already assumes Duhamel. I did not find a closed reverse correspondence from the paper continuous distributional PDE with initial trace/smooth-approximation convention to this Duhamel-based model. The positive forward results do not alone establish the user-required two-way representation equivalence. This is unavailable proof evidence, not a claim that the target theorem is false.

Required evidence: Supply an existing checked declaration or a complete checked two-way correspondence for the paper solution convention and the final Duhamel/ExactSolution model, including initial trace and representatives; do not impose extra solution hypotheses.

Evidence locations: target.pdf p.2 Section 2 exact-solution paragraph; /Users/syyui/projects/Yui-results/benchmark/pure-model-supplement/20261101T114606Z-5d3193f6/work/OriginalProof.lean:399; /Users/syyui/projects/Yui-results/benchmark/pure-model-supplement/20261101T114606Z-5d3193f6/work/OriginalProof.lean:406; /Users/syyui/projects/Yui-results/benchmark/pure-model-supplement/20261101T114606Z-5d3193f6/work/OriginalProof.lean:410; /Users/syyui/projects/Yui-results/benchmark/pure-model-supplement/20261101T114606Z-5d3193f6/work/OriginalProof.lean:424; /Users/syyui/projects/Yui-results/benchmark/pure-model-supplement/20261101T114606Z-5d3193f6/work/OriginalProof.lean:13543; /Users/syyui/projects/Yui-results/benchmark/pure-model-supplement/20261101T114606Z-5d3193f6/work/OriginalProof.lean:13714; /Users/syyui/projects/Yui-results/benchmark/pure-model-supplement/20261101T114606Z-5d3193f6/work/OriginalProof.lean:13816; /Users/syyui/projects/Yui-results/benchmark/pure-model-supplement/20261101T114606Z-5d3193f6/work/OriginalProof.lean:13912

## C1 — FAIL

Complete exact-original-input to exact-original-target chain

The candidate has a closed formal implication from its submitted input types. The mandatory source-fidelity contract fails for bit63, and the requested full target solution-representation equivalence remains unverified. Therefore the complete semantic acceptance chain is not established.

Required evidence: Resolve S8/H8 and T4 while preserving OriginalProof and the original target.

Evidence locations: /Users/syyui/projects/Yui-results/benchmark/pure-model-supplement/20261101T114606Z-5d3193f6/work/OriginalExternals.lean:344; BIT pp.22–23,26–27
