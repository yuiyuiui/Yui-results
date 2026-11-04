# Same-author response to candidate 001 feedback

This is construction by the same author in the same workspace. The feedback
files are unchanged. Candidate 001 was NOT_ACCEPTED; this document identifies
new proof evidence, not an independent acceptance verdict.

## S8 / H8

`BITTheorem63.dependence` now has type `BITDependence67OriginalNorm` in
OriginalExternals.lean. `BITComparisonIndex` preserves theta0=0 below 1/2 and
every theta0>0 at 1/2, as Theorem 6.1 states. The constant and step choices use
the two L-infinity Hdot^theta0 norms in (6.3)/(6.5); they precede T when that
bound C0 is fixed. The complete literal (6.7) norm estimate is retained.

`dependence67_original_to_specialized` in RegularityBridges.lean proves the
former sufficient statement, including the lower-index essential norm comparison
`bitHomSup_mono`. `low_to_historical` uses that consequence internally. The old
specialization is not an independent final input. `dependence67_iff` is explicitly
only a norm/a.e. equivalence of that internal specialization. The separate
`dependence68_subcritical` proves the uniform exponential form (6.8) from the
restored full input, using `iteration_factor_le_exponential`.

## T4

SolutionCorrespondence.lean adds an independent `PaperSolution` convention:
continuous H^gamma path, initial trace, reality/mean, spatial-and-time tested
PDE, and smooth approximation by `PaperSmoothSolution` paths. The latter assume
the actual differentiated classical equation and do not assume Duhamel.

`classical_to_duhamel` proves variation of constants, including the initial
trace and closed endpoint. `paperSmooth_iff_historical` and
`paperApproximation_iff_historical` are checked two-way equivalences.
`approximation_determines_flow` identifies the rough limit with the exact flow
using only the original BIT inputs and the historical exact-flow dependence.
It assumes no integral equation for that limit. Its common initial-data ball
is derived from convergence, not added as a hypothesis. The independent
spatial distribution identity is proved by `kdv_to_paper_distribution`.

`paperSolution_iff_exactSolution` proves both directions for the entire paper
convention, with no extra solution hypotheses. The reverse uses its stipulated
smooth approximation; it does not assert a converse for an arbitrary weak PDE
path without that stipulated approximation. `duhamel_congr_on` and
`continuous_representatives_eq` cover representatives on the entire closed
interval, including both endpoints.

## C1 / target

`theoremOne_iff_paper` proves the complete target statements equivalent, with
the SAME constants, uniform initial-data ball, unchanged update and full grid.
`completed_paper_theorem_1` applies this checked equivalence to the unchanged
historical proof assembly. Both new exported results have the same nine
explicit literature inputs. OriginalProof.lean is not modified.

The current full build, expanded declarations, axiom inspection and source
hashes are recorded in build-status.json, SignatureInspection-build.log,
completion-verification.json and lean-source-hashes.json. All measured time and
usage remain the outside passive recorder's responsibility.
