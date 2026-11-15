# Theorem 1.2: critical annular estimate

This case records Yui's completed unconditional Lean formalization of the
critical annular estimate in Theorem 1.2 of *Local smoothing for the Euclidean
wave equation* (manuscript dated October 25, 2026).

The complete proof and published acceptance records are maintained in the
[public formalization repository](https://github.com/yuiyuiui/critical-annular-estimate-lean).
This catalogue entry points to that published project rather than copying its
proof and evidence.

## Recorded result

| Item | Result |
| --- | --- |
| Completion date | November 13, 2026 |
| Formalized target | Theorem 1.2, the critical annular estimate, with the source hypotheses, normalizations and uniform constants preserved |
| Workflow result | `WORKFLOW-PASSED / UNCONDITIONAL_LEAN` |
| Checked export | `YuiClosed.P` |
| Remaining foundation premises / class-4 assumptions | None |
| Source qualifications | None |
| Prepared foundations | 21: 14 class 1, 6 class 2 and 1 class 3 |
| Local Lean obligations | 69 checked proofs |
| Recorded toolchain | Lean 4.32.2; Mathlib commit `905b95818eb32af7874a58b427f50c1711a5e96c` |

The checked statement is uniform in the frequency parameter and retains the
original mathematical hypotheses. The original and Lean statements are paired in
[the statement record](https://github.com/yuiyuiui/critical-annular-estimate-lean/blob/main/theorem_formalization_statement.json);
the definitions are in the complete Lean source linked below.
The scope recorded here is the critical annular estimate itself.

## Proof and evidence

The public proof entry is `formalization/Solution.lean`. Its final declaration
is `YuiClosed.P`; the public `run.json` records the delivered unconditional scope.

| Record | What it contains |
| --- | --- |
| [Complete Lean proof](https://github.com/yuiyuiui/critical-annular-estimate-lean/blob/main/formalization/Solution.lean#L80026) | The complete source and final declaration `YuiClosed.P` |
| [Delivery record](https://github.com/yuiyuiui/critical-annular-estimate-lean/blob/main/run.json) | Unconditional scope, Audit A/B status and remaining-premise inventory |
| [Mechanical acceptance](https://github.com/yuiyuiui/critical-annular-estimate-lean/blob/main/nl0/lean-evidence/mechanical.json) | Retained mechanical checking evidence |
| [Foundation discharge](https://github.com/yuiyuiui/critical-annular-estimate-lean/blob/main/nl0/lean-evidence/discharge.json) | Retained final dependency-discharge evidence |
| [Reviewed natural-language proof](https://github.com/yuiyuiui/critical-annular-estimate-lean/blob/main/nl0/nl0.json) | The accepted NL0 proof graph |
| [Foundation inventory](https://github.com/yuiyuiui/critical-annular-estimate-lean/blob/main/nl0/inputs/basis-registry.json) | The 21 prepared foundations |
| [Source references](https://github.com/yuiyuiui/critical-annular-estimate-lean/blob/main/nl0/references.json) | Foundation declarations and source revisions |
| [Build instructions](https://github.com/yuiyuiui/critical-annular-estimate-lean#build) | Commands for building the published Lean project |

The accepted chain includes the prepared foundations, Audit A, an independent
semantic interface review, the local Lean proofs, assembly, Audit B and final
foundation discharge. Final Audit B used the independently reviewed frozen
interfaces and native integrity checks; it did not call another final semantic
model. The inspected transitive axiom list is exactly `propext`,
`Classical.choice` and `Quot.sound`.

The proof imports Mathlib and
`OAI.Analysis.Fourier.WavePackets.ThreeSlotFamilyTheorem`. Reproduction therefore
uses the compatible OAI sources retained by the project as well as its recorded
Lean/Mathlib pair. These versions describe this completed case.

The result was completed through repair and continuation, reusing bound,
previously accepted work. This page records the completed formalization and its
published acceptance evidence; it does not report a new execution or a clean-run
timing benchmark.
