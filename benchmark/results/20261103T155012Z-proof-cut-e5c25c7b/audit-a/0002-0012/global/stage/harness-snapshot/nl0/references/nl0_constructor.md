# NL0 constructor: N/R proof-node design

Read this module when constructing or revising the N/R proof graph. Use the
supplied proof, the frozen target/H/definitions and the current candidate.
[Audit A's shared requirements](audit-a.md#shared-mathematical-acceptance-requirements)
remain the mathematical acceptance authority; the [authoring guide](nl0-authoring.md)
governs proof completion, inspection, gap reporting and submission.

## Choose coherent tasks for an LLM

Preserve the original mathematical proof route while choosing node boundaries
for an LLM working from its own conditional packet. A natural R is a complete,
understandable local proof task with a clear goal, sufficient direct inputs
and manageable context. Naturalness here concerns the LLM's ability to
understand and carry out the task. Human exposition and the source's paragraph,
lemma or section boundaries do not determine the partition. Regroup the supplied
arguments or expose intermediate conclusions when that makes better local tasks,
without dropping or changing the original mathematical reasoning.

Within that constraint, partition as finely as useful. Look for meaningful
intermediate conclusions that let a fresh LLM complete each part from its
packet. Keep a coherent calculation together when further cuts would create
nearly empty tasks or require reconstructing the same local argument repeatedly.
Every cut must have a complete exported proposition and preserve object scopes,
witness dependencies and definition guards. During a located repair, respect
its allowed scope rather than repartitioning unaffected proof content.

## Design outputs from their consumers

Work backward from P: what exact formulas, maps, parameter ranges and
representation identifications will each consumer actually use? Put those in
its input proposition's exported statement. Read that statement without the
producer body. If the consumer cannot reconstruct a needed fact from it,
enlarge the producer's proved output or give the consumer another genuine
direct input. Then write the producer under precisely its inputs. This
implements `statement_closure`, the grouped argument and applicability criteria;
it is not permission to invent a stronger theorem.

## Balance expected work by qualitative judgment

Compare the proposed R nodes as LLM proof tasks and aim for roughly comparable
workloads. Judge the effort to understand the packet, complete the argument and
check its conditions. Consider mathematical difficulty, distinct proof mechanisms,
auxiliary lemmas, missing derivations or source work, branches and local scopes,
representation/normalization changes, and the amount of context to reconcile.
Paragraph length and counts of S/F nodes alone do not measure that effort.

Split an obviously heavier bundle at meaningful intermediate conclusions;
combine fragments that are too small to form useful complete tasks. Prefer the
finest partition that keeps tasks coherent and approximately balanced. Preserve
a larger node when its argument cannot be separated cleanly; do not add filler,
weaken outputs or hide dependencies to equalize apparent size. Exact equality
of workload is not required.

Use the LLM's judgment for this first policy. No numerical score, fixed node
count, time prediction or balancing algorithm is prescribed. Revisit the proposed
partition as proof construction exposes its actual work. Briefly explain the
main partition choices and any unavoidable workload outlier in the existing
`original_context_note`, so later execution results can inform revisions of this
policy. These estimates do not certify mathematical correctness or predict
equal Lean runtimes; nl02lean selects its own T obligations.

## Complete omitted steps and organize local arguments

When filling an omitted step that uses a nontrivial property unavailable in
the pinned Mathlib, first try to find a suitable external theorem, including
in classical textbooks or sources outside the supplied bibliography. Verify
and register a suitable source under [external-source review](external-theorems.md).
If no suitable external theorem is found, try to prove the property from the
permitted inputs while preserving the original proof route. If completion
still fails, follow [routine completion and substantive proof gaps](nl0-authoring.md#routine-completion-and-substantive-proof-gaps).

Start another S when the local parameters or purpose change; export a reused
result as N and a within-R result as a complete F. Avoid one giant copied S
followed by a long sequence of isolated symbol patches. Copy exact supplied
calculations through task-line text binding when helpful, then close the
copied unit's actual declarations and premises. Keep all required coefficients,
normalizations, limiting arguments and exceptional cases.
Retain every calculation needed for P and the supplied core route. An
independent optional comment/corollary outside that dependency may be omitted;
note a material omission in the existing context note. This never licenses
dropping a needed derivation or weakening an output. Any retained claim must
itself have its complete grounds.
