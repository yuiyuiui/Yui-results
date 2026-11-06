# Geometry product-dimension run: dependency universes, blocked repair, and cancelled-run finalization

This run was cancelled by the user after an internal Lean interface repair reported `INPUT_CONFLICT`. Audit A has a valid retained standard receipt. The requested unconditional full workflow did not complete: there is no final Audit B acceptance or b2lean closure. All owned processes exited, and authorized cleanup returned `CLEANED`.

The retained evidence supports three separate engineering findings:

1. Internal dependency propositions were copied into consumer telescopes with separately elaborated `Type*` occurrences. Several actual applications failed because their ambient or index universes were unrelated rigid levels.
2. The subsequent repair required declaration universe binding and dependency specialization, while its contract allowed only step edits and preserved the entire header. A trial step field was saved but had no effect on generated Lean. The repair author reported a contract conflict after failed native checks.
3. After cancellation, the observation correctly reported a terminal result, no active incidents and verified process exit, but also retained a historical `counts.PAUSED_ERROR=1`. The entry's `terminal_ready` predicate rejected that count, preventing standard final-report generation. Cleanup nevertheless succeeded.

This is a retrospective engineering record. It contains no new proof certification, model execution, Lean compilation, software fix, resumed experiment, or public issue submission. Proposed fixes below remain proposals. All original records, frozen inputs, runtime files, and judgments remain unchanged.

## 1. Reading map and evidence authority

Start here, then use the generated appendices for exact details:

| Artifact | Purpose |
| --- | --- |
| [EVIDENCE.json](EVIDENCE.json) | Bound configuration, observed states, 89 specifically used source-file hashes, terminal reproduction, usage and final scope |
| [STAGE_TIMELINE.md](STAGE_TIMELINE.md) | All 30 recorded stage intervals in Asia/Shanghai time, with links to the actual result files |
| [STAGE_TIMELINE.json](STAGE_TIMELINE.json) | Machine-readable stage statuses, scope, identity, usage, timing and health |
| [EVIDENCE_APPENDIX.md](EVIDENCE_APPENDIX.md) | Full diagnostics for T002/T003/T005/T008, actual failed compiler results, repair calls, candidate edits, initial semantic review, and relevant frozen code |
| [REPAIR_TOOL_CALLS.json](REPAIR_TOOL_CALLS.json) | Fifteen selected repair-stage calls with exact arguments and responses, including rejected probes |
| [TERMINAL_PREDICATE_REPRODUCTION.json](TERMINAL_PREDICATE_REPRODUCTION.json) | Pure Python reproduction of the cancelled-run reporting defect |
| [collect_evidence.py](collect_evidence.py) | Read-only evidence extraction; writes only this analysis directory, with no model or Lean calls |
| [OWNER_FINAL_REPORT.json](../OWNER_FINAL_REPORT.json) | Original owner closeout, including the standard finish limitation |
| [case-result.json](../workflow/case-result.json) | Runtime's bound `CANCELLED / EXTERNAL_CANCELLED` result |
| [CLEANUP.json](../CLEANUP.json) | Cleanup result and absence of residual owned processes |

Original scientific and runtime records are primary evidence for what this attempt did. Worker diagnoses are retained attributed judgments, not independently established universal impossibility claims. Source-code inspection supports the narrower mechanical explanations below. File hashes identify concrete records and executable versions; they do not certify mathematics.

The collector reads explicitly relevant artifacts and the stage ledger's own file list. It does not incorporate a conditional sibling run, an older proof, or another case's construction. The 89-file manifest is limited to sources actually used in generating the record; it is not an inventory of the whole repository.

## 2. Exact attempt and configuration

| Field | Recorded value |
| --- | --- |
| Case | `geometry-product-dimension` |
| Run ID | `20261105T120350Z-de9cce1dea` |
| Owning chat | `01a1ab95-1773-7c10-8084-20fee65637f3` |
| Entry | `/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/README.md` |
| Run root | `/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261105T120350Z-de9cce1dea` |
| Registered installation | `/Users/syyui/projects/Yui` |
| Goal / track / policy | `unconditional / full / normal` |
| Both phase profiles | `gpt-6.1-sol / high / standard`, no automatic fallback |
| Total time / token / model-call budget | Unlimited in this attempt |
| Native check limit | 180 seconds per configured native call |
| Audit A local concurrency | `auto`, resolved to 8 R nodes |
| Lean local concurrency | `auto`, resolved to 10 T nodes |
| Monitoring | `OWNER_CHAT_WAIT`, ten-minute observations; no automation ID |
| Controller at launch | PID 24534, PGID 24534, recorded start 2026-11-05 20:04:30 Asia/Shanghai |
| Final outcome | `CANCELLED / EXTERNAL_CANCELLED` |

The selected theorem is the Hausdorff-dimension equality for a nonempty compact set `E ⊆ ℝⁿ`, every natural `n` including zero, and `[0,1]`, with the Euclidean metric and any product-norm change justified. Nonemptiness is an explicit approved addition to the printed exercise. The target was read from this run's source and extracted target, rather than imported from historical target-selection files.

The public Lean representation uses `Rn n := EuclideanSpace ℝ (Fin n)`, ordinary product `F n E`, a `WithLp 2` lift, and a coordinate concatenation map into `Rn (n+1)`. The accepted plan includes a separate metric bridge. These choices matter because generic metric-space lemmas must ultimately apply to a concrete universe-zero Euclidean type.

Concrete bindings from [TEST_RUN.json](../TEST_RUN.json):

```text
original problem SHA256:
56242fc597019e658c0e8792098ddb686d913156e0d831a14366d114cbf743f0
selected target SHA256:
02362a5ab49d1bd8f6e482c8aa146f58375107f6938f8d8a8fb825eafe3c809e
job SHA256:
f6cd1793fed26160269cbb114826ca687eae025ff6852bbc4da3ad4bce4eb02f
frozen runtime SHA256:
5caceaf00d753b4ccf3465e05e047733ffce0b18cbf04745ede2561e76f26fb8
```

Lean is pinned to 4.32.2 and Mathlib to `905b95818eb32af7874a58b427f50c1711a5e96c`. At retrospective inspection the current Yui checkout's HEAD was `dfa7fc68ac877ac3d79db54f06b3d1b740850336`, with no tracked changes before this documentation work. That retrospective HEAD is not substituted for the run's own frozen runtime binding. Diagnosis uses the preserved runtime code.

The initial entry-support check reported 44 tests, 10 skipped. The skips included installation-gated tests; this was not a claim that every optional installed-runtime test ran. `run_test.py check` reported the registered installation verified and unconditional capability present. No model was started by those checks.

## 3. Chronology and stage boundaries

All times below are on 2026-11-05 in Asia/Shanghai, UTC+08:00. The JSON files preserve original UTC values. Use [the full stage timeline](STAGE_TIMELINE.md) for exact timestamps; intervals overlap and must not be added as case wall time.

| Time | Event and interpretation |
| --- | --- |
| 20:03:49 | Entry measurement begins; source review is recorded before preparation |
| 20:04:30 | Detached controller launch; PID/start/PGID subsequently verified |
| 20:04:31–20:11:06 | 2basis author stage accepted at its stage scope |
| 20:11:06–20:15:48 | Separate basis statement/use review stage accepted |
| 20:15:48–20:39:40 | NL0 author stage accepted; this alone is structural, not Audit A |
| 20:39:41–20:44:34 | Global Audit A stage accepted |
| 20:44:42–20:48:03 | Eight local Audit A review stages complete |
| 20:48:16–20:49:30 | Lean preparation stage completes |
| 20:49:32–20:55:51 | First interface author stage accepted |
| 20:55:51–21:03:36 | Independent interface semantic review records PASS |
| 21:03:45 | Ten local proof-node workers start |
| 21:04–21:13 | T002/T003/T005/T008 request and receive independent internal-interface diagnoses; six other local workers submit accepted bodies |
| 21:13:21 | Second interface author stage begins under internal-repair protection |
| 21:22:15 | Repair author reports `INPUT_CONFLICT`; controller retains incident `2119ae9942c54eb1801d797515ff6c3a`, nonresumable |
| 21:22:15 | Local alert queued successfully to the owning chat; notification receipt has exit code 0 |
| Owner's next interval | Owner observes the pause, reads the obstacle and actual diagnostic, and requests the user's disposition |
| After explicit user choice | Entry cancellation issued; no implicit conditional fallback or restart |
| Approximately 21:39:39 | Case reaches cancellation after 5708.10 seconds from workflow start |
| By 21:40:51 | Observation confirms terminal record, no pending incident, zero owned processes and no registered owned groups |
| 21:40–21:41 | `finish` fails, cleanup succeeds, `finish` fails again; fallback owner report saved |
| 21:41:36 | Owner closeout records completed cancellation/cleanup/reporting, with mathematical workflow incomplete |

The paused interval remains part of case elapsed time. Neither the time spent awaiting a decision nor retained processes imply continued model reasoning. The normal cancellation was externally requested; it was not a configured deadline expiry.

## 4. Finding F1: dependency universes were not connected to consumer universes

### Observed symptoms

Four separately reviewed local diagnoses select `INTERNAL_INTERFACE_REPAIR`: T002, T003, T005 and T008. Their complete source comparisons and actual compiler evidence are in [the appendix](EVIDENCE_APPENDIX.md), extracted from [repair-diagnostics.json](../workflow/nl0-to-lean/0002/interface/inputs/repair-diagnostics.json) and each review's `own-attempts.json`.

| Consumer | Intended application | Recorded elaborated mismatch |
| --- | --- | --- |
| T002 | Apply T001's zero-measure/cheap-cover package to the target's metric space, then reindex a countable family of finite fibers | Input ambient `Type u_1`, input index `Type u_2`, target ambient `Type u_3`; finite-fiber index needs its actual small-universe instance |
| T003 | Apply T002 to the same `X`, and T001 to `X × ℝ` | T001 ambient `u_1`, T002 ambient `u_3`, target ambient `u_4` |
| T005 | Combine T001's infimum/supremum facts and T004's arbitrary-cover estimate on the same `X` | T001 ambient `u_1`, T004 ambient `u_3`, target ambient `u_4` |
| T008 | Apply T005 to `BasisObjects.Rn n` in the midpoint lower-bound argument | Local `h_T005` expects `Type u_1`, but `Rn n` is in `Type 0` |

The diagnoses explicitly distinguish these mismatches from proof-body problems. For example, T002 also had a failed tail involving `False.elim` and a sigma-sum rewrite issue. Those are additional local candidate defects, not the basis for claiming the source theorem false. The diagnosis points to the pinned `tsum_sigma`/`tsum_sigma'` distinction for the latter without certifying the whole proof.

### Mechanism supported by frozen source inspection

The frozen [ir.py](../workflow/runtime/nl02lean/scripts/ir.py) does the following:

1. `local_packet` copies a producer's `statement` text into a consumer input as its type.
2. `render` independently constructs `(h_Tddd : <producer statement>)` for each listed dependency and emits the consumer statement after `:`.
3. Producer and consumer statements contain fresh `Type*` occurrences. The renderer supplies no per-step declaration-universe parameters or per-edge universe instantiation in this path.
4. Actual compiler errors printed the distinct levels and rejected the intended applications.

The conceptual distinction is between a universe-polymorphic theorem constant and a local hypothesis whose type already contains a particular declaration universe. Copying a polymorphic-looking proposition into a binder does not give that local hypothesis the same instantiation capabilities as the original global declaration. In particular, writing `h_T005.{0}` inside a worker is not an implementation of declaration-level specialization for a local hypothesis.

This explanation is confined to the saved generated declarations and uses. Failed applications do not establish that every imaginable proof body is impossible, that the mathematical proposition is false, or that no representation-preserving repair exists.

### Why this escaped the initial gates

The first interface's successful native strict declaration check established that the generated propositions were well formed. A proposition containing a fixed-universe dependency and a separately quantified target can itself elaborate successfully. That check did not exercise the intended producer-to-consumer applications.

The independent semantic review explicitly recorded `parameters_and_allowed_inputs: PASS` and `statements_and_local_plans: PASS`. It stated that it compared the entire conditional declarations and saw the correct arbitrary metric spaces, source coverage and public parameters. It also correctly limited its scope: no accepted local bodies or assembled kernel closure followed from that review. The later failures reveal a missed connection issue within that reviewed internal plan. They do not erase the review or justify relabeling it after the fact.

The missing discriminating check was whether an allowed dependency, as actually elaborated in that consumer telescope, provides the intended instance at the consumer's ambient and index universes. Comparing statement text or separately successful signatures did not establish that fact here.

### Impact

The defect affected four consumers directly and put their downstream uses at risk. Six local bodies were accepted under the original interface, but no assembled proof or final closure was delivered. The highest-cost affected worker was T002: about 565.10 recorded stage seconds, 13 recorded Lean calls and 1,916,317 observed tokens, followed by a separate diagnosis costing 313,914 observed tokens. These are attempt-specific figures, not a predicted saving from a proposed fix.

## 5. Finding F2: the authorized repair could not express the requested declaration setup

### The actual contract

The second interface stage was a disclosed internal T-plan revision. The frozen prompt says:

> Only steps may change. Preserve all other prior-interface fields, including H/E/P, public header, source output map and pins.

This is enforced, not merely suggested. [internal_interface_repair.py](../workflow/runtime/nl02lean/scripts/internal_interface_repair.py) compares all fields other than `steps` with the previous interface. Its protected contract fields include `header`, `parameters`, `premises`, `conclusion`, pins and representations. This protection is valuable: an internal implementation repair must not silently change the source target or assumptions.

The documented step schema lists `id`, `statement`, `inputs`, `source_steps`, and `explanation`; `inputs` are root/T identifiers. The preserved header contains no `universe u v` command. The diagnosed remedy needs both shared ambient universes and explicit instances at lower-universe uses.

### Exact repair attempts and feedback

The repair stage lasted approximately 529.03 recorded stage seconds and used 1,060,476 observed tokens. It did not submit an accepted revised interface. The retained call sequence includes:

1. A small `Type u` probe with no declaration of `u` fails with `unknown universe level u`.
2. A draft with no explicit edits is rejected: `Supply a nonempty list of explicit edits`.
3. Candidate 1 adds `/steps/0/universe_params = ["u", "v"]` and edits statements. Saving the draft records data and is explicitly not semantic acceptance.
4. Full candidate 2 retains this trial field and submits explicit `Type u` / `Type v` statements. The actual strict check rejects undeclared universe levels. [Generated Check.lean](../workflow/nl0-to-lean/0002/interface/candidates/0002/types/Check.lean) and [result.json](../workflow/nl0-to-lean/0002/interface/candidates/0002/types/result.json) are preserved.
5. Further expression-level probes try to recover a type from a local hypothesis. They fail with parser/sort/type mismatches. Their exact inputs and outputs are retained; they are not treated as validated alternative solutions.
6. Candidate 3 removes the unsupported `universe_params` field and records the unresolved setup problem in its explanation. It is a saved incomplete draft, with no check or semantic acceptance claimed.
7. `report_obstacle` records `INPUT_CONFLICT`, explicitly describing the issue as scope/configuration rather than a false mathematical implication.

The author also rejected restricting all generic metric-space outputs to `Type 0`, because that would narrow the accepted general N001/N002/N003 statements. A universe-zero instance at a concrete consumer edge and global restriction of the producer's mathematical domain are distinct changes; a future design must preserve that distinction.

### Confirmed implementation gap and remaining uncertainty

The frozen validator permits unrecognized keys inside a step object in this path, but the renderer does not consume the trial `universe_params` field. Thus the field could survive saving and inspection while having no effect on generated declarations. The actual failed candidate confirms that it did not bind `u` or `v`.

What is confirmed: the attempted schema extension did not work; the authorized repair remained unsubmitted; the prompt and protection checks prohibited header edits; actual checks rejected explicit undeclared levels.

What remains unverified: whether another clever term encoding could have worked inside the existing allowed schema, whether a proposed new schema will be sufficient across all downstream consumers, and whether a repaired interface would allow this full theorem to finish. The worker's report of inability is not a proof that every possible in-scope construction fails.

### Why widening the header permission alone is insufficient as a design conclusion

Adding a `universe` declaration may address undeclared names, but a complete fix also needs dependency instance selection, the small countable finite-fiber index, the Euclidean universe-zero handoff, actual generated types and final assembly. Permitting arbitrary header edits would also widen the public-change boundary. A reviewed, explicit internal declaration environment is a candidate direction; it has not been implemented or validated here.

## 6. Finding F3: cancelled-run finalization rejected historical pause counts

### Actual post-cancellation state

The runtime's bound case result records `CANCELLED / EXTERNAL_CANCELLED`, with `acceptance_target_satisfied=false`. The final owner observation records:

```json
{
  "all_terminal": true,
  "all_process_exits_verified": true,
  "process_inspection_error": null,
  "terminal_record_present": true,
  "paused_errors": [],
  "live_owned_process_count": 0,
  "registered_groups_still_present": [],
  "counts.PAUSED_ERROR": 1
}
```

The stale `phase=INTERFACE_AUTHORING`, historical waiting/repair counts and old paused task record remained in `execution-status.json`. They were not active proof workers after cancellation. The observation's `controller_identity_matches=false` at this point is consistent with the registered controller having exited; it is not evidence of a live foreign controller, and it must be read together with the verified process/group results.

### Two incompatible terminal interpretations

The frozen `owner_observation.snapshot` derives terminal availability from an actual result plus absence of pending incidents, and independently verifies process exit using registered PID/start/PGID evidence and the OS process table. It separately copies `counts` from `execution-status.json`.

The entry's frozen [common.py](../preparation/startup/entry_support/common.py) `terminal_ready` additionally requires:

```python
not (case.get('counts') or {}).get('PAUSED_ERROR')
```

For this record that extra condition is false. The entry's `finish` therefore raises `Workflow is live, paused or its process exit is unverified` even though none of those descriptions matches the current terminal/process fields. The generic error text hides which boolean failed.

`finish` was attempted before cleanup and again after successful cleanup, with the same failure. The original owner report records both attempts; their command responses were visible in the owning chat. This retrospective does not invent new archived stdout for those historical attempts.

### Read-only reproduction

[TERMINAL_PREDICATE_REPRODUCTION.json](TERMINAL_PREDICATE_REPRODUCTION.json) evaluates the trusted frozen entry function against the saved final observation:

- Actual observation: `terminal_ready == false`.
- In-memory copy changing only `counts.PAUSED_ERROR` from 1 to 0: `terminal_ready == true`.
- No saved observation, status, incident, runtime or source file is changed.

This isolates the rejecting boolean for this case. It does not authorize overriding a live pause, ignoring process ownership, accepting an unbound terminal result, or deleting historical errors.

### Cleanup and reporting consequence

The entry's cleanup path uses the terminal artifact validator and owned-resource cleanup rather than the same `terminal_ready` predicate. It accepted this cancelled case and returned `CLEANED`, no residual owned processes, no stopped processes and no paths removed by that entry cleanup pass. An empty removal list is not a count of all earlier runtime cleanup actions.

The owner separately validated available retained gates: Audit A's standard receipt remains valid, with no source warnings or unresolved reviews; Audit B and basis closure are unavailable. The owner wrote `OWNER_FINAL_REPORT.json` and its Chinese companion. Standard `FINAL_OUTCOME.json` and `FINAL_REPORT.zh.md` were not generated. Owner monitoring is `COMPLETED` only for the authorized cancellation/exit/cleanup/reporting work, with the mathematical workflow explicitly incomplete.

## 7. Observability and tool-contract findings

### O1: task activity was mistaken for a proof-node denominator

The actual frozen plan has ten proof nodes, T001 through T010; the proof concurrency ledger resolves `auto` to ten. During execution, an owner update described thirteen nodes from the observed combination of active and locally checked task counts. That interpretation was incorrect: the task/status projection can include diagnosis activity in addition to proof-node records. The final owner observations also retained six locally checked tasks and four repair-wait tasks while showing additional review states.

Correct statement for this attempt: six of the ten original proof workers recorded accepted local bodies (T001, T004, T006, T007, T009, T010); four requested internal repair (T002, T003, T005, T008). These local results remain conditional on their exact original packets, and six accepted bodies do not constitute an assembled proof.

A future status schema should distinguish proof-node counts, currently active role calls, diagnosis calls, historical task states and current unresolved incidents. An explicit `proof_total=10` should be derived from the frozen plan, rather than inferred by summing role counts.

### O2: recoverable API friction added noise to repair

The exact tool log records rejected calls for an undeclared instruction path, `offset=null`, excessive string pagination limits, an empty edit list, and a forbidden assignment-like expression in a type probe. These are ordinary rejected candidate/tool requests, not provider failures and not proof acceptance. They should be retained as potential instruction/schema usability cases, with lower priority than the universe contract mismatch.

The draft save API's permissive extra step fields deserves specific attention: persisting an unsupported executable-looking key can imply capabilities that the renderer does not have. Either reject unknown step fields with located feedback or explicitly distinguish inert annotations from fields that affect emission. Do not silently implement an unreviewed field solely because a model supplied it.

### O3: fault labels did not identify the actionable layer

The controller retains `workflow_blocked` with `INPUT_CONFLICT`, no automatic retries, and `resumable=false`. It reports the generic absence of a qualified submitted artifact. The detailed reason is in the repair author's obstacle. A more direct owner-facing diagnostic could include a structured reason such as an unsupported internal declaration-universe requirement, alongside the evidence path, immutable fields, permitted changes and valid next actions.

The 30 ledger-listed stage results all record `NO_RECORDED_FAULT` within the native error/stdio observation boundary. That does not establish a flawless harness: the engineering findings above remain. It means this incident should not be attributed to a recorded HTTP outage or quota event. The local blocker is not a provider transport fault, and an externally cancelled unlimited attempt is not `MODEL_BUDGET_EXHAUSTED`.

## 8. Cost, execution health and evidence limits

| Quantity | Value and limit |
| --- | --- |
| Case elapsed to cancellation | 5708.097866791002 seconds, about 1:35:08; includes pause/decision waiting |
| Confirmed observed input | 17,963,226 tokens |
| Confirmed observed output | 171,006 tokens |
| Observed total | 18,134,232 tokens |
| Cached input subset | 16,286,848 tokens; already included in input |
| Reasoning subset | 50,132 tokens; already included in output |
| Usage coverage | `PARTIAL`; provider-response/request coverage remains unknown |
| Ledger reconciliation | `MATCHED`, 30 stage usage files, no missing listed ledgers |
| Recorded stage Lean-call counters | Sum 82; a recorded instrumentation count, not a separately audited count of unique compiler processes |
| Actual backend tier | Not exposed/verified by retained native records; requested tier is Standard |
| Model substitutions | None recorded; selected profiles are fixed with no automatic fallback |
| Original acceptance | Unconditional goal unmet; Audit B and b2lean unavailable |

Do not add stage walls to estimate total elapsed time: concurrent workers and diagnoses overlap. Do not infer that all recorded time was productive reasoning. Do not interpret a matched stage ledger as complete per-provider-response usage coverage. Owner analysis and this retrospective are outside the worker usage total.

## 9. Proposed improvements, owners and acceptance conditions

These are an engineering backlog for later work, not changes made to this attempt. Scope and priority describe the demonstrated failure, without claiming a completed fix.

| ID | Priority / owning component | Proposed change | Required acceptance evidence |
| --- | --- | --- | --- |
| F1-a | High: IR schema/emitter | Represent declaration-level universes and dependency instance selection explicitly, with one validated meaning across packet generation, checks and assembly | Actual producer/consumer applications compile with generic ambient spaces, an independent countable index universe and required concrete instances |
| F1-b | High: preprocessing checks | Add bounded checks of intended dependency uses at their actual consumer types; retain printed elaborated signatures | The original mismatch fails before worker dispatch; valid differently named or intentionally independent universes are not rejected merely by string comparison |
| F1-c | High: semantic interface review | Make dependency instantiation part of allowed-input review, including universe-zero specialization and index types | Review identifies the actual unavailable source use in the generated telescope; separate type well-formedness remains explicitly scoped |
| F2-a | High: internal repair authority | Provide a reviewed internal declaration setup that can express repairs while protecting public H/E/P, definitions, pins and source outputs | The needed internal universe repair is expressible; protected mathematical changes are still rejected; affected-consumer delta review runs |
| F2-b | Medium: schema validation | Reject unsupported emission-affecting step keys, or document them as inert annotations | `universe_params` cannot silently save as if it configured emission when unsupported; feedback names its exact JSON pointer |
| F2-c | Medium: retained repair protocol | Distinguish an internal capability mismatch from protected public-contract drift and unsupported resume | Owner receives a concrete reason, evidence path and supported disposition, without automatic restart or scope weakening |
| F3-a | High: entry terminal predicate | Define current terminal authority consistently across observation, finish and cleanup | Cancelled result plus no pending incidents and verified exit can finalize while historical errors remain visible; real active pauses still block |
| F3-b | High: cancellation status projection | Mark or namespace historical task counts after cancellation, preserving append-only fault history | Terminal observation cannot present historical pause counts as active execution; historical failed state remains inspectable |
| F3-c | Medium: finalization diagnostics | Report the failed predicate rather than a generic live/paused/exit message | This exact fixture identifies the stale count; ownership, active incident and exit failures each produce their own reason |
| O1 | Medium: status/UI | Separate proof nodes from review/diagnosis roles and history | Ten-node plan always reports denominator ten, including concurrent diagnostic stages |
| O2 | Low: tool feedback | Improve small string-read and draft-edit examples in the frozen tool contract | Valid bounded reads and explicit patches work; malformed reads get actionable bounded feedback |

### Suggested regression fixtures

1. Generic producer and consumer with the same ambient universe: check the actual local hypothesis application, not just both proposition declarations.
2. A producer with separate ambient and countable-index universes: specialize the index to `Σ i : ℕ, Fin (N i)` without narrowing the full producer result.
3. Consumer uses at both `X` and `X × ℝ`: confirm the emitted applications and dependency instances.
4. Generic measure inequality consumed at `EuclideanSpace ℝ (Fin n)` in universe zero; include `n=0`.
5. A producer with multiple required universe instances in one consumer: ensure instance selection is explicit and preserved by assembly.
6. Negative fixture: intentionally unrelated rigid universes that typecheck as a proposition but cannot support the recorded direct source application.
7. Full type-print inspection around the fixtures, with no reliance on the spelling of generated `u_1` names.
8. Internal repair changes only approved internal universe/setup data and steps; original H/E/P, metric definitions and source targets remain bound.
9. Negative repair fixtures for a changed premise, weakened target, representation drift, additional class-4 dependency and altered public definition.
10. Unsupported step keys rejected before a saved field can be mistaken for a compiler option.
11. Valid terminal cancellation with historical `PAUSED_ERROR=1`, no active incident and verified owned exit: final report succeeds and retains the historical fault.
12. Same fixture with one live owned process or surviving owned process group: finish/cleanup both refuse premature completion.
13. Same fixture with a real unresolved incident, missing bound terminal result or changed job hash: finalization remains blocked.
14. Successful and conditional terminal deliveries still require their actual bound Audit A/B/b2lean scope; cancellation handling must not bypass acceptance gates.
15. Repeated finalization/cleanup preserves existing reports and evidence; no overwrite, duplicate model launch, sibling deletion or shared-toolchain removal.
16. Status fixture with ten proof nodes and four diagnosis roles reports ten proof nodes and separate role activity, rather than fourteen proof nodes.

Implement these in the owning Yui/entry-support test suites using neutral synthetic fixtures where possible. The retained theorem run is a regression source, not permission to replay a costly experiment. A future full theorem replay requires its own authorization and must create a new run with its own bindings.

## 10. Safe reproduction and use of this record

From this incident directory, the following regenerates the appendices and evaluates only the saved terminal predicate:

```sh
python3 -B collect_evidence.py
```

The script does not execute worker-provided shell/Python, call a model, invoke Lean, mutate original evidence, resume a controller or change the cancelled run. It reads the trusted preserved entry module only to call its pure `terminal_ready` function.

For the universe failure, first inspect the saved generated Lean, exact stdout, original plan and all four independent diagnoses. Minimal test construction belongs in a separate software-development work area. Do not modify the retained `workflow/runtime`, candidate files, original header, accepted reviews or diagnostic evidence to make this historical attempt pass.

Before any later live recovery, inspect the current installed runtime and documented recovery capabilities. This run was nonresumable and then explicitly cancelled; no live continuation is implied by a later software fix. Do not issue `resume-error`, reuse old acceptance for a changed interface, silently downgrade to conditional closure, or restart this experiment based on this report.

## 11. Validation performed for this documentation

The evidence collector ran successfully: 30 retained stages, 89 specifically used source files, 15 selected repair calls. It reproduced `terminal_ready=false` on the actual saved terminal observation and `true` on an in-memory copy with only the historical pause count cleared. It wrote no original source, proof, lifecycle or runtime record.

The report preserves several material uncertainties: no new Lean reproduction of the universe issue, no implemented repair, no new independent review of mathematical correctness, no proof that the permitted schema admits no workaround, no complete provider usage coverage and no attribution of this cancelled attempt to exhausted model capability.

The original issue is therefore recorded as an incomplete unconditional workflow with a located internal dependency/repair-contract obstruction, followed by user cancellation and a separately reproduced finalization defect. These scopes should remain separate in future fixes, benchmark summaries and release notes.
