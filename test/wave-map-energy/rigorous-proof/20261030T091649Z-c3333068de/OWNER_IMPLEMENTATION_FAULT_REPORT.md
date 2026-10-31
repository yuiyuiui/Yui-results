# Retained implementation-fault checkpoint

Status: PAUSED_ERROR (nonterminal); interface-authoring; incident 75a4443e96ed41b78ea76eaa5e2aacff.

Frozen source: Yui V1 c284fba695a7d8cfc97c36cda49d28a1ddd70f32. No harness, rule, prompt, target or input edits were made by the invocation owner.

The actual first interface-stage relay request recorded this implementation error:

    'InterfaceStage' object has no attribute 'relay_stream_lock'

Evidence: nl0-to-lean/0001/interface/stage/relay-errors.jsonl, request_number 1. The request lifecycle records ALLOCATED, NORMALIZED and STREAM_CLOSED. The carrier then recorded RuntimeError: Non-remote relay failure; automatic remote retry is disabled. The error controller classified harness_bug, zero automatic retries, resumable=false, cleanup_authorized=false. An advertised generic resume command is not evidence that this checkpoint supports resume.

Full evidence: nl0-to-lean/0001/interface/stage/error-state.json and error-incidents/. Retain the exact live process/context and owned temporary resources. Human/developer action must verify a software repair and select a supported checkpoint; this invocation does not authorize editing its frozen runtime, rerunning the whole case, or deleting evidence. No automatic recovery was attempted.

This is an execution fault, not a mathematical rejection or a model-budget-exhaustion result. The case reached interface authoring; this report does not independently certify upstream Audit A, any Lean proof, standalone assembly, native trust or final Audit B.

The other two current runs also remain nonterminal PAUSED_ERROR: geometry (response-stream interruption, 10 retries exhausted, incident 6e1e2a5879504266a2a784a9d2e4fa5d) and Lie module (remote read timeout, 10 retries exhausted, incident bf19fe2e85ef434ca9dcd8e24627ab57). Their supported exact-incident resume controls await explicit operator action. Existing usage is partial and remains unknown for unreported responses.

One host heartbeat yui-v1-full remains active for all three exact runs. No workflow was canceled, restarted, finalized or cleaned.
