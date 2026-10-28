# Benchmark startup

These instructions govern the invoking operator, not a measured direct-model
session. The direct supervisor disables project instructions, memories, plugins
and delegation for that isolated session.

1. Before starting either arm, run `python3 benchmark/skill_check.py` from the
   repository root, or use its actual path from another working directory.
   It must find the enabled installed skill named exactly `rigorous-proof` in
   Codex's current skill registry. A nearby checkout or
   `rigorous-proof-development` is not a substitute. Stop with the actual error
   if installation, discovery or the required runtime is unavailable.
2. Start the Yui arm by explicitly invoking `$rigorous-proof` and reading the
   installed `SKILL.md` returned by that check. Use
   `benchmark/prepare_yui.py --workers N` to prepare the concrete invocation
   after N has been confirmed. Follow that skill's own target selection,
   configuration collection and detached execution. The preparation command
   itself starts no model and is not a successful or completed benchmark.
3. After dispatch, register one actual host heartbeat every ten minutes, record
   its ID and end the foreground turn. Each scheduled check is bounded. If host
   scheduling is unavailable, disclose it and return manual observation commands.
4. The direct arm uses `benchmark/pure-model-result/runner.py`. It checks the
   installed skill and resolves only its generic native-session supervisor.
   Its measured prompt remains `prompt.py`; never add Yui proof rules, strategy
   cards, other-arm results or other proof skills to that session.
5. Never hard-code a Yui checkout location, assume the repositories are siblings,
   or fetch an arbitrary runtime when the installed skill is missing. Record the
   actual installed version, profile, inputs, execution faults and missing usage.
   Keep model construction and independent acceptance distinct.
