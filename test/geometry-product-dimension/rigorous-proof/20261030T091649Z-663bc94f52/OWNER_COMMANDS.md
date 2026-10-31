# Yui V1 three-case FULL rerun — owner commands

Source commit: c284fba695a7d8cfc97c36cda49d28a1ddd70f32.
Host heartbeat: yui-v1-full; every ten minutes in this chat.

All three cases are pending mathematical acceptance. N=5 per case, case concurrency=3; both profiles gpt-6.1-sol/high/Standard, fallback disabled; no imposed case/stage/token/call/continuation quota, native Lean call limit 300 seconds.

## Exact run map

- geometry-product-dimension: /Users/syyui/projects/Yui-results/test/geometry-product-dimension/rigorous-proof/20261030T091649Z-663bc94f52
- lie-module-irreducibility: /Users/syyui/projects/Yui-results/test/lie-module-irreducibility/rigorous-proof/20261030T091649Z-5082f9d71c
- wave-map-energy: /Users/syyui/projects/Yui-results/test/wave-map-energy/rigorous-proof/20261030T091649Z-c3333068de

## One bounded read-only observation

```sh
python3 -B /Users/syyui/projects/Yui-results/test/geometry-product-dimension/rigorous-proof/20261030T091649Z-663bc94f52/runtime/nl0/scripts/yui.py observe /Users/syyui/projects/Yui-results/test/geometry-product-dimension/rigorous-proof/20261030T091649Z-663bc94f52 /Users/syyui/projects/Yui-results/test/lie-module-irreducibility/rigorous-proof/20261030T091649Z-5082f9d71c /Users/syyui/projects/Yui-results/test/wave-map-energy/rigorous-proof/20261030T091649Z-c3333068de
```

## Explicit cancellation of all three cases

```sh
python3 -B /Users/syyui/projects/Yui-results/test/geometry-product-dimension/rigorous-proof/20261030T091649Z-663bc94f52/runtime/nl0/scripts/yui.py cancel /Users/syyui/projects/Yui-results/test/geometry-product-dimension/rigorous-proof/20261030T091649Z-663bc94f52 /Users/syyui/projects/Yui-results/test/lie-module-irreducibility/rigorous-proof/20261030T091649Z-5082f9d71c /Users/syyui/projects/Yui-results/test/wave-map-energy/rigorous-proof/20261030T091649Z-c3333068de
```

For one-case cancellation, pass only its exact run. A main-chat Stop is not a verified cancellation of owned background processes.

## Error inspection

```sh
python3 -B /Users/syyui/projects/Yui-results/test/geometry-product-dimension/rigorous-proof/20261030T091649Z-663bc94f52/runtime/nl0/scripts/yui.py errors /Users/syyui/projects/Yui-results/test/geometry-product-dimension/rigorous-proof/20261030T091649Z-663bc94f52
```

```sh
python3 -B /Users/syyui/projects/Yui-results/test/geometry-product-dimension/rigorous-proof/20261030T091649Z-663bc94f52/runtime/nl0/scripts/yui.py errors /Users/syyui/projects/Yui-results/test/lie-module-irreducibility/rigorous-proof/20261030T091649Z-5082f9d71c
```

```sh
python3 -B /Users/syyui/projects/Yui-results/test/geometry-product-dimension/rigorous-proof/20261030T091649Z-663bc94f52/runtime/nl0/scripts/yui.py errors /Users/syyui/projects/Yui-results/test/wave-map-energy/rigorous-proof/20261030T091649Z-c3333068de
```

PAUSED_ERROR is nonterminal: retain this heartbeat and all run resources. Never restart or alter a frozen run. At terminal delivery inspect actual gates and validate existing artifacts using the frozen runtime without new mathematical model/Lean attempts; verify exact owned process/group exits. Remove only the completed heartbeat after all workflows and final reporting finish.
