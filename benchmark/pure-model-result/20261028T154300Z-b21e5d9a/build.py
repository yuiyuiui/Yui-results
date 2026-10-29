from pathlib import Path
import os, subprocess, sys, json, signal
root = Path(__file__).resolve().parent
mathlib = Path('/Users/syyui/formalization-tools/lean-mathlib-v4.32.2/mathlib')
lean = '/Users/syyui/.elan/toolchains/leanprover--lean4---v4.32.2/bin/lean'
paths = [root, mathlib / '.lake/build/lib/lean']
paths += sorted((mathlib / '.lake/packages').glob('*/.lake/build/lib/lean'))
env = dict(os.environ, LEAN_PATH=':'.join(map(str, paths)))
args = sys.argv[1:] or ['Proof.lean']
log_prefix = Path(args[0]).stem + '-'
state_file = root / (log_prefix + 'build-process.json')
log_file = root / (log_prefix + 'build.log')
p = subprocess.Popen([lean, *args], cwd=root, env=env, text=True,
                     stdout=subprocess.PIPE, stderr=subprocess.STDOUT, bufsize=1)
state_file.write_text(json.dumps({'pid': p.pid, 'args': args, 'status': 'running'}) + '\n')
try:
    with log_file.open('w') as log:
        for line in p.stdout:
            log.write(line)
            log.flush()
            print(line, end='', flush=True)
    code = p.wait()
except KeyboardInterrupt:
    p.send_signal(signal.SIGINT)
    code = p.wait()
    code = code or 130
state_file.write_text(json.dumps({'pid': p.pid, 'args': args, 'status': 'finished', 'exit_code': code}) + '\n')
sys.exit(code)
