"""Check the frozen Marcus package and run its two independent exact checkers."""
from pathlib import Path
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile


def main():
    source = Path(__file__).resolve().parent / 'review'
    manifest = json.loads((source / 'MANIFEST.json').read_text())
    for name, expected in manifest['files_sha256'].items():
        actual = hashlib.sha256((source / name).read_bytes()).hexdigest()
        if actual != expected:
            raise RuntimeError('Frozen source mismatch: ' + name)
    with tempfile.TemporaryDirectory(prefix='marcus_three_blocks_') as td:
        work = Path(td) / 'review'
        shutil.copytree(source, work)
        for name in ('check_pure_mixing.py', 'check_literal_layers.py'):
            run = subprocess.run([sys.executable, str(work / name)], cwd=work,
                                 capture_output=True, text=True, timeout=500)
            if run.returncode:
                raise RuntimeError(name + '\n' + run.stdout + run.stderr)
            result = json.loads(run.stdout)
            if not (result.get('status') == 'PASS' or result.get('passed') is True):
                raise RuntimeError('Checker did not pass: ' + name)
            print('PASS', name)
    print('Frozen sources unchanged; finite exact checks corroborate the analytic all-k proof.')


if __name__ == '__main__':
    main()
