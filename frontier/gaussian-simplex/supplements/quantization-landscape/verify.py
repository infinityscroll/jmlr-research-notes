"""Validate copied sources and replay the appendix's exact rational certificate."""
from pathlib import Path
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile


def main():
    base = Path(__file__).resolve().parent
    manifest = json.loads((base / 'PUBLIC_SOURCE_MAP.json').read_text())
    for group in ('source_files', 'dependencies'):
        for name, expected in manifest[group].items():
            actual = hashlib.sha256((base / name).read_bytes()).hexdigest()
            assert actual == expected, name
    with tempfile.TemporaryDirectory(prefix='gaussian-quantization-check-') as tmp:
        target = Path(tmp)
        for name in ('check_dimension_boundary.py',
                     'DIMENSION_BOUNDARY_AND_LLOYD_SEPARATION_20261031.txt'):
            shutil.copy2(base / name, target / name)
        subprocess.run([sys.executable, str(target / 'check_dimension_boundary.py')],
                       check=True, cwd=target, timeout=30)
        fresh = json.loads((target / 'DIMENSION_BOUNDARY_RATIONAL_CHECK.json').read_text())
    retained = json.loads((base / 'DIMENSION_BOUNDARY_RATIONAL_CHECK.json').read_text())
    for key in ('source_sha256', 'checker_sha256', 'arithmetic', 'checks', 'passed', 'total'):
        assert fresh[key] == retained[key], key
    print('PASS source integrity and exact appendix replay; analytic proof is not mechanically verified.')


if __name__ == '__main__':
    main()
