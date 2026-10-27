"""Validate release integrity and run each bounded CPU verification entrypoint."""
from pathlib import Path
import hashlib,json,os,subprocess,sys,time

ROOT=Path(__file__).resolve().parent

def main():
    manifest=json.loads((ROOT/'RELEASE_MANIFEST.json').read_text())
    for name,expected in manifest['files'].items():
        path=ROOT/name
        assert path.is_file() and hashlib.sha256(path.read_bytes()).hexdigest()==expected,name
    print('PASS release integrity:',len(manifest['files']),'files',flush=True)
    env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1',OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',MKL_NUM_THREADS='1')
    cases=['attention/verify.py','hierarchical/reproduce.py','bootstrap/verify.py','topics/reproduce.py','kernel/verify.py','video/verify.py']
    for script in cases:
        start=time.monotonic()
        result=subprocess.run([sys.executable,str(ROOT/script)],cwd=ROOT,env=env,text=True,capture_output=True,timeout=180)
        if result.returncode:
            print(result.stdout);print(result.stderr,file=sys.stderr)
            raise SystemExit('FAILED '+script)
        print('PASS',script,'in',round(time.monotonic()-start,2),'seconds',flush=True)
    print('All six bounded verification entrypoints passed. This does not formally verify the analytic proofs.')

if __name__=='__main__':main()
