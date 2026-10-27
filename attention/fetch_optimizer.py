"""Fetch one pinned upstream file on explicit invocation; never fetch on import."""
from pathlib import Path
import hashlib
import urllib.request

ROOT = Path(__file__).resolve().parent
COMMIT = '30aff9413bc04dce882c4e4a86f0d7d555a5863e'
URL = ('https://raw.githubusercontent.com/addskj2002/AttentionMD/' + COMMIT +
       '/synthetic-data/tools/optimizers.py')
EXPECTED = 'd4ce054aca1fe0001fc9567cfcae1cd72dde60c57910f04198a04172e1f3983b'
DESTINATION = ROOT / 'external_cache' / 'optimizers.py'

def checked_path():
    if not DESTINATION.exists():
        raise FileNotFoundError('Run python fetch_optimizer.py before --native or run_diagnostic.py')
    if hashlib.sha256(DESTINATION.read_bytes()).hexdigest() != EXPECTED:
        raise ValueError('Cached optimizer hash mismatch; refusing to execute it')
    return DESTINATION

def main():
    if DESTINATION.exists():
        checked_path()
        print('Pinned optimizer already present and verified.')
        return
    request = urllib.request.Request(URL, headers={'User-Agent':'attention-research-note/1'})
    with urllib.request.urlopen(request, timeout=30) as response:
        data = response.read(1024 * 1024 + 1)
    if len(data) > 1024 * 1024:
        raise ValueError('Unexpected upstream file size')
    if hashlib.sha256(data).hexdigest() != EXPECTED:
        raise ValueError('Upstream optimizer hash mismatch; nothing saved or executed')
    DESTINATION.parent.mkdir(parents=True, exist_ok=True)
    with DESTINATION.open('xb') as output:
        output.write(data)
    print('Fetched and verified the pinned upstream optimizer (not included in the release).')

if __name__ == '__main__':
    main()
