"""CPU-only comparison with pinned released code; no source mutation, no sampling claim."""
from pathlib import Path
import sys
import json
import math
import hashlib
import os

HERE = Path(__file__).resolve().parent
deps = [HERE.parent/'pilot/deps', HERE.parent.parent/'attention/deps']
os.environ['PYTHONPATH'] = os.pathsep.join(map(str, deps))+os.pathsep+os.environ.get('PYTHONPATH', '')
os.environ['KEOPS_CACHE_FOLDER'] = str(HERE/'keops-cache')
sys.path.insert(0, str(HERE.parent/'pilot'))
from common import verify_source, dense_kernel
import numpy as np
import torch
from fast_krr.models import FullKRR
from fast_krr.opts import ASkotchV2
import importlib
released_module = importlib.import_module('fast_krr.opts.askotchv2')
from check_exact_instability import native_matrix, BLOCKS


class CorrectedFullKRR(FullKRR):
    def _get_block_grad(self, w, block):
        return super()._get_block_grad(w, block)+self.lambd*(w[block]-self.w[block])


def main():
    torch.set_default_dtype(torch.float64)
    torch.set_num_threads(1)
    source = verify_source()
    distance = math.sqrt(-2*math.log(99999/100000))
    x = torch.tensor([[0., 0.], [distance, 0.], [distance/2, math.sqrt(3)*distance/2]])
    kernel = {'type': 'rbf', 'sigma': 1.}
    K = dense_kernel(x, x, kernel)
    lam = 3/20000
    H = K+lam*torch.eye(3)
    target = torch.tensor([1., -1., 0.])
    rhs = H@target
    old_get_block = released_module._get_block
    errors = []
    try:
        for stale, cls in [(True, FullKRR), (False, CorrectedFullKRR)]:
            max_error = 0.
            for indices in BLOCKS:
                fixed = torch.tensor(indices)
                released_module._get_block = lambda *args, fixed=fixed, **kwargs: fixed
                M = np.array([[float(v) for v in row] for row in native_matrix(indices, stale)])
                # Includes the fixed point, each native-state basis, and reachable zero start.
                probes = [np.zeros(6), *np.eye(6), np.array([-1., 1., 0., -1., 1., 0.])]
                for j, state in enumerate(probes):
                    model = cls(x, rhs, x, rhs, kernel, True, lam, 'regression', torch.zeros(3), 'cpu')
                    opt = ASkotchV2(model, block_sz=2, precond_params={'type': 'newton', 'rho': 'regularization'}, accelerated=True)
                    model.w = target+torch.from_numpy(state[:3].copy())
                    opt.v = target+torch.from_numpy(state[3:].copy())
                    opt.y = opt.alpha*opt.v+(1-opt.alpha)*model.w
                    torch.manual_seed(100+j)
                    opt.step()
                    result = torch.cat([model.w-target, opt.v-target]).detach().numpy()
                    err = float(np.max(np.abs(result-M@state)))
                    max_error = max(max_error, err)
                    assert err < 2e-7, (stale, indices, j, err)
            errors.append({'stale': stale, 'one_step_checks': len(BLOCKS)*8, 'max_absolute_error': max_error})
    finally:
        released_module._get_block = old_get_block
    result = {'status': 'PASS', 'official_source': source, 'device': 'cpu', 'dtype': 'float64',
              'inputs': x.tolist(), 'kernel': K.tolist(), 'rhs': rhs.tolist(), 'checks': errors,
              'scope': 'All three blocks and native state basis; proves code-interface match numerically, not the instability theorem.',
              'exact_checker_sha256': hashlib.sha256((HERE/'check_exact_instability.py').read_bytes()).hexdigest(),
              'theorem_sha256': hashlib.sha256((HERE/'theorem.md').read_bytes()).hexdigest(),
              'patch_sha256': hashlib.sha256((HERE/'fix_stale_regularizer.patch').read_bytes()).hexdigest(),
              'checker_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    (HERE/'official_interface_certificate.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__': main()
