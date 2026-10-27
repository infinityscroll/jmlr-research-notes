"""Exact scalar ASGD weights and Algorithm 1 COfB with bounded Rademacher data.

No paper-code formula is substituted: bootstrap RMS is centered at original ASGD,
with Student t_B critical value. Empirical Rademacher resampling is implemented
as Bernoulli draws using the empirical positive fraction, exactly equivalent
in law to resampling observations with replacement.
"""
import json
import math
import time
from pathlib import Path

import numpy as np

TCRIT = {1: 12.706204736432095, 3: 3.182446305284263,
         5: 2.570581835636305, 10: 2.228138851964939}


def weights(n, eta, alpha):
    lr = eta * np.arange(1, n + 1, dtype=float) ** (-alpha)
    # Contribution of x_i to the final sum, computed backwards.
    w = np.empty(n)
    suffix = 0.0
    for i in range(n - 1, -1, -1):
        suffix = 1.0 + (1.0 - lr[i + 1]) * suffix if i < n - 1 else 1.0
        w[i] = lr[i] * suffix / n
    q = float(np.mean(np.cumprod(1.0 - lr)))
    return w, q


def wilson(k, r):
    z = 1.959963984540054
    p = k / r
    den = 1 + z*z/r
    center = (p + z*z/(2*r)) / den
    half = z / den * math.sqrt(p*(1-p)/r + z*z/(4*r*r))
    return [center-half, center+half]


def simulate(n, eta, alpha, x0, reps, seed, B=3, batch=50, sigma=1.0):
    w, q = weights(n, eta, alpha)
    rng = np.random.default_rng(seed)
    k = 0
    widths = []
    for start in range(0, reps, batch):
        r = min(batch, reps-start)
        z = rng.integers(0, 2, (r, n), dtype=np.int8)
        p = z.mean(axis=1)
        original = sigma*(2*np.sum(z*w, axis=1)-w.sum())+q*x0
        d2 = np.zeros(r)
        for _ in range(B):
            boot = rng.random((r, n)) < p[:, None]
            estimate = sigma*(2*np.sum(boot*w, axis=1)-w.sum())+q*x0
            d2 += (estimate-original)**2/B
        radius = TCRIT[B]*np.sqrt(d2)
        k += int(np.count_nonzero(np.abs(original) <= radius))
        widths.extend((2*radius).tolist())
    v = sigma**2*float(w@w)
    d = 2*v-(v+sigma**2*w.sum()**2)/n
    bound = None if q*x0 == 0 else min(1, (math.sqrt(v)+TCRIT[B]*math.sqrt(d))**2/(q*x0)**2)
    return dict(n=n, eta=eta, alpha=alpha, x0=x0, sigma=sigma, B=B, reps=reps, seed=seed,
                hits=k, coverage=k/reps, wilson95=wilson(k,reps),
                mean_width=float(np.mean(widths)), bias=q*x0,
                variance=v, n_variance=n*v, weight_sum=float(w.sum()),
                initial_weight=q, finite_n_coverage_upper_bound=bound)


def limit_coverage(B, nodes=200):
    # X=U+V; D_b=sqrt(2)Z_b-V, with all latent coordinates independent N(0,1).
    v = np.zeros(B+2)
    v[:2] = 1
    d = np.zeros((B, B+2))
    d[:, 1] = -1
    d[:, 2:] = math.sqrt(2)*np.eye(B)
    eig = np.linalg.eigvalsh(np.outer(v,v)-TCRIT[B]**2/B*d.T@d)
    pos = eig[-1]
    neg = -eig[eig < -1e-9]
    # Gaussian quadratic form with one positive eigenvalue. erfc integral
    # and chi-square Laplace transforms reduce its tail to one dimension.
    x, w = np.polynomial.legendre.leggauss(nodes)
    c = np.cos((x+1)*math.pi/4)**2
    f = np.prod(np.sqrt(c[:,None]/(c[:,None]+neg[None,:]/pos)), axis=1)
    return float(1-0.5*np.sum(w*f))


def verify_weights():
    z = np.array([1.,-1.,-1.,1.,1.,-1.,1.])
    for eta, alpha in [(1,1),(.25,1),(.5,.501)]:
        x = 2.0
        history = []
        for t, value in enumerate(z, 1):
            x -= eta*t**(-alpha)*(x-value)
            history.append(x)
        w, q = weights(len(z), eta, alpha)
        assert abs(np.mean(history)-(w@z+q*2)) < 1e-14
        assert abs(w.sum()+q-1) < 1e-14
    for n in [10,100,10000]:
        w,q = weights(n,1,1)
        h = np.sum(1/np.arange(1,n+1))
        assert abs(n*(w@w)-(2-h/n)) < 1e-11


if __name__ == '__main__':
    start = time.time()
    verify_weights()
    result = {'model':'h(x,z)=0.5*(x-z)^2; iid z uniform on {-1,+1}',
              'algorithm':'paper Algorithm 1 ASGD, uniform average, B=3, t_B RMS around original',
              'limit_coverage':{str(B):[limit_coverage(B,k) for k in [100,200,400]] for B in TCRIT},
              'runs':[]}
    settings = [(10000,.5,.501,0,5000,2026102601),
                (10000,1,1,0,10000,2026102602),
                (10000,.25,1,10,5000,2026102603),
                (100000,1,1,0,2000,2026102604)]
    for args in settings:
        r=simulate(*args)
        result['runs'].append(r)
        print(json.dumps(r),flush=True)
    r=simulate(10000,.25,1,1,5000,2026102605,sigma=.01)
    result['runs'].append(r)
    print(json.dumps(r),flush=True)
    result['elapsed_seconds']=time.time()-start
    Path(__file__).with_name('endpoint_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print('Elapsed seconds:',result['elapsed_seconds'],flush=True)
