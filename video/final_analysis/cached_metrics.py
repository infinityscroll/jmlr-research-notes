"""Exact count-weight form of the frozen cubic MMD bootstrap (float64)."""
import numpy as np

SEED = 20261026
REPLICATES = 2000


def kernel(x, y):
    return (x @ y.T / x.shape[1] + 1) ** 3


def within(k, counts):
    """Remove only the diagonal of RESAMPLED positions, retaining duplicates."""
    n = counts.sum(axis=-1)
    return (np.einsum('bi,ij,bj->b', counts, k, counts, optimize=True)
            - counts @ np.diag(k)) / (n * (n - 1))


def count_draws(n, m, replicates=REPLICATES):
    rng = np.random.default_rng(SEED)
    g = np.empty((replicates, n), dtype=np.float64)
    r = np.empty((replicates, m), dtype=np.float64)
    for b in range(replicates):
        # Preserve original RNG, call order, draw size and schedule pairing.
        g[b] = np.bincount(rng.integers(n, size=n), minlength=n)
        r[b] = np.bincount(rng.integers(m, size=m), minlength=m)
    return g, r


def cached_kvd(krr, kgg, krg, r, g):
    return (within(krr, r) + within(kgg, g)
            - 2 * np.einsum('bi,ij,bj->b', r, krg, g, optimize=True)
            / (r.sum(axis=-1) * g.sum(axis=-1)))


def evaluate(ref, gen, replicates=REPLICATES):
    """Point estimates all horizons; same-reference bootstrap early/late."""
    s, n, h, d = gen.shape
    m = len(ref)
    if ref.shape != (m, d) or min(n, m) < 2:
        raise ValueError('Incompatible feature arrays')
    if not np.isfinite(ref).all() or not np.isfinite(gen).all():
        raise ValueError('Nonfinite features')
    krr = kernel(ref, ref)
    gcounts, rcounts = count_draws(n, m, replicates)
    gone, rone = np.ones((1, n)), np.ones((1, m))
    points = np.empty((s, h), dtype=np.float64)
    boot = np.empty((replicates, s), dtype=np.float64)
    for i in range(s):
        ends = {}
        for j in range(h):
            kgg, krg = kernel(gen[i, :, j], gen[i, :, j]), kernel(ref, gen[i, :, j])
            points[i, j] = cached_kvd(krr, kgg, krg, rone, gone)[0]
            if j in (0, h-1):
                # Compute both KVD values separately, as the original does.
                # No cancellation-based rewrite changes the estimator.
                ends[j] = cached_kvd(krr, kgg, krg, rcounts, gcounts)
        boot[:, i] = ends[h-1] - ends[0]
    return points, boot
