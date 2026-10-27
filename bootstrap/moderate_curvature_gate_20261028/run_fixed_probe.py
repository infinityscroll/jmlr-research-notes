"""Fixed paired original-Algorithm-1 probe; see PROTOCOL.md before execution."""
from pathlib import Path
import hashlib
import json
import math
import time
import numpy as np

HERE = Path(__file__).resolve().parent
N, REPS, B = 1_000_000, 512, 3
SEED, ETA, ALPHA, SIGMA = 202610281911, .94, .51, 4.
CUTOFF = 3.182446305284263


def binomial_cdf(k, p):
    return math.fsum(math.comb(REPS, j)*p**j*(1-p)**(REPS-j)
                     for j in range(k+1))


def cp_interval(k):
    def solve(cut, target):
        lo, hi = 0., 1.
        for _ in range(70):
            mid = (lo+hi)/2
            if binomial_cdf(cut, mid) > target:
                lo = mid
            else:
                hi = mid
        return (lo+hi)/2
    return [solve(k-1, .975) if k else 0.,
            solve(k, .025) if k < REPS else 1.]


def g(x):
    return x + .25 * np.log1p(2 * np.sinh(x) ** 2)


def inverse_g(y):
    lo, hi = np.full_like(y, -9.), np.full_like(y, 9.)
    for _ in range(70):
        mid = (lo + hi) / 2
        right = g(mid) < y
        lo = np.where(right, mid, lo)
        hi = np.where(right, hi, mid)
    return (lo + hi) / 2


def summary(stat):
    rms = np.sqrt(np.mean((stat[:, 1:] - stat[:, :1]) ** 2, axis=1))
    covered = np.abs(stat[:, 0]) <= CUTOFF * rms
    k = int(covered.sum())
    ci = cp_interval(k)
    return {"covered": k, "replications": REPS, "coverage": k/REPS,
            "monte_carlo_95_CP": ci,
            "mean_original": float(stat[:, 0].mean()),
            "sd_original": float(stat[:, 0].std(ddof=1)),
            "mean_original_in_sigma_over_sqrt_n_units": float(stat[:, 0].mean()*np.sqrt(N)/SIGMA),
            "mean_rms": float(rms.mean()),
            "mean_radius": float(CUTOFF*rms.mean()),
            "mean_bootstrap_minus_original": float((stat[:, 1:]-stat[:, :1]).mean())}, covered


def main():
    out = HERE / "probe_results.json"
    assert not out.exists(), "Never overwrite a retained run."
    protocol = {"n": N, "replications": REPS, "B": B, "seed": SEED,
                "eta": ETA, "alpha": ALPHA, "sigma": SIGMA, "x0": 0.,
                "cutoff": CUTOFF, "max_wall_seconds": 300,
                "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                "protocol_sha256": hashlib.sha256((HERE/'PROTOCOL.md').read_bytes()).hexdigest()}
    (HERE/'execution_protocol.json').write_text(json.dumps(protocol, indent=2)+'\n')
    rng = np.random.default_rng(SEED)
    counts = rng.binomial(N, .5, size=REPS)
    remaining = counts.copy()
    probs = counts/N
    state = np.zeros((2, REPS, B+1))
    total = state.copy()
    sums = np.zeros((REPS, B+1))
    checkpoints, checkpoint_steps = [], []
    start = time.monotonic()
    complete = False
    for t in range(1, N+1):
        plus = rng.random(REPS) < remaining/(N-t+1)
        remaining -= plus
        draws = np.empty((REPS, B+1))
        draws[:, 0] = SIGMA*(2*plus.astype(np.int8)-1)
        draws[:, 1:] = SIGMA*(2*(rng.random((REPS, B)) < probs[:, None]).astype(np.int8)-1)
        step = ETA*t**(-ALPHA)
        state[0] -= step*(g(state[0])-draws)
        state[1] -= step*(state[1]-draws)
        total += state
        sums += draws
        if t in (100, 1000, 10000, 100000, N):
            checkpoints.append(total/t)
            checkpoint_steps.append(t)
        if t % 1000 == 0 and time.monotonic()-start > 300:
            break
    else:
        complete = True
    averages, means = total/t, sums/t
    results, masks = {}, []
    if complete:
        assert np.all(remaining == 0)
        assert np.array_equal(sums[:, 0], SIGMA*(2*counts-N))
        saa = np.stack((inverse_g(means), means))
        assert np.max(np.abs(g(saa[0])-means)) < 1e-12
        for label, stat in (("logcosh_ASGD", averages[0]), ("quadratic_ASGD", averages[1]),
                            ("logcosh_SAA_control", saa[0]), ("quadratic_SAA_control", saa[1])):
            results[label], mask = summary(stat)
            masks.append(mask)
    else:
        saa = np.empty((0,))
    np.savez_compressed(HERE/'probe_outputs.npz', averaged_iterates=averages,
                        sample_means=means, saa=saa, coverage_masks=np.array(masks),
                        original_plus_counts=counts, checkpoint_steps=np.array(checkpoint_steps),
                        checkpoint_averages=np.array(checkpoints))
    report = {"protocol": protocol, "complete": complete, "completed_steps": t,
              "elapsed_seconds": time.monotonic()-start, "results": results,
              "outputs_sha256": hashlib.sha256((HERE/'probe_outputs.npz').read_bytes()).hexdigest(),
              "claim_scope": "Monte Carlo evidence only; no deterministic coverage theorem or novelty claim."}
    out.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
