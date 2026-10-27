# Default damping, actual random power stepsizes, exact instability certificate

See `theorem.md` for scope. This extends the earlier Newton result to the released full-rank Nyström option `{'type':'nystrom','r':2,'rho':'damped'}` in float64, retaining the actual ten-step random power routine. The proof covers every blockwise stepsize triple in the whole permitted interval, not sampled points.

From `<workspace>`:

```sh
python3 work/jmlr_breakthrough_portfolio_20261026/kernel/default_damping_instability_20261027/check_uniform_stepsizes.py
```

Requires Python 3.9+ standard library only. Expected `PASS`: 27 coefficient matrices for uniform stale growth, 27 for reachable initialization, and 27 for uniform corrected contraction. The JSON certificate includes exact positive LDL pivots, parameters and source hashes. Growth factor is `26/25`; corrected contraction factor is `99/100`; the permitted stepsize interval is `[20001500/20001499, 1502/1501]`.

Run the actual pinned released code using the workspace CPU environment:

```sh
<python-runtime>/bin/python3 work/jmlr_breakthrough_portfolio_20261026/kernel/default_damping_instability_20261027/check_released_damped_interface.py
```

This uses the existing PyTorch, NumPy, PyKeOps and pybind11 dependencies through `kernel/pilot/common.py`. It may compile local CPU extensions in this new folder's `keops-cache`; no GPU or cloud is needed. It records all 48 actual update comparisons and the genuinely varying power-method stepsizes, paired exactly between the stale and corrected versions. Only block choice is controlled to enumerate the three possible blocks.

The original repository and all earlier frozen files remain unchanged. The correction is supplied only through a subclass adding `lambda*(evaluation_point-stored_point)` to the block gradient. The result is a code-level correction, not a refutation of the paper's correctly evaluated convergence theorem or an audit of its benchmark settings.
