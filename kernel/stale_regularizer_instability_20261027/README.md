# Exact ASkotchV2 instability reproduction

The source-bound result is in `theorem.md`. The pinned official checkout is unchanged. The exact certificate proves mean-square divergence for the released gradient and contraction after changing only the stale regularization term. The separate CPU check verifies the correspondence to the actual released update.

From `<workspace>`:

```sh
python3 work/jmlr_breakthrough_portfolio_20261026/kernel/stale_regularizer_instability_20261027/check_exact_instability.py
```

This needs only Python's standard library (Python 3.9 or later). Expected output includes `PASS`, stale growth factor `26/25`, and corrected contraction factor `99/100`. It writes `exact_certificate.json`, including the full rational reduced operators, principal-minor witnesses and source hashes. No numerical eigenvalue calculation or simulation enters this proof.

For the actual released-code interface check in the existing workspace environment:

```sh
<python-runtime>/bin/python3 work/jmlr_breakthrough_portfolio_20261026/kernel/stale_regularizer_instability_20261027/check_official_interface.py
```

This uses Python 3.12, CPU `torch.float64`, and the existing local PyTorch, NumPy, PyKeOps and pybind11 dependencies selected through `kernel/pilot/common.py`. It may compile a small KeOps CPU extension into this folder's `keops-cache`. CUDA and OpenMP are not required. Expected result: 24 released and 24 corrected one-step checks pass, with maximum absolute error approximately `8.50e-11`. The output certificate binds the theorem, exact checker, interface checker, patch and official commit. The random block is controlled only to enumerate its three possibilities; gradient, preconditioner, automatic stepsize and optimizer steps execute the released code.

The one-line proposed correction is preserved in `fix_stale_regularizer.patch`. It passes `git apply --check`, but has **not** been applied or submitted. `current_source_status_20261027.md` records the bounded read-only repository-status check. `nystrom_full_rank_equivalence_20261027.md` separately proves the exact-arithmetic equivalence of a supported full-rank Nyström option; the numerical interface certificate is for Newton only.

The code-level result does not refute Theorem 17, establish an error in the benchmark rankings, or establish novelty. No cloud resource is used by either checker. Local compiler caches are generated dependencies, not proof artifacts.
