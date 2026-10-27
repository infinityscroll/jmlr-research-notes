# Primary sources and external code

The target paper is [Julistiono, Ataee Tarzanagh and Azizan, *Optimizing Attention with Mirror Descent*, JMLR](https://www.jmlr.org/papers/volume27/25-0549/25-0549.pdf). The byte-identical archival notes contain the primary theorem comparisons and URLs. No downloaded paper is redistributed here.

The authors' released repository is [addskj2002/AttentionMD](https://github.com/addskj2002/AttentionMD). `fetch_optimizer.py` retrieves only:

- Commit: `30aff9413bc04dce882c4e4a86f0d7d555a5863e`
- Path: `synthetic-data/tools/optimizers.py`
- SHA256: `d4ce054aca1fe0001fc9567cfcae1cd72dde60c57910f04198a04172e1f3983b`
- [Pinned upstream file](https://github.com/addskj2002/AttentionMD/blob/30aff9413bc04dce882c4e4a86f0d7d555a5863e/synthetic-data/tools/optimizers.py)

The inspected upstream tree did not provide a LICENSE file. This release therefore does **not** redistribute that source or assert permission to relicense it. The explicit fetch helper leaves the upstream file in a git-ignored cache; any rights remain with its original authors. The default verifier does not need it.

The released metric call is [correlation_calculation.py, line 22](https://github.com/addskj2002/AttentionMD/blob/30aff9413bc04dce882c4e4a86f0d7d555a5863e/synthetic-data/correlation_calculation.py#L22): `bregman_correlation(att_svm, Ws[it], p)`. [Its helper](https://github.com/addskj2002/AttentionMD/blob/30aff9413bc04dce882c4e4a86f0d7d555a5863e/synthetic-data/tools/bregman_div.py) normalizes both arguments. The staged verifier independently evaluates the stated formula; it does not copy that helper.

NumPy and PyTorch are installed as dependencies under their respective licenses. They are not vendored. The proof notes and verification scripts should not be attributed to the target paper's authors.
