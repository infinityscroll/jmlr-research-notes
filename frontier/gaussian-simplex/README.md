# Gaussian covariance concavity and simplex optimality near independence

The main result is concavity of Gaussian maximal covariance in the ordinary
positive semidefinite covariance matrix, for every fixed target distribution
with a finite second moment in every finite dimension. Equivalently, squared
Wasserstein distance from that target to a centered Gaussian is convex in its
covariance.

The proof gives the balanced Gaussian first-moment optimum for every cell
count, with regular-simplex equality when the ambient dimension is at least
the cell count minus one. It also supplies centroid coercivity and both-sign
simplex optimality on dimension-independent intervals near zero correlation.
Positive correlation requires balance; the negative single-rule result allows
arbitrary output bias. Constants can depend on the number of cells.

- [Read the manuscript PDF](manuscript.pdf) · [LaTeX source](review/paper/main.tex)
- [Readable proof](review/proof_sources/ALL_DIMENSIONAL_COVARIANCE_CONCAVITY.txt)
- [Precise application scope](review/proof_sources/ALL_M_ENDPOINT_AND_SMALL_NOISE.txt)
- [Explicit all-cell coercivity supplement](review/proof_sources/EXPLICIT_ALL_M_GAP_20261031.txt)
- [New equal-mass Gaussian multi-bubble stability consequence](supplements/bubble-stability/README.md)
- [Audits](review/audits/)
- [Frozen downloadable package](../../archives/gaussian_covariance_simplex_review_20261031.zip)

Run from the repository root after installing `requirements.txt`:

```sh
python frontier/gaussian-simplex/review/reproduce.py
```

The script validates the package manifest and runs both independent exact
checkers in a temporary directory. The analytic theorem received three
independent internal **AI-agent** proof audits, followed by separate manuscript
assembly audits. The LaTeX manuscript compiled successfully. These checks are
not external expert review or Lean formalization.

The full noise-correlation range remains open. In dimensions below the simplex
dimension, the theorem gives a strict benchmark but does not determine the
exact optimum. Current-source comparisons and priority limits are included in
the package. No exhaustive novelty clearance or author endorsement is claimed.

The `review/` directory and ZIP preserve the original frozen local artifact
unchanged. Historical statements inside it about being unpublished refer to
its creation; this directory is its subsequent public release.

Archive SHA256: `252e42d7258c369de78629538c7c5ea6dd9e66e3e5fd7bf26d86802867bdeeb4`.
