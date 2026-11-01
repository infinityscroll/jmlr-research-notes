# Lean verification of negative-voting proof components

This package contains **54 named theorem declarations**, checked by Lean 4.19.0
against an exact mathlib commit. The audit covers **64 compiled theorem constants**,
including compiler-generated proof and definition-equation constants.

The checked mathematics includes actual finite-product Gaussian hyperplane null
sets, almost-everywhere unique linear-score maxima, exponential and first moments,
finite-max and fractional-score integrability, exact centroid pairing, and Gaussian
zero-routing-gap rigidity. It also covers the centered covariance strain identity,
retained centroid-square cancellation, logarithmic remainder decay, and one
threshold uniform over the entire negative voting interval for fixed coefficients.

The full Gaussian simplex inequality, Negative Plurality Is Stablest, and MAX-m-CUT
hardness are not formalized here. The local/exterior analytic comparisons remain
explicit hypotheses of the scalar assembly lemmas. The Gaussian zero-gap rigidity
result proves a genuine first-moment statement; it does not establish that gap is
zero from full-noise competitiveness.

No custom axioms, `sorry`, `admit`, or `native_decide` are used in the project proofs.
Every audited constant depends only on the standard logical axioms `propext`,
`Classical.choice`, and `Quot.sound`.

## Reproduce

Install [Lean's elan toolchain manager](https://lean-lang.org/install/), then run
from this directory:

```sh
lake exe cache get
lake build
python3 verify.py
```

The exact Lean version is in `lean-toolchain`; mathlib and all transitive packages
are pinned in `lake-manifest.json`. `verify.py` rebuilds, reads the compiled Lean
environment, verifies that every project theorem constant is audited and every
source module is imported, and rejects unexpected transitive axiom dependencies.
It does not use a cloud service or a language model.

On macOS hosts whose loader rejects the old native cache executable, the cache can
instead be fetched through the Lean interpreter:

```sh
lake env lean --run .lake/packages/mathlib/Cache/Main.lean get
```

`BUILD_TRANSCRIPT.txt` and `BUILD_RECEIPT.json` record the successful local check.
The receipt pins the released proof and audit sources. Downloaded packages and
build outputs under `.lake/` are excluded from the release.

## Coverage

| Module | Kernel-checked content | Remaining connection to the full manuscript |
| --- | --- | --- |
| `Routing.lean` | Exact simplex routing decomposition; nonnegativity; a quantitative score-margin bound; zero-loss purity; zero integral implies almost-everywhere purity | The full-noise theorem must supply the relevant equality |
| `Integrability.lean` | Finite maxima and measurable simplex-weighted mixtures of integrable scores are integrable; routing integrability is derived | Applied to Gaussian scores by the next module |
| `GaussianRouting.lean` | Actual Gaussian singleton and finite-product hyperplane nullness; distinct linear rows tie with probability zero; unique maxima almost everywhere | Distinctness of the regular centroid rows follows from the manuscript's geometric classification |
| `GaussianMoments.lean` | Actual Gaussian exponential/id integrability, product-coordinate laws, linear-score and maximum integrability; zero expected maximum-minus-mixture gap forces an almost-everywhere unique indicator rule, with a maximizer constructed internally | Deriving zero gap from full-noise competitiveness remains analytic |
| `GaussianCentroid.lean` | Expected fractional linear score equals the score/centroid pairing; self-centroid score equals squared Frobenius norm; exact expected self-centroid routing-gap identity | The sharp upper bound for the expected maximum and its equality classification remain analytic |
| `Centroid.lean` | Exact retained-square cancellation for finite centroid arrays; zero squared mass defect characterizes the mass vector | The local analytic comparison must supply the retained positive square term |
| `EdgeEnergy.lean` | Exact centered symmetric ordered-edge energy identity; Frobenius lower bound; zero energy forces zero matrix | Gaussian facet weights and covariance Hessian bounds remain analytic |
| `Threshold.lean` | Decay of `(1+log x)^p/x^q` for fixed `p >= 0`, `q > 0`; one eventual threshold for the two concrete exterior rates | Constants must be supplied with the claimed uniformity |
| `VotingRange.lean` | Exact endpoint scaling and a single natural threshold valid for every `0 < r <= 1/(m-1)`; conditional assembly with that quantifier order | The Gaussian localization, local comparison and exterior estimates remain explicit hypotheses |
| `Assembly.lean` | Signed-Hermite scalar bound, strict exterior exclusion, zero-deficit local rigidity, and complete scalar two-region closure | Hermite expansion, Gaussian estimates, covariance classification and discrete/UGC transfer are not proved by this module |

## Source mapping

The reference is
[the integrated theorem and proof](https://github.com/infinityscroll/jmlr-research-notes/blob/main/frontier/negative-voting-simplex/supplements/integrated-full-voting-proof-20261102/MAIN_THEOREM_INTEGRATED_PROOF_20261102.txt),
Sections 2B and 3. The formalization now proves the routing-integrability and
Gaussian no-tie facts directly, together with the actual centroid expectation
calculation, the covariance edge-strain identity, and uniform scalar threshold
selection. `GAUSSIAN_ROUTING_COVERAGE.txt` and `VOTING_RANGE_COVERAGE.txt` give the
module-level statements and proof routes.

Completing the full theorem still requires formal versions of the covariance,
optimal-transport, moving-boundary, and Hermite estimates; the discrete consequences
also require invariance and complexity-theoretic transfer. This package exposes
those interfaces rather than turning the desired conclusion into a custom axiom.
