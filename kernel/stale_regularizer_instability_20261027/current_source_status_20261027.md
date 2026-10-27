# Bounded source-status check for the stale regularizer correction

Date: 2026-10-27. Read-only checks; no issue, pull request or message was created.

`git ls-remote origin HEAD` for the [official repository](https://github.com/pratikrathore8/fast_krr) returned `61cdb69cb11adea48ecb13c823ad654d46dc15df`, the commit used by the exact theorem and CPU check. The local source verifier also confirmed that the checkout's `fast_krr` files are unmodified.

GitHub connector searches of the repository returned 22 issue records and the repository's historical pull-request records. Titles and returned bodies contained no identified report of this particular extrapolated-gradient mismatch. This is a bounded search result, **not novelty clearance**, and does not establish that nobody has noticed the defect.

The closest currently open code proposal, [PR #78, “Added the codes for my askotchv3, and some relevant new codes for experiments”](https://github.com/pratikrathore8/fast_krr/pull/78), was inspected at head `2a3c5dc5a97a54b69ffc178f0a97febb829d04b1`. It adds an adaptive-momentum optimizer and experiment files. Its new gradient wrapper still calls `model._get_block_grad`, while the new optimizer evaluates that wrapper at `model.w`. Consequently that particular call does not exercise the discrepancy between the extrapolated point and stored iterate. The inspected diff does not alter `full_krr.py`, identify the ASkotchV2 stale-regularization term, or provide the present mean-square instability construction. It is a different algorithm, and we do not characterize its convergence here.

The result remains scoped to the exact code and Newton configuration in `theorem.md`. A supported configuration with a transparent preconditioner is sufficient to demonstrate an implementation defect; it is not an audit of the default rank-100 Nyström benchmark configuration. Author acknowledgement and broader significance remain open.
