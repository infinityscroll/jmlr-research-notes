ACTUAL GAUSSIAN POLYHEDRON EHRHARD INFRASTRUCTURE

This isolated Lean project proves Ehrhard concavity for finite closed Gaussian
polyhedra, converts it to a literal conditional covariance–mean inequality,
and supplies an explicit positive logarithmic correction coefficient.

For C={x: forall j, <w_j,x> <= b_j}, p=gamma(C) in (0,1), and M1=integral_C<v,x>dgamma,
its final endpoint proves

  Var(<v,X> | X in C)
    <= ||v||^2 - exp(-4)/(2*(1+2*log(1/p))) * (M1/p)^2.

The actual concavity statement is x |-> Phi^{-1}(gamma(C-x)). All smoothing,
limits, moment derivatives, and coefficient estimates are proved, not assumed.
Normals may be redundant, coincident, or zero. The mass condition is the only
nondegeneracy condition on C.

This is classical mathematical infrastructure, not a claim of a new Ehrhard
theorem or completion of the negative-voting research theorem.

UPSTREAM ATTRIBUTION
The 12 OAI source files are verbatim copies of the OpenAI smooth Ehrhard proof
from the pinned vendor snapshot documented in OPENAI-EHRHARD-PROVENANCE.json.
Original source: https://github.com/openai/math at
1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Vendor snapshot: https://github.com/pmaronow/slowequilibration-palomar at
a28aaa336343c4caf43791ababd8ed0ee5c7b58e.
Their Apache-2.0 license is preserved in OPENAI-MATH-LICENSE. They compile
unchanged on the exact Lean 4.35.0-rc2 and mathlib pins recorded in this project.

EXTENSIONS
GaussianSoftPolyhedron.lean: explicit bounded-gradient/Hessian softplus approximants.
GaussianPolyhedronEhrhard.lean: actual indicator limit, Gaussian integrals, and Ehrhard concavity.
GaussianEhrhardCurvature.lean: twice-differentiated inverse-CDF calculus.
GaussianEhrhardMomentBridge.lean: actual restricted Gaussian moments and conditional variance.
GaussianEhrhardCoefficient.lean: explicit short-interval coefficient lower bound.

REPRODUCE
With the version in lean-toolchain installed and lake available:
  lake exe cache get
  python3 verify_ehrhard_complete.py
The verifier builds the final target and audits all 77 extension declarations.
It checks exact source hashes for the full 17-file local closure and the pinned
mathlib revision. It rejects every axiom except propext, Classical.choice,
and Quot.sound. All frozen intermediate receipts must remain unchanged.
The .lake directory is a local cache and is not part of the source distribution.

EHRHARD_COMPLETE_VERIFICATION.json and EHRHARD_COMPLETE_AXIOMS.txt record the
completed verification. The coverage files explain each milestone and its scope.
