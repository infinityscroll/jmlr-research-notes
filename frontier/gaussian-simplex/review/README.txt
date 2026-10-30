GAUSSIAN COVARIANCE CONCAVITY AND SIMPLEX OPTIMALITY NEAR INDEPENDENCE
Research review package — 31 October 2026

START HERE
Open paper/main.tex in the Codex LaTeX editor for the manuscript and PDF preview.
With a standard LaTeX installation, run pdflatex main.tex twice inside paper/.
The core theorem, balanced endpoint and centroid coercivity have passed three
independent internal analytic audits. The all-cell applications were separately
audited. These are AI-agent audits, not external referee reports or Lean proofs.
Priority clearance and external mathematical review remain outstanding.

MAIN RESULT
For every probability law nu on a finite-dimensional Euclidean space with
finite second moment, the maximal covariance

  F_nu(C) = sup E[X dot Y],  X ~ N(0,C), Y ~ nu,

is concave in the ordinary positive semidefinite covariance matrix C.
Equivalently, W2(N(0,C),nu)^2 is convex in C. Homogeneity also makes F_nu(C)^2
concave. For a full simplex target with positive atom masses, the Hessian of
F_nu is negative definite at every positive definite C. Strictness for arbitrary
targets is not asserted.

The proof first treats simplex targets. Gaussian covariance deficits on facets
pay a global cycle residual through an exact simplex-chain identity and a
weighted choice of triangle representative. Singular-covariance continuity,
an exact affine lift and W2 approximation extend the theorem to every nu.
The argument is analytic in arbitrary dimension; finite checks corroborate
its algebra and do not replace its proof.

APPLICATIONS AND SCOPE
For every fixed m>=3, the regular simplex uniquely maximizes the balanced
Gaussian first-moment functional, and a centroid-orbit coercivity bound holds
with a constant depending only on m. Equality requires ambient dimension
at least m-1. The existing transfer arguments then give positive-size
correlation intervals near zero, independent of ambient dimension:

  * positive correlation: balanced simplex noise-stability maximization;
  * negative correlation: minimization for pairs whose corresponding masses
    agree but are free, including single rules with arbitrary output bias;
  * the corresponding fixed-correlation, low-influence discrete conclusions,
    with additive error and the usual m-symbol channel restriction.

The intervals can depend on m. This package does not claim the full Standard
Simplex correlation range, sharp MAX-m-CUT hardness, or a uniform interval
over all m. Read the manuscript and proof_sources/ALL_M_ENDPOINT_AND_SMALL_NOISE.txt for
the exact quantifiers and equality statements.

RELATION TO CURRENT LITERATURE
Heilman's October 23, 2026 preprint explicitly describes four-cell and higher
Standard Simplex cases as open. Its unrestricted-mass propeller theorem and
the recent equal-variance simplex-width results have different constraints.
Section 1.2 of that same preprint specifically identifies the equal-mass
first-moment problem as unresolved, emphasizing N=n+1 cells in dimension n.
The endpoint theorem addresses that precise emphasized regime for every n>=2,
and all higher ambient dimensions. The exact lower-dimensional optimum when
there are more than n+1 cells is not determined here.
The bounded source comparison found no exact overlap with the present theorem;
that is evidence to review, not exhaustive priority clearance.

Primary starting points:
  https://arxiv.org/html/2610.32158v1
  https://arxiv.org/html/1211.7138#S8
  https://arxiv.org/html/2011.05583v2
  https://arxiv.org/html/2209.11216v1
  https://arxiv.org/html/0903.3362v3
  https://www.math.univ-toulouse.fr/~ledoux/BrunnMinkowski.pdf

CONTENTS
paper/          Review manuscript, with full mathematical arguments.
proof_sources/  Original pinned proof and transfer notes.
audits/         Independent internal mathematical audit records.
checks/         Two independently written exact-algebra checkers.
evidence/       Replays and precise source/application scope records.
MANIFEST.json   SHA256 pins for the released files.
reproduce.py    Integrity check and fresh temporary-directory checker runs.

Two separate supplements give an explicit all-m covariance-gap/coercivity
coefficient and the Gaussian-fitting consequences. Elementary mean and scale
reductions in the fitting note are credited as known context. The explicit
coefficient is conservative and does not improve the old four-cell intervals.

Some original notes retain their historical candidate/conditional labels.
They are preserved byte-for-byte; the audit records and this package state
the current status. Neither their original labels nor finite PASS outputs
substitute for reading the arguments.

REPRODUCTION
Use Python 3.10 or newer. In a virtual environment, install the one dependency:

  python -m pip install -r requirements.txt
  python reproduce.py --output /absolute/path/to/reproduction.json

The script verifies every manifest entry and runs both checkers on copied
files in a new temporary directory. It leaves this package unchanged.
The SymPy checker tests 882 local entries and 1,742 assembled identity entries
in dimensions 2 through 6. The independent standard-library Fraction checker
tests 96 assertions on 12 nonregular rational fixtures in dimensions 2 through 7.

The second checker also runs alone without external dependencies:

  python checks/check_chain_geometry.py

That direct command writes a result JSON beside its script; use reproduce.py
to keep the release directory unchanged. Exact fixtures validate finite algebra.
Gaussian integration, covariance positivity, extension arguments, and the
uniform-in-dimension theorem are justified by the mathematical proof and audits.

This is a local review package. It has not been submitted, published, or sent
to an author as part of this continuation.
