# Coupled cactus components in linear Gaussian structural equation models

This technical note counts the generic **entire admissible real fiber** for
a declared class of cyclic linear Gaussian SEMs. It is a subclass result,
not a characterization of all mixed graphs.

The model is

\[
\Sigma=(I-\Lambda)^{-T}\Omega(I-\Lambda)^{-1},
\]

with an invertible directed matrix, unrestricted positive error variances,
positive-definite \(\Omega\), and graph-prescribed directed and error-covariance
zeros. There is no equal-variance or dynamic-stability assumption.

## Exact scope

Each directed component is an isolated vertex, a coherently oriented simple
cycle of length at least three, or a coherent cactus with at least two such
cycles. The cactus has no directed bridges or chords; its undirected cycles
meet only at articulation vertices. Errors inside a nontrivial directed
component are uncorrelated. Arbitrary permitted error correlations **between**
components are allowed and remain unknown.

An outside vertex is a partial error probe of a simple cycle when it is
bidirected-adjacent to a nonempty proper subset of that cycle. If \(u\) counts
simple-cycle components with no such probe, the generic admissible real fiber
has exactly \(2^u\) points. Multi-cycle cactus components are rationally
identified from their marginal covariance. The specified recursive extension
treats the correlated core as one initial block; later independent-error
blocks follow the inherited composition lemma.

Start with [the coupled-cactus proof](proofs/COUPLED_CACTUS_THEOREM.txt).
Its cycle branch and recursive composition dependency is included in
[the inherited block proof](proofs/RECURSIVE_BLOCK_CLASS.txt).
Cycle length at least three is essential; the included length-two fixture
demonstrates why that condition cannot be dropped.

## Bounded verification

Python 3.9 or later, standard library only:

~~~sh
python3 frontier/causal-cactus/verify.py
~~~

Run from the repository root, or use the script's absolute path elsewhere.
The wrapper verifies the pinned copied sources, runs the existing exact
Fraction checker in a temporary directory, and compares both generated JSON
records with the preserved evidence. The temporary directory is removed
automatically; checked-in evidence is not overwritten. The child process has
a 180-second limit and runs with Python assertions enabled.

The finite checks cover branch-transform density at cycle lengths 3–12,
all 512 cross-error support patterns between two three-cycles (2,048 flip
comparisons), five whole-covariance fixtures, 24 cactus reconstructions, and
the length-two boundary example. They support the separate uniform proof;
they do not establish generic identification by finite extrapolation.

## Audit and limitations

[The root audit](audits/ROOT_COUPLED_CACTUS_AUDIT_20261030.txt) and
[independent fixture record](evidence/ROOT_INDEPENDENT_FIXTURE_CHECK.json)
are internal **AI-agent** review and calculations, not external peer review
or formal proof verification. Original files are copied without alteration;
their historical “awaiting audit” wording is followed by the included audit.

[The bounded prior-art comparison](PRIMARY_PRIOR_ART_20261030.txt) records
the inherited simple-cycle result and unresolved overlap with Wang et al.
(2018). It updates historical references in the recursive source: the cited
IIC preprint was withdrawn and is not an established theorem to surpass.
No withdrawn-paper counterexample is promoted as this note's result.
Exhaustive priority clearance, arbitrary mixed-graph identification, and
external review remain open.

SOURCE_PINS.json records unchanged source hashes and original
workspace-relative locations. The repository release manifest also covers
this documentation and the wrapper.

