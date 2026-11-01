CLASSICAL-INPUT HODGE PROOF AND QUANTITATIVE SIMPLEX CURVATURE
2 November 2026

Start with HODGE_COVARIANCE_AND_SIMPLEX_CURVATURE_WITH_CLASSICAL_INPUTS_20261102.txt.
This is the current successor to ../independent-hodge-covariance-20261102/.
It makes two substantive changes to that independent proof route:

1. The September 2026 regularity-preprint dependency is removed. An exact
   reciprocal change of source/target coordinates puts the required dense
   target class within Colombo--Figalli--Jhaveri's published 2017 theorem.
   Classical reverse transport and local regularity give both Hessian bounds.

2. The argument now proves the finite-simplex normal-strain Hessian bound,
   as well as all-target ordinary-covariance concavity. A rank-one Hessian-
   measure limit and a lower-touching barrier retain the exact curvature
   coefficient through the singular finite-target approximation.

This recovers both covariance-theorem inputs to the existing quantitative
finite-gap lemma. The original chain-complex proof is not used by this route.
The remaining facet-density, Brascamp--Lieb and negative-noise estimates are
still separate inputs. The full named conjecture is not claimed solved.

READING ORDER
The assembled theorem file identifies Modules A--F and their complete sources.
Modules A--B use the Hodge proof and Sections 1--5 of the transfer note in the
previous supplement. The current regularity note replaces its Section 7;
Sections 8--9 provide the unchanged scalar concavity and W2-density arguments.
The new normal_strain/ and normal_strain_audit/ notes prove the finite-target
extension. The regularity_audit/ directory contains independent reviews,
including a final addendum pinning the assembled source after clarifications.

ALGORITHMIC CONSEQUENCE
algorithmic/ENDPOINT_ONLY_TRANSFER_QUANTIFIERS_AND_ERROR_ORDER_20261102.txt
checks that Gaussian optimality at the single voting endpoint already
suffices for the exact fixed-alphabet UGC hardness consequence, using the
credited endpoint analysis. It gives explicit error and influence choices.
The FJ approximation guarantee is randomized in expectation, with high
probability by repetition; no deterministic derandomization is supplied.
This transfer remains conditional on the full negative Gaussian theorem.

VERIFICATION AND STATUS
All source and audit files were copied unchanged. The earlier standard-library
Hodge checker and its 1,603 exact algebra checks remain available in the prior
supplement and in repository CI. There is no new numerical claim here.
These checks do not formally verify the analytic proof. Internal reviews
are not external expert endorsement or an exclusive-priority certificate.
The original main theorem, manuscript PDFs and proof archive are preserved.

ESTABLISHED REGULARITY SOURCE
Colombo--Figalli--Jhaveri, Lipschitz changes of variables between perturbations
of log-concave measures, Ann. Sc. Norm. Super. Pisa (2017), Theorems 1.1,2.2,3.2:
https://doi.org/10.2422/2036-2145.201510_009
