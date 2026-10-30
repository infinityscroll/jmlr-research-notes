# Gaussian polynomial independence: extremal critical fibers

This scoped analytic note concerns two real polynomials \(f,g\) on
\(\mathbb R^n\), evaluated at a standard Gaussian vector \(X\).

Suppose that for one real value \(c\), the **entire** critical set

\[
K=\{x:f(x)=c,\ \nabla f(x)=0\}
\]

is nonempty and compact, and every point of \(K\) is a local minimum of \(f\).
If \(f(X)\) and \(g(X)\) are independent, the theorem concludes that \(g\) is
constant. The same conclusion holds when every point is a local maximum.

The Hessians may be completely degenerate and \(K\) may have positive
dimension. The full level set \(f^{-1}(c)\) need not be compact. The condition
concerns the entire critical set at that value, not a selected component.
Both observables are polynomials of Gaussian input; neither is assumed to
have a Gaussian output law.

## Proof and audit

Read [the complete analytic proof](proofs/DEGENERATE_EXTREMAL_CRITICAL_FIBER_20261031.txt)
and [the root mathematical audit](audits/ROOT_DEGENERATE_EXTREMAL_FIBER_AUDIT_20261031.txt).
The proof uses a sign-definite high-moment witness, a semialgebraic
nonstationary estimate at infinity, and a contradiction between smooth
one-sided flatness and a polynomial lower bound on local mass. It includes
a degenerate nonproper example and a limited independence-pencil obstruction.
The nonstationary justification is written out here; its reference to the
earlier Morse note is contextual, not an omitted proof dependency.

The source and audit are preserved verbatim. The source's initial
“independent audit requested” status is followed by the completed audit.
This was internal **AI-agent** review, not external peer review or formal
proof verification.

## Verification and limits

This is an analytic result. No finite numerical test is presented as a
verification of the theorem. The repository release manifest checks the
integrity of the proof, audit, and documentation. From the repository root:

~~~sh
python3 verify_release.py
~~~

There is deliberately no additional polynomial-fixture test for this note.

The full Gaussian polynomial U-conjecture remains unresolved. Indefinite or
mixed-sign critical germs, noncompact critical sets, and everywhere-submersive
pencils are outside the argument.
[The bounded historical comparison](PRIORITY_COMPARISON_20261030.txt)
predates this degenerate extension and records unresolved comparison with
older Kagan–Linnik–Rao material and saddle-point methods. It is context,
not priority clearance for this lemma. No historical novelty or full
conjecture resolution is claimed.

