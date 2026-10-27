# Sparse topic recovery with unknown anchor strength and weak document diversity

28 October 2026. Integrated research statement. Both new proof sources have
separate internal analytic reviews. This document does not assert external
validation, historical priority, practical efficiency or a completed general
resolution of the source paper's open problem.

**The advance.** A single estimator can recover sparse separable topics without
being told how rare the anchor words are, how diverse the document mixtures
are, or how sparse the vocabulary is. Its risk separates those difficulties
and retains the correct transition between short and long documents. A
matching constrained-risk lower bound shows that, even with a fixed vocabulary,
the additional cost of adapting to unknown anchor strength is unavoidable on
a two-topic subclass.

## 1. Experiment and common class

Observe independent X_i~Multinomial(N,A w_i), i=1,...,n, N>=2. Columns of
A and W are probability vectors. W is unknown and deterministic, not a
sample from an assumed latent prior. Put Sigma=WW'/n, mu=W1/n and d=A mu.
The loss is expected entrywise L1 distance between A and the estimator,
minimized over topic-column permutations.

For direct comparison with the held sharp known-anchor-strength theorem, fix
K>=2 and q in (0,1), and use its common class C(alpha,beta,q):

- p>=2K+8 and n>=128(K-1), with integer p,n,N.
- Every mixture coordinate w_ki>=1/(4K), and lambda_min(Sigma)>=beta>0.
- sigma_min(A)>=1/(8sqrt(K)), and every entry of A'A is at least1/64.
- Each topic column has weak-q radius at most four:
  max_j j*A_(j),k^q<=4, with entries sorted decreasingly.
- Every topic has an exact pure anchor of corpus probability d_j>=alpha>0;
  the rows and their strength are unknown. Zero unused vocabulary rows are
  allowed.
- alpha<=1/(64K) and beta<=1/[1024K^2 max(1,K-2)].

K and the fixed class constants are available to the estimator. Alpha, beta,
q, W, and anchor identities are not. These assumptions retain strong
unnormalized topic geometry and exact separability; arbitrary diffuse or
nonseparable topics are outside this statement.

Define the effective information and its equivalent error scale

\[
 G_N=\frac{N(N-1)\beta^2}{1+(N-1)\beta},\qquad T=nG_N,
 \qquad a=\frac1{\sqrt{nN\beta}}
             +\frac1{\beta\sqrt{nN(N-1)}}.
\]

Then T^(-1/2)<=a<=sqrt(2)T^(-1/2). For a<1 let

\[
 F_{q,p}(a)=
 \begin{cases}
 a,&q<1/2,\\
 a\log(2+\min\{p,1/a\}),&q=1/2,\\
 \min\{a^{2(1-q)},a p^{1-1/(2q)}\},&q>1/2.
 \end{cases}
\]

Set F=1 for a>=1. All rate constants below may depend on the fixed K,q and
geometry bounds, but not on n,p,N,alpha,beta.

## 2. Adaptive upper theorem

The observable estimator in `joint_adaptive_upper.md` satisfies, simultaneously
over every admissible alpha,beta,q and every N>=2,

\[
 \sup_{C(\alpha,\beta,q)}E\,d_{\rm topic}(\widehat A,A)
 \le C\min\left\{1,
 F_{q,p}(a)+a\sqrt{\frac{\log(2+1/\alpha)}{\alpha}}
 \right\}.                                             \tag{A}
\]

It forms the factorial-pair moment and its top K spectral coordinates. The
observed Kth eigenvalue supplies the noise scale. Each empirical-frequency
normalized row receives a multiplicative uncertainty weight before maximum
determinant selection. Reconstruction uses the selected weighted rows, followed
by the observed-eigenvalue frequency cutoff, clipping and column normalization.
The method is specified in exact arithmetic. Exhaustive maximum-volume search
is permitted; no computational advantage is asserted.

The stronger instance-level theorem replaces F by
H_a(d)=sum_j min(d_j,a sqrt(d_j)) and analyzes the actual unknown
b=lambda_min(Sigma). The main additional proof obligations were:

1. Preserve selection under the unknown spectral change of coordinates.
   Multiplicative row weights do this; additive raw-determinant penalties do not.
2. Control spurious rare words while the coordinate map can have norm C/b.
   The uncapped empirical penalty forces enough observed counts whenever an
   excess error is possible, cancelling that b dependence in the rare-row test.
3. Control the whole reconstructed vocabulary using the same-data random
   output cutoff, without conditioning on it or treating overlapping token
   pairs as independent.

The all-N rare-cell moment estimate is inherited from the previous sharp
joint theorem. The new selection and empirical-penalty proof is separate.

## 3. A matching price of adaptation

For fixed p>=12, K=2 and q=1/2, take even n and beta<=1/4096. Suppose an
estimator not supplied alpha has uniform risk at most C/sqrt(T) on the
strong-anchor subclass alpha_s=1/128. Along ANY sequence T->infinity and
alpha->0, the new constrained lower proves

\[
 \liminf\frac{\sup_{C(\alpha,\beta,1/2)}
                    E\,d_{\rm topic}(\widehat A,A)}
 {\min\{1,\sqrt{\log(1/\alpha)/(T\alpha)}\}}
 \ge c>0.                                               \tag{B}
\]

The estimator may even know beta in this lower theorem. At fixed p the
vocabulary term in (A) is O(a), so (A) satisfies the strong-class requirement
and matches (B) up to constants as alpha weakens. This is a sharp constrained
adaptive rate on this subclass, not an ordinary minimax lower bound for an
estimator supplied alpha, nor a lower bound for every K,q.

The proof pairs the signs of two documents so every nuisance W in the prior
has exactly the required mean and covariance. This avoids a conditioning-error
floor that would invalidate the constrained-risk argument. The full pair of
multinomial count vectors supplies a short-document likelihood second moment
of order alpha*theta^2*N(N-1)*beta^2. Revealing the pair's sign, without
revealing W, gives the long-document scale alpha*theta^2*N*beta. Combining
them yields exp(C*T*alpha*theta^2), after which a classical constrained-risk
inequality establishes (B).

The exact finite checker enumerates 7,840 pairs of count vectors in two
fixtures and checks the full likelihood identities with rational arithmetic.
This checks the delicate identities at finite points; the all-N statement is
the analytic proof, not a conclusion from the enumeration.

## 4. What knowing alpha buys

The unchanged known-alpha theorem has sharp minimax rate

\[
 \min\left\{1,F_{q,p}(a)+a
 \sqrt{\frac{\log(2+\min\{p,\alpha^{-q}\})}{\alpha}}
 \right\}.                                             \tag{C}
\]

At fixed p, its logarithm stays bounded while the adaptive logarithm grows
like log(1/alpha). Equation (B) shows that this difference cannot generally
be removed while preserving the strong-class rate. With sufficiently large
vocabulary, for example p>=alpha^(-q), the two logarithms are comparable for
fixed q, and (A) attains the known-alpha minimax order as well.

At a fixed total token budget m=nN,

\[
 a=(m\beta)^{-1/2}
       \left[1+\{(N-1)\beta\}^{-1/2}\right].
\]

The document-length transition remains at N of order1/beta, subject to the
class's lower bound on n. Adaptation changes the anchor factor, not this
transition. This is a comparison of statistical experiments; it is not a
claim that regrouping an existing corpus preserves its unknown mixtures.

## 5. Evidence and attribution

The new upper and lower sources were reviewed separately by agents other than
their producers. Root also checked the full source-to-source upper composition.
The proof/audit bindings are:

| Result | Proof | Independent review |
| --- | --- | --- |
| Adaptive upper, all fixed K,q and all N>=2 | `joint_adaptive_upper.md` | `root_adaptive_upper_audit.md` |
| Joint weak-diversity constrained lower, fixed p/K2/q1/2 | `paired_sign_constrained_lower.md` | `independent_paired_sign_lower_audit.md` |
| Exact finite full-count identities | `check_paired_sign_identity.py` | `paired_sign_identity_certificate.json` is a computation record, not a proof audit |

The known-alpha rate (C), all-N moment theorem, and fixed-beta adaptation
already existed in the portfolio and are not counted anew. Statistical
penalization, robust simplex recovery, hidden-sign likelihood mixtures and
constrained-risk inequalities have classical antecedents. The candidate
increment is their uniform joint application to unknown rare-anchor strength,
weak unknown document diversity, arbitrary deterministic mixtures and every
document length. A theorem-level comparison with the closest prior results is
recorded separately. External expert review and historical novelty remain
unresolved.
