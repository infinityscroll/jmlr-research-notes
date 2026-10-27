# Variance-sensitive row moments and the square-root anchor logarithm for all N

28 October 2026. New analytic source by root, held for independent review.
The argument improves the preceding short-document proof without changing its
estimator. The key is a variance-sensitive moment bound for one degenerate
multinomial document row. No independence between overlapping pairs is assumed.

## 1. Statement and dependencies

Keep the model, notation, instance count R_alpha(d), and observable estimator of
`short_document_sharp_log_upper.md`, SHA256
`db1e141e00097be07ad8d884bbe4bda13b2ad098a32445d5ab0d5847876daf8d`.
In particular

    a=1/sqrt(nN beta)+1/[beta sqrt(nN(N-1))],
    R_alpha(d)=sum_j min(1,d_j/alpha),
    L=log(2+R_alpha(d)), H_a(d)=sum_j min(d_j,a sqrt(d_j)).

**Theorem.** For every N>=2, without condition S3 in that dependency,

    E loss <= C min{1, H_a(d)+sqrt(L)*a/sqrt(alpha)}.        (B1)

Constants depend only on fixed K, mean-prevalence floor mu0, and unnormalized
topic singular-value floor kappa0. The estimator knows K and alpha but not
beta, q, sparsity radius, R_alpha(d), or anchor locations. With fixed columnwise
weak-q radius S_A, the bound becomes

    E loss <= C_{K,q,S_A} min{1,
       F_{q,p}(a) + a/sqrt(alpha)
                          *sqrt(log(2+min(p,alpha^{-q})))}. (B2)

F is the earlier three-regime sparse profile, including its q=1/2 logarithm.
Exact anchors, strong topic geometry and known alpha remain assumptions.
This source proves an upper bound only. Matching lower bounds and historical
novelty are separate questions.

The exact factorial-pair decomposition and second moments come from
`../multitopic_frontier_gate_20261027/root_growing_vocabulary_upper.md`, SHA256
`de3cf1d8af33b58a58ed23a019f49e3d71ac48230af291f0f843c446b3e7cdcd`.
The output-threshold argument remains the one in
`../weak_sparsity_frontier_gate_20261028/observable_conditioning_threshold.md`,
SHA256 `c5bfd6b01e846b238acadbaba1caf9b116c72ed20d86f65c5f6b6e59818712b8`.

## 2. Scalar binomial moments retaining a rare-cell factor

Let B be Binomial(l,pi), lambda=l*pi, and S=B-lambda. For every integer r>=2,

    E |S/l|^r <= C^r [(r*pi/l)^{r/2}
                                   + r^r*pi/l^{r-1}].    (B3)

Here C is universal. A direct proof avoids losing the pi factor.

If lambda>=1, the ordinary scalar Bernstein tail, integrated, gives
`||S||_{Lr}<=C(sqrt(r*lambda)+r)`. Raising this to power r and using
lambda>=1 bounds the result by
`C^r[(r*lambda)^{r/2}+r^r*lambda]`.

If lambda<1, write the integer raw moment through factorial moments:

    E B^r = sum_{k=1}^r Stirling2(r,k) E(B)_k
           <= sum_{k=1}^r Stirling2(r,k) lambda^k
           <= lambda*r^r.

The last bound follows because the number of partitions of r labelled objects
is at most r^r. Also lambda^r<=lambda. Therefore
`E|B-lambda|^r<=2^{r-1}(E B^r+lambda^r)<=2^r lambda*r^r`.
Dividing by l^r proves B3 in this case as well. The zero-probability case is
identically zero.

## 3. Dimension-free vector average moments

Let T_1,...,T_h be independent centered one-hot vectors with the same arbitrary
probability vector pi. For b=h^{-1}sum T_t,

    ||b||_{Lr} <= C sqrt(r/h),    every r>=2.              (B4)

For r<=h, the Hilbert Bernstein bound U2 of the dependency gives
`C(sqrt(r/h)+r/h)<=2C sqrt(r/h)`, since the variance sum is at most 1/h
and summand norms are at most sqrt(2)/h. For r>h, the deterministic bound
`||b||<=sqrt(2)` suffices. There is no dimension-dependent constant in B4.

## 4. One document's degenerate row satisfies Bernstein moments

For one document of length N and categorical law pi, put T_t=Z_t-pi and

    Q=[N(N-1)]^{-1} sum_{s!=t} T_s T_t'.

Its jth row is centered and obeys

    E ||Q_j||^2 <= 2*pi_j/[N(N-1)],
    ||Q_j|| <= sqrt(2).                                  (B5)

We claim that for every integer r>=2,

    E ||Q_j||^r <= r! C^r*pi_j/N^r.                      (B6)

First suppose r<=N. Split the tokens at random into l=floor(N/2) and h=N-l
positions and let a,b be their centered averages. The balanced-half identity
from U8 of the dependency is exact, conditionally on the original tokens:

    Q=E_split[(a b'+b a')/2].

Conditional Jensen and convexity of the rth power norm bound the row moment
by the average moments of a_j b and b_j a. For any fixed split these two
groups are independent. Equations B3--B4 therefore give

    E ||a_j b||^r
       <= C^r [(r*pi_j/l)^{r/2}+r^r*pi_j/l^{r-1}]
                                                       *(r/h)^{r/2}.

Since l,h>=N/3, the first term is at most
`C^r r^r*pi_j/N^r`, using pi_j^{r/2}<=pi_j. Relative to that same bound,
the second term has extra factor at most

    r^{r/2} N^{1-r/2} <= r,   because 2<=r<=N.

Absorb r<=2^r into the universal constant. The transposed expression has the
same bound. Finally `r^r<=e^r*r!` proves B6 for r<=N.

For r>N use B5 directly:

    E ||Q_j||^r <= (sqrt(2))^{r-2}*4*pi_j/N^2.

Since `r!>=(r/e)^r` and r>N, this is at most `r! C^r*pi_j/N^r` after
increasing C. Thus B6 holds for all integer r, not just r small relative to
document length. The rare-cell factor pi_j survives both cases.

## 5. Hilbert Bernstein from the moment condition

For independent centered Hilbert vectors Y_i, suppose

    E ||Y_i||^r <= (r!/2) v_i B^{r-2},  integers r>=2.   (B7)

Let v=sum_i v_i. Then

    P(||sum_i Y_i||>sqrt(2v u)+B u)<=2 exp(-u),
    ||sum_i Y_i||_{Lr}<=C[sqrt(r v)+r B].                (B8)

To see the dimension-free argument, take f(x)=cosh(t||x||), 0<t<1/B.
Its Hessian norm is at most t^2 f(x), and f(x+s y)<=f(x) exp(t s||y||).
Second-order Taylor's formula gives

    f(x+y)<=f(x)+Df(x)[y]
                      +f(x)[exp(t||y||)-1-t||y||].

The centered first-order term vanishes on conditioning. Expand the last
expectation and apply B7 to get the multiplicative factor
`1+v_i*t^2/[2(1-tB)]`. Iterating and using 1+z<=exp(z) yields

    E cosh(t||sum Y_i||)<=exp(v*t^2/[2(1-tB)]).

Chernoff optimization gives B8's tail; integration gives its moment bound.
This is the classical moment-form Bernstein argument in Hilbert space,
spelled out here to identify the required variance-sensitive premise.

Apply B6 with Y_i=Q_i,j/n. Choose a sufficiently large universal C0 so that
B7 holds with

    B=C0/(nN), v_i=C0^2*pi_ij/(n^2 N^2).

The sum of v_i is C0^2*d_j/(nN^2). Consequently

    ||Qbar_j||_{Lr}
        <=C[sqrt(r*d_j/(nN(N-1)))+r/(nN)].              (B9)

Replacing N^2 by N(N-1) only enlarges the displayed first term. The result
holds for nonidentical document laws because B6 is documentwise and the sum
uses their average d_j. The difference from the short-document argument is
the bounded-increment scale 1/(nN), rather than 1/n.

## 6. Completing the estimator bound at the actual diversity

Analyze with actual b=lambda_min(Sigma). Combine B9 with the unchanged
whitened first-order and empirical-frequency moment inequalities. The row
envelope now obeys

    ||delta_j+|dhat_j-d_j|||_{Lr}
       <=C[sqrt(r)*a(b)*sqrt(d_j)+r/(nN b)].            (B10)

The proof of S10 in the short-document dependency, with exactly the same
J_*, R_alpha(d) and L, yields

    E rho<=C[sqrt(L)*a(b)/sqrt(alpha)+L/(nN b alpha)].  (B11)

Its mass-weighted false-inclusion bound S12, deterministic simplex geometry,
spectral event, clipping, normalization, and random observed-eigenvalue cutoff
arguments remain unchanged. In particular the expected thresholded row error
remains H_{a(b)}(d), with no independence assumption for that cutoff. They give

    E loss<=C min{1,H_{a(b)}(d)
                  +sqrt(L)*a(b)/sqrt(alpha)+L/(nN b alpha)}.

Set z=sqrt(L)*a(b)/sqrt(alpha). Because a(b)^2>=1/(nN b), the final term
is at most z^2 for EVERY N>=2. It is absorbed by z when z<=1, and bounded
loss handles z>1. Monotonicity b>=beta proves B1.

Finally S15 of the dependency gives
`R_alpha(d)<=min(p,S*alpha^{-q}/(1-q))` under a fixed weak-q envelope;
its established sparse profile bound gives B2. No short-document condition
is used in this last step or in B6--B11.

## 7. Limits

This removes a proof loss from the full-document upper bound. It does not
remove the unknown-anchor square-root logarithm, prove it necessary for every
N, make maximum-volume search efficient, or remove exact anchors and known
alpha. The constituent moment and concentration methods are classical. The
new claim to audit is their uniform rare-cell application to the degenerate
multinomial row, followed by the existing joint-diversity estimator analysis.
