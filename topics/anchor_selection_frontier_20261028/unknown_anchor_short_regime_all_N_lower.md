# Unknown-anchor likelihood correlations for every short-information document length

28 October 2026. New proof by root, held for independent audit. This closes
the weighted likelihood-cross-term seam beyond N=2. The argument uses the
missing-information identity and a twice-centered smooth function, rather
than bounding a signed numerator by a denominator lower bound.

## 1. Model and claim

Use the topic matrices, common sign prior, conditioning event E, and constants
of `unknown_anchor_short_document_lower.md`, SHA256
`a9b2bf464a168958da011917bc1faf52f8c9fa33ef83da9a2333336b6a1cea56`.
Keep its fixed K,q, p>=2K+8, n>=128(K-1), alpha and beta domains, strong
topic geometry, radius-four weak sparsity, and interior deterministic W.
Here N is any integer >=2 satisfying

    N beta <= 2.                                             (C1)

Write a0=4K alpha for the mass of a candidate anchor entry, M for the same
number of candidate pairs, and L=log(2+M). This notation a0 avoids confusing
the anchor entry with the joint estimation scale. As before
`L` is comparable to `Lambda=log(2+min(p,alpha^{-q}))`.

**Theorem.** Under C1 the minimax expected topic error satisfies

    R >= c_{K,q} min{1,
            sqrt(Lambda)/[beta sqrt(n N(N-1) alpha)]}.       (C2)

All constants are independent of n,p,N,alpha,beta. They may depend on K,q.
Combining this with the revealed-sign long-document lower bound covers every
N>=2: if (N-1)beta<1, then N beta<1+beta<=2, so C1 applies. In that case
the joint scale a(beta) is within a factor2 of its degenerate-pair term.
When (N-1)beta>=1, the long-document term is within a factor2 of a(beta).

## 2. Conditional group labels and sign likelihoods

Fix a document i and suppress i. Partition vocabulary into each candidate
pair, the common pair, and individual zero-contrast words. Let G_t be the
group of token t. Each nonzero-contrast pair has equal baseline probabilities
for its two words. Under the null and every alternative, the group masses
are unchanged, independent of the hidden document sign xi. Hence their
joint law is the same multinomial grouping experiment for all hypotheses.

For the moment condition on the complete group-label sequence. On a pair,
write epsilon_t=+1 or -1 for the word selected, and r_g for its positive null
relative contrast. Under the product baseline law, these signs are independent
fair bits. For zero-contrast singletons take r_g=0 and omit their signs.
Candidate groups have r_g=r_i; the common group has r_g=r_i/2.

Conditional on xi, each pair sign has probability
`(1+xi*r_g*epsilon_t)/2`. Put

    H=sum_t atanh(r_{G_t}) epsilon_t,
    Q=product_t sqrt(1-r_{G_t}^2).

The null sign-mixture density relative to the fair-sign baseline is

    F0=Q cosh(H),    P(xi=+1 | data)=e^H/[2 cosh(H)].       (C3)

The construction gives r_i^2<=1/32 and r_i^2<=C_K beta. Thus C1 bounds
`N r_i^2` by a K-dependent constant, even if N itself grows.

For alternative j, only candidate group j changes r_i to (1+kappa)r_i,
where kappa=2theta/(1-2theta), 0<=theta<=1/16. Its COMPLETE likelihood
ratio given xi=+1 or -1, respectively, is

    L_j^+ = product_{t:G_t=j} (1+kappa*b_t^+),
    L_j^- = product_{t:G_t=j} (1+kappa*b_t^-),
    b_t^+ = r_i epsilon_t/(1+r_i epsilon_t),
    b_t^- = -r_i epsilon_t/(1-r_i epsilon_t).              (C4)

The observed likelihood ratio is the posterior average of these two ratios.
The formulas refer to ordered tokens, but every observed ratio is permutation
invariant. Therefore all likelihood integrals below agree exactly for the
actual multinomial count experiment.

## 3. An exact missing-information cross identity

Let j!=k, and put D_j=L_j^+-L_j^- and D_k analogously. Conditional on xi and
the group labels, signs in the two groups are independent and each complete
likelihood ratio has mean1. Their complete cross inner product is therefore1.
Decomposing its conditional product by posterior covariance gives

    E_0[L_j L_k | groups]-1
       = -E_0[p(1-p) D_j D_k | groups]
       = -(Q/4) E_fair[D_j D_k sech(H) | groups].          (C5)

The second equality uses C3 and p(1-p)=1/[4cosh(H)^2]. No sign of the
integrand is assumed. In particular this is not obtained by dropping F0
from a signed cross-likelihood integral.

Let m_j be the number of tokens in group j and H_j=atanh(r_i) times their
sign sum. The fair measure is invariant under flipping every sign in this
group, which exchanges L_j^+ and L_j^-. Consequently

    E_fair D_j=0,    E_fair H_j^2<=C m_j r_i^2.           (C6)

It is the difference D_j that has fair mean zero. The individual complete
likelihood ratios need not have fair mean1.

## 4. A uniform moment bound for the likelihood difference

For independent fair signs in a candidate group, define
`P_m(s)=product_{t=1}^m (1+s b_t^+)`, 0<=s<=kappa. With r=r_i, direct
two-point averaging gives

    E b_t^+=-r^2/(1-r^2),
    E (b_t^+)^2=r^2(1+r^2)/(1-r^2)^2<=C r^2.

Put A_s=E(1+s b_t^+)^2. Because E b_t^+<=0,
`A_s<=1+C s^2 r^2`; also `|E[b_t^+(1+s b_t^+)]|<=C r^2`.
Expanding the square of the derivative gives, for m>=2,

    E |P_m'(s)|^2
      =m E b^2 A_s^{m-1}
        +m(m-1){E[b(1+s b)]}^2 A_s^{m-2}
      <=C (m r^2+m^2 r^4) exp(C kappa^2 m r^2).          (C7)

For m=1 only the first term occurs; for m=0 the derivative is zero. Since
m r^2<=N r_i^2<=C_K under C1, C7 is at most C_K m r^2 uniformly in s.
The minus-sign product has the same moment bound by fair-sign symmetry.
Both products equal1 at s=0. Integrating their derivative difference in L2
therefore yields

    E_fair D_j^2 <= C_K kappa^2 m_j r_i^2,
    E_fair |D_j H_j| <= C_K kappa m_j r_i^2.             (C8)

The latter follows from C6 and Cauchy--Schwarz. It also holds when m_j=0.

## 5. Twice centering retains the second rare-group factor

Write H=H_out+H_j+H_k. The two groups and the remaining signs are independent
under the fair measure. For f=sech, ||f''||_infinity is bounded by a universal
constant. Using E D_j=E D_k=0, subtract three zero-integral terms to write

    E[D_jD_k f(H)]
      =E D_jD_k { f(H_out+H_j+H_k)-f(H_out+H_j)
                         -f(H_out+H_k)+f(H_out) }.

The expression in braces has absolute value at most C|H_j H_k| by the
integral form of the mixed second difference. Equations C5 and C8, Q<=1,
and independence of the two groups therefore imply

    |E_0[L_j L_k | groups]-1|
          <=C_K kappa^2 m_j m_k r_i^4.                 (C9)

Each candidate pair has unchanged group mass c_i=2a0*t_i. For distinct
groups, E m_j m_k=N(N-1)c_i^2. Since
`t_i^2 r_i^4<=256K^2 beta^2`, averaging C9 gives

    |E_0[L_j L_k]-1|
          <=C_K a0^2 theta^2 N(N-1) beta^2.             (C10)

This is the required extra a0 factor over a diagonal bound. The bound permits
negative individual cross corrections; the later product argument only uses
their displayed upper bound and nonnegativity of likelihood inner products.

## 6. The diagonal has the expected weak-information scale

Here the squared likelihood difference is nonnegative, so a denominator lower
bound is legitimate. Return to the full product baseline word law d_i^N.
For any contrast vector z define

    F_z=(product_t(1+z(X_t))+product_t(1-z(X_t)))/2.

All contrasts have baseline mean zero. Thus with
`g_N(s)=((1+s)^N+(1-s)^N)/2`, independence of baseline tokens gives

    E_d F_z F_w=g_N(sum_x d_i(x) z(x) w(x)).             (C11)

Put V=sum d_i z_i^2<=C_K beta and u=c_i r_i^2<=C_K a0 beta.
Changing only group j multiplies its contrast by1+kappa. Therefore

    E_d(F_j-F0)^2
      =g_N(V+(2kappa+kappa^2)u)-2g_N(V+kappa u)+g_N(V).

For 0<=s<=C_K beta the elementary derivative bounds are

    |g_N''(s)|<=C_K N(N-1),
    |g_N'(s)|<=C_K N(N-1) s,                            (C12)

under C1. They follow directly from the binomial formula, bounding
`(1+s)^{N-2}` by exp(Ns) and integrating g_N'' from0, where g_N'(0)=0.
All s actually used are below1; the original r_i^2 bound also shows this.
Split the preceding finite difference into a step of length kappa^2 u and
a second difference of step kappa u. Equations C12 yield

    E_d(F_j-F0)^2
       <=C_K N(N-1) kappa^2 (u beta+u^2)
       <=C_K a0 theta^2 N(N-1) beta^2.                  (C13)

Pointwise F0>=Q>=exp(-C_K N beta)>=c_K>0 by r_i^2<=1/32 and C1.
Dividing the NONNEGATIVE squared numerator by F0 therefore gives

    E_0(L_j-1)^2<=C_K a0 theta^2 N(N-1) beta^2.          (C14)

Constants c_K,C_K may be small or large but are uniform in every varying
statistical parameter. No Gaussian approximation is used.

## 7. Product experiment, conditioning and testing

Before conditioning the latent signs on E, documents are independent. The
candidate groups are symmetric, and C10--C14 hold uniformly across documents.
For a uniform mixture over M alternatives, take a fixed sufficiently small
c_K>0 and

    theta=c_K min{1,
            sqrt(L/[n a0 N(N-1) beta^2])}.              (C15)

Choose c_K also so that theta<=1/16 and the cumulative diagonal and
off-diagonal bounds are at most epsilon L and epsilon a0 L respectively,
where epsilon=1/256. Products of the cross inner products are then bounded
by the corresponding exponentials, regardless of the signs of their
corrections. The same exact null-versus-mixture expansion as in A18 gives

    chi-square(P_bar,P_0)
      <=[(M+2)^epsilon-1]/M+exp(epsilon*a0*L)-1<1/64.

The last inequality uses a0*log(2+M)<=1/4, already proved for the unchanged
candidate family. Conditioning the common sign prior on E changes each law
by at most1/64; the total-variation bound is therefore at most3/32. Every
conditioned W is an admissible deterministic nuisance parameter.

The unchanged quotient separation from A0 is at least2b*theta. The same
threshold test gives minimax risk at least c*theta. Substituting a0=4K alpha
and the comparison of L with Lambda proves C2. This is a full multinomial
document lower bound, not a sum of allegedly independent pair experiments.

## 8. Scope

The missing-information calculation supplies the rare-location cross bound
that the N=2 formula alone could not justify. It complements, rather than
replaces, the simpler revealed-sign long-document proof. All generic tools
used here—likelihood mixtures, posterior covariance, and smooth centering—are
classical. Correctness review and a theorem-level historical comparison remain
required before attaching novelty or significance to the resulting matched
joint frontier.
