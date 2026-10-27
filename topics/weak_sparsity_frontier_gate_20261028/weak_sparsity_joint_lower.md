# Fixed-radius weak-sparsity lower bounds with the full diversity/length scale

28 October 2026. Root's new analytic source for independent review. The ordinary weak-sparsity profiles at fixed conditioning are established antecedents, including earlier portfolio results. This proof tracks shrinking mixture diversity jointly with all document lengths and rare anchors. It does not claim historical priority or resolution of every question in the original paper.

Bound dependency: `../multitopic_frontier_gate_20261027/growing_vocabulary_lower.md`, SHA256 `a2f855ed3a2bb1ee5280ba04adce315ee1be07ed877da8c72a7815e729582091`. Its independent review is `independent_growing_vocabulary_lower_audit.md`. The conditioned deterministic-mixture prior and full-document even-subset information argument from that source are reused explicitly below.

## 1. Model and lower theorem

Fix K>=2 and q in (0,1). Let p=K+2+2r with integer r>=4, n>=128(K-1), N>=2, and

    0<alpha<=1/(64K),
    0<beta<=1/[256K^2 max(1,K-2)].

Observe independent multinomial documents X_i~Multinomial(N,A w_i), with unknown deterministic stochastic W. Require each w_ki>=1/(4K), sigma_min(A)>=1/(8sqrt(K)), every Gram entry (A'A)_kl>=1/64, lambda_min(WW'/n)>=beta, and an exact anchor of corpus mass at leastalpha for each topic. In addition impose the SOURCE PAPER'S columnwise weak-q convention, with fixed radius4:

    max_k max_j j [A_(j),k]^q <=4.                    (S1)

The loss is expected entrywise-L1 topic error modulo a permutation. Set

    G_N=N(N-1)beta^2/[1+(N-1)beta],
    e=1/sqrt(nG_N),
    a=1/sqrt(nNbeta)+1/[beta sqrt(nN(N-1))].          (S2)

Then e<=a<=sqrt(2)e. For 0<a<1 define

    F_(q,p)(a)=a,                                      q<1/2;
    F_(1/2,p)(a)=a log(2+min{p,1/a});
    F_(q,p)(a)=min{a^(2(1-q)),a p^(1-1/(2q))},          q>1/2.

For a>=1 set F_(q,p)(a)=1; harmless universal caps can also be applied to the formulas above. **Theorem:** the minimax risk over this class obeys

    R >= c_(K,q) min{1, a/sqrt(alpha)+F_(q,p)(a)}.    (S3)

Constants may depend on fixed K and q, but not p,n,N,alpha,beta. The weak-q radius does not grow with vocabulary size. The lower bound holds even when designated anchor indices and their topic-column probabilities are revealed. Zero-probability unused rows are permitted in the statistical class; positive mass on every possible word is not asserted. The many active tail coordinates in the first lower family are strictly positive.

## 2. A common admissible prior on deterministic mixtures

Use the dependency's construction with u=1/K times the all-ones vector, e0=(e_1-e_2)/sqrt(2), and H={x:x_1=x_2}. For K>=3, cycle the vectors

    B_i=u +/- (1/(2K))[e_j-(e_1+e_2)/2], j=3,...,K.

For K=2 set B_i=u. In both cases B_i1=B_i2, each entry is at least1/(2K), and

    Sigma_B=BB'/n >=c0 P_H,
    c0=1/[8K^2 max(1,K-2)].

Initially take independent fair signs xi_i and set

    w_i=B_i+4sqrt(beta) xi_i e0.

Every mixture entry is at least1/(4K). Condition the signs on

    E={||Pi_B xi||^2/n<=1/2},

where Pi_B is the orthogonal projector onto the row space of B. Its complement has probability at most2(K-1)/n<=1/64. The standardized covariance cross block is at most1/sqrt2, so every conditioned W satisfies

    WW'/n >=(1-1/sqrt2)min(c0,16beta) I >=beta I.

These are the same explicit algebraic identities as V2--V4 of the dependency. The sign event is independent of the topic parameter. The prior is a device for proving a minimax bound over deterministic W; it does not assume iid random mixtures in the model. Product likelihood arguments below occur before conditioning; total variation handles conditioning afterward.

## 3. A nonuniform topic hypercube inside radius4

Put

    b_* = min{(1-q)/32, 8^(-1/q)},
    b_j=b_* j^(-1/q), j=1,...,r,
    T=2 sum_(j=1)^r b_j,
    h=(1-1/16-T)/2, s0=1/4.

The integral bound sum_(j>=1)j^(-1/q)<=1/(1-q) gives T<=1/16 and h>=7/16. The first two columns of A have four core rows

    (1/16,0), (0,1/16),
    (h+s0,h-s0), (h-s0,h+s0),

and for each j a pair of tail rows

    (b_j(1+v_j/2), b_j(1-v_j/2)),
    (b_j(1-v_j/2), b_j(1+v_j/2)), v_j in [-1,1].    (S4)

For each extra topic k=3,...,K use mass1/4 at each of the two common core rows and mass1/2 at its own extra anchor. The first two columns vanish on these K-2 extra rows. All columns are stochastic. Every tail entry of the first two columns is between b_j/2 and3b_j/2.

The common core block has least singular value2s0=1/2. The extra anchor rows reveal their coefficient vector divided by2. The same block reconstruction as in the dependency proves sigma_min(A)>=1/(8sqrt(K)), uniformly in r and v. The two old columns have common-word inner product at least2[(7/16)^2-(1/4)^2]=33/128; old-extra inner products are h/2>=7/32; distinct extras have inner product1/8. These prove every required Gram floor. The anchor corpus masses are at least1/(64K) for the old topics and1/(8K) for the extras, covering the wholealpha domain.

The weak-q radius is uniformly bounded. Each old column has only THREE positive core entries. Its tail's lth largest entry is at most

    (3/2)b_* ceil(l/2)^(-1/q)
       <=(3/2)b_* (l/2)^(-1/q).

For an overall order index t>=4, the tth largest full-column entry is no larger than the (t-3)th largest tail entry, because at most three core entries can precede it. Hence

    t A_(t),k^q
       <=2(3/2)^q b_*^q t/(t-3)
       <=8(3/2)^q/8 <=3/2.

For t<=3, the bound is at most3 because each probability is at most1. Extra topics have three positive entries and satisfy the same radius3 bound. Thus the entire hypercube lies strictly within the fixed radius4 in S1, for EVERY fixed q in (0,1). The choice of b_* becomes small near q=0 or q=1; the theorem's constants may depend on q.

## 4. Information for one tail bit

Take hypercube coordinates v_j=gamma_j theta_j with theta_j in {-1,+1} and amplitudes0<gamma_j<=1. The baseline d_i=A_v B_i is independent of all v because B_i1=B_i2. At the two rows of tail pair j, its mass is

    d_i,tail=2B_i1 b_j.

After marginalizing a fair sign, one document is a mixture of N-token categorical product laws with token probabilities d_i(1+xi_i z_i,v). For the first pair of topics,

    d_i z_i,v=(4sqrt(beta)/sqrt2)(A_v,:1-A_v,:2).

Thus at tail pair j,

    partial_(v_j) z_i,v = +/-sqrt(2beta)/B_i1,
    E_(d_i)[partial_(v_j)z_i,v]^2=8beta b_j/B_i1
                                      <=C_K beta b_j.       (S5)

The perturbation and derivative have zero mean under d_i. Uniformly over the entire parameter box, max|z|<=1/2, max|z|^2<=C_Kbeta, and E_d z^2<=C_Kbeta. The constants are independent of r because the total tail mass is bounded and its relative contrast is O_K(sqrt(beta)).

The exact even-subset likelihood expansion from Section5 of general_k_lower.md now applies with derivative moment U<=C_Kbeta b_j and ordinary moment V<=C_Kbeta. For Nbeta<=1, orthogonality of distinct subset derivatives and the likelihood floor exp(-C_KNbeta) give information at most C_K b_j N(N-1)beta^2. For Nbeta>1, revealing the sign gives information at most2NU<=C_K b_j Nbeta. Combining the ranges yields the uniform directional bound

    I_(i,N),v_j(v)<=C_K b_j G_N.                    (S6)

This uses all N observed tokens exactly and remains valid for nonidentical baselines d_i. It is not a Gaussian approximation or an independence assumption for overlapping token pairs.

## 5. Coordinate-specific testing and the sharp sparse profile

Choose a sufficiently small constant c_K>0 and set

    gamma_j=min{1, c_K/sqrt(nG_N b_j)}.

Before sign conditioning, a Hellinger path of length2gamma_j and S6 bound the total variation of neighboring hypercube observation laws by1/8. After conditioning, it is at most1/8+2/64=5/32<1/4. This holds separately for every coordinate even though its amplitude depends on j.

A differing bit changes four topic entries, each by b_j gamma_j. Thus the identity matching loss is

    4 sum_(j:theta_j!=theta'_j) b_j gamma_j.          (S7)

Its total is at most4sum b_j<=1/8. Swapping the old topics costs2 on the common rows; moving an extra topic costs at least1 on its own anchor row. Identity is therefore optimal for every pair of hypercube points, so S7 is their exact permutation-quotient distance.

Nearest-hypercube decoding of an arbitrary estimator loses at most a factor2 by the quotient triangle inequality. Pairing neighboring configurations gives average error at least3/8 for each bit. Consequently Assouad's elementary testing argument yields

    R >= c_K sum_(j=1)^r b_j gamma_j
      >= c_K sum_(j=1)^r min{b_j, e sqrt(b_j)}.       (S8)

The factor c_K in gamma only changes the universal-in-parameters lower constant. This construction keeps all the anchor indices and masses fixed, so revealing them does not weaken S8.

For clarity, summing the actual power-law sequence in S8 gives, up to constants depending on q and fixed K, the dimension-adapted profiles in S3. Split at J approximately (sqrt(b_*)/e)^(2q). Before J, the sum is e sqrt(b_*) sum j^(-1/(2q)); after J it is b_* sum j^(-1/q). If q<1/2 the first series is bounded above and below by constants, yielding order e. If q=1/2 it is harmonic, yielding e log(2+min{r,1/e}). If q>1/2 it yields order min{e^(2(1-q)), e r^(1-1/(2q))}. The case where J<1 has a positive q-dependent constant lower bound from the first tail coordinate and can be absorbed into the bounded-loss truncation. Since r and p are comparable for fixed K and r>=4, replacing r by p changes only K-dependent constants. Replacing e by a also changes only constants. This proves the F_(q,p) part of S3, including the critical logarithm.

## 6. A sparse rare-anchor lower family

The rare-anchor obstruction can be made sparse without a growing weak-q radius. Put a0=Kalpha and let s vary in [3/16,1/4]. Use first two topic columns with only four possible core rows,

    (4a0,0), (0,4a0),
    (h_s+s,h_s-s), (h_s-s,h_s+s),
    h_s=(1-4a0)/2.

Here h_s actually does not depend on s; the subscript labels the family. Every old column has only three nonzero entries and is stochastic. Give each extra topic mass1/4 on each common row and mass1/2 on its own anchor. Append zero rows to reach p. Every column again has weak-q radius at most3 for every q in (0,1).

Use the B_i from Section2 and w_i(s)=B_i+(sqrt(beta)/s)xi_i e0, with the same conditioning event E. The positivity and covariance calculation is exactly the one in general_k_lower.md: r(s)^2>=16beta, c0>=32beta, and the maximum coordinate perturbation is at most1/(4K) on the stated beta domain. All anchor corpus masses meetalpha. The main old block has least singular value2s>=3/8; the old-old, old-extra and extra-extra Gram floors are larger than those in the dependency because h_s>=15/32 and the extra shared mass is concentrated on the common rows. Thus all geometric conditions persist.

The baseline A_s B_i is independent of s. As before, its only s-dependent sign contrasts occur at the two rare anchor rows; the common-word contrasts are independent of s. Their baseline masses are of order_K(alpha), so the ordinary score moment is O_K(beta) and the derivative score moment is O_K(alpha beta). The exact full-document calculation therefore gives information at most C_K alpha G_N per document. Conditioning costs at most2/64 in a two-point comparison, and the quotient topic distance between s and s+Delta is4Delta. The earlier Hellinger/two-point argument yields

    R >=c_K min{1,1/sqrt(n alpha G_N)}.              (S9)

This family also permits revelation of anchor indices and topic-column masses, which are identical at both hypotheses. Its unused zero rows are explicit; the result makes no positivity claim for those vocabulary entries.

## 7. Combination and significance boundary

Taking the larger of S8 and S9 and using equivalence of a and e proves S3. The maximum of the two capped quantities controls their capped sum within a constant factor. Both lower families lie inside the same fixed-radius weak-q class with all the stated interior-mixture and geometry restrictions.

Combined with a valid upper theorem, this can close the sparse joint frontier up to the displayed anchor-identification logarithm, uniformly in beta and N. It does not create the ordinary weak-q profile: those distribution-estimation rates, including the critical logarithm, are classical and already appear at fixed conditioning in prior portfolio work. The additional proof obligation handled here is their full multinomial transfer with unknown deterministic mixtures while beta weakens, together with a rare-anchor obstruction in the SAME fixed-radius class.

The source paper fixes mixture conditioning and imposes its own anchor-frequency premise. Specializing parameters to that premise requires retaining its exact constants and confidence level; this note does not declare the full published open question solved by an informal substitution. No nonseparable, growing-K, uniform-in-q-endpoints or novelty claim is made.
