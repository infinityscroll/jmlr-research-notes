# Growing vocabulary: an Assouad lower bound and the rare-anchor obstruction

27 October 2026. New analytic candidate by root. Constants below may depend on the fixed topic count K, but not on vocabulary size p, n, N, alpha or beta. This source does not claim historical priority. A separate upper bound and independent review are required.

## 1. Statement

Fix K>=2, set k0=max(1,K-2), and let

    p=K+2+2m, m>=4,
    n>=128(K-1), N>=2,
    0<alpha<=1/(64K), 0<beta<=1/[256K^2 k0].

Consider the same deterministic-mixture multinomial experiment as in general_k_upper.md. Require stochastic topic columns and mixture columns, every mixture weight at least1/(4K), sigma_min(A)>=1/(8sqrt(K)), every Gram entry (A'A)_kl>=1/64, lambda_min(WW'/n)>=beta, and an exact anchor of corpus mass at leastalpha for each topic. Use expected entrywise-L1 loss modulo topic permutation. Write

    G_N=N(N-1)beta^2/[1+(N-1)beta],
    a_n=1/sqrt(nNbeta)+1/[beta sqrt(nN(N-1))].

**Theorem.** The minimax risk over this class satisfies

    R >=c_K min{1,(sqrt(p)+1/sqrt(alpha)) a_n}.       (V1)

The bound remains true if designated anchor identities and their topic-column probabilities are revealed. It is enough to prove two separate lower families: one gives sqrt(p) a_n, the other gives a_n/sqrt(alpha). These families need not coincide, since the supremum over the class is at least the supremum over either family. The sum and maximum of the two displayed terms differ by at most a factor two.

The document count and beta restrictions are deliberately conservative. The theorem covers the displayed arbitrarily large vocabularies; a matching upper bound with only a logarithmic anchor-search gap is stated separately. No sharp constant or dimension-free lower bound for arbitrary growing K is asserted.

## 2. A dimension-uniform nuisance-mixture prior

Use the orthonormal contrast e=(e_1-e_2)/sqrt(2), u=1/K times the all-ones vector, and H={x:x_1=x_2}. For K>=3, cycle

    B_i=u +/- (1/(2K))[e_j-(e_1+e_2)/2], j=3,...,K.

For K=2 simply set B_i=u for every i. In both cases, B_i1=B_i2, all B_ki>=1/(2K), and

    Sigma_B=BB'/n >=c0 P_H,
    c0=1/[8K^2 k0].                                  (V2)

For K>=3 this is the complete-cycle covariance calculation in general_k_lower.md. The n restriction ensures at least half the empirical mass can be extracted as complete cycles. For K=2, Sigma_B=uu' has its sole nonzero eigenvalue1/2, which exceeds c0=1/32.

Let xi_i be initially independent fair signs and define the common, parameter-independent design family

    w_i=B_i+4sqrt(beta) xi_i e.                      (V3)

The coordinate perturbation is sqrt(8beta)<=1/(4K); hence every w_ki>=1/(4K). Condition the sign prior on

    E={||Pi_B xi||^2/n<=1/2},

where Pi_B projects onto the row space of B. As in the earlier lower proof,

    P(E^c)<=2(K-1)/n<=1/64,
    c' Sigma_B^dagger c<=1/2, c=Bxi/n.

The standardized cross block is at most1/sqrt2. Consequently

    WW'/n >=(1-1/sqrt2)min(c0,16beta) I >=beta I.     (V4)

The final inequality uses c0>=32beta. Thus every conditioned sign vector is a legitimate deterministic nuisance parameter, with constants independent of p. All subsequent information calculations use the independent prior before conditioning; the change of data law is handled afterward in total variation.

## 3. A topic hypercube with many genuine word coordinates

Take s0=1/4 and h=7/16. The first two topic columns have first four rows

    (1/16,0), (0,1/16),
    (h+s0,h-s0), (h-s0,h+s0).

For each j=1,...,m add a pair of tail rows

    (b+v_j/(64m), b-v_j/(64m)),
    (b-v_j/(64m), b+v_j/(64m)), b=1/(32m).           (V5)

Here v_j ranges in [-1,1]. The remaining K-2 rows are zero in these two columns. For topic k=3,...,K use

    A_:k=(1/4)e_3+(1/4)e_4+(1/2)e_(2m+k+2).       (V6)

Every column sums to1. All tail entries of the first two topics are at least b/2. Pure anchors are rows1,2 and the extra-topic rows. Their corpus masses are at least1/(64K) for the old topics and1/(8K) for the extras, and therefore exceed the requiredalpha throughout the domain.

The fixed common-word block of the first two columns has least singular value2s0=1/2. For extra-topic coefficient vector t, the extra rows of A z equal t/2. Reconstructing the two old coefficients from the top block exactly as in general_k_lower.md proves sigma_min(A)>=1/(8sqrt(K)), uniformly in m and v. Extra topics share the nonnegative vector (e_3+e_4)/4 of norm at most1/2; this is no larger than the nuisance vector used in that earlier calculation.

All Gram entries have uniform positive floors. The old pair contributes at least2(h^2-s0^2)=33/128>1/64 through rows3,4 alone. Every old-extra entry is h/2=7/32, every distinct extra-extra entry is1/8, and diagonal entries are larger. Tail perturbations cannot reduce these nonnegative contributions.

Take the hypercube v_j=gamma theta_j, theta_j in {-1,+1}, with 0<gamma<=1. For two hypercube points the identity topic matching has L1 distance

    ||A_theta-A_theta'||_1
          =[gamma/(8m)] Hamming(theta,theta').       (V7)

An old-pair swap costs at least2 on rows3,4. Any permutation moving an extra topic costs at least1 on its unique anchor row. Since the identity loss is at mostgamma/8<=1/8, it is always optimal. Thus V7 is also the exact quotient distance. This avoids assuming a fixed topic labeling for an arbitrary estimator.

## 4. Information for changing a single tail coordinate

For each document, its baseline d_i=A_v B_i is independent of the entire vector v because B_i1=B_i2. Its tail masses are all

    d_i,tail=2B_i1 b=B_i1/(16m).

Conditional on xi_i, its token law is

    d_i(1+xi_i b_i,v),
    d_i b_i,v=(4sqrt(beta)/sqrt2)(A_v,:1-A_v,:2).    (V8)

All baseline masses are positive. As the coordinate perturbation in V3 is at most half the relevant baseline mixture weights, max|b_i,v|<=1/2, uniformly over v in [-1,1]^m. More precisely,

    max|b_i,v|^2<=C_K beta,
    E_(d_i)b_i,v^2<=C_K beta.                       (V9)

These constants do not depend on m: the entire tail mass is fixed, and its relative contrast is O_K(sqrt(beta)) even when every v_j is nonzero. For a derivative in one coordinate v_j, only its two tail rows change. Their relative derivative equals +/-sqrt(2beta)/B_i1, by substitution into V5--V8. Hence

    E_(d_i) partial_(v_j)b_i,v=0,
    E_(d_i)[partial_(v_j)b_i,v]^2
           = beta/[4m B_i1] <=C_K beta/m.           (V10)

Also E_(d_i)b_i,v=0. The explicit V10 calculation is included to retain the dimension factor; replacing it by a global worst-case derivative would lose the required1/m.

Marginalize the fair sign for a document of N ordered tokens. Its likelihood relative to d_i^N is the sum of even products of b over token subsets. Differentiating in v_j gives orthogonal components indexed by distinct subsets, because a coordinate in their symmetric difference has mean-zero b or mean-zero derivative. As in L8 of general_k_lower.md,

    E (partial_(v_j)L)^2
       <=2 U N(N-1)V(1+V)^(N-2),
    U<=C_K beta/m, V<=C_K beta.

The likelihood is at least exp(-C_K Nbeta) by the arithmetic-geometric mean bound and V9. For Nbeta<=1, the observed directional Fisher information is therefore at most

    C_K N(N-1)beta^2/m.

For Nbeta>1, revealing the fair sign yields the complete-data information bound2NU<=C_K Nbeta/m. Marginalization can only reduce it. Combining the two regimes gives

    I_(i,N),v_j(v)<=C_K G_N/m                       (V11)

uniformly over every coordinate and every interpolation point v in [-1,1]^m. Counting the ordered tokens cannot increase the relevant statistical distances, so the same upper bound is sufficient for the observed count experiment.

## 5. Conditioning and Assouad's argument

Before conditioning the signs, independent documents give additive directional information. Two neighboring hypercube parameters differ along a path of length2gamma in a single coordinate. The Hellinger path bound and V11 imply

    TV(P_theta,P_theta')
          <=gamma sqrt(C_K nG_N/m).

Choose

    gamma=min{1, [1/(8sqrt(C_K))]sqrt(m/(nG_N))}.

Then neighboring observation laws have total variation at most1/8. Conditioning the common sign prior on E changes either law by at most1/64. Neighboring conditioned laws thus have total variation at most5/32<1/4. Every prior support point is admissible by V4.

For completeness, an arbitrary topic estimator can be decoded to a nearest member of the finite topic hypercube in quotient-L1 distance, with deterministic ties. The triangle inequality implies its loss to the true topic matrix is at least half the decoded hypercube distance. For each bit, pair the other2^(m-1) configurations and use the neighboring-law testing bound: the average bit error is at least(1-TV)/2>=3/8. Summing the bits and applying V7 gives average topic risk at least

    (1/2)[gamma/(8m)] m (3/8)=3gamma/128.

Because these are priors on the stated deterministic-W parameter class, minimax risk is no smaller. Since p=K+2+2m with m>=4 and K fixed, this proves

    R >=c_K min{1,sqrt(p)/(sqrt(nG_N))}.             (V12)

Anchor indices and topic-column masses are constant over this family and can be revealed without affecting the testing problem.

## 6. The rare-anchor family embeds without a vocabulary penalty

For K>=3, start with general_k_lower.md on its p0=K+10 vocabulary. For K=2, use that same displayed two-column A_s construction with a=Kalpha, B_i=u, c0 as in V2 and w_i=B_i+(sqrt(beta)/s)xi_i e. Its proof works verbatim: the only K-2 denominators were in the base-cycle covariance, now replaced by the stronger constant-design rank-one covariance. The present beta and n restrictions imply every earlier positivity, projection-conditioning and spectral bound. The full-document information remains at most C_K alpha G_N per document.

To obtain p>=p0, split ONE of the eight equal padding-word rows into p-p0+1 identical proportional child rows. Their masses sum to the original row in every topic. The new experiment is statistically equivalent to the old one: collapse the children to recover the old word, or independently split each occurrence of that old word uniformly to generate the new observations. This randomization is parameter independent. Topic L1 distances are unchanged by this split.

The fixed main block and unique extra anchors used in the singular-value proof are unchanged; the shared extra-topic vector remains of norm at most1. Thus the same singular-value floor persists. The largest possible decrease of a distinct extra-extra Gram entry is the old row's product(1/20)^2=1/400. It leaves the old1/40 floor at least9/400>1/64. Old-extra and old-old losses from this single row are smaller and do not threaten their displayed floors. Anchor rows and their masses are untouched.

This yields, uniformly in p,

    R >=c_K min{1,1/sqrt(n alpha G_N)}.              (V13)

Finally a_n is within a factor sqrt2 of1/sqrt(nG_N). Combining V12 and V13, and using max(x,y)>= (x+y)/2 with the bounded-loss truncation, proves V1.

## 7. Meaning and remaining work

The sqrt(p) term describes estimating many genuine common-word probabilities; the alpha term describes identifying topic coordinates through rare anchors. The lower constructions have strong topic separation, interior weights and positive full-rank mixture covariance throughout. Neither uses a rank-deficient or zero-weight extra topic. Both use the exact full-document multinomial likelihood rather than a Gaussian approximation.

If the separate proposed growing-vocabulary upper bound is correct, the combined result is minimax up to a logarithmic factor on the anchor-search term, uniformly over document length, rare-anchor mass, weak mixture diversity and the displayed growing vocabularies. This source alone proves only the lower bound and does not establish novelty or that a published open problem has been solved.
