# Independent analytic audit of the p=3/2 selected-path theorem

28 October 2026. Hostile source-level review by hcm_adversarial_boundary.

**Bound source:** `p_three_halves_dynamics.md`, SHA256 **262392416101c3332a636c66ddc3df899ff1ca3bba9e303b5e0e7b2f1571e23d**.

**Verdict:** no mathematical blocker or source repair requested within the stated architecture and quantifiers. This review reconstructs the non-Euclidean proof directly; it does not infer correctness from the Euclidean result. No producer file was changed and no new training trajectory was run.

## 1. Native update, full gradient and dual closure

Reread the held released `SMD` implementation. With normalize=False it performs exactly the entrywise dual subtraction and inverse signed power in N2, with no extra normalization or factor p. The full attention derivatives in N6 contain both the moving upper-query term and the negative upper-key term. The paired-sign mean loss supplies the single-example gradient without an extra factor two.

Every dual increment, not every primal increment, has right factor d'. The Euclidean projection defining r_l and E_l consequently makes E_l constant. Nonzero E_l is allowed. This is the appropriate replacement for the p=2 primal rank-one-plus-constant reduction.

## 2. Exact offset identity and signs

For a row, under the stated large-r sign condition,

    sum_j d_j J_3(r d_j+E_j)
       =sign(r)[c r²+2r sum_j |d_j|d_j E_j
                       +sum_j |d_j|E_j²].

Completing the square proves N8 with exactly the printed h(E). The extra d_j in its numerator is essential. Weighted Cauchy–Schwarz with weights |d_j| proves e(E)>=0. Differencing the fixed-sign polynomial gives N9, including the sign of its quadratic term for a negative row.

The working region implies q_lower,1=s-x>0 and q_lower,2=-delta s-log s+O(1)<0. The first upper row has projection s>0. Since offsets are uniformly bounded, sufficiently large R forces all three dual-row signs and every involved entry sign without assuming a rank-one initialization. The bounded upper second row is correctly exempt from this argument.

## 3. Finite-step mobility and reduced field

The exact square roots in N12 give the lower-to-upper mobility ratios 1+O(1/s) and sqrt(delta)+O(log s/s). The logarithm is required because the lower second projection includes -log s. All offset remainders are uniform for the fixed compact E bound.

N13 follows from the exact forward expressions and bounded k_2. Independently, that bound is

    sum_j |d_j|(2|d_j|+1)² = 219/16 < 14.

For a complete step, each large-row dual increment is O_eta(exp(-s)), so it cannot approach or cross a large-row sign boundary. N9 therefore applies to the actual update. Its upper leading mobility is 2 sqrt(c) sqrt(s), with alpha=eta Q(3/4); no Euclidean ||d||² factor belongs in alpha. The squared increment divided by Delta s is O_eta(exp(-s)/sqrt(s)).

This yields the printed lower logit ratios and the reduced field

    F1=1-u+v/4, F2=v(u/4-9v/16), u=exp(x-v).

At the equilibrium v*=1/2,u*=9/8, its Jacobian is N16. Direct rational algebra checks J'P+PJ=-I. P-I/10 is positive definite and trace(P)<5. The conservative local Hessian remainder and the very small working ellipsoid make the stated negative Lyapunov drift valid.

## 4. Coupled discrete basin, especially the transverse dual row

The exact ratio in N18 follows by factoring alpha U from both the transverse increment and N14:

    Delta(r_2)_2/Delta s
      =epsilon/[2c T(1-D epsilon)+c alpha U(1-D epsilon)²].

It is nonnegative and O(exp(-s)/sqrt(s)) uniformly on every stopped prefix. With Delta s<=1, its sum is controlled by a constant multiple of the corresponding integral. This bounds total transverse dual motion by less than one after choosing finite R. No smoothness, fixed sign or rank-one assertion about that row is needed.

The Lyapunov annulus argument includes the finite-step overshoot check from the inner ellipsoid. The E coordinates are conserved and s is strictly increasing. These three controls close the first-exit induction simultaneously, before any limit is assumed.

N19 is a nonempty open set of all eight primal entries. The signed-power maps are continuous even at zero; differentiability there is not needed for openness. The example with E=0 only supplies one interior point. Every condition in N19 is strict and remains valid under sufficiently small arbitrary matrix perturbations.

## 5. Convergence and exact logarithmic clocks

A bounded s contradicts N14's positive lower increment bound. Thus the total s-clock diverges. The vanishing-forcing scalar recursion from N17 proves y->0 even without summability of log(s)/s in that clock. N18 gives absolute convergence of the upper transverse dual row and hence convergence of its whole finite primal row.

The exact increment of G(s)=exp(s)/sqrt(s) tends to the printed positive K. Cesaro averaging gives N20, including the +1/2 loglog n correction in s and l1 and the -loglog n term in l2. Inverting G first yields s/log n->1 and then the additive constants; no continuous-time approximation is needed.

Expanding each large primal row gives its leading projection-minimizing row plus O(sqrt(s)). That error need not stay bounded, but it vanishes after division by log n. Thus conserved dual offsets do not produce an omitted leading matrix component.

## 6. Full lp comparator and official Bregman order

Holder's rowwise equality gives the unique full-space minimizer e1 J_3(d)'/c. The trained limit has row projections (1,-delta), so the margin fraction is exactly

    (1+delta^(3/2))^(-2/3)=(8/9)^(2/3).

This is neither a factorized comparator nor an all-query surrogate. The alternative problem with the extra x2'Wd<=0 constraint is explicitly kept separate; it has minimum row projection (1,-delta).

I checked the actual released `correlation_calculation.py` call: it passes `bregman_correlation(att_svm, Ws[it], p)`. The released function normalizes both arguments in lp and computes the corresponding power-potential divergence. Thus the official order is SVM first, trained second, giving

    1-(1+delta^p)^(-(p-1)/p)=1-(8/9)^(1/3),

as printed in N5. Reversing the arguments gives 1-(8/9)^(2/3); the source correctly distinguishes them. The upper actual comparator tends to a nonzero normal and its normalized optimal direction matches N3.

## Limits

The result is a non-Euclidean selected-path failure in genuinely coupled two-layer self-attention with distinct limiting memories. It remains a fixed-head, identity-value, two-token paired-sign, p=3/2 theorem with a sufficiently large finite favorable basin. It provides no random/small-start guarantee, no independently perturbed multi-example data neighborhood, and no generalization claim. This audit neither establishes historical novelty nor refutes the published one-layer result.

