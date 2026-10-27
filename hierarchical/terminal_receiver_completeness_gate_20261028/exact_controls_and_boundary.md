# Exact controls for the terminal-receiver theorem

28 October 2026. These are finite checks and scope controls, not additional graph-wide theorems. The source `separated_receiver_completeness.md` remains unchanged at SHA256 `9b6d81b482c7fbf5b63e703d20e5e6af4a12bea865ac48341b3b4d7c7f15f2ce`.

## 1. Positive identified, changed, nonreset response

The original kernels are T12 in the theorem. Direct enumeration of the hidden subunit H and independent reconstruction of the front-door functional from each observed q agree for both hard A values and the positive soft policy. The four natural receiver inputs are

    21/64, 41/128, 27/64, 55/128.

The two policy inputs are 21/64 and 27/64. Each has positive natural probability. Neither is an unsupported extrapolation, and the policy input is not constant across units. With the illustrative nonlinear receiver k(s)=1/4+s^2/2,

    natural risk = 21077/65536,
    policy risk  = 2633/8192 = 21064/65536,
    change       = -13/65536.

The response function is not an oracle input to the theorem: its values at these policy inputs are natural observed conditionals. This example uses front-door identification, which is classical; it checks the HCM support and unit-outcome composition.

## 2. Positive nonidentification reaches an original unit outcome

Let a,z,h be signs. A hidden fair subunit root H parents A and Z, and A parents Z. An independent fair private unit flag t controls A. In model sigma in {−1,+1},

    P(A=a|h,t) = 1/2 + t a h/4,
    P_sigma(Z=z|a,h) = 1/2 + sigma z(1/32-a h/8).

At t=0 the entire A table is the queried fair policy. It has natural probability one half. All cells are positive. Integrating H gives

    q_(sigma,t)(a,z) = [1+sigma(1-2t)z/16]/4.

The natural table laws are the same equal mixture of q_+ and q_−. Append an observed unit Y receiving Z, with the same kernel k(s)=1/4+s/2 in both models. The complete natural law of (Q_(A,Z),Y) remains identical. Under the actual policy, unit risks are 31/64 and 33/64, gap 1/32.

For a finite record use k at the empirical Z-success frequency. The checker verifies 168 complete record/outcome atom equalities for record sizes 1,2,3. The general equality for every record size follows directly from the common conditional channel, not from these finite counts.

## 3. Separate input laws do not require identification of their union

Take observed subunits A,D1,D2 with the sole directed arrow A->D2 and bidirected chain A<->D1<->D2. The two pairwise hidden roots are independent: H1 is a fair sign and H2=(H_i,H_o) is uniform on four sign pairs. A has its own independent fair unit switch t. Set

    P(A=a|H1,t) = 1/2+t a H1/4,
    P_sigma(D1=b|H1,H2)
        = 1/2+sigma b(H_i/16-H1 H_o/16),
    P(D2=d|A=a,H2)
        = 1/2+d(H_i/16+a H_o/4).

All local cells are at least 3/16. The exact joint is

    q_(sigma,t)(a,b,d)=1/8+sigma(1-2t)bd/512.

The full natural table laws agree, and the whole fair A policy has support one half. Under it the parity event D1=D2 differs by 1/64 across the models, so the joint input law is not identified. Yet each separate marginal is fair in the pair. Graphically, D1 has no directed action path; for D2, the path A<->D1<->D2 is blocked at the collider D1 without conditioning, so its marginal is identified by adjustment with the empty set.

Consequently two terminal receivers, one receiving D1 alone and one receiving D2 alone, do not receive this unidentified within-subunit joint. For the full model class their two post-policy marginal laws are simultaneous known functions of the same observed q. Any separated terminal response block of their *received marginal laws* is covered by T3. A single receiver with both D1 and D2 as subunit parents receives their joint and can expose the ambiguity through T9.

This illustrates the exact criterion's per-receiver input sets. It does not claim the elementary marginal-versus-joint distinction is new.

## 4. Exact obstruction to dropping the receiver separator

This control reconstructs an ordinary confounded bow; it is not a new causal counterexample.

Let an upstream hidden unit U be a fair sign. A binary subunit A has numerical success table S_r=1/2+r/4, r in {−1,+1}, with

    P(R=r|U=u)=1/2+ru/4.

The queried whole policy is pi(A=1)=3/4, or r=+1, with conditional support at least 1/4. An observed unit Y receives A and also U. At the two natural inputs its conditional sign mean in model j is

    E_j[Y|u,S_r]=v_j r+w_j u,
    (v_0,w_0)=(1/8,1/4), (v_1,w_1)=(3/16,1/8).

Use r(s)=clip(4s-2,-1,1) elsewhere to obtain a continuous positive receiver kernel. This gives local outcome cells at least 5/16, and physical A cells at least 1/4.

Both models have exactly the same complete limiting natural law

    P_j(R=r,Y=y)=[1+yr/4]/4.

Under the policy their risks are 9/16 and 19/32. The receiver input law under pi is known exactly: the point mass at 3/4. It is also supported naturally. Nevertheless the common observed conditional at that input is 5/8, different from both actual policy risks.

Thus knowing and supporting S^pi does not justify using P(Y|S) when a latent unit cause selects S and also enters Y. This pinpoints the failure of T7 if the graph separator is removed. It does not attack T6, and it does not show the source authors' complete augmentation toolbox fails.

## Reproducibility

Run `python3 check_receiver_closure.py`. The script uses only Fraction arithmetic and standard-library enumeration. It records its own and the theorem's SHA256, direct kernel calculations, independent front-door reconstruction, finite-record equality, and the shared-cause and separate-input controls in `receiver_closure_certificate.json`. These checks validate the displayed fixtures and their interpretation. They do not certify historical novelty or replace the general proof.

