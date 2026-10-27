# Independent audit of the revealed-sign long-document lower bound

28 October 2026. Root's independent analytic review binds
`unknown_anchor_long_document_lower.md`, SHA256
`7390561c70dea239f91c018446504b240f6246631ce4ede711b2d1e78fd6d7ce`.
The common family and its class membership were separately reconstructed in
`independent_unknown_anchor_lower_audit.md`; no producer source was changed.

**Verdict: no blocker found.** The lower bound holds at its stated
first-order information scale for every N and matches the two-term joint
scale when (N-1)beta>=1. The adjacent short-regime argument is needed for the
remaining document lengths.

The auxiliary information is the generating sign vector, not the actual W.
The sign prior conditioned on E is the same in every hypothesis, while the
parameter map from that sign to W differs between null and alternatives.
Every parameter produced by this prior is legal. Augmenting the data by the
sign can only make estimation easier; indistinguishability in this experiment
therefore supplies a valid lower bound for the original count observations.

Conditional on any fixed sign, the token perturbation for candidate j has
zero sum and is supported only on that pair. Distinct perturbations have
disjoint support. Expanding their one-token likelihood inner product gives
exactly1, not an approximation. For the diagonal, the two opposite word
contrasts give

    chi_i=c_i*kappa^2*r_i^2/(1-r_i^2),

independent of the sign. With c_i=2a*t_i, r_i^2=8beta/t_i^2 and
t_i>=1/(2K), this is at most64K*a*kappa^2*beta, and then at most
2^10 K*a*theta^2*beta. The source's constants are conservative.

For a multinomial count vector the likelihood inner product is the Nth power
of the one-token quantity. Conditional document independence supplies the
product over i. Both the off-diagonal value1 and the diagonal product are
constant in the sign vector, so averaging over the conditioned sign prior
preserves these identities exactly. The proof neither assumes signs remain
independent after conditioning nor pays an unnecessary conditioning error.

The chosen amplitude keeps the cumulative diagonal exponent below
(1/256)log(2+M). The mixture chi-square is consequently the diagonal excess
divided by M, with no cross excess. Concavity gives the stated bound below
1/64. Forgetting the auxiliary sign cannot increase total variation.
The previously checked quotient separation and threshold test then give the
capped risk rate with constants uniform in the varying statistical parameters.

Finally the ratio of the second term of a_n to its first is exactly
1/sqrt((N-1)beta). Thus in the claimed long regime a_n lies between the
first term and twice that term. The conclusion uses the same alpha, beta,
weak-q class and hidden sign family as the short-document lower.

No historical novelty, external expert validation, or broader causal claim
is certified by this audit. No repair is requested.
