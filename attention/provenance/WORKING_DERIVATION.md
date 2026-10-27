# Coupled original queries: selected-path failure candidate

28 October 2026. Working derivation only. No invariant-basin or asymptotic theorem is yet claimed. This investigates the exact selected-query metric, not the easier lower all-query margin.

## Exact architecture and coordinates

Take `x1=(1,0)'`, `x2=(delta,1)'`, `0<=delta<1`, `d=x1−x2`, `D=1−delta`, `s=||d||²`. The positive example has these two tokens, head `w=e1`, and final query1. Its negative copy has tokens `−x1,−x2` and label−1; the two signed predictions and parameter gradients agree. Both complete direct matrices W1,W2 train with the released unnormalized p=2 update (ordinary simultaneous gradient descent in these coordinates). Values and head are fixed identities/e1; no residual, mask, detachment or memory replacement occurs.

Write `l_r=x_r' W1 d`, `a=sigmoid(l1)`, `b=sigmoid(l2)`, `h1=x2+a d`, `h2=x2+b d`, `k=W2 d`, `m=(a−b)h1'k`, `pi=sigmoid(m)`. The signed prediction and logistic loss are exactly

    f=delta+D c,    c=b+pi(a−b),    L=log(1+exp(−f)).

Let `Q=1/(1+exp(f))`. Differentiating the actual evolving query, keys and values gives

    c_a=pi+pi(1−pi)[m+(a−b)^2 d'k],
    c_b=(1−pi)(1−pi m),
    A=a(1−a)c_a,
    B=b(1−b)c_b.

The full matrix gradients and simultaneous updates therefore are

    grad_W1 f=D(A x1+B x2)d',
    grad_W2 f=D(a−b)^2 pi(1−pi)h1 d',
    W_l^+=W_l+eta Q grad_W_l f.

Thus, with `rho=eta Q D s`,

    Delta l1=rho(A+delta B),
    Delta l2=rho(delta A+(1+delta²)B),
    Delta k=rho(a−b)^2 pi(1−pi)h1.

These equations include the upper query derivative. The reduction uses only the exact two-token softmax identity and has no gradient-flow substitution. All coordinates orthogonal to the right factor d remain at their finite initial values; they are present and trainable, and are irrelevant to the full-space token comparisons too.

Two exact linear combinations isolate positive and negative clocks:

    Delta[l1−delta l2/(1+delta²)]=rho A/(1+delta²),
    Delta[l2−delta l1]=rho B.

When `a>b`, `d'k>=0` and `m` is large enough that `pi m>1`, A>0 and B<0. This gives monotonicity of those combinations, NOT of l1 and l2 separately. Treating the two rows as independent is the old one-hot proof's invalid step after this perturbation.

## Candidate asymptotics and actual comparator

The candidate is `a->1`, `b->0`, `k/||k||->e1`, with

    l1~log t,    l2~−log log t.

If these relations hold, then the first column-coordinate vector `W1 d` is asymptotic to `(1,−delta)' log t`, because `l1=(W1d)_1` and `l2=delta(W1d)_1+(W1d)_2`. Consequently

    W1/log t -> (1,−delta)' d'/s.

The lower **selected-path** SVM has the single full-matrix constraint `x1' W d>=1`; its exact global Frobenius minimizer is `x1 d'/s`. The candidate normalized margin fraction is therefore

    1/sqrt(1+delta²),

strictly below one for delta>0. This differs from the old noncollapse example, where only the all-query comparator failed. The upper checkpoint normal is `h1(h1−h2)'` and tends to `x1 d'`; its optimal unit-norm margin stays `sqrt(s)>0` if the candidate noncollapse is proved. The fixed data remain nonsingular and both lower memories are used as upper key/value rows.

The missing step is an actual finite invariant basin and discrete proof of feature convergence and the competing clocks. The candidate asymptotics are not assumptions of a theorem here. In particular a pointwise negative B need not make l2 decrease, and an upper key weight going to zero does not imply its accumulated lower gradient is negligible.

## Fixed diagnostic protocol, before observing outcomes

One bounded local CPU diagnostic uses delta=0 and delta=1/2, eta=.1, p=2, 50,000 simultaneous steps, balanced positive/negative examples, and exact initial logits `(l1,l2)=(4,−4)` with `k=(4,0)'`. Choose minimum-Frobenius matrices implementing these coordinates, i.e. `W1=X^(-1)(4,−4)'d'/s` and `W2=4e1 d'/s`. There are no randomized starts, tuning loops, stopping rules based on outcomes or additional steps. Save all prespecified logarithmic checkpoints, both full matrices, actual matrix forwards, exact selected-path margin fractions and the reduced-interface residuals. The unchanged released optimizer is used. This is a diagnostic of a candidate mechanism, not evidence proving its limit or an open basin.

Internal antecedents read: `noncollapse_architecture_gate_20261028/no_residual_open_basin.md`, its `input_perturbation_boundary.md`, `noncollapse_frontier_gate_20261028/moving_memory_noncollapse_restoration.md`, and `interior_row_cancellation_boundary.md`. The new seam is the nonorthogonal query Gram matrix, not another unused-query comparison.
