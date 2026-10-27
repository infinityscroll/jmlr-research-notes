# Sparse topic recovery with weak anchors and document diversity

This package contains statistical proofs, their dependency chain, and exact algebra checks. It is **not externally peer reviewed or Lean-verified**. “Independent” and “root” audit files are internal reviews by separate AI agents, not human referee reports or novelty clearance.

The main entry points are the [joint adaptive frontier](joint_adaptation_gate_20261028/JOINT_ADAPTIVE_FRONTIER.md), the [computable selector theorem](efficient_joint_adaptation_gate_20261028/design_compression_selector_theorem.md), and the [proof map](PROOF_MAP.md).

## Statistical experiment and result

We observe independent multinomial document counts

$$
X_i\sim\operatorname{Multinomial}(N,Aw_i),\qquad i=1,\ldots,n,
$$

with unknown deterministic document mixtures $W=[w_1,\ldots,w_n]$. The topic count $K$ is fixed. Topic columns and mixture columns are stochastic. The class has exact pure anchors, a fixed positive lower bound on the topic matrix's smallest singular value, and positive mean topic prevalence. The anchor parameter $\alpha$ measures corpus probability; $b=\lambda_{\min}(WW^\top/n)$ measures document-mixture diversity.

Define

$$
a(t)=\frac1{\sqrt{nNt}}+
      \frac1{t\sqrt{nN(N-1)}},\qquad
H_a(d)=\sum_j\min\{d_j,a\sqrt{d_j}\},\quad d=A\bar w.
$$

The adaptive estimator is not supplied $\alpha,b,q,W$, anchor identities, or a sparsity radius. Its expected entrywise $L_1$ error, modulo topic permutation, satisfies

$$
\mathbb E\ell(\widehat A,A)
\le C\min\left\{1,
H_{a(b)}(d)+a(b)\sqrt{\frac{\log(2+1/\alpha)}{\alpha}}\right\}.
$$

This holds for all document lengths $N\ge2$, with constants uniform in $n,p,N,\alpha,b$ under the fixed geometry assumptions. The proof works with the actual factorial-pair statistic; it does not count overlapping token pairs as independent samples.

For a fixed weak-$q$ sparsity class, the ordinary vocabulary term has the profile

| Regime, $0<a<1$ | $F_{q,p}(a)$ |
|---|---|
| $0<q<1/2$ | $a$ |
| $q=1/2$ | $a\log(2+\min\{p,1/a\})$ |
| $1/2<q<1$ | $\min\{a^{2(1-q)},a p^{1-1/(2q)}\}$ |

For $a\ge1$, the risk is capped by a constant. Constants need not stay bounded as $K$ grows or $q$ approaches an endpoint.

## Three distinct conclusions

1. **Known anchor strength:** [the matched all-document-length theorem](anchor_selection_frontier_20261028/MATCHED_ALL_N_FRONTIER.md) gives matching upper and lower rates on its exact common class, with anchor logarithm $\log(2+\min\{p,\alpha^{-q}\})$. Its estimator knows $\alpha$.
2. **Adaptation:** [the joint upper](joint_adaptation_gate_20261028/joint_adaptive_upper.md) removes that input. [The constrained lower](joint_adaptation_gate_20261028/paired_sign_constrained_lower.md) shows the adaptation cost on a fixed-vocabulary, two-topic, weak-$1/2$ subclass: estimators uniformly achieving the strong-anchor rate must incur the displayed weaker-anchor order. This is not an ordinary minimax lower for every adaptive class.
3. **Computation:** [the selector theorem](efficient_joint_adaptation_gate_20261028/design_compression_selector_theorem.md) replaces exhaustive row-tuple enumeration with approximate D-optimal design, support compression, whitening, and greedy projection while retaining the adaptive risk bound. Its guarantee is polynomial **exact-real arithmetic**, with accuracy-dependent cost. It is not a finite-bit stability theorem, a full production implementation, or an empirical speed comparison.

## Restrictions and prior work

The class remains separable: every topic has an exact pure anchor. The topic matrix retains a fixed singular-value floor. The theorem allows weak mixture diversity, not arbitrary simultaneous degeneracy of every geometric parameter. Its sharper lower bounds use the explicit vocabulary, sample-size, interior-mixture, and geometry restrictions in their statements.

Co-occurrence estimation, anchor recovery, SPA, D-optimal design, and constrained-risk inequalities have established antecedents. The candidate contribution is their uniform statistical composition with weakening anchors, weakening document diversity, and all document lengths—not a claim to have invented those mechanisms. Read [the primary subsumption assessment](joint_adaptation_historical_gate_20261028/PRIMARY_SUBSUMPTION_AND_SIGNIFICANCE.md), [the adaptive comparison](joint_adaptation_gate_20261028/primary_joint_adaptation_gate.md), and [the computational comparison](efficient_joint_adaptation_gate_20261028/primary_comparison.md). These are bounded literature checks, not proof of historical priority or a blanket resolution of the source paper's open problem.

## Reproduce the algebra checks

From the repository root, with Python 3.9 or later and its standard library:

```sh
python3 topics/reproduce.py
```

The runner verifies the source manifest, runs the included checks in a temporary copy, and compares regenerated JSON certificates with the saved copies. It leaves the checkout unchanged; no cloud, GPU, package installation, or network is needed. `--list` shows the checks and `--only NAME` selects one.

The checks cover moment identities, finite likelihood calculations, permutation-aware distances, row-selection geometry, and selector algebra. They do not prove the analytical concentration or minimax theorems, and they do not run a topic-model benchmark. [PROVENANCE.json](PROVENANCE.json) records unchanged research sources and hashes. Dated headers saying “awaiting review” are preserved; later internal reviews are separate files.
