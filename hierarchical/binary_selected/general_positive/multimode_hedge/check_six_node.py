#!/usr/bin/env python3
"""Exact finite-sum check of actual positive CPTs, not a rank certificate.

The six-node graph has no routing-compatible hedge. Every observed variable is
binary; the four original edge latents each have four states (two fair bits).
Run with stdlib Python. No external packages, network, or random numbers.
"""
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import hashlib
import json

HERE = Path(__file__).resolve().parent
NAMES = ("U", "A", "R", "Z", "B", "Y")
HIDDEN_EDGES = (("U", "R"), ("A", "Y"), ("R", "Y"), ("U", "B"))
PARENTS = {
    "U": ("H0", "H3"),
    "A": ("U", "H1"),
    "R": ("H0", "H2"),
    "Z": ("R",),
    "B": ("A", "Z", "H3"),
    "Y": ("B", "H1", "H2"),
}
T = Q(3, 16)
LAM = T ** 5


def hidden_sign(state, mode):
    return 1 - 2 * ((state >> mode) & 1)


def prob_plus(model, node, env):
    """Only the listed observed/hidden parents are read at each node."""
    def h(edge, mode):
        return hidden_sign(env[f"H{edge}"], mode)
    if node == "Z":
        return Q(1, 2) + Q(1, 4) * env["R"]
    if model == "outer":
        if node == "U":
            return Q(1, 2) + T * (h(0, 0)*h(3, 0) + h(0, 1)*h(3, 1))
        if node == "A":
            return Q(1, 2) + T * env["U"] * (h(1, 0) + h(1, 1))
        if node == "R":
            return Q(1, 2) + T * (h(0, 0)*h(2, 0) + h(0, 1)*h(2, 1))
        if node == "B":
            return (Q(1, 2) + Q(1, 4)*env["Z"]
                    + T/Q(32)*env["A"]*h(3, 0)
                    + T/Q(64)*env["A"]*env["Z"]*h(3, 1))
        if node == "Y":
            return Q(1, 2) + T*(h(1, 0)*h(2, 0) + env["B"]*h(1, 1)*h(2, 1))
    if model == "inner":
        if node in ("U", "A"):
            return Q(1, 2)
        if node == "R":
            return Q(1, 2) + T*h(2, 0)
        if node == "B":
            return Q(1, 2) + Q(1, 4)*env["Z"]
        if node == "Y":
            return Q(1, 2) + T**4/Q(4)*env["B"]*h(2, 0)
    raise AssertionError((model, node))


def rational(q):
    return str(q.numerator) + "/" + str(q.denominator)


def make_tables(model):
    result = {}
    lookup = {}
    denominators = {}
    from math import lcm
    for node in NAMES:
        rows = []
        values = {}
        ranges = [range(4) if p.startswith("H") else (-1, 1) for p in PARENTS[node]]
        for pa in product(*ranges):
            q = prob_plus(model, node, dict(zip(PARENTS[node], pa)))
            assert Q(1, 8) <= q <= Q(7, 8), (model, node, pa, q)
            values[pa] = q
            rows.append({"parent_values": list(pa), "p_plus": rational(q)})
        d = lcm(*(q.denominator for q in values.values()))
        lookup[node] = {pa: int(q*d) for pa, q in values.items()}
        denominators[node] = d
        result[node] = {"parents": list(PARENTS[node]), "rows": rows,
                        "integer_denominator": d,
                        "minimum_cell": rational(min(min(q, 1-q) for q in values.values()))}
    return result, lookup, denominators


def enumerate_model(model):
    tables, lookup, denominators = make_tables(model)
    denom = 4**4
    for node in NAMES:
        denom *= denominators[node]
    observed = {}
    targets = {-1: [0, 0], 1: [0, 0]}
    intervention_joint = {-1: {}, 1: {}}
    for x in product((-1, 1), repeat=6):
        env0 = dict(zip(NAMES, x))
        obs_num = 0
        do_num = 0
        for h in product(range(4), repeat=4):
            env = dict(env0, **{f"H{i}": h[i] for i in range(4)})
            full = 1
            truncated = 1
            for node in NAMES:
                pnum = lookup[node][tuple(env[p] for p in PARENTS[node])]
                value = pnum if env[node] == 1 else denominators[node] - pnum
                full *= value
                if node != "A":
                    truncated *= value
            obs_num += full
            do_num += truncated
        observed[x] = Q(obs_num, denom)
        action = env0["A"]
        p_do = Q(do_num, denom // denominators["A"])
        intervention_joint[action][tuple(env0[n] for n in NAMES if n != "A")] = p_do
        targets[action][int(env0["Y"] == 1)] += p_do
    assert sum(observed.values()) == 1
    for a in (-1, 1):
        assert sum(targets[a]) == 1
        assert sum(intervention_joint[a].values()) == 1
    return tables, observed, targets, intervention_joint


def main():
    tables_f, obs_f, targets_f, do_f = enumerate_model("outer")
    tables_i, obs_i, targets_i, do_i = enumerate_model("inner")
    assert obs_f == obs_i
    gap = LAM/Q(8)
    assert gap == Q(243, 8388608)
    for a in (-1, 1):
        assert targets_f[a][1] == Q(1, 2)
        assert targets_i[a][1] == Q(1, 2) + gap
        assert targets_i[a][1] - targets_f[a][1] == gap
    # A second exact identity checks the density formula on all 64 atoms.
    for x, p in obs_f.items():
        u, a, r, z, b, y = x
        pz = Q(1, 2)*(1 + Q(1, 2)*z*r)
        pb = Q(1, 2)*(1 + Q(1, 2)*b*z)
        baseline = Q(1, 16)*pz*pb
        perturbation = LAM*r*y*(Q(b, 4))*Q(1, 4)*pz*pb
        assert p == baseline + perturbation
    out = {
        "status": "PASS", "scope": "exact CPT finite enumeration; no sampling or ranks",
        "observed_order": list(NAMES), "observed_states": [-1, 1],
        "directed_edges": [["U", "A"], ["A", "B"], ["B", "Y"], ["R", "Z"], ["Z", "B"]],
        "hidden_edges": [list(e) for e in HIDDEN_EDGES],
        "hidden_states": [0, 1, 2, 3], "hidden_laws": "independent uniform",
        "outer_hedge": ["U", "A", "R", "B", "Y"], "inner_hedge": ["R", "Y"],
        "routing_edges": [["R", "Z"], ["Z", "B"], ["B", "Y"]],
        "t": rational(T), "lambda": rational(LAM),
        "outer_coefficient": "U*A/32 + U*A*B*Z/64",
        "inner_coefficient": "B/4",
        "all_local_cell_lower_bound": "1/8",
        "minimum_common_observed_atom": rational(min(obs_f.values())),
        "observational_atoms_checked": len(obs_f), "hidden_assignments_per_atom": 4**4,
        "models": {"outer": tables_f, "inner": tables_i},
        "common_observed_law": [{"values": list(x), "probability": rational(p)} for x, p in obs_f.items()],
        "targets": {str(a): {"outer_p_plus": rational(targets_f[a][1]),
                              "inner_p_plus": rational(targets_i[a][1]),
                              "gap": rational(gap)} for a in (-1, 1)},
        "gap_decimal_descriptive_only": float(gap),
        "ATE_gap": "0/1",
        "full_intervention_laws": {
            model: {str(a): [{"values_without_A": list(x), "probability": rational(p)}
                            for x, p in laws[a].items()] for a in (-1, 1)}
            for model, laws in (("outer", do_f), ("inner", do_i))},
        "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "theorem_sha256": hashlib.sha256((HERE/"theorem.md").read_bytes()).hexdigest(),
    }
    path = HERE/"six_node_certificate.json"
    path.write_text(json.dumps(out, indent=2) + "\n")
    print(json.dumps({"status": "PASS", "path": str(path), "gap": rational(gap),
                      "gap_decimal": float(gap), "minimum_observed_atom": out["minimum_common_observed_atom"]}))


if __name__ == "__main__":
    main()
