"""Exact capacity-compression checks. No simulation or external dependencies."""
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import hashlib
import json

HERE = Path(__file__).resolve().parent
MAIN = HERE.parent / "multimode_hedge/theorem.md"
MAIN_SHA = "60e9bae29d787b80f2056a96e681276b3ec9c3f1d49f2eb0c0435136469e1147"


def mul(vals):
    ans = Q(1)
    for val in vals:
        ans *= val
    return ans


def phi(j, z):
    """Rational unnormalized Helmert contrast; j=0 is the constant label."""
    if j == 0:
        return Q(1)
    return Q(1 if z <= j else -j if z == j + 1 else 0)


def norm(j, states):
    return Q(1) if j == 0 else Q(j * (j + 1), states)


def configurations(names):
    for values in product((-1, 1), repeat=len(names)):
        yield dict(zip(names, values))


def matrix_rank(matrix):
    a = [[Q(z) for z in row] for row in matrix]
    rank = 0
    for col in range(len(a[0])):
        pivot = next((i for i in range(rank, len(a)) if a[i][col]), None)
        if pivot is None:
            continue
        a[rank], a[pivot] = a[pivot], a[rank]
        pivot_value = a[rank][col]
        a[rank] = [v / pivot_value for v in a[rank]]
        for i in range(len(a)):
            if i != rank:
                scale = a[i][col]
                a[i] = [x - scale * y for x, y in zip(a[i], a[rank])]
        rank += 1
        if rank == len(a):
            break
    return rank


def orthogonality_checks():
    count = 0
    for states in range(2, 9):
        for j, k in product(range(states), repeat=2):
            value = sum(phi(j, z) * phi(k, z) for z in range(1, states + 1)) / states
            assert value == (norm(j, states) if j == k else 0)
            count += 1
    # Walsh characters reuse bits; mode independence is not assumed.
    for bits in range(1, 5):
        states = 2 ** bits
        for j, k in product(range(states), repeat=2):
            val = sum((-1) ** (((j & z).bit_count() + (k & z).bit_count()) % 2)
                      for z in range(states))
            assert val == (states if j == k else 0)
    # Full three-vertex tree contraction, with four nonbaseline modes.
    states = 5
    surviving = []
    for labels in product(range(states), repeat=3):
        value = sum(phi(labels[0], e1) * phi(labels[1], e1)
                    * phi(labels[1], e2) * phi(labels[2], e2)
                    for e1, e2 in product(range(1, states + 1), repeat=2)) / states ** 2
        expected = norm(labels[0], states) ** 2 if len(set(labels)) == 1 else 0
        assert value == expected
        if value:
            surviving.append(labels)
    assert len(surviving) == states
    return {"helmert_gram_entries": count, "walsh_bit_counts": [1, 2, 3, 4],
            "three_vertex_tree_label_patterns": states ** 3,
            "surviving_tree_patterns": [list(x) for x in surviving]}


def compressed_hedge():
    nodes = ("U", "A", "R", "Z", "B", "Y")
    outer = {"U", "A", "R", "B", "Y"}
    edges = (("A", "Y"), ("Y", "R"), ("R", "U"), ("U", "B"))
    delta = Q(1, 16)
    lam = delta ** 5
    states = 3
    coeff = {1: Q(1, 32), 2: Q(1, 64)}

    def base(v, x):
        if v == "Z":
            return (1 + Q(1, 2) * x["Z"] * x["R"]) / 2
        if v == "B":
            return (1 + Q(1, 2) * x["B"] * x["Z"]) / 2
        return Q(1, 2)

    def kernel(model, v, x, hidden):
        ans = base(v, x)
        if model == "outer" and v in outer:
            for mode in (1, 2):
                b = delta * coeff[mode] / norm(mode, states) ** 4 if v == "U" else delta
                factor = Q(1)
                if v == "A":
                    factor = x["U"]
                elif v == "B":
                    factor = x["A"] * (x["Z"] if mode == 2 else 1)
                elif v == "Y" and mode == 2:
                    factor = x["B"]
                latent = mul(phi(mode, hidden[e]) for e, endpoints in enumerate(edges) if v in endpoints)
                ans += x[v] * b * factor * latent
        elif model == "inner" and v in ("R", "Y"):
            b = delta if v == "R" else delta ** 4 / (4 * norm(1, states))
            ans += x[v] * b * (x["B"] if v == "Y" else 1) * phi(1, hidden[1])
        return ans

    cache = {}
    lows = {"outer": Q(1), "inner": Q(1)}
    all_hidden = list(product(range(1, states + 1), repeat=len(edges)))
    for model in ("outer", "inner"):
        for x in configurations(nodes):
            key = tuple(x[v] for v in nodes)
            for hidden in all_hidden:
                row = []
                for v in nodes:
                    p = kernel(model, v, x, hidden)
                    flipped = dict(x)
                    flipped[v] *= -1
                    assert p + kernel(model, v, flipped, hidden) == 1
                    assert Q(1, 8) <= p <= Q(7, 8)
                    lows[model] = min(lows[model], p)
                    row.append(p)
                cache[model, key, hidden] = row

    def law(model, action=None):
        result = {}
        for x in configurations(nodes):
            if action is not None and x["A"] != action:
                continue
            key = tuple(x[v] for v in nodes)
            total = Q(0)
            for hidden in all_hidden:
                row = cache[model, key, hidden]
                total += mul(p for v, p in zip(nodes, row) if action is None or v != "A") / len(all_hidden)
            result[key] = total
        assert sum(result.values()) == 1
        return result

    obs_outer, obs_inner = law("outer"), law("inner")
    assert obs_outer == obs_inner
    for key, value in obs_outer.items():
        x = dict(zip(nodes, key))
        expected = mul(base(v, x) for v in nodes)
        expected += lam * x["R"] * x["Y"] * x["B"] / 4 * mul(base(v, x) for v in nodes if v not in ("R", "Y"))
        assert value == expected
    action_results = {}
    for action in (-1, 1):
        lf, li = law("outer", action), law("inner", action)
        yf = sum(p for x, p in lf.items() if x[-1] == 1)
        yi = sum(p for x, p in li.items() if x[-1] == 1)
        assert yi - yf == lam / 8
        action_results[str(action)] = {"outer_y_positive": str(yf), "inner_y_positive": str(yi),
                                       "gap": str(yi - yf), "joint_atoms_each": len(lf)}
    return {"same_graph_as_six_node_obstruction": True, "edge_root_states_each": states,
            "edge_roots": [list(e) for e in edges], "hidden_joint_states": len(all_hidden),
            "lambda": str(lam), "local_cell_minima": {m: str(z) for m, z in lows.items()},
            "equal_observation_atoms": len(obs_outer), "action_results": action_results,
            "mode_count_outer": 2, "route_reentry_count_h": 1,
            "old_independent_bit_states_each": 4}


def universal_lemma_rank_boundary():
    """No hidden root with <=4 states can realize this *specified* kernel."""
    states = 5
    delta = Q(1, 16)
    lam = delta ** 2
    settings = list(product((-1, 1), repeat=2))

    def chars(a):
        return (1, a[0], a[1], a[0] * a[1])

    def kx(x, a, h):
        return Q(1, 2) + x * delta * sum(aa * phi(j, h) for j, aa in enumerate(chars(a), 1))

    def ky(y, b, h):
        return Q(1, 2) + y * delta * sum(bb * phi(j, h) / norm(j, states)
                                       for j, bb in enumerate(chars(b), 1))

    low = Q(1)
    covariance = []
    observed_total = Q(0)
    for a in settings:
        cov_row = []
        for b in settings:
            law = {}
            for x, y in product((-1, 1), repeat=2):
                for h in range(1, states + 1):
                    px, py = kx(x, a, h), ky(y, b, h)
                    low = min(low, px, py)
                    assert px + kx(-x, a, h) == py + ky(-y, b, h) == 1
                value = sum(kx(x, a, h) * ky(y, b, h) for h in range(1, states + 1)) / states
                c = sum(aa * bb for aa, bb in zip(chars(a), chars(b)))
                assert c == (4 if a == b else 0)
                assert value == Q(1, 4) + lam * x * y * c
                law[x, y] = value
                observed_total += value / 16
            assert sum(law.values()) == 1
            assert sum(x * value for (x, y), value in law.items()) == 0
            assert sum(y * value for (x, y), value in law.items()) == 0
            cov_row.append(sum(x * y * value for (x, y), value in law.items()))
        covariance.append(cov_row)
    assert observed_total == 1 and low == Q(1, 4)
    rank = matrix_rank(covariance)
    assert rank == 4
    assert all(covariance[i][j] == (Q(1, 16) if i == j else 0) for i, j in product(range(4), repeat=2))
    return {"observed_nodes": ["A1", "A2", "B1", "B2", "X", "Y"],
            "directed_edges": [["A1", "X"], ["A2", "X"], ["B1", "Y"], ["B2", "Y"]],
            "sole_bidirected_edge": ["X", "Y"], "latent_states_used": states,
            "mode_count": 4, "lambda": str(lam), "minimum_local_cell": str(low),
            "conditional_covariance_matrix": [[str(x) for x in row] for row in covariance],
            "rank": rank, "required_latent_states_at_least": rank + 1,
            "conditional_marginals_X_Y": "uniform for every external parent setting",
            "observed_atoms_checked": 64,
            "scope": "Lower bound for this specified connected-set perturbation law on this graph, not an impossibility theorem for binary-root hedge witnesses."}


def main():
    assert hashlib.sha256(MAIN.read_bytes()).hexdigest() == MAIN_SHA
    result = {"status": "PASS", "arithmetic": "exact fractions.Fraction",
              "frozen_main_sha256": MAIN_SHA,
              "orthogonality": orthogonality_checks(),
              "compressed_actual_hedge": compressed_hedge(),
              "universal_realization_boundary": universal_lemma_rank_boundary()}
    (HERE / "certificate.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
