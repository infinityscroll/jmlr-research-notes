"""Exact polynomial and rational checks for the Hessian-Hodge proof.

This does not verify the functional analysis, transport regularity theorem,
or the resulting analytic covariance theorem. No third-party dependency.
"""
from fractions import Fraction as F
from itertools import combinations
import json
import random


class Poly:
    def __init__(self, terms=None):
        self.t = {k: F(v) for k, v in (terms or {}).items() if v}

    @staticmethod
    def lift(x):
        return x if isinstance(x, Poly) else Poly({(0, 0, 0): x})

    def __add__(self, other):
        other = self.lift(other)
        out = dict(self.t)
        for k, v in other.t.items():
            out[k] = out.get(k, F(0)) + v
        return Poly(out)

    __radd__ = __add__

    def __neg__(self):
        return Poly({k: -v for k, v in self.t.items()})

    def __sub__(self, other):
        return self + -self.lift(other)

    def __rsub__(self, other):
        return self.lift(other) + -self

    def __mul__(self, other):
        other = self.lift(other)
        out = {}
        for k, v in self.t.items():
            for l, w in other.t.items():
                q = tuple(a + b for a, b in zip(k, l))
                out[q] = out.get(q, F(0)) + v * w
        return Poly(out)

    __rmul__ = __mul__

    def __eq__(self, other):
        return self.t == self.lift(other).t


def main():
    if not __debug__:
        raise RuntimeError("Exact checks require assertions; do not use Python -O.")
    alpha, beta, gamma = [Poly({tuple(int(i == j) for i in range(3)): 1})
                          for j in range(3)]
    tau = alpha + beta + gamma
    u = [alpha + beta, beta + gamma, gamma + alpha]
    mat = [[u[i] * u[j] for j in range(3)] for i in range(3)]
    for i, j, value in [(0, 1, beta), (1, 2, gamma), (0, 2, alpha)]:
        mat[i][j] = mat[j][i] = mat[i][j] - 2 * tau * value
    checks = 0
    for row in mat:
        assert sum(row, Poly()) == 0
        checks += 1
    for i, j in combinations(range(3), 2):
        assert mat[i][i] * mat[j][j] - mat[i][j] * mat[j][i] == 4 * tau * alpha * beta * gamma
        checks += 1
    det = (mat[0][0] * (mat[1][1]*mat[2][2]-mat[1][2]*mat[2][1])
           - mat[0][1] * (mat[1][0]*mat[2][2]-mat[1][2]*mat[2][0])
           + mat[0][2] * (mat[1][0]*mat[2][1]-mat[1][1]*mat[2][0]))
    assert det == 0
    checks += 1

    rng = random.Random(20261102)
    fixtures = 0
    for d in range(2, 9):
        for _ in range(6):
            lam = [F(rng.randint(1, 15), rng.randint(1, 7)) for i in range(d)]
            A = [[F(0) for j in range(d)] for i in range(d)]
            DA = [[[F(0) for j in range(d)] for i in range(d)] for k in range(d)]
            for i, j in combinations(range(d), 2):
                A[i][j] = F(rng.randint(-8, 8), 5)
                A[j][i] = -A[i][j]
                for k in range(d):
                    DA[k][i][j] = F(rng.randint(-8, 8), 5)
                    DA[k][j][i] = -DA[k][i][j]
            third = {}
            for i in range(d):
                for j in range(i, d):
                    for k in range(j, d):
                        third[i, j, k] = F(rng.randint(-8, 8), 7)
            D = lambda k, i, j: third[tuple(sorted((k, i, j)))]
            raw = sum((lam[i]*DA[l][i][j]*DA[j][i][l]
                       for i in range(d) for j in range(d) for l in range(d)), F(0))
            split = sum((lam[i]*DA[j][i][j]**2
                         for i in range(d) for j in range(d) if i != j), F(0))
            correction = F(0)
            for i, j, k in combinations(range(d), 3):
                aa, bb, cc = DA[k][i][j], DA[i][j][k], DA[j][k][i]
                al, be, ga = lam[i], lam[j], lam[k]
                q = -2*(be*aa*bb + ga*bb*cc + al*cc*aa)
                kval = (al+be)*aa + (be+ga)*bb + (ga+al)*cc
                split += q
                correction += kval*kval/(2*(al+be+ga))
                dm = sum((sum((D(z, x, r)*A[r][y] + A[x][r]*D(z, r, y)
                               for r in range(d)), F(0))
                          for x, y, z in [(i,j,k),(j,k,i),(k,i,j)]), F(0))
                assert dm == 0, (d, i, j, k, "Codazzi cancellation")
                assert q + kval*kval/(2*(al+be+ga)) >= 0
                checks += 2
            assert raw == split
            assert raw + correction >= 0
            checks += 2
            fixtures += 1
    print(json.dumps({"status": "PASS", "exact_checks": checks,
                      "rational_fixtures": fixtures, "dimensions": [2, 8],
                      "polynomial_identities": 7,
                      "scope": "Algebra only; no analytic or external-theorem verification."}, indent=2))


if __name__ == "__main__":
    main()
