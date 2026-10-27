"""Exact continuum certificate; actual random steps enter via their mean.

The separate theorem must justify the mean-step bound and PSD Jensen. This
file does not replace ten-step powering by a deterministic spectral estimate.
"""
from fractions import Fraction as F
from math import comb
from pathlib import Path
import hashlib
import json
from general_block_operator import image

HERE = Path(__file__).resolve().parent
N, B = 10000, 100
S, LAM = F(1, 100000), F(1, 100000000)
LEFT, RIGHT = F(1, 20000000000), F(1, 5000000000)
GROWTH, REACH = F(1000001, 1000000), F(1, 1000)
GAMMA = F(1000)
WITNESS = [F(1), F(0), F(499), F(0), F(500800), F(0)]
INITIAL = [F(1), F(0), F(1), F(0), F(1), F(0)]


def bounds(delta):
    return ((LAM+2*delta)/(LAM+F(203, 200)*delta),
            (LAM+2*delta)/(LAM+delta))


def denominator(delta):
    return ((LAM+2*delta)*(B+LAM-(B-2)*delta)
            *(LAM+F(203, 200)*delta)*(LAM+delta))


def positive(row):
    a, b, c, d, e, f = row
    assert a > 0 and a*e-c*c > 0, ('contrast', list(map(str, row)))
    assert b >= 0 and f >= 0 and b*f-d*d >= 0, ('mean', list(map(str, row)))
    assert d == GAMMA*b and f == GAMMA*GAMMA*b
    return {'contrast_first_pivot':str(a), 'contrast_determinant':str(a*e-c*c),
            'mean_first_pivot':str(b), 'mean_determinant':str(b*f-d*d)}


def solve(A, values):
    mat = [r[:]+v[:] for r, v in zip(A, values)]
    n = len(mat)
    for j in range(n):
        k = next(i for i in range(j, n) if mat[i][j])
        mat[j], mat[k] = mat[k], mat[j]
        divisor = mat[j][j]
        mat[j] = [x/divisor for x in mat[j]]
        for i in range(n):
            if i != j:
                factor = mat[i][j]
                mat[i] = [x-factor*y for x, y in zip(mat[i], mat[j])]
    return [row[n:] for row in mat]


def eta_bernstein(delta, stale, covariance):
    lo, hi = bounds(delta)
    rows = [image(N, B, S, delta, eta, stale, covariance)
            for eta in (lo, (lo+hi)/2, hi)]
    rows[1] = [2*m-(a+b)/2 for a, m, b in zip(*rows)]
    u = F(2, 7)
    assert image(N, B, S, delta, lo+(hi-lo)*u, stale, covariance) == [
        (1-u)**2*a+2*u*(1-u)*m+u*u*b for a, m, b in zip(*rows)]
    return rows


def run():
    assert LAM == F(N, B)*S*S
    assert LAM*F(N, B) < 1 and LAM < F(N, B)
    assert LEFT > F(1, 2**52) and RIGHT < LAM
    assert F(52, 51)**20 < F(3, 2)
    assert WITNESS[0]*WITNESS[4]-WITNESS[2]**2 > 0
    records = []
    for stale in (True, False):
        for label, covariance, scale in (
                ('growth', WITNESS, GROWTH), ('zero_start', INITIAL, REACH)):
            offset = [scale*x for x in WITNESS]
            values = []
            for k in range(9):
                delta = LEFT+(RIGHT-LEFT)*F(k, 8)
                den = denominator(delta)
                values.append([[den*den*(x-y) for x, y in zip(row, offset)]
                               for row in eta_bernstein(delta, stale, covariance)])
            powers, bernstein = [], []
            for j in range(3):
                coeff = solve([[F(k, 8)**a for a in range(9)] for k in range(9)],
                              [v[j] for v in values])
                powers.append(coeff)
                bernstein.append([[sum(coeff[a][i]*F(comb(k, a), comb(8, a))
                                       for a in range(k+1)) for i in range(6)]
                                  for k in range(9)])
            for u in (F(2, 7), F(5, 13), F(11, 17)):
                delta = LEFT+(RIGHT-LEFT)*u
                den = denominator(delta)
                rows = eta_bernstein(delta, stale, covariance)
                for j in range(3):
                    expected = [den*den*(x-y) for x, y in zip(rows[j], offset)]
                    got = [sum(powers[j][a][i]*u**a for a in range(9))
                           for i in range(6)]
                    assert got == expected
                    assert got == [sum(bernstein[j][a][i]*comb(8, a)*u**a
                                       *(1-u)**(8-a) for a in range(9))
                                   for i in range(6)]
            record = {'update':'stale' if stale else 'corrected',
                      'claim':label, 'coefficients':[]}
            for j in range(3):
                for k, row in enumerate(bernstein[j]):
                    proof = positive(row)
                    record['coefficients'].append({'delta_index':k, 'mean_eta_index':j,
                                                   'coordinates':list(map(str, row)), **proof})
            records.append(record)
            print(record['update'], label, 'PASS27', flush=True)
    result = {'status':'PASS', 'arithmetic':'Fraction-only bivariate Bernstein PSD certificate',
              'n':N, 'block_size':B, 'rank':B, 's':str(S), 'lambda':str(LAM),
              'delta_interval':[str(LEFT), str(RIGHT)], 'growth':str(GROWTH),
              'reach':str(REACH), 'witness_coordinates':list(map(str, WITNESS)),
              'step_scope':'certificate covers the interval containing E[eta], not every realized eta; theorem supplies covariance Jensen and actual random-power mean bound',
              'checks':records, 'source_hashes':{
                  name:hashlib.sha256((HERE/name).read_bytes()).hexdigest()
                  for name in ['general_block_operator.py','check_rank100_mean_step.py']}}
    out = HERE/'rank100_mean_step_certificate.json'
    with out.open('x') as f:
        json.dump(result, f, indent=2)
        f.write('\n')
    print('PASS', sum(len(r['coefficients']) for r in records), 'coefficient matrices')


if __name__=='__main__':
    run()
