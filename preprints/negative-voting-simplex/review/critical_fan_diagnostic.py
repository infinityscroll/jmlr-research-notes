#!/usr/bin/env python3
"""Independent tetrahedral Gaussian-fan diagnostic; NOT a rigorous certificate.

Only NumPy and Python's standard library are required. This reconstructs
facet moments from one-dimensional integration instead of calling any of
the historical algebra checkers. A finite floating-point check cannot prove
the analytic identities or their arbitrary-dimensional extensions.
"""
import argparse
import itertools
import json
import math
from pathlib import Path
import statistics

import numpy as np


def run(nodes_count=512):
    phi = lambda t: np.exp(-np.asarray(t)**2 / 2) / np.sqrt(2*np.pi)
    Phi = np.vectorize(lambda x: .5*math.erfc(-x/math.sqrt(2)))
    inv_phi = statistics.NormalDist().inv_cdf
    nodes, quadrature_weights = np.polynomial.legendre.leggauss(nodes_count)
    edges = list(itertools.combinations(range(4), 2))
    faces = list(itertools.combinations(range(4), 3))
    boundary2 = np.zeros((6, 4))
    for j, face in enumerate(faces):
        for k in range(3):
            edge = tuple(x for l, x in enumerate(face) if l != k)
            boundary2[edges.index(edge), j] = (-1)**k
    boundary3 = np.array([
        (-1)**next(k for k in range(4) if k not in face)
        for face in faces], float)[:, None]
    incidence = np.zeros((6, 4))
    for j, (i, k) in enumerate(edges):
        incidence[j, i], incidence[j, k] = 1, -1
    rng = np.random.default_rng(20261102)
    checks = []
    for case in range(12):
        T = np.eye(3) + .28*rng.normal(size=(3, 3))
        if abs(np.linalg.det(T)) < .15:
            T += np.eye(3)
        y = np.vstack([np.zeros(3), T])
        translation = .6*rng.normal(size=3)
        volume = abs(np.linalg.det(T))/6
        triangle_mass, triangle_mean, area = [], [], []
        for face in faces:
            i, j, k = face
            u = np.cross(y[j]-y[i], y[k]-y[i])
            area.append(np.linalg.norm(u)/2)
            u /= np.linalg.norm(u)
            other = next(l for l in range(4) if l not in face)
            if np.dot(y[i]-y[other], u) < 0:
                u = -u
            s = np.dot(translation, u)
            normal_part = translation - s*u
            tail = float(Phi(-s))
            triangle_mass.append(np.exp(-normal_part@normal_part/2)/(2*np.pi)*tail)
            triangle_mean.append(normal_part + u*phi(s)/tail)
        triangle_mass = np.array(triangle_mass)
        triangle_mean = np.array(triangle_mean)
        D = np.diag(2*np.array(area)/triangle_mass)
        weights, deficits, means, frames, inverses, probabilities = [], [], [], [], [], []
        normals, lengths, moment_errors, ehrhard_min = [], [], [], []
        B = np.zeros((4, 4))
        for ei, (i, j) in enumerate(edges):
            difference = y[i]-y[j]
            length = np.linalg.norm(difference)
            normal = difference/length
            others = [k for k in range(4) if k not in (i, j)]
            tangent = np.eye(3)-np.outer(normal, normal)
            u = tangent@(y[i]-y[others[0]])
            u /= np.linalg.norm(u)
            v = np.cross(normal, u)
            if np.dot(v, y[i]-y[others[1]]) < 0:
                v = -v
            frame = np.column_stack([u, v])
            au, av = translation@u, translation@v
            other_difference = y[i]-y[others[1]]
            ratio = other_difference@u/(other_difference@v)
            x = au+(nodes+1)*(14-au)/2
            threshold = av+ratio*(au-x)
            prob, density = Phi(-threshold), phi(threshold)
            vals = np.array([prob, x*prob, density, x*x*prob,
                             x*density, prob+threshold*density]) @ (
                                 quadrature_weights*phi(x)*(14-au)/2)
            p = vals[0]
            mean2 = vals[1:3]/p
            covariance2 = np.array([[vals[3], vals[4]], [vals[4], vals[5]]])/p
            covariance2 -= np.outer(mean2, mean2)
            normal_offset = translation@normal
            weight = phi(normal_offset)*p/length
            deficit2 = weight*(np.eye(2)-covariance2)
            deficit = frame@deficit2@frame.T
            mean = normal_offset*normal+frame@mean2
            adjacent = [k for k, f in enumerate(faces) if i in f and j in f]
            columns = []
            for fi in adjacent:
                k = next(k for k in faces[fi] if k not in (i, j))
                inward = tangent@(y[i]-y[k])
                inward /= np.linalg.norm(inward)
                columns.append(frame.T@(triangle_mass[fi]/length*inward))
            N = np.column_stack(columns)
            inverse = np.linalg.inv(N)
            facet_B = inverse@deficit2@inverse.T
            signs = boundary2[ei, adjacent]
            B[np.ix_(adjacent, adjacent)] += signs[:, None]*facet_B*signs[None, :]
            moment_matrix = np.column_stack([frame.T@(mean-triangle_mean[fi])
                                            for fi in adjacent])
            moment_errors.append(np.linalg.norm(deficit2-N@moment_matrix.T)
                                 /(1+np.linalg.norm(deficit2)))
            coefficient = 1+inv_phi(p)*p/phi(inv_phi(p))
            ehrhard_min.append(np.linalg.eigvalsh(
                deficit2-weight*coefficient*np.outer(mean2, mean2)).min())
            weights.append(weight); deficits.append(deficit); means.append(mean)
            frames.append(frame); inverses.append(inverse); probabilities.append(p)
            normals.append(normal); lengths.append(length)
        w, means = np.array(weights), np.array(means)
        A = boundary2.T@np.diag(1/w)@boundary2
        point_mass = phi(0)**3*np.exp(-translation@translation/2)
        rhs = -D@boundary3@np.array([[point_mass/(6*volume)]])@boundary3.T@D
        factor_error = np.linalg.norm(A-B-rhs)/(1+np.linalg.norm(A)+np.linalg.norm(B))
        H = rng.normal(size=(3, 3)); H = (H+H.T)/2
        differences = incidence@(y@H.T)
        c = np.einsum('ij,ij->i', differences, means)
        laplacian = incidence.T@np.diag(w)@incidence
        b = -np.linalg.pinv(laplacian)@incidence.T@(w*c)
        cycle = w*(c+incidence@b)
        representative = np.linalg.lstsq(
            np.vstack([boundary2, boundary3.T@D]), np.r_[cycle, 0.], rcond=None)[0]
        cycle_energy = np.dot(cycle/w, cycle)
        raw_energy = sum(differences[e]@deficits[e]@differences[e] for e in range(6))
        residual, refinement = 0., 0.
        for e, (i, j) in enumerate(edges):
            adjacent = [k for k, f in enumerate(faces) if i in f and j in f]
            eta = boundary2[e, adjacent]*representative[adjacent]
            corrected = differences[e]-frames[e]@inverses[e].T@eta
            residual += corrected@deficits[e]@corrected
            q = -translation@normals[e]
            x = (y[i]-y[j])@H@(y[i]-y[j])/lengths[e]
            p = probabilities[e]
            coefficient = 1+inv_phi(p)*p/phi(inv_phi(p))
            refinement += w[e]*coefficient*(b[i]-b[j]-q*x)**2
        checks.append({
            'case': case, 'sites': y.tolist(), 'translation': translation.tolist(),
            'covariance_direction': H.tolist(),
            'factor_relative_error': float(factor_error),
            'boundary_moment_relative_error': float(max(moment_errors)),
            'cycle_residual_error': float(abs(residual-(raw_energy-cycle_energy))
                                          /(1+abs(raw_energy)+abs(cycle_energy))),
            'refined_gap': float(raw_energy-cycle_energy-refinement),
            'min_intrinsic_Ehrhard_eigenvalue': float(min(ehrhard_min)),
        })
    result = {
        'status': 'floating-point diagnostic, not an interval or formal certificate',
        'numpy_version': np.__version__, 'seed': 20261102,
        'quadrature_nodes': nodes_count, 'quadrature_upper_cutoff': 14,
        'case_count': len(checks), 'cases': checks,
    }
    for key in ('factor_relative_error', 'boundary_moment_relative_error', 'cycle_residual_error'):
        result['max_'+key] = max(c[key] for c in checks)
    for key in ('refined_gap', 'min_intrinsic_Ehrhard_eigenvalue'):
        result['minimum_'+key] = min(c[key] for c in checks)
    result['diagnostic_checks_pass'] = all(
        c['factor_relative_error'] < 1e-9 and c['boundary_moment_relative_error'] < 1e-9
        and c['cycle_residual_error'] < 1e-9 and c['refined_gap'] > -1e-9
        and c['min_intrinsic_Ehrhard_eigenvalue'] > -1e-9 for c in checks)
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--nodes', type=int, default=512)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = run(args.nodes)
    encoded = json.dumps(result, indent=2, sort_keys=True)+'\n'
    if args.output:
        args.output.write_text(encoded)
    print(json.dumps({k: v for k, v in result.items() if k != 'cases'}, indent=2))
    raise SystemExit(0 if result['diagnostic_checks_pass'] else 1)
