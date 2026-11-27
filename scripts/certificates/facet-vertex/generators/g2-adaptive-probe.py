"""Search for shared prism weights on the exact G2 envelope."""

import argparse
from fractions import Fraction as Q
from functools import cache
import json
from math import log2
from pathlib import Path

import numpy as np
from scipy.optimize import linprog


DEPTH = Q(1, 500)
FLOOR = Q(23, 1000)
WEIGHT_DEN = 2**30
EXPONENT = log2(3)
Q_LOWER = Q(1054, 665)
SIGNS = np.array([[1, 1, 1], [-1, -1, 1], [-1, 1, -1], [1, -1, -1]])
PARTNERS = np.array([[3, 2, 1], [2, 3, 0], [1, 0, 3], [0, 1, 2]])


def triangles(top, bottom=FLOOR):
    def lower(y):
        x = Q(123, 1000) - y
        return (1 - x - y, x, y)

    def upper(y):
        x = 4*y + Q(1, 120)
        return (1 - x - y, x, y)

    return [(lower(bottom), lower(top), upper(top)), (lower(bottom), upper(bottom), upper(top))]


def vertices(triangle):
    return [(*b, Q(0)) for b in triangle] + [
        (*(x * (1 - DEPTH) for x in b), DEPTH) for b in triangle
    ]


@cache
def row_samples(n):
    edge = 2.0 ** -np.arange(2, 16)
    near = np.r_[edge, 1 - edge]
    knots = np.unique(np.r_[np.linspace(-1, 1, n), near, -near])
    a, b = [grid.ravel() for grid in np.meshgrid(knots, knots)]
    rows = []
    for axis in range(3):
        x = np.ones((len(a), 3))
        first, second = [j for j in range(3) if j != axis]
        x[:, first], x[:, second] = a, b
        rows.append(x)
    return np.vstack(rows)


def outside_cone(rows, rho):
    signed = rows * np.array([1, -1, -1])
    same_sign = (np.min(signed, axis=1) > 0) | (np.max(signed, axis=1) < 0)
    magnitude = np.abs(signed)
    return ~(same_sign & (np.max(magnitude, axis=1) <= (1 + float(rho)) * np.min(magnitude, axis=1)))


def coefficients(point):
    return SIGNS * (point[:, None] + point[PARTNERS])


def taylor_upper(rho):
    return Q(8, 3) if rho == Q(1, 4) else (1 - 2*rho)**-2


def fit(vertices_, rho, sample):
    constraints, bounds = [], []
    outside = outside_cone(sample, rho)
    powers = np.abs(sample)**EXPONENT
    kappa = float(rho * (1 + 2*taylor_upper(rho)) * (2-Q_LOWER) / 3) * 1.02
    for v, point in enumerate(vertices_):
        b, d = point[:3], point[3]
        # Subtract the common target margin from each directed row gap.
        ap = (np.abs(sample @ coefficients(point).T)**EXPONENT)
        ap[:, :3] += powers
        ap[:, 3] -= powers @ (2*b - 1)
        rows = np.column_stack((ap, -d*powers, np.ones(len(sample))))
        rhs = powers @ (1 - b)
        constraints.append(rows[outside] if v < 3 else rows)
        bounds.append(rhs[outside] if v < 3 else rhs)
        nonneg = np.zeros((3, 8))
        nonneg[:, :3] = np.eye(3)
        nonneg[:, 3] = 1 - 2*b
        nonneg[:, 4:7] = -d*np.eye(3)
        constraints.append(nonneg)
        bounds.append(1 - b)
        if v >= 3:
            continue
        for j, k, l in ((0, 1, 2), (0, 2, 1), (1, 2, 0)):
            pair = np.zeros(8)
            pair[j], pair[k], pair[l] = -b[j], -b[k], 1-b[j]-b[k]
            for m in range(3):
                gamma = -nonneg[m]
                constraints.append((kappa*gamma/b[m] - pair/(b[j]*b[k]))[None, :])
                bounds.append(np.array([1 - kappa*(1-b[m])/b[m]]))
    constraints.append(np.array([[0, 0, 0, -2, 1, 1, 1, 0]]))
    bounds.append(np.array([-1.0]))
    solution = linprog(
        [0, 0, 0, 0, 0, 0, 0, -1],
        A_ub=np.vstack(constraints), b_ub=np.concatenate(bounds),
        A_eq=[[1, 1, 1, 1, 0, 0, 0, 0]], b_eq=[1],
        bounds=[(0, 1)]*4+[(-5, 5)]*3+[(None, None)], method="highs",
    )
    return solution.x if solution.success else None


def worst_rows(vertices_, rho, weights, validation):
    gaps = []
    outside = outside_cone(validation, rho)
    powers = np.abs(validation)**EXPONENT
    for v, point in enumerate(vertices_):
        b, d = point[:3], point[3]
        gamma = (1-b) - weights[:3] + weights[3]*(2*b-1) + d*weights[4:7]
        delta = powers @ gamma - np.abs(validation @ coefficients(point).T)**EXPONENT @ weights[:4]
        if v < 3:
            delta[~outside] = np.inf
        indices = np.argpartition(delta, 5)[:5]
        gaps.extend((delta[i], validation[i]) for i in indices)
    return min(gap for gap, _ in gaps), np.array([row for _, row in gaps])


def dyadic_weights(weights):
    p = [round(x * WEIGHT_DEN) for x in weights[:4]]
    p[max(range(4), key=p.__getitem__)] += WEIGHT_DEN - sum(p)
    slope = [int(np.floor(x * WEIGHT_DEN)) for x in weights[4:7]]
    slope[-1] -= max(0, sum(slope) + WEIGHT_DEN - 2*p[3])
    return p, slope


def exact_budgets(tri, rho, p, slope):
    pi = [Q(x, WEIGHT_DEN) for x in p]
    c = [Q(x, WEIGHT_DEN) for x in slope]
    assert sum(pi) == 1 and all(x >= 0 for x in pi)
    cone = []
    for point in vertices(tri):
        b, d = point[:3], point[3]
        gamma = [1 - pi[3] - pi[j] + (2*pi[3]-1)*b[j] + c[j]*d for j in range(3)]
        if min(gamma) < 0 or sum(gamma) > 1:
            return None
        if d > 0:
            continue
        gamma_max = max(g/bj for g, bj in zip(gamma, b, strict=True))
        lam = min(
            (b[j]*b[k] - (pi[j]+pi[l])*b[j] - (pi[k]+pi[l])*b[k] + pi[l])/(b[j]*b[k])
            for j, k, l in ((0, 1, 2), (0, 2, 1), (1, 2, 0))
        )
        if 3*lam < rho*(1+2*taylor_upper(rho))*(2-Q_LOWER)*gamma_max:
            return None
        cone.append((lam, gamma_max))
    return cone


def probe(tri, rho):
    numeric_vertices = np.asarray(vertices(tri), dtype=float)
    sample, validation = row_samples(13), row_samples(85)
    for _ in range(5):
        result = fit(numeric_vertices, rho, sample)
        if result is None:
            return None
        worst, cuts = worst_rows(numeric_vertices, rho, result, validation)
        if worst >= result[-1] - 1e-9:
            break
        sample = np.vstack((sample, cuts))
    p, slope = dyadic_weights(result)
    cone = exact_budgets(tri, rho, p, slope)
    weights = np.r_[p, slope] / WEIGHT_DEN
    worst, _ = worst_rows(numeric_vertices, rho, weights, validation)
    return {"margin": worst, "p": p, "slopes": slope, "cone_exact": cone is not None,
            "rho": str(rho), "triangle": [[str(x) for x in point] for point in tri]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--top", type=Q, default=Q(3, 125))
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    records = []
    for i, tri in enumerate(triangles(args.top)):
        for rho in (Q(1, 8), Q(1, 16), Q(1, 4)):
            result = probe(tri, rho)
            print("triangle", i, "radius", rho, "result", result, flush=True)
            if result is not None and result["cone_exact"]:
                records.append(result)
    args.output.write_text(json.dumps(records, indent=2) + "\n")


if __name__ == "__main__":
    main()
