"""Exact G2 geometry and cone budgets used to emit retained witnesses.

The definitions come from g2-adaptive-probe.py. The original optimizer
is retained separately in that file.
"""

from fractions import Fraction as Q


DEPTH = Q(1, 500)
FLOOR = Q(23, 1000)
WEIGHT_DEN = 2**30
Q_LOWER = Q(1054, 665)


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


def taylor_upper(rho):
    return Q(8, 3) if rho == Q(1, 4) else (1 - 2*rho)**-2


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
