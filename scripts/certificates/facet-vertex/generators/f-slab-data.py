"""Prepare exact row trees for the balanced F slab endpoints."""

import argparse
from fractions import Fraction as Q
from functools import cache
from itertools import product
import json
from math import lcm
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
FACET = runpy.run_path(str(HERE / "facet-archive.py"))
TC = FACET["CHECK"]
DA, K = TC["DA"], TC["K"]
PAIRINGS = (((0, 0),), ((1, 1),), ((0, 1), (1, 0)))
KNOTS = [Q(i, 4096) for i in range(74, 230)] + [Q(7, 125)]
CHARTS = FACET["CHARTS"]


def slab_weight(i):
    if i < 28:
        return Q(21, 100)
    if i < 90:
        return Q(23, 100)
    if i < 122:
        return Q(1, 4)
    return Q(27, 100)


def knot_weights(i):
    return sorted({slab_weight(j) for j in (i-1, i) if 0 <= j < len(KNOTS)-1})


class MissingRowBox(Exception):
    pass


class Band:
    def __init__(self, depth, e0, e1, mu, radius, table):
        self.table = table
        self.radius = radius
        d = depth.denominator
        m = depth.numerator
        e = lcm(e0.denominator, e1.denominator)
        a, b = mu.numerator, mu.denominator
        self.den = 2*d*e
        self.gamma = ((b*d-a*(d-m))*e, (b*d-a*(d-m))*e, 2*a*(d-m)*e)
        points, weights = [], []
        for edge in (e0, e1):
            n = int(edge*e)
            points.append(((d-m)*e+n*d, (d-m)*e-n*d, 2*m*e, 0))
            weights.append([a*(e-n)*d, a*(e+n)*d, (b-a)*e*d, (b-a)*e*d])
        self.terms = [[(weights[w][i], tuple(s * (points[v][i] + points[v][j])
                                           for s, j in zip(TC["SIGNS"][i], TC["PARTNERS"][i], strict=True)))
                       for v, w in group for i in range(4)] for group in PAIRINGS]

    @cache
    def terms_at(self, j, k, l, a, b):
        return [[(p, abs(g[j]*DA+g[k]*a+g[l]*b)) for p, g in terms] for terms in self.terms]

    @cache
    def upper_at(self, j, k, l, a, b):
        y = (self.den*DA)**2
        values = [sum(p*self.table.term(g*g, y) for p, g in terms)
                  for terms in self.terms_at(j, k, l, a, b)]
        return max(values[0], values[1], (values[2]+1)//2)

    def find_codes(self, j, k, l, bounds):
        a1, a2, b1, b2 = bounds
        g = self.gamma
        factor = self.den**2*DA
        targets = [(abs(a), abs(b), TC["ceil_div"](self.upper_at(j,k,l,a,b), factor)-g[j]*K*DA)
                   for a, b in product((a1,a2), (b1,b2))]
        options_a = TC["candidate_codes"](a1,a2)
        options_b = TC["candidate_codes"](b1,b2)
        for ca, cb in product(options_a, options_b):
            ia, sa = self.table.lower(ca)
            ib, sb = self.table.lower(cb)
            if all(g[k]*(ia*DA+sa*a)+g[l]*(ib*DA+sb*b) >= target for a,b,target in targets):
                return ca, cb
        return None

    def near_gate(self, j, k, l, bounds):
        if min(map(abs, bounds)) < Q(15,16)*DA:
            return False
        a1, a2, b1, b2 = bounds
        r = 1-Q(abs(a1)+abs(a2),2*DA)
        s = 1-Q(abs(b1)+abs(b2),2*DA)
        g = self.gamma
        for a,b in product((a1,a2), (b1,b2)):
            rhs = g[j]+g[k]*FACET["near_lower"](1-Q(abs(a),DA),r)+g[l]*FACET["near_lower"](1-Q(abs(b),DA),s)
            for i, terms in enumerate(self.terms_at(j,k,l,a,b)):
                movements = [(p,Q(x,self.den*DA)-1) for p,x in terms]
                if any(u <= -1 for _,u in movements):
                    return False
                if sum(p*FACET["near_upper"](u) for p,u in movements) > (2 if i==2 else 1)*rhs:
                    return False
        return True

    def box(self, j, k, l, bounds, depth=0):
        a1, a2, b1, b2 = bounds
        scale = self.radius.numerator + self.radius.denominator
        cutoff = self.radius.denominator * DA
        if -a2*scale >= cutoff and (-b2 if j == 0 else b1)*scale >= cutoff:
            return ["cone"]
        witness = self.find_codes(j,k,l,bounds)
        if witness is not None:
            return ["box", *witness]
        if self.near_gate(j,k,l,bounds):
            return ["taylor"]
        if depth == 23:
            raise MissingRowBox((j, bounds))
        if a2-a1 >= b2-b1:
            m = (a1+a2)//2
            return ["splitA", self.box(j,k,l,(a1,m,b1,b2),depth+1), self.box(j,k,l,(m,a2,b1,b2),depth+1)]
        m = (b1+b2)//2
        return ["splitB", self.box(j,k,l,(a1,a2,b1,m),depth+1), self.box(j,k,l,(a1,a2,m,b2),depth+1)]

    def chart(self, j, k, l):
        return ["splitA", *[["splitB", *[self.box(j,k,l,(a0,a1,b0,b1))
                                        for b0,b1 in ((-DA,0),(0,DA))]]
                            for a0,a1 in ((-DA,0),(0,DA))]]


def counts(tree):
    if tree[0] == "cone":
        return (1,0,0)
    if tree[0] == "taylor":
        return (0,1,0)
    if tree[0] == "box":
        return (0,0,1)
    return tuple(a+b for a,b in zip(counts(tree[1]),counts(tree[2]),strict=True))


def tile(depth, mu, radius, table, e0=Q(0), e1=Q(1,2), level=0):
    band = Band(depth,e0,e1,mu,radius,table)
    try:
        charts = [band.chart(*jkl) for jkl in CHARTS]
        print(f"{depth} {e0}–{e1}: {list(map(counts,charts))}",flush=True)
        return [{"e": [str(e0),str(e1)], "charts": charts}]
    except MissingRowBox as exc:
        if level == 6:
            raise
        print(f"{depth} {e0}–{e1}: split at {exc}",flush=True)
    finally:
        band.upper_at.cache_clear()
        band.terms_at.cache_clear()
    middle = (e0+e1)/2
    return tile(depth,mu,radius,table,e0,middle,level+1)+tile(depth,mu,radius,table,middle,e1,level+1)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("indices", type=int, nargs="*")
    parser.add_argument("--weight", type=Q, default=Q(1,4))
    parser.add_argument("--radius", type=Q, default=Q(1,64))
    parser.add_argument("--scheduled", action="store_true")
    args = parser.parse_args()
    indices = args.indices or range(len(KNOTS))
    table = TC["Tables"]()
    with args.output.open("w") as out:
        for idx in indices:
            weights = knot_weights(idx) if args.scheduled else [args.weight]
            for weight in weights:
                bands = tile(KNOTS[idx],weight,args.radius,table)
                print(json.dumps({"knot": idx, "l": str(KNOTS[idx]), "weight": str(weight),
                                  "radius": str(args.radius), "bands": bands}), file=out, flush=True)


if __name__ == "__main__":
    main()
