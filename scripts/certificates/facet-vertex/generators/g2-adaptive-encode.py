"""Construct exact FacetNumeric row trees for the lower G2 pilot prisms."""

import argparse
from fractions import Fraction as Q
from functools import cache
from itertools import product
import json
from math import lcm
from pathlib import Path
import re


HERE = Path(__file__).resolve().parent
LEAN = HERE.parent / "lean" / "HlawkaSchatten/BelowExponent"
DA = 2**30
DW = 2**30
K = 2**72
UPPER_N, UPPER_D = 24727, 15601
LOWER_N, LOWER_D = 1054, 665
SIGNS = ((1, 1, 1), (-1, -1, 1), (-1, 1, -1), (1, -1, -1))
PARTNERS = ((3, 2, 1), (2, 3, 0), (1, 0, 3), (0, 1, 2))


def ceil_div(n, d):
    return (n+d-1)//d


def unpack(number, count):
    return [(number >> (72*i)) % K for i in range(count)]


class Tables:
    def __init__(self):
        text = (LEAN / "Tangent/FineData.lean").read_text()
        literal = {name: int(value, 16)
                   for name, value in re.findall(r"(P1|Qlo|Qhi) := (0x[\da-f]+)", text)}
        self.p1 = unpack(literal["P1"], 3072)
        self.qlo = unpack(literal["Qlo"], 64)
        self.qhi = unpack(literal["Qhi"], 64)

    @cache
    def upper(self, m, e):
        n, d = self.p1[m-1024], 1
        if e <= 6:
            n *= 3**(6-e)
        else:
            d *= 3**(e-6)
        intercept = ceil_div(n * (LOWER_D-LOWER_N//2)*256, d*LOWER_D)
        incline = ceil_div((n * UPPER_N*256) << (2*e), d*2*UPPER_D*m)
        return intercept, incline

    def term(self, x, y):
        if not x:
            return 0
        threshold = y*1024
        e = max(0, (threshold.bit_length()-x.bit_length())//2)
        while x << (2*e) < threshold:
            e += 1
        while e > 0 and x << (2*(e-1)) >= threshold:
            e -= 1
        m = (2*(x << (2*e))+y)//(2*y)
        if m >= 4096:
            m, e = 1024, max(0, e-1)
        a, b = self.upper(max(m, 1024), e)
        return a*y+b*x

    @cache
    def lower(self, code):
        if not code:
            return (0, 0)
        e, i = divmod(code-1, 64)
        m, e = 64+i, 6+e
        n, d = (UPPER_N-UPPER_D)*self.qhi[i]*256, UPPER_D
        if e <= 7:
            n *= 3**(7-e)
        else:
            d *= 3**(e-7)
        slope = (LOWER_N*self.qlo[i] << (e+8)) // (LOWER_D*m*3**(e-6))
        return -ceil_div(n, d), slope


def snap(magnitude):
    if not magnitude:
        return 0
    e = 37-magnitude.bit_length()
    m = ((magnitude << e) + DA//2) // DA
    if m == 128:
        m, e = 64, e-1
    return 1 + 64*(e-6) + (max(64, min(m, 127))-64)


def candidate_codes(lo, hi):
    a, b = sorted((abs(lo), abs(hi)))
    midpoint = (a+b)//2
    mean = snap(midpoint)
    rough = [mean, snap(a), snap(b), snap((3*a+b)//4), snap((a+3*b)//4), 0]
    return list(dict.fromkeys(rough + [max(0, n+s) for n in rough for s in (-1, 1)]))


class Prism:
    def __init__(self, record, tables):
        tri = [tuple(map(Q, b)) for b in record["triangle"]]
        depth = Q(1, 500)
        self.rho = Q(record["rho"])
        points = [(*b, Q(0)) for b in tri] + [(*(x*(1-depth) for x in b), depth) for b in tri]
        self.den = lcm(*(v.denominator for point in points for v in point))
        self.vertices = [tuple(int(x*self.den) for x in p) for p in points]
        self.p, self.slope = record["p"], record["slopes"]
        assert sum(self.p) == DW and all(x >= 0 for x in self.p)
        self.gamma = [tuple(
            (DW-self.p[3]-self.p[j])*self.den + (2*self.p[3]-DW)*v[j] + self.slope[j]*v[3]
            for j in range(3)
        ) for v in self.vertices]
        assert all(min(gamma) >= 0 and sum(gamma) <= DW*self.den for gamma in self.gamma)
        self.weights = [p*self.den for p in self.p]
        self.coeff = [tuple(tuple(s*(v[i]+v[j]) for s, j in zip(SIGNS[i], PARTNERS[i], strict=True))
                            for i in range(4)) for v in self.vertices]
        self.tables = tables

    @cache
    def lhs(self, j, k, l, a, b):
        y = (self.den*DA)**2
        entries = []
        for terms in self.coeff:
            entries.append(sum(
                p*self.tables.term((g[j]*DA+g[k]*a+g[l]*b)**2, y)
                for p, g in zip(self.weights, terms, strict=True)
            ))
        return entries

    def inside_cone(self, j, a2, b1, b2):
        threshold = DA*self.rho.denominator
        scale = self.rho.denominator+self.rho.numerator
        return -a2*scale >= threshold and (-b2 if j == 0 else b1)*scale >= threshold

    def find_codes(self, j, k, l, a1, a2, b1, b2):
        points = list(product((a1, a2), (b1, b2)))
        first_vertex = 3 if self.inside_cone(j, a2, b1, b2) else 0
        factor = self.den**2*DA
        # At each corner the two signed input tangents must cover the upper bound at every checked vertex.
        targets = [
            (abs(a), abs(b), self.gamma[v][k], self.gamma[v][l],
             ceil_div(self.lhs(j, k, l, a, b)[v], factor)-self.gamma[v][j]*K*DA)
            for a, b in points for v in range(first_vertex, 6)
        ]
        left, right = candidate_codes(a1, a2), candidate_codes(b1, b2)
        for ca, cb in product(left, right):
            ia, sa = self.tables.lower(ca)
            ib, sb = self.tables.lower(cb)
            if all(gk*(ia*DA+sa*a)+gl*(ib*DA+sb*b) >= want for a, b, gk, gl, want in targets):
                return ca, cb
        return None

    def box_tree(self, j, k, l, a1, a2, b1, b2, depth=0):
        assert a1 < a2 and b1 < b2
        assert depth <= 44, (j, a1, a2, b1, b2)
        pair = self.find_codes(j, k, l, a1, a2, b1, b2)
        if pair is not None:
            return ("box", *pair)
        if a2-a1 >= b2-b1:
            m = (a1+a2)//2
            return ("splitA", self.box_tree(j, k, l, a1, m, b1, b2, depth+1),
                    self.box_tree(j, k, l, m, a2, b1, b2, depth+1))
        m = (b1+b2)//2
        return ("splitB", self.box_tree(j, k, l, a1, a2, b1, m, depth+1),
                self.box_tree(j, k, l, a1, a2, m, b2, depth+1))

    def chart(self, j, k, l):
        return ("splitA", *[
            ("splitB", *[self.box_tree(j, k, l, lo, hi, low, high)
                         for low, high in ((-DA, 0), (0, DA))])
            for lo, hi in ((-DA, 0), (0, DA))
        ])


def lean_tree(tree, indent=2):
    if tree[0] == "box":
        return [f"{' '*indent}(.box {tree[1]} {tree[2]})"]
    return [f"{' '*indent}(.{tree[0]}", *lean_tree(tree[1], indent+2), *lean_tree(tree[2], indent+2), f"{' '*indent})"]


def box_count(tree):
    return 1 if tree[0] == "box" else box_count(tree[1]) + box_count(tree[2])


def encode(index, record, tables, *, series="Tip", trees=None):
    name = f"g2{series}{index}"
    prism = Prism(record, tables)
    literal_vertices = ", ".join("⟨" + ", ".join(map(str, v)) + "⟩" for v in prism.vertices)
    lines = [
        "module", "", "public import HlawkaSchatten.BelowExponent.FacetNumeric", "", "@[expose] public section",
        "", "namespace HlawkaSchatten.BelowExponent.FacetNumeric", "", f"def {name} : Prism := {{",
        f"  vertices := [{literal_vertices}]", f"  profileDen := {prism.den}",
        f"  pi := {prism.p}", f"  slope := {prism.slope}",
        f"  radiusNum := {prism.rho.numerator}", f"  radiusDen := {prism.rho.denominator}", "}", "",
        "set_option maxRecDepth 40000", "set_option maxHeartbeats 0", "",
        f"theorem {name}_data_ok : dataOK {name} = true := by decide +kernel", "",
    ]
    for j, k, l in ((0, 1, 2), (1, 0, 2), (2, 0, 1)):
        tree = prism.chart(j, k, l) if trees is None else trees[j]
        print(f"prism {index}, chart {j}, boxes {box_count(tree)}", flush=True)
        chart = f"{name}Chart{j}"
        lines += [
            f"def {chart} : RowTree :=", *lean_tree(tree), "",
            f"theorem {chart}_ok : checkChart {name} {j} {k} {l} {chart} = true := by decide +kernel", "",
        ]
    lines += ["end HlawkaSchatten.BelowExponent.FacetNumeric", ""]
    assert len(lines) < 10_000
    target = LEAN / "FacetG2" / f"{series}{index}Data.lean"
    target.parent.mkdir(exist_ok=True)
    target.write_text("\n".join(lines))
    print(f"Wrote {target.name}", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("candidates", type=Path)
    args = parser.parse_args()
    candidates = json.loads(args.candidates.read_text())
    passing = [row for row in candidates if row["margin"] > 0 and row["cone_exact"]]
    assert len(passing) == 2
    tables = Tables()
    for index, record in enumerate(passing):
        encode(index, record, tables)


if __name__ == "__main__":
    main()
