"""Read archived F0–F2 prisms and translate their row trees to the certified fine table."""

import argparse
from fractions import Fraction as Q
from hashlib import sha256
from itertools import product
import json
from math import lcm
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
CHECK = runpy.run_path(str(HERE / "g2-adaptive-encode.py"))
DA, DW, K = (CHECK[name] for name in ("DA", "DW", "K"))
SIGNS, PARTNERS = (CHECK[name] for name in ("SIGNS", "PARTNERS"))
CHARTS = ((0, 1, 2), (1, 0, 2), (2, 0, 1))
FILES = ("facet_big.txt", "facet_s1.txt", "facet_s2.txt")
PROJECT = HERE.parent / "lean" / "HlawkaSchatten/BelowExponent" / "FacetArchive"
QLO, QHI = Q(1054, 665), Q(24727, 15601)
C2LO, C2HI = QLO * (QLO - 1) / 2, QHI * (QHI - 1) / 2
C3LO = QLO * (QLO - 1) * (2 - QHI) / 6
C3HI = QHI * (QHI - 1) * (2 - QLO) / 6


def near_upper(u):
    if u <= 0:
        return 1 + QLO*u + C2HI*u*u + C3HI*(-u)**3/(1+u)**2
    return 1 + QHI*u + C2HI*u*u - C3LO*u**3/(1+u)**2


def near_lower(v, r):
    return 1 - C2LO*r*r - 2*C3LO*r**3 + (-QHI + 2*C2LO*r + 3*C3LO*r*r)*v


class UnresolvedBox(Exception):
    pass


def read_archive(path):
    raw = path.read_bytes()
    header, *lines = (line.strip() for line in raw.decode("ascii").splitlines() if line.strip())
    magic, version, *flags = header.split()
    params = dict(flag.split("=", 1) for flag in flags)
    assert (magic, version) == ("FACET-PRISM-CERT", "v1")
    assert tuple(params[k] for k in ("Dw", "KBOX", "NODEBITS", "D")) == (str(DW), "30", "14", "1/400")
    root = tuple(tuple(map(Q, term.split(","))) for term in params["root"].split(";"))
    assert len(root) == 3 and all(len(v) == 3 and min(v) > 0 and sum(v) == 1 for v in root)
    print(f"{path.name} sha256={sha256(raw).hexdigest()}", flush=True)
    pending = iter(lines)
    records = []

    def read(triangle):
        line = next(pending)
        if line.startswith("T "):
            i, j = map(int, line.split()[1:])
            assert 0 <= i < j < 3
            m = tuple((x + y) / 2 for x, y in zip(triangle[i], triangle[j], strict=True))
            left, right = list(triangle), list(triangle)
            left[i], right[j] = m, m
            return [i, j, read(tuple(left)), read(tuple(right))]
        assert line.startswith("F")
        weight_text, *charts = line[1:].split(";")
        *coefficients, cone = weight_text.split()
        assert len(coefficients) == 7 and len(charts) == 3
        p = list(map(int, coefficients[:4]))
        slope = list(map(int, coefficients[4:]))
        records.append((triangle, p, slope, Q(cone), charts))
        return len(records)

    tree = read(root)
    assert next(pending, None) is None
    return root, tree, records


class ArchivedPrism(CHECK["Prism"]):
    def __init__(self, triangle, p, slope, rho, tables):
        depth = Q(1, 400)
        points = [(*b, Q(0)) for b in triangle] + [(*(x * (1 - depth) for x in b), depth) for b in triangle]
        self.den = lcm(*(x.denominator for point in points for x in point))
        self.vertices = [tuple(int(x * self.den) for x in point) for point in points]
        self.p, self.slope, self.rho, self.tables = p, slope, rho, tables
        self.use_near = False
        assert sum(p) == DW and min(p) >= 0
        self.gamma = [tuple((DW - p[3] - p[j]) * self.den + (2 * p[3] - DW) * v[j] + slope[j] * v[3]
                            for j in range(3)) for v in self.vertices]
        assert all(min(gamma) >= 0 and sum(gamma) <= DW * self.den for gamma in self.gamma)
        self.weights = [weight * self.den for weight in p]
        self.coeff = [tuple(tuple(sign * (v[i] + v[j])
                                  for sign, j in zip(SIGNS[i], PARTNERS[i], strict=True))
                            for i in range(4)) for v in self.vertices]

    def gate(self, j, k, l, bounds, a_code, b_code):
        a1, a2, b1, b2 = bounds
        first = 3 if self.inside_cone(j, a2, b1, b2) else 0
        factor = self.den**2 * DA
        ia, sa = self.tables.lower(a_code)
        ib, sb = self.tables.lower(b_code)
        for a, b in product((a1, a2), (b1, b2)):
            sums = self.lhs(j, k, l, a, b)
            for v in range(first, 6):
                g = self.gamma[v]
                rhs = g[j] * K * DA + g[k] * (ia * DA + sa * abs(a)) + g[l] * (ib * DA + sb * abs(b))
                if sums[v] > rhs * factor:
                    return False
        return True

    def near_gate(self, j, k, l, bounds):
        if min(map(abs, bounds)) < Q(15, 16) * DA:
            return False
        a1, a2, b1, b2 = bounds
        r = 1 - Q(abs(a1) + abs(a2), 2*DA)
        s = 1 - Q(abs(b1) + abs(b2), 2*DA)
        first = 3 if self.inside_cone(j, a2, b1, b2) else 0
        scale = self.den * DA
        for a, b in product((a1, a2), (b1, b2)):
            for v in range(first, 6):
                d = [Q(abs(g[j]*DA + g[k]*a + g[l]*b), scale) - 1 for g in self.coeff[v]]
                if any(u <= -1 for u in d):
                    return False
                lhs = sum(p * near_upper(u) for p, u in zip(self.weights, d, strict=True))
                g = self.gamma[v]
                rhs = g[j] + g[k] * near_lower(1-Q(abs(a), DA), r) + g[l] * near_lower(1-Q(abs(b), DA), s)
                if lhs > rhs:
                    return False
        return True

    def adapt(self, j, k, l, bounds, codes, depth=0):
        ca, cb = codes
        if self.gate(j, k, l, bounds, ca, cb):
            return ("box", ca, cb)
        for da, db in product((0, -1, 1, -2, 2), repeat=2):
            aa, bb = max(0, ca + da), max(0, cb + db)
            if self.gate(j, k, l, bounds, aa, bb):
                return ("box", aa, bb)
        best = self.find_codes(j, k, l, *bounds)
        if best is not None:
            return ("box", *best)
        if self.use_near and self.near_gate(j, k, l, bounds):
            return ("box", 10000, 0)
        if depth == 16:
            raise UnresolvedBox((j, bounds, codes))
        a1, a2, b1, b2 = bounds
        if a2 - a1 >= b2 - b1:
            m = (a1 + a2) // 2
            assert a1 < m < a2
            children = ((a1, m, b1, b2), (m, a2, b1, b2))
            axis = "splitA"
        else:
            m = (b1 + b2) // 2
            assert b1 < m < b2
            children = ((a1, a2, b1, m), (a1, a2, m, b2))
            axis = "splitB"
        return (axis, *(self.adapt(j, k, l, child, codes, depth + 1) for child in children))

    def translate(self, j, k, l, chart):
        pending = iter(chart.split())

        def read(a1, a2, b1, b2):
            token = next(pending)
            if token == "a":
                m = (a1 + a2) // 2
                return "splitA", read(a1, m, b1, b2), read(m, a2, b1, b2)
            if token == "b":
                m = (b1 + b2) // 2
                return "splitB", read(a1, a2, b1, m), read(a1, a2, m, b2)
            assert (a1 >= 0 or a2 <= 0) and (b1 >= 0 or b2 <= 0)
            codes = tuple(CHECK["snap"](n << 16) for n in map(int, token.split(",")))
            assert len(codes) == 2
            return self.adapt(j, k, l, (a1, a2, b1, b2), codes)

        tree = read(-DA, DA, -DA, DA)
        assert next(pending, None) is None
        return tree


def encode(region, index, prism, charts):
    module = f"F{region}Prism{index}"
    name = f"f{region}Archived{index}"
    vertices = ",\n    ".join("⟨" + ", ".join(map(str, v)) + "⟩" for v in prism.vertices)
    module_path = "FacetArchive.NearCover" if prism.use_near else "FacetNumeric"
    lines = ["module", "", f"public import HlawkaSchatten.BelowExponent.{module_path}", "", "@[expose] public section", "",
             "namespace HlawkaSchatten.BelowExponent.FacetNumeric", "", f"def {name} : Prism := {{", f"  vertices := [{vertices}]",
             f"  profileDen := {prism.den}", f"  pi := {prism.p}", f"  slope := {prism.slope}",
             f"  radiusNum := {prism.rho.numerator}", f"  radiusDen := {prism.rho.denominator}", "}", "",
             "set_option maxRecDepth 40000", "set_option maxHeartbeats 0", "",
             f"theorem {name}_data_ok : dataOK {name} = true := by decide +kernel", ""]
    counts = []
    for (j, k, l), chart in zip(CHARTS, charts, strict=True):
        tree = prism.translate(j, k, l, chart)
        counts.append(CHECK["box_count"](tree))
        chart_name = f"{name}Chart{j}"
        gate = (f"checkMixedChart {name} {j} {chart_name}" if prism.use_near else
                f"checkChart {name} {j} {k} {l} {chart_name}")
        lines += [f"def {chart_name} : RowTree :=", *CHECK["lean_tree"](tree), "",
                  f"theorem {chart_name}_ok : {gate} = true := by decide +kernel", ""]
    lines.extend(("end HlawkaSchatten.BelowExponent.FacetNumeric", ""))
    PROJECT.mkdir(exist_ok=True)
    target = PROJECT / f"{module}Data.lean"
    content = "\n".join(lines)
    if not target.exists() or target.read_text() != content:
        target.write_text(content)
    return counts


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("archive", type=Path)
    parser.add_argument("manifest", type=Path)
    args = parser.parse_args()
    tables = CHECK["Tables"]()
    manifest, failed = [], []
    for region, basename in enumerate(FILES):
        root, tree, records = read_archive(args.archive / basename)
        cells = []
        for index, (triangle, p, slope, rho, charts) in enumerate(records, start=1):
            prism = ArchivedPrism(triangle, p, slope, rho, tables)
            try:
                try:
                    counts = encode(region, index, prism, charts)
                except UnresolvedBox:
                    prism.use_near = True
                    counts = encode(region, index, prism, charts)
                print(f"F{region} prism {index}: {counts}, {'mixed' if prism.use_near else 'ordinary'}", flush=True)
            except UnresolvedBox as exc:
                print(f"F{region} prism {index}: unresolved {exc}", flush=True)
                counts = None
                failed.append([region, index])
            finally:
                prism.lhs.cache_clear()
            cells.append({"triangle": [list(map(str, v)) for v in triangle], "p": p, "slopes": slope,
                          "rho": str(rho), "boxes": counts, "mixed": prism.use_near})
        manifest.append({"root": [list(map(str, v)) for v in root], "tree": tree, "cells": cells})
    args.manifest.write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"Unresolved prisms: {failed}", flush=True)


if __name__ == "__main__":
    main()
