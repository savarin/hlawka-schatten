"""Bisect the upper G2 band, accepting each prism by exact integer row checks."""

import argparse
from fractions import Fraction as Q
from itertools import combinations
import json
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
OPT = runpy.run_path(str(HERE / "g2-adaptive-probe.py"))
CHECK = runpy.run_path(str(HERE / "g2-adaptive-encode.py"))
RADII = (Q(1, 16), Q(1, 8), Q(1, 32), Q(1, 4))
CHARTS = ((0, 1, 2), (1, 0, 2), (2, 0, 1))


def as_strings(triangle):
    return [[str(x) for x in point] for point in triangle]


def bisect(triangle):
    def length_squared(edge):
        a, b = (triangle[i] for i in edge)
        return sum((x-y)**2 for x, y in zip(a, b, strict=True))
    i, j = max(combinations(range(3), 2), key=length_squared)
    middle = tuple((a+b)/2 for a, b in zip(triangle[i], triangle[j], strict=True))
    left, right = list(triangle), list(triangle)
    left[i], right[j] = middle, middle
    return [i, j], left, right


def try_prism(triangle, tables):
    for rho in RADII:
        record = OPT["probe"](triangle, rho)
        if record is None or not record["cone_exact"] or record["margin"] <= 0:
            continue
        prism = CHECK["Prism"](record, tables)
        try:
            trees = [prism.chart(*chart) for chart in CHARTS]
        except AssertionError:
            continue
        finally:
            prism.lhs.cache_clear()
        return record, trees
    return None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("route", type=Path)
    parser.add_argument("--max-depth", type=int, default=16)
    args = parser.parse_args()
    roots = OPT["triangles"](Q(1, 20), bottom=Q(3, 125))
    tables = CHECK["Tables"]()
    with args.route.open("x") as records:
        def save(row):
            print(json.dumps(row), file=records, flush=True)

        queue = [(str(i), tuple(root), 0) for i, root in enumerate(roots)]
        accepted = failures = 0
        while queue:
            path, triangle, depth = queue.pop()
            result = try_prism(triangle, tables)
            if result is not None:
                record, trees = result
                counts = [CHECK["box_count"](tree) for tree in trees]
                record.update(kind="prism", path=path, leaf=accepted, boxes=counts)
                CHECK["encode"](accepted, record, tables, series="Upper", trees=trees)
                save(record)
                print(f"Accepted {path}, radius {record['rho']}, {sum(counts)} row boxes", flush=True)
                accepted += 1
                continue
            if depth == args.max_depth:
                save({"kind": "unresolved", "path": path, "triangle": as_strings(triangle)})
                failures += 1
                continue
            edge, left, right = bisect(triangle)
            save({"kind": "split", "path": path, "edge": edge, "triangle": as_strings(triangle)})
            queue.extend(((path+"1", right, depth+1), (path+"0", left, depth+1)))
    print(f"{accepted} accepted prisms; {failures} unresolved.", flush=True)


if __name__ == "__main__":
    main()
