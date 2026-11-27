"""Index the parameter corners shared by the VC and SC certificate cells."""

import argparse
from itertools import product
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from vertex_root_witnesses import zone_cells


# These six parents use the eight-child covers in vertex-region-vc-m-refined.txt.
REFINED_VC_M = {1, 28, 29, 31, 59, 61}


def corner_index(source_root):
    groups = {}
    for zone, parents in zone_cells(source_root):
        # VC certifies all normalized rows. SC's corner test covers the exterior
        # of its cone, including on the common VC/SC parameter face.
        group = "VC" if zone.startswith("Vc") else "SC"
        rows = groups.setdefault(group, [])
        for parent, bounds in enumerate(parents):
            boxes = [bounds]
            if zone == "VcM" and parent in REFINED_VC_M:
                pairs = [((lo, (lo+hi)/2), ((lo+hi)/2, hi)) for lo, hi in bounds]
                boxes = list(product(*pairs))
            for child, box in enumerate(boxes):
                rows.append((zone, parent, child, list(product(*box))))

    result = {}
    for group, rows in groups.items():
        points = sorted({point for _, _, _, corners in rows for point in corners})
        index = {point: i for i, point in enumerate(points)}
        cells = [
            {"zone": zone, "parent": parent, "child": child, "corners": [index[p] for p in corners]}
            for zone, parent, child, corners in rows
        ]
        for cell, (_, _, _, corners) in zip(cells, rows, strict=True):
            if [points[i] for i in cell["corners"]] != corners:
                raise ValueError("Corner index failed to reconstruct the cell")
        result[group] = {"points": [[str(x) for x in p] for p in points], "cells": cells}
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source_root", type=Path)
    parser.add_argument("--output", type=Path, help="write coordinate and corner-reference tables")
    args = parser.parse_args()
    data = corner_index(args.source_root)
    for group, table in data.items():
        count = len(table["cells"])
        print(f"{group}: {count} cells, {8*count} corner uses, {len(table['points'])} distinct points")
    if args.output:
        args.output.write_text(json.dumps(data, separators=(",", ":")) + "\n")
