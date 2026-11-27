"""Emit staged Lean curvature checks for a named range of prepared vertex cells."""

import argparse
from fractions import Fraction
from pathlib import Path
import re
import subprocess
import time


HERE = Path(__file__).resolve().parent
VERTEX = HERE.parent / "lean/HlawkaSchatten/BelowExponent/Vertex"
CELLS = re.compile(r"^def (\w+)Cell : ParameterCell :=", re.MULTILINE)
REFINED = re.compile(r"^(vcM\d+)Child([0-7])$")
ZONES = ("VcM", "VcS1", "ScS", "ScD", "ScE")
BUILD_BATCH = 4
MAX_SINGLE_SUBCELLS = 192
SUBCELLS_PER_PART = 96


def vector(values):
    return "![" + ", ".join(map(str, values)) + "]"


def numeric_module(imports, description, declarations):
    import_lines = "\n".join(imports)
    body = "\n".join(declarations)
    return f"""module

{import_lines}

/-! {description} -/

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

{body}

end HlawkaSchatten.BelowExponent.Vertex
"""


def emit_partition(name, stem, root_module, config, goal, na, layer_size, unfold_child):
    data_prefix = f"HlawkaSchatten.BelowExponent.Vertex.CurvatureData.{stem}"
    root_import = f"HlawkaSchatten.BelowExponent.Vertex.RootData.{root_module}"
    cases_import = "meta import Mathlib.Tactic.FinCases"
    yield stem + "/Config", numeric_module(
        ["public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCheck", f"public import {root_import}", cases_import],
        f"Curvature caps and floor for {name}.", config,
    )

    layer_imports = [f"public import {data_prefix}.Config", "meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureReplay",
                     f"meta import {data_prefix}.Config", f"meta import {root_import}"]
    part_imports = []
    layers_per_part = max(1, SUBCELLS_PER_PART // layer_size)
    for part, start in enumerate(range(0, na, layers_per_part)):
        label = f"Part{part:02d}"
        part_imports.append(f"public import {data_prefix}.{label}")
        declarations = [f"theorem {name}_layer{i} : {goal} {i} = true := by\n"
                        f"{unfold_child}  replay_curvature_layer\n"
                        for i in range(start, min(start + layers_per_part, na))]
        yield stem + "/" + label, numeric_module(layer_imports, f"Exact curvature layers for {name}.", declarations)

    cases = "".join(f"  · exact {name}_layer{i}\n" for i in range(na))
    join = f"theorem {name}_grid_layers (i : Fin {na}) : {goal} i = true := by\n  fin_cases i\n{cases}"
    yield stem, numeric_module([*part_imports, cases_import],
                               f"The joined curvature and weight certificate for {name}.", [join])


def emit(record, root_modules):
    name, *columns = record
    na, nb, n_eta = map(int, columns[:3])
    caps_and_bounds = list(map(Fraction, columns[3:]))
    if len(caps_and_bounds) != 13 or min(na, nb, n_eta) <= 0:
        raise ValueError(f"Invalid curvature record for {name}")
    caps = caps_and_bounds[:9]
    weight_floor = caps_and_bounds[9]
    margins = caps_and_bounds[10:]
    if weight_floor <= 0 or min(caps + margins) < 0:
        raise ValueError(f"Invalid caps or floor for {name}")

    child = REFINED.fullmatch(name)
    parent = child[1] if child else name
    text = [f"""module

public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCheck
public import HlawkaSchatten.BelowExponent.Vertex.RootData.{root_modules[parent]}
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureReplay
meta import HlawkaSchatten.BelowExponent.Vertex.RootData.{root_modules[parent]}

/-! Exact curvature and normalized-weight certificate for {name}. -/

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxHeartbeats 2500000
set_option maxRecDepth 8192
"""]
    cell, roots = f"{name}Cell", f"{parent}Roots"
    if child:
        index = int(child[2])
        i, j, k = index // 4, (index // 2) % 2, index % 2
        text.append(f"""def {cell} : ParameterCell :=
  ⟨{parent}Cell.a.subinterval 2 {i}, {parent}Cell.b.subinterval 2 {j}, {parent}Cell.η.subinterval 2 {k}⟩

theorem {name}_roots_ok : {cell}.rootsOK {roots} = true := by decide +kernel
""")
    cap_rows = vector(vector(caps[i:i+3]) for i in range(0, 9, 3))
    text.append(f"""def {name}Caps : Fin 3 → Fin 3 → ℚ := {cap_rows}
def {name}WeightFloor : ℚ := {weight_floor}
def {name}Margins : Fin 3 → ℚ := {vector(margins)}

theorem {name}_caps_nonneg (k i : Fin 3) : 0 ≤ {name}Caps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem {name}_margin_le (i : Fin 3) : curvatureLoss {cell} {name}Caps i ≤ {name}Margins i := by
  fin_cases i <;> decide +kernel
""")
    goal = f"gridLayerCurvatureOK {cell} {roots} {na} {nb} {n_eta} {name}Caps {name}WeightFloor"
    unfold_child = f"  unfold {cell}\n" if child else ""
    stem = name[0].upper() + name[1:]
    if na * nb * n_eta > MAX_SINGLE_SUBCELLS:
        return list(emit_partition(name, stem, root_modules[parent], text[1:], goal, na,
                                   nb * n_eta, unfold_child))

    for i in range(na):
        text.append(f"private theorem layer{i} : {goal} {i} = true := by\n"
                    f"{unfold_child}  replay_curvature_layer\n")
    cases = "".join(f"  · exact layer{i}\n" for i in range(na))
    text.append(f"theorem {name}_grid_layers (i : Fin {na}) : {goal} i = true := by\n  fin_cases i\n{cases}")
    text.append("end HlawkaSchatten.BelowExponent.Vertex\n")
    return [(stem, "\n".join(text))]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("zone", choices=ZONES)
    parser.add_argument("start", type=int, help="zero-based row offset in the selected zone")
    parser.add_argument("count", type=int)
    parser.add_argument("--build", action="store_true", help="replay the generated targets in batches")
    parser.add_argument("--refinements", type=Path, help="replace selected cells with finer prepared grids")
    args = parser.parse_args()
    prefix = args.zone[0].lower() + args.zone[1:]
    candidates = HERE / "vertex-curvature-candidates.tsv"
    rows = [line.split("\t") for line in candidates.read_text().splitlines() if line.startswith(prefix)]
    if args.refinements:
        overrides = [line.split("\t") for line in args.refinements.read_text().splitlines()]
        by_name = {row[0]: row for row in overrides}
        if len(by_name) != len(overrides) or by_name.keys() - {row[0] for row in rows}:
            parser.error("refinements must name distinct cells of the selected zone")
        rows = [by_name.get(row[0], row) for row in rows]
    end = args.start + args.count
    if args.start < 0 or args.count <= 0 or end > len(rows):
        parser.error(f"requested range outside the {len(rows)} rows of {args.zone}")
    modules = {cell: path.stem for path in (VERTEX / "RootData").glob("*.lean")
               for cell in CELLS.findall(path.read_text())}
    output = VERTEX / "CurvatureData"
    output.mkdir(exist_ok=True)
    selected = [row for row in rows[args.start:end] if row[0] not in ("vcM0", "scS0")]
    for offset in range(0, len(selected), BUILD_BATCH):
        batch = selected[offset:offset+BUILD_BATCH]
        targets = []
        for row in batch:
            name = row[0]
            stem = name[0].upper() + name[1:]
            for module, contents in emit(row, modules):
                path = output / (module + ".lean")
                if not path.exists() or path.read_text() != contents:
                    path.parent.mkdir(exist_ok=True, parents=True)
                    path.write_text(contents)
            targets.append(f"HlawkaSchatten.BelowExponent.Vertex.CurvatureData.{stem}")
        if args.build:
            start = time.monotonic()
            subprocess.run(["lake", "build", *targets], cwd=VERTEX.parents[2], check=True)
            elapsed = time.monotonic() - start
            print(f"Checked {batch[0][0]} through {batch[-1][0]} in {elapsed:.2f}s", flush=True)
        else:
            print("\n".join(targets))


if __name__ == "__main__":
    main()
