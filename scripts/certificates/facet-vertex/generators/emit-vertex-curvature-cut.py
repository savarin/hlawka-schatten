"""Emit the checked curvature cut on the original closed VC and SC parameter grids."""

import argparse
from dataclasses import dataclass
from fractions import Fraction
import json
from math import prod
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
LAYOUT = runpy.run_path(str(HERE / "emit-vertex-curvature.py"))
PREFIX = "HlawkaSchatten.BelowExponent.Vertex.CurvatureCut"
DESTINATION = HERE.parent / "lean" / "HlawkaSchatten/BelowExponent" / "Vertex" / "CurvatureCut"
CELLS_PER_INPUT_FILE = 32
SUBCELLS_PER_CHECK_FILE = 32
FAMILIES = {
    "VcMiddle": ("vcCutMiddleCertificates", "vcMiddleRefinedGrid", "VcParameterGrid", "vcCutMiddleLinks"),
    "VcBand": ("vcCutBandCertificates", "vcBandParameterGrid", "VcParameterGrid", "vcCutBandLinks"),
    "Side": ("scCutCurvatureCertificates", "scParameterGrid", "SideConeParameterGrid", "scCutLinks"),
}


@dataclass(frozen=True)
class Certificate:
    name: str
    counts: tuple[int, int, int]
    caps: tuple[Fraction, ...]
    weight_floor: Fraction
    margins: tuple[Fraction, ...]
    fallback: bool

    @property
    def stem(self):
        return self.name if self.fallback else self.name + "Cut"


def read_plan():
    result = {}
    for line in (HERE / "vertex-curvature-cut-plan.tsv").read_text().splitlines():
        name, old_size, size, a, b, depth, fallback, floor, *values = line.split("\t")
        counts = int(a), int(b), int(depth)
        if name in result or len(values) != 12 or fallback not in ("true", "false"):
            raise ValueError(f"Invalid curvature plan row for {name}")
        keep = fallback == "true"
        if (keep and counts != (0, 0, 0)) or (not keep and prod(counts) != int(size)):
            raise ValueError(f"Invalid curvature grid for {name}")
        if int(size) > int(old_size):
            raise ValueError(f"The new grid grew for {name}")
        result[name] = Certificate(name, counts, tuple(map(Fraction, values[:9])),
                                   Fraction(floor), tuple(map(Fraction, values[9:])), keep)
    return result


def write(name, imports, description, declarations):
    contents = LAYOUT["numeric_module"](imports, description, declarations)
    dest = DESTINATION / f"{name}.lean"
    if not dest.exists() or dest.read_text() != contents:
        dest.write_text(contents)


def box_literal(spans):
    return "⟨" + ", ".join(f"⟨{lo}, {hi}⟩" for lo, hi in spans) + "⟩"


def input_declarations(cert, spans, roots, vector):
    name = cert.stem
    caps = vector(vector(cert.caps[k:k+3]) for k in range(0, 9, 3))
    line = f"""def {name}Cell : ParameterCell := {box_literal(spans)}
def {name}Roots : Fin 3 → RatBounds := {vector(f"⟨{lo}, {hi}⟩" for lo, hi in roots)}
def {name}Caps : Fin 3 → Fin 3 → ℚ := {caps}
def {name}WeightFloor : ℚ := {cert.weight_floor}
def {name}Margins : Fin 3 → ℚ := {vector(cert.margins)}

theorem {name}_roots_ok : {name}Cell.rootsOK {name}Roots = true := by decide +kernel

theorem {name}_caps_nonneg (k i : Fin 3) : 0 ≤ {name}Caps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem {name}_margin_le (i : Fin 3) : curvatureLoss {name}Cell {name}Caps i ≤ {name}Margins i := by
  fin_cases i <;> decide +kernel
"""
    return line


def layer_declaration(cert, layer):
    name = cert.stem
    na, nb, depth = cert.counts
    return f"""theorem {name}_layer{layer} : gridLayerCurvatureOK
    {name}Cell {name}Roots {na} {nb} {depth} {name}Caps {name}WeightFloor {layer} = true := by
  replay_curvature_layer
"""


def certificate_expression(cert):
    name = cert.stem
    counts = ""
    if cert.fallback:
        if name == "vcM58":
            return "  vcM58PilotCertificate"
        proof = f"{name}_grid_layers"
    else:
        na, nb, depth = cert.counts
        counts = f"\n    (na := {na}) (nb := {nb}) (nη := {depth})"
        layers = "\n".join(f"      · exact {name}_layer{i}" for i in range(cert.counts[0]))
        proof = "(by\n      intro i\n      fin_cases i\n" + layers + ")"
    return f"""  CurvatureCellCertificate.of_layer_checks (c := {name}Cell) (roots := {name}Roots)
    (caps := {name}Caps) (weightFloor := {name}WeightFloor) (margins := {name}Margins){counts}
    {name}_roots_ok {proof}
    (by decide +kernel) {name}_caps_nonneg {name}_margin_le (by decide) (by decide +kernel)"""


def list_declarations(table, lean_type, values):
    chunks = []
    declarations = []
    for start in range(0, len(values), CELLS_PER_INPUT_FILE):
        name = f"{table}{start:03}"
        chunks.append(name)
        joined = ",\n  ".join(values[start:start+CELLS_PER_INPUT_FILE])
        declarations.append(f"def {name} : List ({lean_type}) := [\n  {joined}]\n")
    joined = " ++\n  ".join(chunks)
    declarations.append(f"def {table} : List ({lean_type}) :=\n  {joined}\n")
    return declarations


def emit_family(family, entries, root_intervals, vector):
    table, grid, geometry, _ = FAMILIES[family]
    fresh = [(cert, spans) for cert, spans, _ in entries if not cert.fallback]
    input_modules = {}
    for start in range(0, len(fresh), CELLS_PER_INPUT_FILE):
        group = fresh[start:start+CELLS_PER_INPUT_FILE]
        source = f"{family}Inputs{start:03}"
        for cert, _ in group:
            input_modules[cert.name] = f"{PREFIX}.{source}"
        write(source, ["public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCheck", "meta import Mathlib.Tactic.FinCases"],
              "Parameter boxes and exact curvature budgets for the cut.",
              [input_declarations(cert, spans, root_intervals(spans), vector) for cert, spans in group])

    checks = []
    pending = []
    volume = 0

    def flush():
        if not pending:
            return
        source = f"{family}Checks{len(checks):03}"
        deps = sorted({input_modules[cert.name] for cert, _ in pending})
        write(source, [*(f"public import {dep}" for dep in deps),
                       "meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureReplay", *(f"meta import {dep}" for dep in deps)],
              "Kernel arithmetic proofs for the closed curvature subcells.",
              [layer_declaration(cert, k) for cert, k in pending])
        checks.append((f"{PREFIX}.{source}", pending.copy(), volume))

    for cert, _ in fresh:
        na, nb, depth = cert.counts
        for layer in range(na):
            if pending and volume + nb * depth > SUBCELLS_PER_CHECK_FILE:
                flush()
                pending.clear()
                volume = 0
            pending.append((cert, layer))
            volume += nb * depth
    flush()

    fallbacks = []
    for cert, _, _ in entries:
        if cert.fallback:
            if cert.name == "vcM58":
                fallbacks.append("public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcM58Pilot.Certificate")
                continue
            old = "CurvaturePilotVcM" if cert.name == "vcM0" else "CurvatureData." + cert.name[0].upper() + cert.name[1:]
            fallbacks.append(f"public import HlawkaSchatten.BelowExponent.Vertex.{old}")
    expressions = [certificate_expression(cert).removeprefix("  ") for cert, _, _ in entries]
    write(family, ["public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCertificates",
                   f"public import HlawkaSchatten.BelowExponent.Vertex.{geometry}", "meta import Mathlib.Tactic.FinCases",
                   *(f"public import {source}" for source, _, _ in checks), *fallbacks],
          "Checked curvature and weights on the same closed parameter grid.", [
              *list_declarations(table, "CurvatureCellCertificate", expressions),
              "set_option maxRecDepth 30000 in\nset_option maxHeartbeats 0 in",
              f"theorem {table}_cells :\n"
              f"    {table}.map CurvatureCellCertificate.cell = {grid} := by\n  decide +kernel",
          ])
    return checks


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("corner_index", type=Path)
    args = parser.parse_args()
    plan = read_plan()
    index = json.loads(args.corner_index.read_text())
    root_intervals = runpy.run_path(str(HERE / "vertex_root_witnesses.py"))["root_intervals"]
    vector = LAYOUT["vector"]
    families = {name: [] for name in FAMILIES}
    for family, data in index.items():
        points = [tuple(map(Fraction, point)) for point in data["points"]]
        for cell in data["cells"]:
            zone, parent = cell["zone"], cell["parent"]
            name = f"{zone[0].lower()}{zone[1:]}{parent}"
            if name not in plan:
                name += f"Child{cell['child']}"
            indices = cell["corners"]
            spans = list(zip(points[indices[0]], points[indices[-1]], strict=True))
            dest = "Side" if family == "SC" else "VcMiddle" if zone == "VcM" else "VcBand"
            families[dest].append((plan[name], spans, indices))
    families["VcMiddle"].sort(key=lambda item: "Child" in item[0].name)
    if {cert.name for rows in families.values() for cert, _, _ in rows} != plan.keys():
        raise ValueError("The candidate plan and the indexed cells differ")
    if [len(rows) for rows in families.values()] != [250, 212, 510]:
        raise ValueError("Incorrect cell counts for the three regional grids")
    DESTINATION.mkdir(parents=True, exist_ok=True)
    addresses = []
    for family, entries in families.items():
        checks = emit_family(family, entries, root_intervals, vector)
        for mod, layers, volume in checks:
            roots = ",".join(f"HlawkaSchatten.BelowExponent.Vertex.{cert.stem}_layer{k}" for cert, k in layers)
            print(mod, volume, roots, sep="\t")
        address_name = FAMILIES[family][3]
        values = ["#v[" + ", ".join(map(str, indices)) + "]" for _, _, indices in entries]
        addresses.extend(list_declarations(address_name, "Vector Nat 8", values))
    write("Addresses", ["public import HlawkaSchatten.BelowExponent.Vertex.CornerPointData"],
          "The eight shared corner indices for each curvature certificate.", addresses)


if __name__ == "__main__":
    main()
