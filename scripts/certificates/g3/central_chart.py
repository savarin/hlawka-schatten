"""Reproduce the middle and upper central-chart Lean modules from their witness trees."""

import argparse
from fractions import Fraction as F
import gzip
from hashlib import sha256
import json
from pathlib import Path
from tempfile import NamedTemporaryFile
from zipfile import ZipFile
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import layout  # noqa: E402  (scripts/certificates/layout.py)


HERE = Path(__file__).resolve().parent
MODULE = "HlawkaSchatten.BelowExponent.G3PCutBands"
GRIDS = {"Mid": (F(1, 20), F(3, 20), 10, 8), "Top": (F(3, 20), F(1, 5), 10, 16)}
PLAN_SHA = "ec5a05e56dfaab486dfdcd566e2a767986d10ec26958a9eb00c70b617aaf0fa2"
MANIFEST_SHA = "07468a12f17bc7d68d20a41375c8203a23c433ad17d238162b0b2b707858d41c"

def lean_witness(data):
    low, high, jensen, far = data
    jw = ".zero" if jensen[0] == "zero" else f"(.direct {jensen[1]} {jensen[2]})"
    if far[0] == "variance":
        fw = f"(.variance {far[1]})"
    else:
        _, factor, left, right = far
        if factor[0] == "universal":
            ff = ".universal"
        elif factor[0] == "midpoint":
            ff = "(.midpoint ⟨" + ", ".join(map(str, factor[1:])) + "⟩)"
        else:
            ff = "(.secant " + " ".join(map(str, factor[1:])) + ")"
        fw = f"(.chord {ff} {left} {right})"
    return f"⟨{low}, {high}, {jw}, {fw}⟩"


def lean_tree(node, depth=1):
    if len(node) == 1:
        label, *data = node[0]
        return f".{label}" if label in ("cone", "empty") else f".row {lean_witness(data[0])}"
    axis, knot, left, right = node
    indent = "  " * (depth + 1)
    return (f".cut {axis} ({knot})\n{indent}({lean_tree(left, depth + 1)})"
            f"\n{indent}({lean_tree(right, depth + 1)})")


def leaf_count(node):
    return 1 if len(node) == 1 else leaf_count(node[2]) + leaf_count(node[3])


def module_source(imports, code):
    declarations = "\n".join("public import " + name for name in imports)
    return (f"module\n\n{declarations}\n\n@[expose] public section\n\n"
            f"namespace HlawkaSchatten.BelowExponent.G3P\n\n{code}\n\nend HlawkaSchatten.BelowExponent.G3P\n")


def lean_box(box):
    lo, hi = (", ".join(str(b[k]) for b in box) for k in (0, 1))
    return f"⟨![{lo}], ![{hi}]⟩"


def tree_declarations(name, box, tree, sign, proof):
    positive = "true" if sign > 0 else "false"
    return f"""def {name}Box : Box := {box}

set_option maxRecDepth 16000 in
def {name}Tree : CertTree :=
  {tree}

set_option maxRecDepth 16000 in
theorem {name}_checked : {name}Tree.commonOK {name}Box {positive} = true := {proof}"""


def emit_tree(write, name, box, sign, tree, size):
    """Shard only at existing tree nodes and use the very same child boxes in each join."""
    root_box = lean_box(box)
    dependencies = []

    def subtree(node, cell):
        if leaf_count(node) <= size:
            part = f"{name}Part{len(dependencies)}"
            dependencies.append(MODULE + "." + part)
            code = tree_declarations(part, cell, lean_tree(node), sign, "by decide +kernel")
            write(f"{part}.lean", module_source(["HlawkaSchatten.BelowExponent.G3PCommonDen"], code))
            return part + "Tree", part + "_checked"
        axis, knot, lower, upper = node
        lt, lp = subtree(lower, f"({cell}).lowerChild {axis} ({knot})")
        rt, rp = subtree(upper, f"({cell}).upperChild {axis} ({knot})")
        return (f".cut {axis} ({knot}) ({lt}) ({rt})",
                f"CertTree.commonCut_ok ({lp}) ({rp})")

    if leaf_count(tree) <= size:
        code = tree_declarations(name, root_box, lean_tree(tree), sign, "by decide +kernel")
        dependencies = ["HlawkaSchatten.BelowExponent.G3PCommonDen"]
    else:
        root, proof = subtree(tree, f"({root_box} : Box)")
        code = tree_declarations(name, root_box, root, sign, proof)
    write(f"{name}.lean", module_source(dependencies, code))


def metadata(archive, group, i, j):
    records = []
    for sign, suffix in ((1, "Pos"), (-1, "Neg")):
        name = f"{group}{i:02}H{j:02}{suffix}"
        record = json.loads(archive.read(name + ".json"))
        if (record["group"], record["sigma"], record["height"], record["sign"], record["name"]) != (
                group, i, j, sign, name) or not record["merged"]:
            raise ValueError(f"The plan for {name} does not describe the expected central chart")
        records.append(record)
    return records


def box_pair_proof(pos, neg, hlow, hhigh, slow, shigh):
    return (f"exact box_pair {pos} {neg} hh hσ hσ₁ hCap hs hz\n"
            f"      (by simpa using {hlow}) (by simpa using {hhigh}) "
            f"(by simpa using {slow}) (by simpa using {shigh})")


def gap_statement(name, h0, h1, s0, s1):
    return f"""theorem {name} {{h σ s z : ℝ}} (hh : 0 < h)
    (hσ : 0 < σ) (hσ₁ : σ ≤ 1 / 5) (hCap : h ≤ 1 / (2 - σ / (2 - σ)))
    (hLow : {h0} ≤ h) (hHigh : h ≤ {h1}) (sLow : {s0} ≤ σ)
    (sHigh : σ ≤ {s1}) (hs : |s| ≤ 1) (hz : |z| ≤ 8) :
    0 ≤ g3FacetGap h σ 1 s z := by"""


def emit_patch(write, archive, group, i, j):
    low, high, ns, nh = GRIDS[group]
    ds, dh = (high - low) / ns, F(9, 17) / nh
    h0, h1 = j * dh, (j + 2) * dh
    s0, s1 = low + i * ds, low + (i + 2) * ds
    base = f"Cut{group}{i // 2}H{j // 2}"
    imports = ["HlawkaSchatten.BelowExponent.G3PCertSound", "HlawkaSchatten.BelowExponent.G3PCommonDenSound"]
    for record, suffix in zip(metadata(archive, group, i, j), ("Pos", "Neg")):
        packed = archive.read(record["name"] + ".json.gz")
        box, sign, tree = json.loads(gzip.decompress(packed))
        bounds = [tuple(map(F, interval)) for interval in box]
        if (bounds != [(h0, h1), (s0, s1), (0, 1), (-8, 8)]
                or sign != record["sign"] or leaf_count(tree) != record["selected"]):
            raise ValueError(f"Wrong bounds, sign or leaf count in {record['name']}")
        emit_tree(write, base + suffix, box, sign, tree, 128)
        imports.append(MODULE + "." + base + suffix)
    pos, neg = [f"(CertTree.ok_of_commonOK {base}{sign}_checked)" for sign in ("Pos", "Neg")]
    body = gap_statement(base + "_gap", h0, h1, s0, s1)
    body += "\n  " + box_pair_proof(pos, neg, "hLow", "hHigh", "sLow", "sHigh")
    write(base + ".lean", module_source(imports, body))


def band_statement(name, s0, s1):
    return f"""theorem {name} {{h σ s z : ℝ}} (hh : 0 < h)
    (hσ : 0 < σ) (hσ₁ : σ ≤ 1 / 5) (hCap : h ≤ 1 / (2 - σ / (2 - σ)))
    (sLower : {s0} ≤ σ) (sUpper : σ ≤ {s1}) (hs : |s| ≤ 1) (hz : |z| ≤ 8) :
    0 ≤ g3FacetGap h σ 1 s z := by"""


def emit_joins(write, group):
    low, high, ns, nh = GRIDS[group]
    ds, dh = (high - low) / ns, F(9, 17) / nh
    bands = []
    for i in range(0, ns, 2):
        prefix = f"Cut{group}{i//2}"
        bands.append(prefix + "Band")
        roots = [f"{prefix}H{j//2}" for j in range(0, nh, 2)]
        body = band_statement(prefix+"_gap", low+i*ds, low+(i+2)*ds)
        body += "\n  have h0 : (0 : ℝ) ≤ h := hh.le"
        for index, root in enumerate(roots):
            last = index+1 == len(roots)
            if last:
                body += "\n  have hHi := g3_h_max hσ₁ hCap"
            else:
                body += f"\n  rcases le_total h ({(index+1)*2*dh}) with hHi | h{index+1}"
            indent = "\n  " if last else "\n  · "
            body += indent + f"exact {root}_gap hh hσ hσ₁ hCap h{index} hHi sLower sUpper hs hz"
        write(bands[-1] + ".lean", module_source([MODULE+"."+r for r in roots], body))
    body = band_statement("cut_"+group.lower()+"_chart", low, high)
    for index in range(len(bands)):
        last = index+1 == len(bands)
        sl = "sLower" if index == 0 else f"s{index}"
        if not last:
            body += f"\n  rcases le_total σ ({low+(index+1)*2*ds}) with sHi | s{index+1}"
        indent = "\n  " if last else "\n  · "
        sh = "sUpper" if last else "sHi"
        body += indent + f"exact Cut{group}{index}_gap hh hσ hσ₁ hCap {sl} {sh} hs hz"
    write(f"Cut{group}Complete.lean", module_source([MODULE+"."+b for b in bands], body))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check", type=Path, metavar="LEAN_DIR", help="compare with existing modules")
    mode.add_argument("--output", type=Path, metavar="DIR", help="write the generated modules here")
    args = parser.parse_args()
    archive_path = HERE / "plans.zip"
    manifest = (HERE / "outputs.sha256").read_bytes()
    if sha256(archive_path.read_bytes()).hexdigest() != PLAN_SHA or sha256(manifest).hexdigest() != MANIFEST_SHA:
        raise SystemExit("The input archive or output manifest has changed")
    expected = {name: digest for digest, name in (line.split("  ") for line in manifest.decode().splitlines())}
    produced = set()
    if args.output:
        args.output.mkdir(parents=True, exist_ok=True)

    def write(name, text):
        data = layout.to_repo(f"HlawkaSchatten/BelowExponent/G3PCutBands/{name}", text).encode("utf-8")
        if name in produced or sha256(data).hexdigest() != expected.get(name):
            raise ValueError(f"Unexpected output for {name}")
        produced.add(name)
        if args.check:
            if (args.check / name).read_bytes() != data:
                raise ValueError(f"Contents differ in {name}")
        else:
            target = args.output / name
            if not target.exists() or target.read_bytes() != data:
                with NamedTemporaryFile(dir=args.output, delete=False) as temp:
                    temp.write(data)
                Path(temp.name).replace(target)

    with ZipFile(archive_path) as archive:
        for group, (_, _, ns, nh) in GRIDS.items():
            for i in range(0, ns, 2):
                for j in range(0, nh, 2):
                    emit_patch(write, archive, group, i, j)
            emit_joins(write, group)
    if produced != set(expected):
        raise ValueError("Generated filenames differ from the release manifest")
    if args.check and {p.name for p in args.check.glob("*.lean")} != produced:
        raise ValueError("The supplied directory has a different set of Lean files")
    print(f"Verified {len(produced)} modules against SHA-256 manifest {MANIFEST_SHA}")


if __name__ == "__main__":
    main()
