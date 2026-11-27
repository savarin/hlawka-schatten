"""Emit VC coefficient literals from the checked point declarations and prove their exact equality."""
from pathlib import Path
import argparse
import subprocess
import tempfile

PROJECT = Path(__file__).resolve().parents[3] / "lean"
NPOINTS = 882
ENCODER = r"""
open HlawkaSchatten.BelowExponent.Vertex

private def interval (b : DyadicBounds) : String := s!"⟨{b.lo}, {b.hi}, {b.ok}⟩"
private def vec (xs : List String) : String := "#v[" ++ String.intercalate ", " xs ++ "]"
private def literal (P : OuterPointBounds) : String :=
  let ds := vec (P.diagonal.toList.map interval)
  let cs := vec (P.coupling.toList.map fun row => vec (row.toList.map interval))
  let args := vec (P.argument.toList.map fun v => s!"{v.num}/{v.den}")
  s!"⟨{ds}, {cs}, {args}⟩"

def main : IO Unit := do
  for (p,roots) in inputs do
    IO.println (literal (OuterPointBounds.atPoint p.a p.b p.eta p.margin roots))
"""


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cut", action="store_true", help="Use the revised, coarser curvature budgets")
    args = parser.parse_args()
    family = "VcCutCorners" if args.cut else "VcCornerData"
    prefix = "vcCutP" if args.cut else "vcOuterP"
    output = PROJECT / "HlawkaSchatten/BelowExponent/Vertex" / ("VcCutCorners" if args.cut else "VcCornerBounds")
    names = [f"{prefix}{i:03}" for i in range(NPOINTS)]
    chunks = list(range(0, NPOINTS, 32))
    modules = [f"HlawkaSchatten.BelowExponent.Vertex.{family}.Points{offset:03}" for offset in chunks]
    subprocess.run(["lake", "build", "HlawkaSchatten.BelowExponent.Vertex.OuterRowCheck", *modules], cwd=PROJECT, check=True)
    imports = ["HlawkaSchatten.BelowExponent.Vertex.OuterRowCheck", *modules]
    header = "".join(f"import {module}\n" for module in imports)
    values = ",\n".join(f"  ({name}, {name}Roots)" for name in names)
    inputs = "\nopen HlawkaSchatten.BelowExponent.Vertex\n\ndef inputs : Array (SideCornerEntry × (Fin 3 → RatBounds)) := #[\n"
    with tempfile.TemporaryDirectory(prefix="hlawka-vc-bounds-") as temporary:
        source = Path(temporary) / "Emit.lean"
        source.write_text(header + inputs + values + "]\n" + ENCODER)
        result = subprocess.run(["lake", "env", "lean", "--run", source], cwd=PROJECT,
                                capture_output=True, text=True, check=True)
    records = result.stdout.splitlines()
    if len(records) != NPOINTS or not all(v.startswith("⟨#v[") and v.endswith("]⟩") for v in records):
        raise ValueError("Lean did not return all 882 point literals")
    output.mkdir(exist_ok=True)
    for start, module in zip(chunks, modules, strict=True):
        body = [f"module\n\npublic import {module}\npublic import HlawkaSchatten.BelowExponent.Vertex.OuterRowCheck\n",
                "@[expose] public section\n\nnamespace HlawkaSchatten.BelowExponent.Vertex\n"]
        for name, value in zip(names[start:start+32], records[start:start+32], strict=True):
            body.append(f"def {name}Bounds : OuterPointBounds := {value}\n"
                        f"theorem {name}_bounds_eq : {name}Bounds = .atPoint {name}.a {name}.b "
                        f"{name}.eta {name}.margin {name}Roots := by decide +kernel\n")
        body.append("end HlawkaSchatten.BelowExponent.Vertex\n")
        path = output / f"Bounds{start:03}.lean"
        content = "\n".join(body)
        if not path.is_file() or path.read_text() != content:
            path.write_text(content)
    print(f"Emitted {len(records)} coefficient witnesses from {len(chunks)} VC point modules")


if __name__ == "__main__":
    main()
