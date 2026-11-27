"""Write the revised VC points, keeping the original checked fifth-root intervals."""
import csv
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
POINTS = HERE / "vertex-curvature-cut-shared-margins.tsv"
ORIGINAL = HERE / "vertex-corner-curvature-margins.tsv"
OUTPUT = HERE.parent / "lean/HlawkaSchatten/BelowExponent/Vertex/VcCutCorners"
NAMESPACE = "HlawkaSchatten.BelowExponent.Vertex"


def records(source):
    with source.open() as f:
        result = [r for r in csv.DictReader(f, delimiter="\t") if r["family"] == "VC"]
    if [int(r["corner"]) for r in result] != list(range(882)):
        raise ValueError("Expected 882 VC points in index order")
    return [(tuple(Fraction(r[k]) for k in ("a","b","eta")),
             tuple(Fraction(r[f"margin{i}"]) for i in range(3))) for r in result]


def save(name, imports, body):
    text = "\n".join(["module", "", *[f"public import {m}" for m in imports], "",
                      "@[expose] public section", "", f"namespace {NAMESPACE}", "", *body,
                      "", f"end {NAMESPACE}", ""])
    path = OUTPUT / f"{name}.lean"
    if not path.exists() or path.read_text() != text:
        path.write_text(text)


def main():
    old, current = records(ORIGINAL), records(POINTS)
    if any(a != b for (a,_),(b,_) in zip(old,current,strict=True)):
        raise ValueError("The revised point indices do not match the existing coordinates")
    OUTPUT.mkdir(exist_ok=True)
    arrays, modules = [], []
    for start in range(0,len(current),32):
        suffix = f"{start:03}"
        body, names = [], []
        for i, (coords, margins) in enumerate(current[start:start+32], start):
            prev, new = f"vcOuterP{i:03}", f"vcCutP{i:03}"
            names.append(new)
            a,b,eta = coords
            margin = ", ".join(map(str,margins))
            body.extend([f"def {new} : SideCornerEntry := ⟨{a}, {b}, {eta}, #v[{margin}]⟩",
                         f"abbrev {new}Roots := {prev}Roots",
                         f"theorem {new}_roots : {new}.cell.rootsOK {new}Roots = true := by decide +kernel", ""])
        block = "vcCutPoints" + suffix
        arrays.append(block)
        modules.append(f"{NAMESPACE}.VcCutCorners.Points{suffix}")
        body.extend([f"def {block} : Array SideCornerEntry := #[", "  " + ",\n  ".join(names) + "]"])
        save("Points"+suffix, [f"{NAMESPACE}.VcCornerData.Points{suffix}"], body)
    save("PointTable", modules, ["def vcCutPointBlocks : List (Array SideCornerEntry) := [",
         "  " + ",\n  ".join(arrays) + "]", "", "def vcCutPoints : Array SideCornerEntry :=",
         "  " + " ++\n  ".join(arrays), "", "theorem vcCutPoints_toList :",
         "    vcCutPointBlocks.flatMap Array.toList = vcCutPoints.toList := by",
         "  simp only [vcCutPointBlocks, vcCutPoints, List.flatMap_cons, List.flatMap_nil,",
         "    Array.toList_append, List.append_nil, List.append_assoc]"])
    print("882 VC coordinates matched;", sum(x[1]!=y[1] for x,y in zip(old,current,strict=True)),
          "changed margin vectors", flush=True)


if __name__ == "__main__":
    main()
