"""Encode the raw R002 certificate as Lean literals and shard its kernel checks."""

import argparse
from dataclasses import dataclass
import gzip
from hashlib import file_digest
from pathlib import Path
import re


HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent / "lean" / "HlawkaSchatten/BelowExponent" / "Tangent"
HEADER = "TANGENT-COVER-CERT v2 rc=1/500 eta=1/500 Dw=1073741824 KBOX=30 TAB=fine"
CODE_BITS = 10
SPLIT_BY_FACE = 900
ROW_BOX_BUDGET = 1350
SUBTREE_BOX_BUDGET = 320
SUBTREE_FILE_BUDGET = 480
# These closed cell checks reached the independent replay time limit.
REPLAY_FACE_SPLITS = {133, 139, 147, 154, 157}
PILOTS = (9, 23, 100, 165, 166)


@dataclass(frozen=True)
class Cell:
    index: int
    weights: list[int]
    faces: list[int]
    counts: list[int]

    @property
    def name(self):
        return f"R002_c{self.index}"

    @property
    def box_count(self):
        return sum(self.counts)


def encode_face(tokens):
    packed, offset, pending, leaves = 0, 0, 1, 0
    for token in tokens:
        assert pending > 0, "surplus row-tree token"
        if token in ("a", "b"):
            packed |= (token == "b") << offset
            offset += 2
            pending += 1
        else:
            ca, cb = map(int, token.split(","))
            assert 0 <= ca < 2**CODE_BITS and 0 <= cb < 2**CODE_BITS
            packed |= (2 | (ca << 2) | (cb << (2 + CODE_BITS))) << offset
            offset += 2 + 2 * CODE_BITS
            pending -= 1
            leaves += 1
    assert pending == 0
    return packed | (1 << offset), leaves


def read_cells(path):
    with gzip.open(path, "rt", encoding="ascii") as stream:
        assert next(stream).strip() == HEADER
        lines = [line.strip() for line in stream if line.strip()]
    tree, cells = [], []
    pending = 1
    for line in lines:
        assert pending > 0, "surplus profile-tree token"
        tag = line[0]
        if tag in ("R", "T"):
            label, first, second = line.split()
            tree.append((label, int(first), int(second)))
            pending += 1
            continue
        assert tag in ("c", "C")
        tree.append((tag,))
        pending -= 1
        if tag == "c":
            assert line == "c"
            continue
        weight_text, *streams = line[1:].split(";")
        weights = list(map(int, weight_text.split()))
        assert len(weights) == 7 and all(value >= 0 for value in weights)
        assert sum(weights[:4]) == 2**30 and sum(weights[4:]) <= 2**30
        assert len(streams) == 3
        faces, counts = zip(*(encode_face(face.split()) for face in streams), strict=True)
        cells.append(Cell(len(cells), weights, list(faces), list(counts)))
    assert pending == 0 and len(cells) == 167 and tree.count(("c",)) == 7
    assert sum(cell.box_count for cell in cells) == 69_129
    return tree, cells


def check_pilot_data(tree, cells, directory):
    source = (SOURCE / "TreeData.lean").read_text()
    literal_tree = re.search(r"def R002_tree : CT :=(.*?)def R002_geoms", source, re.S)[1]
    lean_tree = []
    for tag, first, second in re.findall(r"\.([TRcC])(?:\s+(\d+)\s+(\d+))?", literal_tree):
        lean_tree.append((tag, int(first), int(second)) if first else (tag,))
    assert lean_tree == tree
    for index in PILOTS:
        source = (directory / f"R002_Cell{index:03}.lean").read_text()
        vectors = re.search(r"p := \[([^]]+)\], g := \[([^]]+)\]", source)
        weights = [int(i) for i in re.findall(r"\d+", vectors[1] + ", " + vectors[2])]
        streams = [int(n, 16) for n in re.findall(r"\bf[123] := (0x[\da-f]+)", source)]
        assert weights == cells[index].weights and streams == cells[index].faces, index


def split_required(cell):
    return cell.index in REPLAY_FACE_SPLITS or cell.box_count >= SPLIT_BY_FACE


def shards(cells):
    """First run a short shard, then group small cells and isolate larger ones."""
    yield cells[:10]
    group, row_boxes = [], 0
    for cell in cells[10:]:
        split_faces = split_required(cell)
        if group and (split_faces or row_boxes + cell.box_count > ROW_BOX_BUDGET):
            yield group
            group, row_boxes = [], 0
        if split_faces:
            yield [cell]
        else:
            group.append(cell)
            row_boxes += cell.box_count
    if group:
        yield group


def nat_list(values):
    return "[" + ", ".join(map(str, values)) + "]"


def cell_literal(cell):
    n = cell.name
    p, g = nat_list(cell.weights[:4]), nat_list(cell.weights[4:])
    lines = [f"def {n} : CellData := {{", f"  p := {p}, g := {g},"]
    for face, packed in enumerate(cell.faces, 1):
        lines.append(f"  f{face} := {packed:#x}" + ("," if face < 3 else " }"))
    lines.append("")
    return lines


def cell_source(cell):
    n = cell.name
    return cell_literal(cell) + [
        f"theorem {n}_ok : cellOK R002_hdr (R002_geoms.getD {cell.index} default) {n} = true :=",
        "  by decide +kernel", "",
    ]


@dataclass(frozen=True)
class BoxNode:
    tag: int
    begin: int
    end: int
    fuel: int
    bounds: tuple[int, int, int, int]
    boxes: int
    children: tuple


def read_subtree(packed, offset, fuel, bounds):
    assert fuel > 0
    tag = (packed >> offset) % 4
    if tag == 2:
        return BoxNode(tag, offset, offset + 2 + 2*CODE_BITS, fuel, bounds, 1, ())
    a, b, c, d = bounds
    if tag == 0:
        m = (a+b)//2
        left, right = (a, m, c, d), (m, b, c, d)
    else:
        assert tag == 1
        m = (c+d)//2
        left, right = (a, b, c, m), (a, b, m, d)
    lhs = read_subtree(packed, offset + 2, fuel - 1, left)
    rhs = read_subtree(packed, lhs.end, fuel - 1, right)
    return BoxNode(tag, offset, rhs.end, fuel, bounds, lhs.boxes + rhs.boxes, (lhs, rhs))


def proof_name(cell, face, node):
    return f"{cell.name}_face{face}_bit{node.begin}"


def walk_statement(cell, face, node, visibility=""):
    rows = " ".join(map(str, node.bounds))
    name = proof_name(cell, face, node)
    stream = f"{cell.name}.f{face}"
    return [
        f"{visibility}theorem {name} :",
        f"    walkBox (mkCtx R002_hdr) {cell.name}_rowFace{face} {node.fuel}",
        f"      ({stream} >>> {node.begin}) {rows} = (true, {stream} >>> {node.end}) :=",
    ]


def split_face(cell, face, node, atomics, joins, limit):
    if node.boxes <= limit:
        atomics.append((face, node))
        return
    left, right = node.children
    split_face(cell, face, left, atomics, joins, limit)
    split_face(cell, face, right, atomics, joins, limit)
    method = "A" if node.tag == 0 else "B"
    joins.extend((
        *walk_statement(cell, face, node, "private "),
        f"  walkBox_split{method} (fuel := {node.fuel - 1}) (by decide +kernel)",
        f"    {proof_name(cell, face, left)} {proof_name(cell, face, right)}", "",
    ))


def numeric_header(*imports):
    return ["module", "", *(f"public import {name}" for name in imports), "",
            "@[expose] public section", "",
            "-- Generated by scripts/certificates/facet-vertex/generators/e2-production-generate.py from the R002 certificate.",
            "namespace TC", "", "set_option maxRecDepth 100000", "set_option maxHeartbeats 0", ""]


def split_cell(folder, stem, cell):
    n = cell.name
    module = f"HlawkaSchatten.BelowExponent.Tangent.Cells.{stem}"
    subtree_limit, file_limit = (160, 240) if cell.index in REPLAY_FACE_SPLITS else (
        SUBTREE_BOX_BUDGET, SUBTREE_FILE_BUDGET)
    parts = folder / stem
    parts.mkdir(exist_ok=True)
    data = numeric_header("HlawkaSchatten.BelowExponent.Tangent.TreeData") + cell_literal(cell)
    data += [f"def {n}_geom : Geom := R002_geoms.getD {cell.index} default", ""]
    for i, arguments in enumerate(("0 1 2", "1 0 2", "2 0 1"), 1):
        data.extend((
            f"def {n}_rowFace{i} : Face := mkFace (mkCtx R002_hdr)",
            f"    (cellVerts {n}_geom).1 (cellVerts {n}_geom).2 {n}.p {n}.g {arguments}", "",
        ))
    data += ["end TC"]
    write(parts / "Data.lean", data)
    yield f"{module}.Data", 0, len(data), "data"
    atomics, joins, face_joins = [], [], []
    for face, packed in enumerate(cell.faces, 1):
        root = read_subtree(packed, 0, 64, (0, 2**31, 0, 2**31))
        assert root.boxes == cell.counts[face - 1] and packed >> root.end == 1
        split_face(cell, face, root, atomics, joins, subtree_limit)
        face_joins.extend((
            f"private theorem {n}_face{face} :",
            f"    faceOK (mkCtx R002_hdr) {n}_rowFace{face} R002_hdr.KBOX {n}.f{face} = true :=",
            f"  faceOK_of_walkBox {proof_name(cell, face, root)}", "",
        ))
    groups, group, count = [], [], 0
    for face, node in atomics:
        if group and count + node.boxes > file_limit:
            groups.append(group)
            group, count = [], 0
        group.append((face, node))
        count += node.boxes
    groups.append(group)
    import_modules = []
    for index, group in enumerate(groups):
        part = f"Part{index:02}"
        qualified = f"{module}.{part}"
        import_modules.append(qualified)
        lines = numeric_header(f"{module}.Data", "HlawkaSchatten.BelowExponent.Tangent.WalkSplit")
        for face, node in group:
            lines.extend((*walk_statement(cell, face, node), "  by decide +kernel", ""))
        lines += ["end TC"]
        write(parts / f"{part}.lean", lines)
        yield qualified, sum(node.boxes for _, node in group), len(lines), "checks"
    lines = numeric_header("HlawkaSchatten.BelowExponent.Tangent.FaceJoin", *import_modules)
    lines += joins + face_joins + [
        f"theorem {n}_ok : cellOK R002_hdr (R002_geoms.getD {cell.index} default) {n} = true :=",
        f"  cellOK_of_faces R002_hdr {n}_geom " + " ".join(map(str, cell.weights)),
        f"    {n}.f1 {n}.f2 {n}.f3 (by decide +kernel)",
        f"    {n}_face1 {n}_face2 {n}_face3", "", "end TC",
    ]
    write(folder / f"{stem}.lean", lines)
    yield module, 0, len(lines), "cell"


def write(path, lines):
    assert len(lines) < 10_000
    content = "\n".join(lines) + "\n"
    if not path.is_file() or path.read_text() != content:
        path.write_text(content)


def generate(cells):
    folder = SOURCE / "Cells"
    folder.mkdir(exist_ok=True)
    modules = []
    print("module\tfirst\tlast\trow_boxes\tface_split\tlines\tkind")
    for group in shards(cells):
        first, last = group[0].index, group[-1].index
        stem = f"Cell{first:03}" if first == last else f"Cells{first:03}_{last:03}"
        module = f"HlawkaSchatten.BelowExponent.Tangent.Cells.{stem}"
        modules.append(module)
        if first == last and split_required(group[0]):
            for part, count, size, kind in split_cell(folder, stem, group[0]):
                print(f"{part}\t{first}\t{last}\t{count}\t1\t{size}\t{kind}")
            continue
        lines = numeric_header("HlawkaSchatten.BelowExponent.Tangent.TreeData")
        for cell in group:
            lines.extend(cell_source(cell))
        lines.append("end TC")
        write(folder / f"{stem}.lean", lines)
        total = sum(cell.box_count for cell in group)
        print(f"{module}\t{first}\t{last}\t{total}\t0\t{len(lines)}\tcell")
    lines = ["module", "", "public import HlawkaSchatten.BelowExponent.Tangent.Tree"]
    lines.extend(f"public import {module}" for module in modules)
    lines.extend(["", "@[expose] public section", "", "namespace TC", ""])
    lines.extend(["/-- Cell data in the order of the checked partition's non-centre leaves. -/",
                  "def R002_cells : List CellData := ["])
    lines.extend(f"  {cell.name}," for cell in cells[:-1])
    leaf_set = [
        "    walkCT R002_hdr R002_tree (root R002_hdr) = some R002_geoms ∧",
        "    R002_cells.length = R002_geoms.length ∧",
        "    ∀ i < R002_geoms.length,",
        "      cellOK R002_hdr (R002_geoms.getD i default) (R002_cells.getD i default) = true",
    ]
    lines += [
        f"  {cells[-1].name}]", "",
        "set_option maxRecDepth 10000 in",
        "theorem R002_cells_length : R002_cells.length = R002_geoms.length := by rfl",
        "",
        "set_option maxRecDepth 100000 in",
        "set_option maxHeartbeats 0 in",
        "/-- Symbolic assembly from the separately replayable arithmetic lemmas. -/",
        "theorem R002_leaf_set_of_checks",
    ]
    for cell in cells:
        lines.append(f"    (h{cell.index:03} : cellOK R002_hdr "
                     f"(R002_geoms.getD {cell.index} default) {cell.name} = true)")
    lines[-1] += " :"
    lines += [
        *leaf_set[:-1], leaf_set[-1] + " := by",
        "  have checked : CertifiedCells R002_hdr R002_geoms R002_cells := by",
        "    exact ⟨",
    ]
    lines.extend(f"      h{cell.index:03}," for cell in cells)
    lines += [
        "      True.intro⟩",
        "  exact ⟨R002_walkCT_eq, R002_cells_length, fun _ hi => checked.getD hi⟩",
        "",
        "set_option maxRecDepth 100000 in",
        "set_option maxHeartbeats 0 in",
        "/-- The checked partition lists exactly the geometries with indexed numeric certificates. -/",
        "theorem R002_leaf_set :",
        *leaf_set[:-1], leaf_set[-1] + " :=",
        "  R002_leaf_set_of_checks",
    ]
    lines.extend(f"    {cell.name}_ok" for cell in cells)
    lines += [
        "",
        "theorem R002_cellOK {i : Nat} (hi : i < R002_geoms.length) :",
        "    cellOK R002_hdr (R002_geoms.getD i default) (R002_cells.getD i default) = true :=",
        "  R002_leaf_set.2.2 i hi",
        "", "end TC",
    ]
    write(SOURCE / "Certificates.lean", lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("pilot", type=Path, help="directory with the audited Pilot cell literals")
    parser.add_argument("--split-cells", type=int, nargs="+", help="rebuild selected individual cell modules as parts")
    args = parser.parse_args()
    tree, cells = read_cells(args.certificate)
    check_pilot_data(tree, cells, args.pilot)
    with args.certificate.open("rb") as stream:
        print("Certificate SHA-256", file_digest(stream, "sha256").hexdigest())
    if args.split_cells:
        folder = SOURCE / "Cells"
        indices = sorted(set(args.split_cells))
        if any(not 0 <= index < len(cells) or not (folder / f"Cell{index:03}.lean").is_file()
               for index in indices):
            parser.error("--split-cells requires existing individual cell modules")
        print("module\tfirst\tlast\trow_boxes\tface_split\tlines\tkind")
        for index in indices:
            for part, count, size, kind in split_cell(folder, f"Cell{index:03}", cells[index]):
                print(f"{part}\t{index}\t{index}\t{count}\t1\t{size}\t{kind}")
    else:
        generate(cells)


if __name__ == "__main__":
    main()
