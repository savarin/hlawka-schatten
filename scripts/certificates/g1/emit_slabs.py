"""Write compact G1 slab proofs with four-bin kernel checks."""

import argparse
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import layout  # noqa: E402  (scripts/certificates/layout.py)


def slab_source(index):
    lines = [
        "module",
        "",
        "public import HlawkaSchatten.BelowExponent.G1CompactIntegerBlocks",
        "meta import Mathlib.Tactic.FinCases",
        "",
        f"/-! Exact corner comparisons for compact G1 slab {index}, four bins per check. -/",
        "",
        "public section",
        "",
        "namespace HlawkaSchatten.BelowExponent",
        "",
        "open G1CompactData",
        "",
        "set_option maxRecDepth 16000",
        "set_option maxHeartbeats 0",
    ]
    for label, endpoint in (("left", "false"), ("right", "true")):
        for block in range(16):
            lines.extend([
                "",
                f"private theorem {label}Block{block:02d} : intSideBlock {index} {endpoint} {block} = true := by",
                "  decide +kernel",
            ])
        lines.extend([
            "",
            f"private theorem {label}Blocks (block : Fin 16) : intSideBlock {index} {endpoint} block = true := by",
            "  fin_cases block",
        ])
        lines.extend(f"  · exact {label}Block{block:02d}" for block in range(16))
    lines.extend([
        "",
        f"theorem compactCornerChecks{index:02d} : ∀ right j, compactCornersOK {index} right j := by",
        f"  apply compactCorners_of_blocks (i := {index})",
        "  intro right",
        "  cases right",
        "  · exact leftBlocks",
        "  · exact rightBlocks",
        "",
        "end HlawkaSchatten.BelowExponent",
        "",
    ])
    return "\n".join(lines)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    parser.add_argument("slabs", type=int, choices=range(13), nargs="+")
    args = parser.parse_args()
    for slab in args.slabs:
        path = args.directory / f"Slab{slab:02d}.lean"
        source = layout.to_repo(f"HlawkaSchatten/BelowExponent/G1CompactSlabs/{path.name}", slab_source(slab))
        if not path.exists() or path.read_text() != source:
            path.write_text(source)
