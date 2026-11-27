"""Pack the existing signed G1 ordinates without changing their values."""

import argparse
import ast
from pathlib import Path
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import layout  # noqa: E402

ROOT = Path(__file__).resolve().parents[3]
RELATIVE = "HlawkaSchatten/BelowExponent/G1CompactOrdinateTable.lean"


def source():
    text = (ROOT / "HlawkaSchatten/BelowExponent/G1CompactDataCore.lean").read_text()
    values = ast.literal_eval("[" + re.search(
        r"def lowerOrdinates : Array ℤ := #\[(.*?)\]", text, re.S)[1] + "]")
    assert len(values) == 65
    bias = max(0, -min(values))
    bits = max(n + bias for n in values).bit_length()
    packed = sum((n + bias) << (bits*i) for i, n in enumerate(values))
    assert all(((packed >> (bits*i)) & (2**bits-1))-bias == n
               for i, n in enumerate(values))
    text = "\n".join([
        "module", "", "public import HlawkaSchatten.BelowExponent.G1CompactDataCore", "",
        "/-! Packed signed ordinates for the compact G1 integer corner check. -/", "",
        "@[expose] public section", "",
        "namespace HlawkaSchatten.BelowExponent.G1CompactData", "",
        f"def compactOrdinateBias : Nat := {bias}",
        f"def compactOrdinateBits : Nat := {bits}",
        f"def packedLowerOrdinates : Nat := {packed:#x}", "",
        "end HlawkaSchatten.BelowExponent.G1CompactData", "",
    ])
    return layout.to_repo(RELATIVE, text)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    path, generated = ROOT / RELATIVE, source()
    if args.check:
        assert path.read_text() == generated, "Packed G1 ordinates differ from the source table"
        print("Packed G1 ordinates match the source table.")
    else:
        path.write_text(generated)
