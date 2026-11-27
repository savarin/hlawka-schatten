# Central and head certificates at the vertex

The central chart bounds the critical row on its middle and upper parameter ranges.
Each of the 120 sign-specific patches has a JSON record for its box and a compressed
tree of witnesses. The trees cover the closed boxes through successive cuts. Lean
checks the leaves and joins the two signs on each box.

From the repository root, compare the generated modules with the proof sources.

```sh
python3 scripts/certificates/g3/central_chart.py --check HlawkaSchatten/BelowExponent/G3PCutBands
python3 scripts/certificates/g3/head_literals.py --check HlawkaSchatten/BelowExponent/G3HeadDataCore.lean
```

The first command reproduces the 1,528 Lean files from `plans.zip`, puts them into the
committed layout with [`layout.py`](../layout.py) and checks every file against `outputs.sha256`. To write those files elsewhere, pass `--output DIR`.
The archive contains the recorded subdivisions, rational endpoints and witnesses.

The second command reproduces the head chart’s 2,049 power bounds and 50 ratio
rows. With no arguments it writes the Lean table declarations to standard output.
Integer powers determine the nearest integer at scale `2^28`, and each positive
power enclosure has two units of outward padding. The generated table declarations
match the Lean source byte for byte. Its exact inequalities are in `headPowerOK` and `headRatioOK`.

Both scripts use the Python standard library. The Lean build checks the stored
certificates directly.
