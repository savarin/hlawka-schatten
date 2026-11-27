# Central and head certificates at the vertex

The central chart bounds the critical row on its middle and upper parameter ranges.
Each of the 120 sign-specific patches has a JSON record for its box and compressed
witness trees. The trees cover closed boxes through successive cuts. Lean checks
the leaves and joins the two signs on each box.

From the repository root, compare the generated modules with the proof sources.

```sh
python3 scripts/certificates/g3/central_chart.py --check HlawkaSchatten/BelowExponent/G3PCutBands
python3 scripts/certificates/g3/head_literals.py --check HlawkaSchatten/BelowExponent/G3HeadDataCore.lean
```

The first command reproduces the 1,427 Lean files from `plans.zip`, puts them into the
committed layout with [`layout.py`](../layout.py) and checks every file against `outputs.sha256`. To write those files elsewhere, pass `--output DIR`.
The archive contains the recorded subdivisions, rational endpoints and witnesses.

For 78 patches, a ratio chart replaces the part where the far-row center divided
by the signed row magnitude lies in `[-1,1]`. A tree in the original coordinates
covers the remainder, including zero row magnitude. The other 42 patches retain
the original construction. The total leaf count is 55,094, down from 82,005;
these counts describe the witnesses, not checking time.

The original `.json.gz` trees remain in the archive. Selected records add `ratio`
metadata and `.chart.json.gz` and `.remainder.json.gz` trees. `ratio-selection.json`
records the selection rule, original archive digest and counts for every patch.
The emitter performs no search. It checks signs, bounds and leaf counts before
writing the two trees. `ratioUnion_signedGap` proves their union covers the same
closed physical box, and `signed_box_pair` joins both signs without losing zero.

Each signed patch has a checked table of complete endpoint and sigma power inputs.
The geometry checker reuses a comparison only after an exact key match; otherwise
it performs the full comparison. Its exact fraction arithmetic is proved equivalent
to the original rational helpers on all inputs. Numeric modules import the checker
and table; the physical patch assembly imports the soundness proofs.

The second command reproduces the head chart’s 2,049 power bounds and 50 ratio
rows. With no arguments it writes the Lean table declarations to standard output.
Integer powers determine the nearest integer at scale `2^28`, and each positive
power enclosure has two units of outward padding. The generated table declarations
match the Lean source byte for byte. Its exact inequalities are in `headPowerOK` and `headRatioOK`.

Both scripts use the Python standard library. The Lean build checks the stored
certificates directly.
