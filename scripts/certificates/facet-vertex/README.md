# Facet, bulk and vertex certificates

Run `python3 scripts/certificates/facet-vertex/emit.py FAMILY --output NEW_DIRECTORY` from the project root. The emitter validates the retained inputs, regenerates the source in a temporary directory, puts each file into the committed layout with [`layout.py`](../layout.py) and verifies it against its SHA-256 manifest before writing the result. It uses the Python standard library. The enclosing checkout supplies the project sources.

| Family | Lean files | Input |
|---|---:|---|
| `bulk-tables` | 2 | The original fine power table and the E2 tree declarations |
| `e2` | 167 | Tree table, E2 certificate and five pilot witness files |
| `fslab` | 165 | Fine table and the slab schedule, which reconstructs the input JSONL |
| `facet-interior` | 235 | Fine table and the F0–F2 facet prism records |
| `facet-g2` | 80 | Fine table and retained tip and upper-forest witnesses |
| `vertex` | 252 | Corner grid, five vertex witness files and recorded curvature and margin bounds |

The [catalog](catalog.json) pins the inputs, generator records, table hashes and per-family output manifests. The 16 source witnesses are included in [witnesses.zip](witnesses.zip). An existing archive with the same layout and hashes can be used with `--archive-root DIR`. Use `--lean-source DIR` to select another copy of the pinned source literals.

For E2 the retained gzip has SHA-256 `dd2ab2cf4ea21eb8c25e2b1ae58c56bb4dcb0c6af1aace4e1efd460eb0a7ef3f`. On November 21, 2026, the original proposer used the parameters below with Python 3.13.18, NumPy 2.5.3 and SciPy 1.18.1. The catalog distinguishes the proposer revision used in that run from the later archive copy. The deterministic emitter starts from the retained witness. Lean checks the 167 cells and their coverage.

```text
python3 tgen.py 1/500 1/500 certs/cert_v2_rc0.002_eta0.002.txt --mu 2e-6 --tab fine --dw 30 --kbox 30 --kmax 18 --maxleaves 40000
```

For VC, the emitted direct checks cover 882 corner points. For SC, `python3 scripts/certificates/facet-vertex/side_sample.py 0` independently constructs the 12 outer trees for point zero and compares the complete Lean file, after the layout step. The same command accepts a point from 0 through 879. The Lean-assisted preparation sources are retained in `compiled-preparation/`; they import the library with `meta import`, so `lake env lean --run` can execute them under the module system. The archived outer preparation drivers retain the import names of the earlier grid. The release command uses the cut root table and generator in `support/`, outside the proof library. The [regional guide](../README.md) identifies the final theorems that use the bounds.


A second side sample reconstructs the near-cone certificate for cell 2. It contains 137 row rectangles and 763 leaves, and its rows cite the shared axis bank `SideConeAxisBank.lean`. The bank has one entry for each distinct axis interval listed in `side-axis-bank-bounds.txt` (85 lines), and the same driver regenerates it.

```sh
lake build HlawkaSchatten.BelowExponent.Vertex.SideConeCoarseTree HlawkaSchatten.BelowExponent.Vertex.SideConeFastTree HlawkaSchatten.BelowExponent.Vertex.SideConeParameterGrid
lake env lean --run scripts/certificates/facet-vertex/compiled-preparation/sc-near-coarse-prepare.lean --production-banked /tmp/hlawka-banked 2 3
python3 scripts/certificates/layout.py /tmp/hlawka-banked/Cell2.lean --as HlawkaSchatten/BelowExponent/Vertex/SideConeCoarseData/Cell2.lean
cmp /tmp/hlawka-banked/Cell2.lean HlawkaSchatten/BelowExponent/Vertex/SideConeCoarseData/Cell2.lean
lake env lean --run scripts/certificates/facet-vertex/compiled-preparation/sc-near-coarse-prepare.lean --axis-bank-production /tmp/hlawka-banked/SideConeAxisBank.lean scripts/certificates/facet-vertex/side-axis-bank-bounds.txt
python3 scripts/certificates/layout.py /tmp/hlawka-banked/SideConeAxisBank.lean --as HlawkaSchatten/BelowExponent/Vertex/SideConeAxisBank.lean
cmp /tmp/hlawka-banked/SideConeAxisBank.lean HlawkaSchatten/BelowExponent/Vertex/SideConeAxisBank.lean
```
