# Reproducing the below-exponent certificates

Lean reads the committed witnesses and proves their bounds. The generators below provide a separate check of where those witnesses came from. Run the commands from the repository root with Python 3.11 or later and the Lean toolchain in `lean-toolchain`.

Each generator writes a plain Lean module. [`layout.py`](layout.py) then gives it the form of the committed files: the licence header, a one-line description naming the region and the generating script, and the elaboration settings the proof was written under. The comparisons below are made after that step.

| Region | Checked input and reproduction | Where the real inequality is proved |
|---|---|---|
| Bulk E2 and center | `bulk-tables` reproduces the fine power table and the subdivision tree. `e2` emits 167 Lean modules certifying all 167 cells of the retained tangent cover. The center has an analytic covariance bound. | [Bulk](../../HlawkaSchatten/BelowExponent/AdaptiveCoverage.lean) |
| Facet interior | `facet-interior` reads three retained prism records and emits 235 modules. | [Interior](../../HlawkaSchatten/BelowExponent/FacetArchive/Complete.lean) |
| Edge junction | Joins the balanced edge limit to its overlap estimate. The source manifest below pins these inputs. | [Edge junction](../../HlawkaSchatten/BelowExponent/BalancedJunctions.lean) |
| Balanced edge G1 | The committed rational witnesses supply 26 blocks of 64 triples. The slab emitter writes all 13 kernel-check modules. | [Balanced edge](../../HlawkaSchatten/BelowExponent/G1Complete.lean) |
| Facet strip F | `fslab` computes the rational schedule and emits 165 modules using the fine power table. | [Strip](../../HlawkaSchatten/BelowExponent/FSlabData/Complete.lean) |
| Deep facet G2 | `facet-g2` emits 80 modules from the retained upper and tip prism witnesses. | [Deep facet](../../HlawkaSchatten/BelowExponent/FacetG2/Complete.lean) |
| Vertex middle VC | `vertex` emits the root and curvature records and the direct point decisions. | [Vertex middle](../../HlawkaSchatten/BelowExponent/Vertex/CurvatureCut/VcComplete.lean) |
| Vertex band VC | Uses the same curvature proof and point bounds as the middle. | [Vertex band](../../HlawkaSchatten/BelowExponent/Vertex/CurvatureCut/VcComplete.lean) |
| Vertex side SC | `vertex` emits the side assembly and shared inputs. Lean-assisted samples reconstruct an outer point and a complete packed near-cone cell. | [Vertex side](../../HlawkaSchatten/BelowExponent/Vertex/SideCutCorners/CoarseComplete.lean) |
| Vertex edge | Reuses the balanced edge limit and the head, low and side charts at the vertex. | [Vertex edge](../../HlawkaSchatten/BelowExponent/G3EdgeComplete.lean) |
| Vertex corner G3 | The recorded central-chart plans reproduce all 1,307 middle and upper files, choosing ratio charts with a physical remainder on 78 patches. Integer powers reproduce the 2,049 power bounds and 50 ratio rows in the head. | [Vertex corner](../../HlawkaSchatten/BelowExponent/G3Wider.lean) |

### Commands

To regenerate and byte-compare all 2,221 Python-emitted Lean files and the G3 head table, run the first command. The remaining commands isolate individual families, pin the junction inputs and reproduce a Lean-assisted side witness.

```sh
python3 scripts/certificates/check.py
python3 scripts/certificates/facet-vertex/emit.py e2 --output /tmp/hlawka-e2
python3 scripts/certificates/g3/central_chart.py --check HlawkaSchatten/BelowExponent/G3PCutBands
python3 scripts/certificates/g3/head_literals.py --check HlawkaSchatten/BelowExponent/G3HeadDataCore.lean
mkdir -p /tmp/hlawka-g1
python3 scripts/certificates/g1/emit_slabs.py /tmp/hlawka-g1 0 1 2 3 4 5 6 7 8 9 10 11 12
diff -r /tmp/hlawka-g1 HlawkaSchatten/BelowExponent/G1CompactSlabs
shasum -a 256 -c scripts/certificates/regional-inputs.sha256
lake build HlawkaSchatten.BelowExponent.BalancedJunctions HlawkaSchatten.BelowExponent.G3EdgeComplete
python3 scripts/certificates/facet-vertex/side_sample.py 0
```

The [facet and vertex guide](facet-vertex/README.md) lists each family and its inputs. The [central and head guide](g3/README.md) describes the G3 witness format. The [proof guide](../../BLUEPRINT.md#below-exponent-proof-library) maps each certificate to its theorem and the final assembly.
