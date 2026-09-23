# Hlawka inequalities for Schatten norms

Dimension-independent Hlawka constants for Schatten p-norms, formalized
in Lean 4 against Mathlib. Prepared for submission to
[Palomar](https://palomar-registry.org).

## Main results

- `PalomarHlawkaSchatten.dimension_independent_hlawka_constant_for_schatten_norms`
  (Challenge declaration): existence of a finite dimension-independent
  Hlawka constant for interior exponents, and failure at both endpoints.
- `PalomarHlawkaSchatten.ConstructionDiagonal.diagonal_hlawka_bound` and
  `diagonal_hlawka_sharp`: for every real `p ≥ 256`, an explicit cyclic
  maximum is admissible for complex diagonal Schatten norms in every finite
  dimension and sharp in each dimension at least three.
- `PalomarHlawkaSchatten.ConstructionDiagonal.cyclic_maximum_attained`:
  a cyclic parameter in `[1/2, 2]` attains that maximum.

## Scope

Hlawka's inequality says that in any inner product space, the triple
deficit is at most the sum of the pair deficits. For the Schatten p-norm
on linear maps between finite-dimensional complex inner product spaces,
the inequality fails in general but a dimension-independent multiplicative
constant C_p rescues it whenever 1 < p < ∞.

Audenaert and Kittaneh posed the existence of such a constant as an open
problem (arXiv:1201.5232, Section 8.2, Problem 7). The p = ∞ obstruction
was already noted there. This formalization supplies a proof of interior
finiteness, proves a new obstruction at p = 1 via a rank-one projector
family in dimension 2, and records the known p = ∞ obstruction with an
explicit 3 × 3 diagonal witness. The sharp value of the interior constant
for arbitrary operators remains open.

The proof obtains an admissible constant M_p / m_p as the extrema of
a compactified scalar Bregman-to-Mazur ratio. The scalar comparison is
derived directly from the convexity of the power potential; it does not
invoke the Ball–Carlen–Lieb uniform convexity/smoothness theorems,
although the approach was motivated by their framework. The ratio lifts
to operators via spectral overlap weights, transfers to rectangular
operators via Hermitian dilation, and closes through a radial Mazur map
into Hilbert–Schmidt space where the classical Hlawka inequality applies.

The project also determines the sharp constant for complex diagonal
Schatten norms, or equivalently scalar ℓ_p spaces. No explicit sharp
Hlawka constant for ℓ_p spaces valid at infinitely many exponents
appears in the Marinescu–Niculescu survey (arXiv:2407.03278),
Audenaert–Kittaneh (arXiv:1201.5232) and its forward citations, or
recent Schatten-norm work through September 2026. The
generic-norm counterexample theorem (an informal verified result
from the proof development, not formalized in Lean) shows that a
sharp equal-norm reduction cannot hold for arbitrary
smooth strictly convex norms, so the ℓ_p structure is essential.

The proof reduces real coordinate triples to three dimensions,
localizes a hypothetical strict counterexample near the cyclic sign
matrix using an explicit scalar confinement, and proves convexity of
the sharp deficit on that region. Permutation averaging gives the
cyclic bound. Circle averaging then transfers the result to complex
coordinates, and the diagonal singular-value identity identifies their
norm with the Schatten norm. The theorem includes unequal-norm triples;
it assumes no equal-norm reduction. The construction does not settle
exponents below 256 or sharpness for general matrices.

The audience is researchers in operator inequalities, noncommutative
L^p geometry, and the formalization community working on functional
analysis in Lean/Mathlib. No Hlawka constant material exists in Mathlib
at the pinned revision (v4.34.0). Cross-prover novelty has not been
searched.

See [BLUEPRINT.md](BLUEPRINT.md) for both proof routes, the explicit
constant formulas, the diagonal module map, and formalization choices.

## Trust boundary

Each result has a separate Mathlib-only Challenge and a Solution delegating
to the sorry-free proof library under `HlawkaSchatten/`:

| Challenge | Solution | Selected theorems | Definition holes |
|---|---|---:|---:|
| [ExistenceChallenge.lean](ExistenceChallenge.lean) | [ExistenceSolution.lean](ExistenceSolution.lean) | 1 | 0 |
| [ConstructionDiagonalChallenge.lean](ConstructionDiagonalChallenge.lean) | [ConstructionDiagonalSolution.lean](ConstructionDiagonalSolution.lean) | 3 | 0 |

The diagonal Challenge defines the norm directly through singular values,
and specifies the constant by a complete formula and compact supremum.
Only the selected Challenge theorems contain deliberate `sorry` holes.

- Imports: Mathlib only
- Permitted axioms: `propext`, `Classical.choice`, `Quot.sound`

## Proof architecture

```
ScalarBregman ─── ScalarRatio
                      │
               SchattenNorm ─── HilbertSchmidt
                      │               │
              SpectralLift ──── Variational
                      │               │
           HermitianSpectral    MazurGapComparison
                      │               │
           HermitianDilation ─── Final ─── Classification
                                             │
                              TraceEndpoint  EndpointObstruction
```

The diagonal library is assembled by
[HlawkaSchatten/DiagonalConstruction.lean](HlawkaSchatten/DiagonalConstruction.lean).
Its modules separate dimension reduction, scalar confinement, joint
coordinate geometry, the Hessian comparison, orbit averaging, and transfer
to complex diagonal operators.

## Build and verify

Lean and Mathlib v4.34.0 are pinned.

```bash
lake exe cache get
lake build
python3 scripts/check_boundary.py
python3 scripts/check_boundary.py comparator-construction-diagonal.json
```

Negative control (requires pinned Comparator and lean4export binaries):

```bash
COMPARATOR=<path> LEAN4EXPORT=<path> bash scripts/negative_control.sh
COMPARATOR=<path> LEAN4EXPORT=<path> bash scripts/negative_control.sh comparator-construction-diagonal.json
```

Optional Comparator smoke test:

```bash
COMPARATOR=<path> LEAN4EXPORT=<path> bash scripts/run_comparator.sh
COMPARATOR=<path> LEAN4EXPORT=<path> bash scripts/run_comparator.sh comparator-construction-diagonal.json
```

Both scripts default to `comparator-existence.json`. On macOS, setting
`FAKE_LANDRUN` to Comparator's development shim permits an unsandboxed local
smoke test; this does not reproduce the protected submission environment.

Palomar runs its own pinned Comparator, Landrun sandbox, and NanoDa
kernel independently; `enable_nanoda` is set to `false` in the local
config because the NanoDa binary is not distributed.

## Verification

Each negative control requires the unmodified baseline to pass, mutates one
Challenge theorem, confirms that the mutated boundary still elaborates, and
requires rejection of that specific theorem. The existence mutation replaces
`m ≤ M` with `M < m`; the diagonal mutation strengthens the range from
`p ≥ 256` to `p ≥ 255`. This tests statement matching, not whether the
stronger diagonal theorem is mathematically false. The script restores both
the original source and its compiled artifact on exit.

`check_boundary.py` validates the closed Comparator schema,
verifies Mathlib-only imports, checks the deliberate sorry count, confirms
each selected declaration is present in the Challenge, and audits that all
declarations use only the permitted axioms.

Validated locally on 2026-09-22: the full Lake build, both boundary/axiom
audits, both Comparator baselines, and both negative controls passed.
Comparator at upstream `8d84e67` used the Lean 4.33-compatible exporter and the macOS development
Landrun shim. Its default Lean kernel accepted the solutions; protected
Landrun/NanoDa validation was not run locally.

CI builds both proof libraries and checks both publication boundaries.
Palomar replays every proof through its protected NanoDa kernel at
submission, independently of local settings.

## License

Apache-2.0.
