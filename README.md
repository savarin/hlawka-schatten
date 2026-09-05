# Hlawka inequalities for Schatten norms

A formal proof that every finite Schatten p-norm with 1 < p admits a
dimension-independent Hlawka constant, and that no such constant exists
at the trace norm (p = 1, dimension 2) or the operator norm
(p = infinity, dimension 3).

## Main results

- `PalomarHlawkaSchatten.dimension_independent_hlawka_constant_for_schatten_norms`
  (Challenge declaration): existence of a finite dimension-independent
  Hlawka constant for interior exponents, and failure at both endpoints.

The proof library constructs explicit constants from the compactified
scalar Bregman-to-Mazur ratio; the Challenge boundary quantifies
existentially over those constants.

## Scope

The interior theorem proves that for every p > 1, there exist positive
constants 0 < m <= M such that M/m is a Hlawka constant for the Schatten
p-norm, uniformly over all finite rectangular complex dimensions. The
proof lifts a scalar two-sided Bregman-to-Mazur estimate through spectral
overlap weights, transfers to rectangular operators via Hermitian dilation
and functional calculus, and closes the triple-to-pair comparison through
a radial Mazur map into Hilbert-Schmidt space.

At p = 1, a two-dimensional projector family forces the ratio of triple
deficit to pair-deficit sum above any proposed constant. At p = infinity,
three signed diagonal 3 x 3 matrices have all pair deficits zero and
positive triple deficit.

See [BLUEPRINT.md](BLUEPRINT.md) for the mathematical proof route.

## Trust boundary

The 78-line Mathlib-only [ExistenceChallenge.lean](ExistenceChallenge.lean)
exposes the Palomar boundary: one theorem, zero definition holes.
[ExistenceSolution.lean](ExistenceSolution.lean) delegates to the
sorry-free proof library under `HlawkaSchatten/`.

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

## Build and verify

Lean v4.33.0, Mathlib v4.33.0.

```bash
lake exe cache get
lake build
python3 scripts/check_boundary.py
```

Negative control (requires pinned Comparator and lean4export binaries):

```bash
COMPARATOR=<path> LEAN4EXPORT=<path> bash scripts/negative_control.sh
```

Optional Comparator smoke test:

```bash
COMPARATOR=<path> LEAN4EXPORT=<path> bash scripts/run_comparator.sh
```

Palomar runs its own pinned Comparator and NanoDa independently;
`enable_nanoda` is set to `false` in the local config because the NanoDa
binary is not distributed.

## Verification

The Comparator accepts the Challenge/Solution pair. The negative control
mutates the Challenge (strengthening `m ≤ M` to `M < m`) and confirms the
Comparator rejects the inconsistent boundary. `check_boundary.py` verifies
Mathlib-only imports, one deliberate sorry, and no unexpected axioms.

## License

Apache-2.0.
