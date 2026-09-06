# Hlawka inequalities for Schatten norms

Dimension-independent Hlawka constants for Schatten p-norms, formalized
in Lean 4 against Mathlib. Prepared for submission to
[Palomar](https://palomar-registry.org).

## Main results

- `PalomarHlawkaSchatten.dimension_independent_hlawka_constant_for_schatten_norms`
  (Challenge declaration): existence of a finite dimension-independent
  Hlawka constant for interior exponents, and failure at both endpoints.

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
remains open.

The proof obtains an admissible constant M_p / m_p as the extrema of
a compactified scalar Bregman-to-Mazur ratio. The scalar comparison is
derived directly from the convexity of the power potential; it does not
invoke the Ball–Carlen–Lieb uniform convexity/smoothness theorems,
although the approach was motivated by their framework. The ratio lifts
to operators via spectral overlap weights, transfers to rectangular
operators via Hermitian dilation, and closes through a radial Mazur map
into Hilbert–Schmidt space where the classical Hlawka inequality applies.

The audience is researchers in operator inequalities, noncommutative
L^p geometry, and the formalization community working on functional
analysis in Lean/Mathlib. No Hlawka constant material exists in Mathlib
at the pinned revision (v4.33.0). Cross-prover novelty has not been
searched.

See [BLUEPRINT.md](BLUEPRINT.md) for the mathematical proof route.

## Trust boundary

The 79-line Mathlib-only [ExistenceChallenge.lean](ExistenceChallenge.lean)
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

Lean and Mathlib v4.33.0 are pinned.

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

Palomar runs its own pinned Comparator, Landrun sandbox, and NanoDa
kernel independently; `enable_nanoda` is set to `false` in the local
config because the NanoDa binary is not distributed.

## Verification

The Comparator accepts the Challenge/Solution pair. The negative control
requires the unmodified baseline to pass, then mutates the Challenge
(strengthening `m ≤ M` to `M < m`), confirms the mutated boundary still
elaborates, and verifies that Comparator rejects specifically the named
theorem. `check_boundary.py` validates the closed Comparator schema,
verifies Mathlib-only imports, checks the deliberate sorry count, confirms
each selected declaration is present in the Challenge, and audits that all
declarations use only the permitted axioms.

Last validated 2026-09-06 against the pinned Comparator and lean4export.
Palomar replays every proof through its protected NanoDa kernel at
submission, independently of local settings.

## License

Apache-2.0.
