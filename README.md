# Dimension-independent Hlawka constants for Schatten norms

Two results on Hlawka's inequality for Schatten p-norms, formalized in
Lean 4 against Mathlib and prepared for submission to
[Palomar](https://palomar-registry.org). **Existence:** a finite
dimension-independent Hlawka constant exists for every 1 < p < ∞, and none
exists at either endpoint. **Construction:** for complex diagonal matrices
and every real p ≥ 256, the sharp constant is an explicit cyclic maximum
K_p.

## Main results

Existence, stated in [ExistenceChallenge.lean](ExistenceChallenge.lean):

- `PalomarHlawkaSchatten.dimension_independent_hlawka_constant_for_schatten_norms`:
  for every real p > 1 there are 0 < m ≤ M such that M / m is a Hlawka
  constant for the Schatten p-norm on linear maps between any
  finite-dimensional complex inner product spaces; no constant exists for
  the trace norm on 2 × 2 operators or the operator norm on 3 × 3
  matrices.

Construction, stated in
[ConstructionDiagonalChallenge.lean](ConstructionDiagonalChallenge.lean)
(namespace `PalomarHlawkaSchatten.ConstructionDiagonal`), for every real
p ≥ 256:

- `diagonal_hlawka_bound`: K_p is a Hlawka constant for the Schatten
  p-norm on complex diagonal matrices of every size;
- `diagonal_hlawka_sharp`: from size three up, no smaller constant works;
- `cyclic_maximum_attained`: some t ∈ [1/2, 2] attains K_p.

## The two results

Hlawka's inequality says that in an inner product space the triple
deficit N(x) + N(y) + N(z) − N(x + y + z) is at most the sum of the three
pair deficits N(x) + N(y) − N(x + y). For the Schatten p-norm it fails in
general. Audenaert and Kittaneh asked whether a multiplicative constant
C_p, independent of dimension, rescues it (arXiv:1201.5232, Section 8.2,
Problem 7), and noted that none exists at p = ∞.

The existence result answers their question. A finite constant exists for
every 1 < p < ∞, and none exists at either endpoint. The obstruction at
p = 1 is new: a rank-one projector family in dimension 2. The known
obstruction at p = ∞ is recorded with an explicit witness, the diagonal
matrices diag(−1, 1, 1), diag(1, −1, 1), diag(1, 1, −1). The proof yields
the admissible constant M_p / m_p but does not identify the smallest one.

The construction identifies the smallest constant in the commutative
case. For complex diagonal matrices of size at least three (equivalently,
complex ℓ_p spaces) and every real p ≥ 256, it is K_p: the largest ratio
of triple deficit to pair-deficit sum along the cyclic family
(−t, 1, 1), (1, −t, 1), (1, 1, −t) with t ∈ [1/2, 2]. The family's t = 1
member is the p = ∞ witness above, and the library proves
939p/2000 < K_p ≤ p, so the sharp diagonal constant grows linearly in p,
in line with the failure at p = ∞. Because diagonal matrices are
operators, every Hlawka constant for the Schatten p-norm on n × n complex
matrices with n ≥ 3 is at least K_p (immediate from the two Challenge
statements; not stated separately in Lean). The exponent cutoff p ≥ 256
is sufficient for the proof; no optimality of the cutoff is claimed.

This repository does not determine the sharp constant for general
operators, nor the diagonal constant for 1 < p < 256.

## How the proofs work

The existence proof compares the Bregman divergence of the scalar power
potential |t|^p / p with the squared distance between scalar Mazur
images. The quotient extends continuously and positively to the
compactified real line, so compactness gives constants 0 < m_p ≤ M_p.
The comparison uses the convexity of the power potential directly; it
does not invoke the Ball–Carlen–Lieb uniform convexity and smoothness
theorems that motivated the approach. Spectral overlap weights lift it to
operators, Hermitian dilation carries it to rectangular operators, and a
radial Mazur map into Hilbert–Schmidt space closes the argument with the
classical Hlawka inequality.

The construction argues by contradiction. It reduces a counterexample to
three real coordinates, confines it near the cyclic sign triple, where
the sharp deficit is convex, and averages over permutations to reach a
member of the cyclic family, which satisfies the bound by the definition
of K_p. Circle averaging passes from real to complex entries, and the
singular-value identity for diagonal operators turns the coordinate norm
into the Schatten norm. Triples of unequal norms are included; no
equal-norm reduction is assumed. The construction reuses the existence
library's gap definitions, the convexity of |t|^p and the spectral trace
identity, but not the existence theorem.

[BLUEPRINT.md](BLUEPRINT.md) gives both proof routes step by step, the
explicit constants, and the import graph from each step to its Lean
modules.

## Novelty and audience

A search of the Marinescu–Niculescu survey (arXiv:2407.03278),
Audenaert–Kittaneh (arXiv:1201.5232) and its forward citations, and
recent Schatten-norm work through September 2026 found no prior proof of
either result. For ℓ_p spaces with p ∈ [1, 2], the sharp Hlawka constant
is 1 via the classical L^1 embedding; the novelty claim applies to
p > 2. The proofs have not been examined in depth by human experts;
novelty of the ideas has not been established. Cross-prover novelty has
not been searched.

The audience is researchers in operator inequalities, noncommutative L_p
geometry, and the formalization community working on functional analysis
in Lean/Mathlib. No Hlawka constant material exists in Mathlib at the
pinned revision (v4.35.0-rc2).

## Trust boundary

Each result has a separate Mathlib-only Challenge and a Solution delegating
to the sorry-free proof library under `HlawkaSchatten/`:

| Challenge | Solution | Selected theorems | Definition holes |
|---|---|---:|---:|
| [ExistenceChallenge.lean](ExistenceChallenge.lean) | [ExistenceSolution.lean](ExistenceSolution.lean) | 1 | 0 |
| [ConstructionDiagonalChallenge.lean](ConstructionDiagonalChallenge.lean) | [ConstructionDiagonalSolution.lean](ConstructionDiagonalSolution.lean) | 3 | 0 |

Both Challenges define the Schatten norm through Mathlib's singular values;
the diagonal Challenge also specifies the constant by an explicit formula
and a compact supremum. Only the selected Challenge theorems contain
deliberate `sorry` holes.

- Imports: Mathlib only
- Permitted axioms: `propext`, `Classical.choice`, `Quot.sound`

## Proof architecture

One Lake library, `HlawkaSchatten`, holds both proofs. The existence proof
lives in `HlawkaSchatten/` and closes in `Classification`; the construction
lives in `HlawkaSchatten/DiagonalConstruction/`, assembled by
[HlawkaSchatten/DiagonalConstruction.lean](HlawkaSchatten/DiagonalConstruction.lean).
The construction imports three existence modules — `GapComparison`,
`ScalarBregman` and `HermitianDilation` — for the gap definitions, the
convexity of |t|^p and the spectral trace identity. It imports neither
`Final` nor `Classification`, so the existence theorem is not a premise.
[BLUEPRINT.md § Code mapping](BLUEPRINT.md#code-mapping) maps each proof
step to its modules and main declarations.

## Build and verify

Lean and Mathlib v4.35.0-rc2 are pinned.

```bash
lake exe cache get
lake build
python3 scripts/check_boundary.py comparator-existence.json
python3 scripts/check_boundary.py comparator-construction-diagonal.json
```

Negative controls (require the pinned Comparator and a lean4export built for
the toolchain in `lean-toolchain`):

```bash
COMPARATOR=<path> LEAN4EXPORT=<path> bash scripts/negative_control.sh comparator-existence.json
COMPARATOR=<path> LEAN4EXPORT=<path> bash scripts/negative_control.sh comparator-construction-diagonal.json
```

Optional Comparator smoke tests:

```bash
COMPARATOR=<path> LEAN4EXPORT=<path> bash scripts/run_comparator.sh comparator-existence.json
COMPARATOR=<path> LEAN4EXPORT=<path> bash scripts/run_comparator.sh comparator-construction-diagonal.json
```

On macOS, setting `FAKE_LANDRUN` to Comparator's development shim permits an
unsandboxed local smoke test; this does not reproduce the protected submission
environment.

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

`check_boundary.py` validates the closed Comparator schema, verifies
Mathlib-only direct imports, checks the deliberate sorry count, confirms
each selected declaration is present in the Challenge, and audits that each
selected declaration uses only the permitted axioms. The zero sorry count
in the metadata refers to the Solutions and proof library; the Challenges
deliberately contain sorry placeholders that the Solutions fill.

Validated locally on 2026-09-22: the full Lake build and both boundary/axiom
audits pass at `b3375b8` with Lean and Mathlib v4.35.0-rc2. The last Comparator
and negative-control runs on record passed at `79aa498` on v4.33.0 with
Comparator at upstream `8d84e67`, the macOS development Landrun shim, and
the default Lean kernel.

CI builds the library and both Challenge/Solution pairs and runs both
boundary audits. Palomar replays every proof through its protected NanoDa
kernel at submission, independently of local settings.

## License

Apache-2.0.
