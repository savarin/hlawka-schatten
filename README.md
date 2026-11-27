# Dimension-independent Hlawka constants for Schatten norms

[![Palomar entry PALOMAR-2026-09-07-000005 (existence)](https://img.shields.io/badge/Palomar_%C2%B7_existence-PALOMAR--2026--09--07--000005-0b7285)](https://palomar-registry.org/entry?id=PALOMAR-2026-09-07-000005&version=1)
[![Palomar entry PALOMAR-2026-09-25-000006 (construction)](https://img.shields.io/badge/Palomar_%C2%B7_construction-PALOMAR--2026--09--25--000006-0b7285)](https://palomar-registry.org/entry?id=PALOMAR-2026-09-25-000006&version=1)

This project formalizes three results on Hlawka's inequality in Lean 4
against Mathlib. **Existence.** A finite dimension-independent Hlawka
constant exists for every 1 < p < ∞, and none exists at either endpoint.
**Construction.** For complex diagonal matrices of size at least three
and every real p ≥ 256, the sharp constant is an explicit cyclic maximum K_p.
**Constant one below the critical exponent.** In every finite-dimensional
real ℓ_p space, Hlawka's inequality holds with constant one for
2 ≤ p ≤ p_W = log(3)/log(3/2) ≈ 2.7095. Above p_W it fails in dimension
three and higher. Palomar, a public registry of machine-checked Lean proofs,
lists the first two results.
[Palomar records](#palomar-registry)

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

Constant one below the critical exponent, stated in
[ConstructionDiagonalBelowExponentChallenge.lean](ConstructionDiagonalBelowExponentChallenge.lean)
(namespace `HlawkaSchatten.LpThreshold`):

- `hlawka_holds_below_exponent` proves that for every real exponent
  2 ≤ p ≤ log(3)/log(3/2) and every natural dimension n, all triples
  x, y, z in real ℓ_pⁿ satisfy

  ```text
  ‖x+y‖ₚ + ‖y+z‖ₚ + ‖z+x‖ₚ ≤ ‖x‖ₚ + ‖y‖ₚ + ‖z‖ₚ + ‖x+y+z‖ₚ.
  ```

  The quantifiers include dimension zero and zero vectors.
  [Solution](ConstructionDiagonalBelowExponentSolution.lean) ·
  [Prove2Me statement](https://prove2.me/missions/Sharp_diagonal_Hlawka_constants%3A_lower_the_cutoff_to_2)

## Palomar registry

Palomar checked the following two entries at their respective commits.

| Result | Entry | Registered | Commit | Statements checked | Independent checkers |
|---|---|---|---|---|---|
| Existence | [PALOMAR-2026-09-07-000005](https://palomar-registry.org/entry?id=PALOMAR-2026-09-07-000005&version=1), version 1 | 2026-09-07 | [`97c3363`](https://github.com/savarin/hlawka-schatten/tree/97c3363af2722dd6e94ce4d3ef749fab1efab6bf) | [1 theorem](https://github.com/savarin/hlawka-schatten/blob/97c3363af2722dd6e94ce4d3ef749fab1efab6bf/ExistenceChallenge.lean) | nanoda |
| Construction | [PALOMAR-2026-09-25-000006](https://palomar-registry.org/entry?id=PALOMAR-2026-09-25-000006&version=1), version 1 | 2026-09-25 | [`1829591`](https://github.com/savarin/hlawka-schatten/tree/1829591140522193a81ae721330e4d775c81123e) | [3 theorems](https://github.com/savarin/hlawka-schatten/blob/1829591140522193a81ae721330e4d775c81123e/ConstructionDiagonalChallenge.lean) | nanoda, con-ron |

The theorem links open each Challenge file as registered. Between
`97c3363` and `1829591`, `ExistenceChallenge.lean` and
`ExistenceSolution.lean` changed in comments only.

For each entry, Palomar rebuilt the project at that entry's commit in a
sandbox. It confirmed that the Solution file (`ExistenceSolution.lean`,
`ConstructionDiagonalSolution.lean`) proves exactly the statements in its
Challenge (see [Trust boundary](#trust-boundary)), using no axioms beyond
`propext`, `Quot.sound` and `Classical.choice`. It then rechecked the
proofs with Lean's kernel and the independently written checkers in the
table. The construction entry lists two because it was checked on Lean
v4.35.0-rc2, which ships both; the existence entry was checked on v4.33.0.

Palomar's AI editorial review found no blocking problem and raised no
warnings on either entry. That review checks that each Lean statement
matches its written description and that the result has a plausible
research audience. Palomar is a registry, not a journal: the review does
not claim novelty and is not review by a human expert.

Each registration covers only the listed commit and its pinned
dependencies.

- Machine-readable records:
  [PALOMAR-2026-09-07-000005-v1.json](https://data.palomar-registry.org/entries/PALOMAR-2026-09-07-000005-v1.json),
  [PALOMAR-2026-09-25-000006-v1.json](https://data.palomar-registry.org/entries/PALOMAR-2026-09-25-000006-v1.json)
- Palomar's preserved copies of the source:
  [existence snapshot](https://github.com/PalomarArchive/savarin--hlawka-schatten--2a35a3d9f959/tree/palomar/PALOMAR-2026-09-07-000005-v1/97c3363af2722dd6e94ce4d3ef749fab1efab6bf),
  [construction snapshot](https://github.com/PalomarArchive/savarin--hlawka-schatten--2a35a3d9f959/tree/palomar/PALOMAR-2026-09-25-000006-v1/1829591140522193a81ae721330e4d775c81123e)

## The three results

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

In real ℓ_p spaces, the classical isometric embedding in L¹ gives
constant one for 1 ≤ p ≤ 2. The triple (−1, 1, 1), (1, −1, 1),
and (1, 1, −1), used by Witsenhausen and credited to D. M. and M. F.
Smiley, has three pair sums of norm 2. Its three vectors and their sum
each have norm 3^(1/p), so its inequality is 6 ≤ 4 · 3^(1/p). It fails
exactly when p > p_W. [Witsenhausen, Corollary 1.2 and Proposition 2](https://doi.org/10.1090/S0002-9939-1973-0390916-0)

The third result proves constant one for 2 ≤ p ≤ p_W in every finite
dimension, including Lee's endpoint conjecture in dimension three.
Together with the classical range and the signed triple, this gives
the exact range 1 ≤ p ≤ p_W for real ℓ_p in dimension at least three.
It answers Marinescu and Niculescu’s Problem 1 in the negative for
2 < p ≤ p_W. The Lean theorem covers 2 ≤ p ≤ p_W. In positive
dimension, the triple (x, −x, 0) with x ≠ 0 forces every admissible
constant to be at least one. In dimension zero both deficits vanish.
[Marinescu–Niculescu, Problem 1](https://arxiv.org/abs/2407.03278) ·
[Lee, Proposition 3.8 and Conjecture 4.9](https://arxiv.org/abs/2610.23785v1)

This repository does not determine the sharp constant for general
operators, the complex diagonal constant for 1 < p < 256, or the real
constant for p_W < p < 256. The Prove2Me problem also asks whether K_p
bounds every triple in real ℓ_p³ for p_W ≤ p ≤ 4. The lower endpoint
follows from this theorem and K_p ≥ 1 (not stated separately in Lean).
The external Prove2Me theorem `HlawkaSchatten.DiagonalCutoff4.cutoff4`
covers p ≥ 4. Its proof is maintained outside this repository. The
open interval is p_W < p < 4.
[Prove2Me statement](https://prove2.me/missions/Sharp_diagonal_Hlawka_constants%3A_lower_the_cutoff_to_2) ·
[Proved cutoff-4 theorem](https://prove2.me/theorems/0ee0074e-f0be-4d07-89a9-f8012acf0199)

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

At p_W the dual exponent is q = log₂ 3. Lee’s four-ball criterion
reduces the inequality for x, y, z and −(x + y + z) to finding a common
point of four ℓ_q unit balls. Klee’s intersection lemma gives the
covering reduction. The covering reduction and the bulk certificate were
produced with Claude Fable 5.2 (Anthropic) in a Claude Code session,
21 November 2026. Symmetry leaves one ordered
chamber. The proof covers it with eleven regions, using separate charts
and equality arguments where margins vanish at the boundary. Lean checks
the certificates and their coverage.
[Lee, Theorem 4.10](https://arxiv.org/html/2610.23785v1#S4.Thmtheorem10) ·
[Klee (1951), (2.1)](https://doi.org/10.4153/CJM-1951-031-2)

For 2 < p < p_W, independent positive stable variables express the ℓ_p
norm as a scaled average of ℓ_{p_W} norms. Lee uses this averaging
argument in dimension three. Molchanov and Nagel proved a broader
nesting result for norms represented by diagonal scalings. The Lean
proof constructs the stable laws and carries out the averaging in every
finite dimension. At p = 2 the norm is Euclidean.
[Lee, Theorem 4.6](https://arxiv.org/html/2610.23785v1#S4.Thmtheorem6) ·
[Molchanov–Nagel, Lemma 4.9 and Theorem 4.12](https://arxiv.org/abs/1806.08036)

[BLUEPRINT.md](BLUEPRINT.md) gives the three proof routes step by step, the
explicit constants, and the import graph from each step to its Lean
modules.

## Novelty and audience

A search of the Marinescu–Niculescu survey (arXiv:2407.03278),
Audenaert–Kittaneh (arXiv:1201.5232) and its forward citations, and
recent Schatten-norm work through September 2026 found no prior proof of
the first two results. A further search on November 21, 2026 found no
resolution of Lee’s Conjecture 4.9. For positive-dimensional real ℓ_p
spaces with p ∈ [1, 2], the sharp Hlawka constant is 1 via the classical
L^1 embedding; the novelty claim applies to p > 2. The proofs have not
been examined in depth by human experts; novelty of the ideas has not
been established. Cross-prover novelty has not been searched.

AI agents developed and reviewed the written argument, generated
certificates and formalized the third result under the author's
direction. Most of its 4,180 modules, in `HlawkaSchatten/BelowExponent/`, contain
generated certificate data. A case-insensitive search for Hlawka in the pinned
Mathlib sources returned no matches.

The audience is researchers in operator inequalities, noncommutative L_p
geometry, real ℓ_p geometry, and the formalization community working on
functional analysis in Lean/Mathlib.

## Trust boundary

Each result has a separate Mathlib-only Challenge and a Solution delegating
to the sorry-free proof library under `HlawkaSchatten/`.

| Challenge | Solution | Selected theorems | Definition holes |
|---|---|---:|---:|
| [ExistenceChallenge.lean](ExistenceChallenge.lean) | [ExistenceSolution.lean](ExistenceSolution.lean) | 1 | 0 |
| [ConstructionDiagonalChallenge.lean](ConstructionDiagonalChallenge.lean) | [ConstructionDiagonalSolution.lean](ConstructionDiagonalSolution.lean) | 3 | 0 |
| [ConstructionDiagonalBelowExponentChallenge.lean](ConstructionDiagonalBelowExponentChallenge.lean) | [ConstructionDiagonalBelowExponentSolution.lean](ConstructionDiagonalBelowExponentSolution.lean) | 1 | 0 |

The first two Challenges define the Schatten norm through Mathlib's
singular values. The high-exponent Challenge also specifies the
constant by an explicit formula and a compact supremum. The third
Challenge defines `pairGap`, `tripleGap`, `pairGapSum`,
`HasHlawkaConstant` and the finite coordinate norm `lpNorm` inline.
Only the selected Challenge theorems contain
deliberate `sorry` holes.

The vertex-curvature tactic uses `evalExpr` to compute witness tables.
Lean's kernel checks the resulting Boolean certificates.
[Witness replay](HlawkaSchatten/BelowExponent/Vertex/CurvatureReplay.lean)

- Imports: Mathlib only
- Permitted axioms: `propext`, `Classical.choice`, `Quot.sound`

## Proof architecture

One Lake library, `HlawkaSchatten`, holds all three proofs. The existence proof
lives in `HlawkaSchatten/` and closes in `Classification`; the construction
lives in `HlawkaSchatten/DiagonalConstruction/`, assembled by
[HlawkaSchatten/DiagonalConstruction.lean](HlawkaSchatten/DiagonalConstruction.lean).
The construction imports three existence modules — `GapComparison`,
`ScalarBregman` and `HermitianDilation` — for the gap definitions, the
convexity of |t|^p and the spectral trace identity. It imports neither
`Final` nor `Classification`, so the existence theorem is not a premise.
[BLUEPRINT.md § Code mapping](BLUEPRINT.md#code-mapping) maps each proof
step to its modules and main declarations.

The modules under `HlawkaSchatten/BelowExponent/` prove the third result. `RouteT` reduces the
endpoint to the scalar row inequality via norming and Klee's
intersection lemma. `Coverage` gives the eleven regions, and
`RegionalCertificates` assembles their proofs. `Assembly` adds the
Euclidean case and the stable-law transfer. `Complete` supplies
the unconditional theorem to the Solution.
[Endpoint reduction](HlawkaSchatten/BelowExponent/RouteT.lean) ·
[Regional proofs](HlawkaSchatten/BelowExponent/RegionalCertificates.lean) ·
[Unconditional theorem](HlawkaSchatten/BelowExponent/Complete.lean) ·
[Region and import map](BLUEPRINT.md#below-exponent-proof-library)

## Build and verify

This branch pins Lean v4.37.0-rc1 and Mathlib at the matching revision
`31ce06eaadf4a200c0e1407c5f10953cf606b8f8`. The third proof accounts
for most of the build time. A clean build of the 4,235 project modules
takes 37 min on a 16-core Apple M4 Max; the largest Lean process peaks
at 8.3 GB.

```bash
lake exe cache get
lake build
python3 scripts/check_boundary.py comparator-existence.json
python3 scripts/check_boundary.py comparator-construction-diagonal.json
python3 scripts/check_boundary.py comparator-construction-diagonal-below-exponent.json
```

For the first two results, the negative controls build an independently
strengthened Challenge and check that the toolchain's Comparator rejects it.

```bash
bash scripts/negative_control.sh comparator-existence.json
bash scripts/negative_control.sh comparator-construction-diagonal.json
```

The following command runs the complete below-exponent audit. It builds the
boundary, exports the Solution once, checks the original Challenge with
stock Lean and four-thread NanoDa, and compares the strengthened Challenge
with the same export. It writes logs, hashes and a verification receipt to
a new directory. On a trusted macOS checkout, add `--local` to use the
toolchain's unsandboxed development mode.

```bash
python3 scripts/verify_below_exponent.py --output /tmp/hlawka-below-verification
```

The [certificate guide](scripts/certificates/README.md) gives the input
manifests, regeneration commands and checking theorems for the eleven regions.

The scripts also accept a standalone Comparator and matching exporter via
`COMPARATOR` and `LEAN4EXPORT`. For that older runner on macOS, setting
`FAKE_LANDRUN` to its development shim permits an
unsandboxed local smoke test; this does not reproduce the protected submission
environment.

Palomar runs its own checks, independently of these local settings; each
entry's record lists the tools its run used (see
[Palomar registry](#palomar-registry)). The two older configurations retain their original
`enable_nanoda` field. Palomar supplies its protected checker configuration.

## Verification

Each negative control checks the original Challenge, strengthens one theorem,
elaborates it and requires a rejection naming that specific theorem. The existence mutation replaces
`m ≤ M` with `M < m`; the diagonal mutation strengthens the range from
`p ≥ 256` to `p ≥ 255`. The two older controls restore the source and compiled Challenge on exit.
The third extends the upper endpoint by one and builds both versions
in temporary directories against the pinned dependencies. Its positive and
negative comparisons use the same Solution bytes.

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

For the third result, on November 26, 2026, a clean local build with Lean
v4.37.0-rc1, the three boundary and axiom audits, the byte-for-byte
regeneration of the certificates and the two Lean-assisted side samples
passed. The stock Lean and NanoDa checks of the Solution export and the
strengthened-statement control are run with `verify_below_exponent.py`;
their results for this version are still to be recorded. Palomar allows
5.5 hours for setup, build, export and the mandatory checks together.

CI builds the whole repository on GitHub's standard runner in seven jobs:
one for the library, the statements and the smaller certificate groups,
five for the largest certificate groups side by side, and a final job
that builds the Solutions and runs the three boundary audits.
[Workflow](.github/workflows/build.yml)

## License

Apache-2.0.
