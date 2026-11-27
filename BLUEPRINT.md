# Dimension-independent Hlawka constants for Schatten norms

## Target

Prove that for every Schatten exponent p > 1, there exists a finite
constant C_p such that for all linear maps X, Y, Z between finite-dimensional
complex inner product spaces of any dimension,

  N(X) + N(Y) + N(Z) - N(X+Y+Z) ≤ C_p [N(X)+N(Y)-N(X+Y) + N(X)+N(Z)-N(X+Z) + N(Y)+N(Z)-N(Y+Z)]

where N is the Schatten p-norm. Prove that no such constant exists at the
trace norm (p = 1, 2 × 2 operators) or the operator norm (p = ∞,
3 × 3 matrices). For every real p ≥ 256, determine the sharp constant for complex diagonal
Schatten norms. The cyclic family is the triple (−t, 1, 1), (1, −t, 1),
(1, 1, −t) for t > 0. Its singleton norms are A_p(t) = (t^p + 2)^(1/p),
its pair-sum norms are B_p(t) = (2 |1-t|^p + 2^p)^(1/p), and its total
norm is 3^(1/p) |2-t|, so its ratio of triple deficit to pair-deficit sum is

    R_p(t) = (3 A_p(t) - 3^(1/p) |2-t|) / (6 A_p(t) - 3 B_p(t)).

The constant K_p is the maximum of R_p over t ∈ [1/2, 2]. Prove that K_p
is admissible in every finite dimension and sharp in each dimension at
least three.

The third target is Hlawka's inequality with constant one on real
coordinates. For 2 ≤ p ≤ p_W = log(3)/log(3/2) and every n ≥ 0, the
triple deficit in ℝⁿ with the ℓ_p norm is at most the sum of the
three pair deficits. In dimension three the triple (−1, 1, 1),
(1, −1, 1), (1, 1, −1), credited by Witsenhausen to D. M. and
M. F. Smiley, breaks the bound for p > p_W. Its pair sums have norm
2, and the remaining four vectors have norm 3^(1/p).
[Formal statement](ConstructionDiagonalBelowExponentChallenge.lean) ·
[Witsenhausen, Proposition 2](https://doi.org/10.1090/S0002-9939-1973-0390916-0)

## Proof route

### Interior existence and endpoints

**Scalar comparison.** The scalar power potential t → |t|^p / p has
Bregman divergence β_p(a,b). Dividing by the squared distance of the
scalar Mazur images ψ_p(a) = sgn(a)|a|^{p/2} gives a quotient that extends
continuously and positively to the compactified real line. By compactness,
there exist 0 < m_p ≤ M_p with

  m_p |ψ_p(a) - ψ_p(b)|² ≤ β_p(a,b) ≤ M_p |ψ_p(a) - ψ_p(b)|².

**Spectral lift.** For two Hermitian operators with eigenbases {e_i}, {f_j},
the Bregman and squared-Mazur quantities decompose as double sums weighted
by |⟨e_i, f_j⟩|². These weights are nonnegative with rows and columns summing
to one, so the scalar two-sided estimate lifts without changing m_p, M_p.

**Hermitian dilation.** Every rectangular operator T embeds as the
off-diagonal block of a Hermitian operator whose Schatten p-norm is
2^{1/p} ‖T‖_p. The odd functional calculus extracts the rectangular
Mazur map, while the even functional calculus identifies its Schatten-2
power with the original Schatten-p power. The factor 2^{1/p} appears on
both sides of the deficit inequality and cancels.

**Variational comparison.** On the Schatten power sphere, weighted Bregman
objectives attain the triple/pair deficits; weighted squared Hilbert
distances attain twice the corresponding Schatten-2 gaps. Comparing minima
gives a two-sided inequality between deficits.

**Radial Mazur map.** A radial (non-spherical) version of the Mazur map
sends each operator to a Hilbert vector of the same individual norm,
removing the sphere normalization. Hilbert Hlawka bounds the mapped triple
deficit by the mapped pair deficits. Combining the triple upper estimate
with the three pair lower estimates yields the constant M_p/m_p.

**Trace norm endpoint (p = 1).** A family built from rank-one projectors,
parameterized by s, has triple deficit 4s² and pair-deficit sum at most
8s⁴; choosing s after a proposed constant gives a contradiction. The
calculation uses the exact 2D identity ‖T‖₁² = ‖T‖₂² + 2 normDet(T).

**Operator norm endpoint (p = ∞).** Three signed diagonal 3 × 3
matrices have all three pair deficits equal to zero but positive triple
deficit.

### Sharp diagonal constant (p ≥ 256)

The first route shows that some constant works, not which is smallest. On
complex diagonal matrices the smallest is K_p, and the operator-norm witness
above is the t = 1 member of the cyclic family that defines it: after
normalization, a strict counterexample would have to lie near that triple.
This route shares three inputs with the first — the gap definitions, the
convexity of |t|^p and the spectral trace identity for diagonal operators —
and does not use the existence theorem.

**Three-coordinate reduction.** Fix the three pair power sums and vary
nonnegative coordinate weights. The positive part of the desired inequality
is concave in those weights; a compact minimization produces a minimizer
supported on at most three coordinates.

**Scalar confinement.** The four vectors x, y, z, -(x+y+z) form a
zero-sum quadruple whose permutations preserve pair norms. Normalizing
singleton norms to sum to one and relabeling so the total norm is largest,
the weighted scalar convexity inequality with cyclic witness t = p^{-1/p}
and the function

    f_p(q) = (1 - q) / (2 (1 - ((1 + q^p) / 2)^{1/p}))

evaluated at q₀ = 53/150 give the separation chain

    f_p(q₀) < (939/2000) p < K_p ≤ p,     p ≥ 256

which confines a strict counterexample to total norm below q₀, with small
pair deficits.

**Coordinate localization.** Each nearly saturated pair chooses a
coordinate; two pairs cannot share one without violating the total-norm
bound. After reorienting, the triple lies in a radius-19/100 entrywise
box around J − 2I (the t = 1 member of the cyclic family).

**Curvature and averaging.** The Hessian coefficients

    b_p = (p-1) (43/100)^{p-2} / (3 (157/100)^{p-1})
    d_p = 2 (p-1) (38/100)^{p-2} / (162/100)^{p-1}

satisfy 1200 p d_p < b_p for p ≥ 256, making the sharp deficit convex
throughout the box. Permutation averaging yields a cyclic triple whose
bound follows from the definition of the constant.

**Complex and diagonal transfer.** Circle projections reproduce complex
norm powers up to a positive factor; the closed convex hull passes the
real bound to the circle integral. The diagonal singular-value identity
identifies the coordinate power sum with the Schatten norm.

**Sharpness and attainment.** The cyclic vectors embed into every
dimension at least three. Their ratio is continuous on [1/2, 2] and
attains a maximum by compactness; no closed formula for the maximizing
parameter is asserted.

### Constant one below the critical exponent

**Splitting the exponent range.** At p = 2, averaging the scalar
Hlawka inequality over Gaussian projections gives every finite
dimension. The argument below proves p_W, then transfers it to
2 < p < p_W. The interior-exponent proof handles dimensions 0 and
1 directly.
[Euclidean case](HlawkaSchatten/BelowExponent/Euclidean.lean) · [Assembly](HlawkaSchatten/BelowExponent/Assembly.lean)

**Transfer by positive stable laws.** For 2 < p < p_W let α = p/p_W
and take independent nonnegative Sᵢ with Laplace transform
E exp(−λSᵢ) = exp(−λ^α). For W = Σᵢ Sᵢ |xᵢ|^(p_W), independence gives
the Laplace transform exp(−λ^α ‖x‖ₚ^p). Hence W has the law of
‖x‖ₚ^(p_W) S₁ and E W^(1/p_W) = c_p ‖x‖ₚ, where
c_p = E S₁^(1/p_W) is positive and finite because 1/p_W < α.
This represents the norm as a scaled average of ℓ_{p_W} norms after
diagonal rescaling. Both deficits are linear in the norm, so the
inequality passes to the average. For the law, the proof takes a
compact limit of the laws of exp(−S) on [0, 1], where S is a finite
Pareto sum. The limit gives zero mass to 0, so applying u ↦ −log u
gives the stable law. A fractional moment formula gives c_p.
[Transfer](HlawkaSchatten/BelowExponent/Transfer.lean) · [Stable law](HlawkaSchatten/BelowExponent/StableLaw.lean) ·
[Fractional moment](HlawkaSchatten/BelowExponent/FractionalMoment.lean) ·
[Lee’s dimension-three transfer](https://arxiv.org/html/2610.23785v1#S4.Thmtheorem6) ·
[Stable-law nesting, Molchanov–Nagel](https://arxiv.org/abs/1806.08036)

**The endpoint as a row inequality.** At p_W the dual exponent is
q = log₂ 3, so 2^q = 3. Write x₀ = x, x₁ = y, x₂ = z and
x₃ = −(x + y + z). The inequality bounds the sum of the three pair
norms by Σ_s ‖x_s‖. Use the sign rows (+++), (−−+), (−+−)
and (+−−). Let r_j(s) be the other row with the same j-th sign as s.
For weights t in the simplex Δ ⊂ ℝ⁴ and v ∈ ℝ³, put

    g_s(t, v) = Σ_j ε_j(s) (t_s + t_{r_j(s)}) v_j.

The row inequality (R_t) asks for π ∈ Δ and γ ∈ ℝ³, with γ ≥ 0 and
Σ_j γ_j ≤ 1, such that

    Σ_s π_s |g_s(t, v)|^q ≤ Σ_j γ_j |v_j|^q   for every v ∈ ℝ³.

Take norming vectors u_j in the ℓ_q unit ball for the three pair
sums and put c_s = ½ Σ_j ε_j(s) u_j. A common point w of the four
unit balls centered at c_s gives the desired bound by Hölder's
inequality. The zero sum cancels w. Set P(t) = −Σ_r t_r c_r.
Applying (R_t) coordinate by coordinate shows that the sets
C_s = {t ∈ Δ : ‖c_s − P(t)‖_q ≤ 1} cover Δ. They are compact and
convex. Two sign rows agree in one place, so the vertex e_r lies
in every C_s with s ≠ r. Klee's intersection lemma gives t in
all four sets, and w = P(t).
[Rows](HlawkaSchatten/BelowExponent/Defs.lean) · [Norming](HlawkaSchatten/BelowExponent/Norming.lean) ·
[Endpoint reduction](HlawkaSchatten/BelowExponent/Reduction.lean) ·
[Klee's lemma](HlawkaSchatten/BelowExponent/Intersection.lean) ·
[Lee’s four-ball criterion, Theorem 4.10](https://arxiv.org/html/2610.23785v1#S4.Thmtheorem10)

**Ordered chamber.** Relabelling t permutes the three pairings and
can reverse their signs. It suffices to treat t₀ ≥ t₁ ≥ t₂ ≥ t₃ > 0.
At t₃ = 0 a point-mass certificate handles the closed boundary.
[Symmetry](HlawkaSchatten/BelowExponent/Symmetry.lean) · [Boundary](HlawkaSchatten/BelowExponent/Boundary.lean)

**Eleven regions.** Use depth ε = 1 − t₀, edge mass ℓ = t₂ + t₃,
τ = t₀/(t₀ + t₁), imbalance e = t₀ − t₁, σ = ℓ/ε,
facet coordinate f = t₂/(1 − t₃), and directions m = t₃/ε and
M = t₁/ε. For the corner put h = 1 − e and k = σ/(2 − σ).
The theorem `ordered_mem_region` covers the ordered chamber.
[Exact region predicates](HlawkaSchatten/BelowExponent/Coverage.lean)

| Region | Inequalities | Proof |
|---|---|---|
| Bulk | t₃ ≥ 1/500 | A 167-cell tangent cover outside the central cube and a covariance estimate inside |
| Facet interior | t₃ ≤ 1/500, f ≥ 1/20 | Adaptive row certificates on 116 prisms |
| Edge junction | ℓ ≤ 1/4000, 1/4 ≤ τ ≤ 3/4 | Balanced weights |
| Balanced edge | 1/4096 ≤ ℓ ≤ 74/4096, 0 ≤ e ≤ 1/2 | Balanced weights on 13 slabs |
| Facet strip | 1/64 ≤ f ≤ 1/20, 1/4 ≤ τ ≤ 3/4, t₃ ≤ 1/400, 8t₃ ≤ t₂ | Balanced weights on slabs |
| Deep facet | t₃ ≤ 1/500, f ≤ 1/20, ε ≥ 1/8, σ ≥ 1/5, τ ≥ 3/4 | Adaptive row certificates |
| Vertex middle | m ≥ 1/20, M ≤ 4/5, ε ≤ 1/20 | Bounds on the value, first derivative and second derivative, plus corner checks |
| Vertex band | 1/40 ≤ m ≤ 1/20, M ≤ 4/5, ε ≤ 1/12 | The same interval method as the middle region |
| Vertex side | m ≤ 1/40, M ≤ 4/5, ε ≤ 1/8 | Vertex bounds and 510 near-cone cells |
| Vertex edge | σ ≤ 7/10000, ε ≤ 13/50 | Balanced weights |
| Vertex corner | 7/10000 ≤ σ ≤ 1/5, 0 < h ≤ 1/(2 − k) | Balanced weights in separate charts |

The central cube is maxₛ |tₛ − 1/4| ≤ 1/500. The tangent proof starts
on its boundary. [Bulk tangent cover](HlawkaSchatten/BelowExponent/Tangent/OutsideCube.lean#L23)

**Balanced weights.** One family uses

    π = (μ(1 − e)/2, μ(1 + e)/2, (1 − μ)/2, (1 − μ)/2)
    γ = ((1 − μ(1 − ℓ))/2, (1 − μ(1 − ℓ))/2, μ(1 − ℓ)).

The row values have closed forms for every real q. The balanced edge
uses fixed μ values on 13 slabs. The vertex corner takes
μ = a · (3/5)(1 + h/16) σ^(12/25), with a = 1 when σ < 3/20
and a = 49/50 otherwise.
[Balanced weights](HlawkaSchatten/BelowExponent/Balanced.lean#L28) · [Edge schedule](HlawkaSchatten/BelowExponent/G1Far.lean#L32) ·
[Corner charts](HlawkaSchatten/BelowExponent/G3Wider.lean)

**From a certificate to a real inequality.** Lean checks the
certificate's exact integer or dyadic arithmetic. Soundness lemmas
turn a passing check into a real inequality on a closed box, and
coverage lemmas join the boxes. The rational bounds
1054/665 < log₂ 3 < 485/306 follow from 2^1054 < 3^665 and
3^306 < 2^485. Several charts use tighter local intervals.
[Exponent brackets](HlawkaSchatten/BelowExponent/Exponents.lean)

## Key lemmas

#### Interior existence and endpoints

- Compactness of the scalar Bregman-to-Mazur ratio on the extended real
  line gives the constants m_p, M_p.
- The spectral overlap matrix has nonnegative entries summing to one along
  rows and columns — the convexity engine for the lift.
- Hermitian dilation scales Schatten norms by 2^{1/p}; the factor cancels
  in the deficit comparison. The odd functional calculus preserves the
  off-diagonal block structure.
- The Hilbert Hlawka inequality (triple deficit ≤ sum of pair deficits in
  inner product spaces) is the final comparison tool.
- The 2D trace-norm identity links the Schatten 1-norm to the Frobenius
  norm plus normDet(T), the product of the two singular values.

#### Sharp diagonal constant

- The sparse minimizer of the concave objective has support at most three,
  proved by a second maximization over squared weights.
- The scalar separation f_p(q₀) < (939/2000) p and the rough bound
  K_p ≤ p confine a strict counterexample.
- The cyclic witness t = p^{-1/p} gives a lower bound forcing total norm
  below 53/150.
- Distinct pair-maximizing coordinates: two saturated pairs cannot share a
  coordinate without violating the total-norm bound.
- The curvature margin 1200 p d_p < b_p makes the complete deficit
  Hessian nonnegative on the box for every real p ≥ 256.
- The circle-projection hull transfer: finite convex combinations satisfy
  the real bound, and continuity passes it to the closed convex hull
  containing the circle integral.
- The diagonal singular-value identity: a diagonal operator's
  singular-value power sum equals its coordinate power sum.

#### Constant one below the critical exponent

- A common point of the four dual unit balls gives the desired endpoint
  bound by Hölder’s inequality and the zero sum of the four primal
  vectors. [Norming](HlawkaSchatten/BelowExponent/Norming.lean)
- The row estimate covers the weight simplex by four compact convex
  sets. Each three share a simplex vertex. Klee’s intersection lemma
  supplies a point in all four sets. [Reduction](HlawkaSchatten/BelowExponent/Reduction.lean) ·
  [Klee’s lemma](HlawkaSchatten/BelowExponent/Intersection.lean)
- The integer comparisons 2^1054 < 3^665 and 3^306 < 2^485 give the
  interval 1054/665 < log₂ 3 < 485/306 used to enclose real powers.
  [Exponent brackets](HlawkaSchatten/BelowExponent/Exponents.lean)
- Relabelling and the zero-weight certificate extend the result on
  the ordered chamber to the closed simplex. [Symmetry](HlawkaSchatten/BelowExponent/Symmetry.lean) ·
  [Boundary](HlawkaSchatten/BelowExponent/Boundary.lean)
- For 2 < p < p_W and W = Σᵢ Sᵢ |xᵢ|^(p_W), the fractional moment
  satisfies E W^(1/p_W) = c_p ‖x‖ₚ with c_p > 0. Integrating the
  endpoint inequality gives constant one at p.
  [Stable moments](HlawkaSchatten/BelowExponent/StableMoments.lean) · [Transfer](HlawkaSchatten/BelowExponent/Transfer.lean)

## Pitfalls

#### Interior existence and endpoints

- The odd functional calculus preserves the off-diagonal block structure of
  the Hermitian dilation, but proving this requires tracking the dilation's
  spectral decomposition through the functional calculus.
- The radial Mazur map must preserve individual norms without sphere
  normalization — the sphere version introduces denominators that break
  the Hlawka application.
- The exact 2D trace-norm identity (‖T‖₁² = ‖T‖₂² + 2 normDet(T)) is
  specific to 2 × 2 matrices; in higher dimensions the p = 1 obstruction
  follows by embedding the 2 × 2 family via zero-padding (not formalized).
- The p = ∞ witness uses 3 × 3 diagonal matrices because every
  two-dimensional real normed space satisfies Hlawka; three diagonal
  coordinates are the minimum needed for a counterexample.

#### Sharp diagonal constant

- Averaging is valid only after localization into the convex box — an
  equal-norm assumption alone does not justify it.
- The total-norm Hessian is essential: singleton Hessians alone miss
  relative radial motions of the three columns.
- |1-t| must stay an absolute value because Mathlib's real rpow of a
  negative base gives |x|^y · cos(πy), not the intended power.
- The cutoff is set by localization, which has 0.004375 of slack at
  p = 256, not by curvature, which has margin of order 10¹¹.

#### Constant one below the critical exponent

- Margins that are positive in the bulk can vanish at the boundary.
  Separate ratio charts and equality arguments cover those cases.
- Integer power comparisons bound q before the interval checks.
  [Exponent bounds](HlawkaSchatten/BelowExponent/Exponents.lean)
- Checking the exported proof dominated the measured local run. The
  original clean build took 1 h 44 min and its stock Lean replay took
  9 h 26 min. The verification table identifies each export by hash.
  [Local timings](README.md#verification)
- Regional NanoDa diagnostics isolated a reused corner proof and
  a costly staged equality. The checked repair proves the corner facts directly
  and compares the staged parameter fields to common expressions.

## Code mapping

Edges show direct imports; see import headers for Mathlib dependencies.
The boundary namespaces `PalomarHlawkaSchatten` (existence) and
`PalomarHlawkaSchatten.ConstructionDiagonal` differ from the library
namespace `HlawkaSchatten.DiagonalConstruction`.

The third boundary retains the mission's declaration name,
`HlawkaSchatten.LpThreshold.hlawka_holds_below_exponent`. Its Solution states it from
[the unconditional theorem](HlawkaSchatten/BelowExponent/Complete.lean),
`HlawkaSchatten.BelowExponent.hlawka_holds_below_exponent`. The two refined vertex
assemblies are [middle and band](HlawkaSchatten/BelowExponent/Vertex/CurvatureCut/VcComplete.lean)
and [side](HlawkaSchatten/BelowExponent/Vertex/SideCutCorners/CoarseComplete.lean).
The corner charts meet in [the full corner theorem](HlawkaSchatten/BelowExponent/G3Wider.lean).

### Existence proof library

Modules are under `HlawkaSchatten/`.

```
Basic ─── ScalarBregman ─── ScalarRatio ─── SpectralLift ─── HermitianSpectral
  │                                                                  │
GapComparison                                  SchattenNorm ─── HermitianDilation
  │       │                                      │                   │
HilbertHlawka ─── MazurGapComparison        HilbertSchmidt ─── Variational
       │                  │                      │                   │
EndpointObstruction       │                 TraceEndpoint         Final
       │                  │                      │                   │
       └──────────────────┴──────────────────────┴──── Classification
```

Multi-parent imports not drawn: HilbertSchmidt ← {SchattenNorm, HilbertHlawka},
HermitianDilation ← {HermitianSpectral, SchattenNorm},
Variational ← {HilbertSchmidt, HermitianDilation},
Final ← {Variational, MazurGapComparison}.
Off path: ScalarHlawka (← GapComparison).

### Diagonal construction library

Modules are under `HlawkaSchatten/DiagonalConstruction/`.

```
                  Basic ─── Cyclic ─── CyclicWitness
                    │                       │
WeightedConvex ─── ScalarBounds ─── ScalarEnvelope
                                         │
              Normalization ─── TailEstimates
                    │                │
               Confinement ──────────┘
                    │
               Coordinates
                    │
WeightedCoordinates ─── DimensionReduction ─── Localization
         │                    │              │         │
    Sparsification      OrbitAveraging    BoxGeometry  │
                              │           │       │    │
                              │   BoxCoordinates  HessianBounds ─── NormHessian
                              │        │               │
                              │        │        CurvatureEstimate
                              │        │               │
                              │     BoxHessian ────────┘
                              │        │
                         BoxConvexity ─┘
                              │
                  CircleProjection ─── ComplexTransfer
                                            │
                                       DiagonalNorm
```

Multi-parent imports not drawn: ScalarBounds ← {Basic, WeightedConvex},
Confinement ← {Normalization, TailEstimates},
DimensionReduction ← {WeightedCoordinates, Sparsification},
OrbitAveraging ← {Localization, DimensionReduction},
HessianBounds ← {NormHessian, BoxGeometry},
BoxHessian ← {CurvatureEstimate, BoxCoordinates},
BoxConvexity ← {BoxHessian, OrbitAveraging},
ComplexTransfer ← {BoxConvexity, CircleProjection}.
From the existence library: Basic ← GapComparison,
ScalarBounds ← ScalarBregman, DiagonalNorm ← HermitianDilation.

The existence entry point is `Classification.lean`; the diagonal entry
point is `HlawkaSchatten/DiagonalConstruction.lean`. The top-level
`HlawkaSchatten.lean` aggregates both libraries.

### Below-exponent proof library

Names below are relative to `HlawkaSchatten/BelowExponent/` unless qualified. Each arrow
points from a module to a selection of its direct imports.

```text
ConstructionDiagonalBelowExponentSolution → BelowExponent → Complete
Complete → Assembly, RegionalCertificates,
           Vertex/CurvatureCut/VcComplete, Vertex/SideCutCorners/CoarseComplete
Assembly → Euclidean, StableLaw
StableLaw → ParetoApproximation, StableLimit
ParetoApproximation → StableMoments
StableLimit → StableMoments
StableMoments → Transfer, FractionalMoment
Transfer → RouteT
RouteT → Boundary, Coverage, Exponents, Norming, Reduction, Symmetry
Norming → Defs, Target
Reduction → Defs, Intersection
Target → HlawkaSchatten/DiagonalConstruction/CoordinateNorm, HlawkaSchatten/GapComparison/Defs
```

**Mathematical assembly.** The regional theorems give the row
inequality on the ordered chamber. The endpoint argument uses the
resulting simplex estimate, and the stable-law argument extends the
exponent range. These are proof steps. The diagram above is the
import map from the current Solution.

| Region | Lean theorem |
|---|---|
| Bulk | [`rowAt_bulk_of_e2_and_center`](HlawkaSchatten/BelowExponent/AdaptiveCoverage.lean#L36) |
| Facet interior | [`rowAt_facetInterior_adaptive`](HlawkaSchatten/BelowExponent/FacetArchive/Complete.lean#L23) |
| Edge junction | [`rowAt_edgeJunction`](HlawkaSchatten/BelowExponent/BalancedJunctions.lean#L25) |
| Balanced edge | [`rowAt_g1`](HlawkaSchatten/BelowExponent/G1Complete.lean#L233) |
| Facet strip | [`rowAt_facetStrip_balanced`](HlawkaSchatten/BelowExponent/FSlabData/Complete.lean#L195) |
| Deep facet | [`rowAt_deepFacet_adaptive`](HlawkaSchatten/BelowExponent/FacetG2/Complete.lean#L602) |
| Vertex middle | [`rowAt_vertexMiddle_optimized`](HlawkaSchatten/BelowExponent/Vertex/CurvatureCut/VcComplete.lean#L33) |
| Vertex band | [`rowAt_vertexBand_optimized`](HlawkaSchatten/BelowExponent/Vertex/CurvatureCut/VcComplete.lean#L38) |
| Vertex side | [`rowAt_vertexSide_optimized`](HlawkaSchatten/BelowExponent/Vertex/SideCutCorners/CoarseComplete.lean#L36) |
| Vertex edge | [`rowAt_vertexEdge_balanced`](HlawkaSchatten/BelowExponent/G3EdgeComplete.lean#L22) |
| Vertex corner | [`rowAt_vertexCorner_balanced`](HlawkaSchatten/BelowExponent/G3Wider.lean#L35) |

The module names use historical labels. E2 is the bulk tangent cover,
F0–F2 the facet prisms, F the facet strip, G1 the balanced edge, G2 the
deep facet and G3 the vertex corner. VC covers the middle and band,
and SC the vertex side. Search programs supply witness data. Lean
verifies the certificates and their covers.


### Written and formal certificates

The written bulk, facet-interior and deep-facet arguments use fixed partitions.
Lean uses the E2 tangent tree in the bulk, F0–F2 prisms on the facet
and adaptive upper and tip prisms in G2. The written edge junction U′ and
vertex-edge cases VE and G4 are covered in Lean by the balanced edge limit
and the overlapping vertex charts. The balanced edge and facet strip use
slab bounds. At the vertex, the middle, band and side proofs join curvature
estimates to checked outer points. The side also uses a packed near-cone
cover. The G3 corner joins its head, low and central charts. The
[certificate guide](scripts/certificates/README.md) gives the inputs,
regeneration commands and final row theorem for each of the eleven regions.

The library uses explicit binders and Mathlib’s standard linters. The
below-exponent modules keep the settings they were written under, set at
the top of each file: implicit auto-bound names on and, where Mathlib is in
reach, Mathlib's standard linter set off, since the generated data files
have long literal lines. `Complete.lean` uses the library defaults. The maintained
vertex-side assembly scopes its recursion setting to its single theorem. [Lake configuration](lakefile.toml)
