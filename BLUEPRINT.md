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

## Code mapping

Edges show direct imports; see import headers for Mathlib dependencies.
The boundary namespaces `PalomarHlawkaSchatten` (existence) and
`PalomarHlawkaSchatten.ConstructionDiagonal` differ from the library
namespace `HlawkaSchatten.DiagonalConstruction`.

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
