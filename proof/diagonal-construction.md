# The sharp cyclic constant for diagonal Schatten norms

For every real `p ≥ 256`, the sharp dimension-independent Hlawka constant
for finite complex diagonal Schatten spaces is the explicit cyclic maximum
defined below. It is sharp in each dimension at least three. The inequality
allows arbitrary complex diagonal entries and unequal singleton norms.

This document records the construction formalized in
[ConstructionDiagonalSolution.lean](../ConstructionDiagonalSolution.lean).
The independent statement is
[ConstructionDiagonalChallenge.lean](../ConstructionDiagonalChallenge.lean),
and the comparison configuration is
[comparator-construction-diagonal.json](../comparator-construction-diagonal.json).
The proof library contains no `sorry` or additional axioms.

## Statement and explicit constant

Write `N` for the Schatten `p`-norm of a diagonal operator, and set

```text
S = N(x) + N(y) + N(z)
T = N(x + y + z)
P = N(x + y) + N(x + z) + N(y + z).
```

For the cyclic triple `(-t,1,1), (1,-t,1), (1,1,-t)`, define

```text
A_p(t) = (t^p + 2)^(1/p)
B_p(t) = (2 |1-t|^p + 2^p)^(1/p)
R_p(t) = (3 A_p(t) - 3^(1/p) |2-t|) / (6 A_p(t) - 3 B_p(t))
K_p    = sup { R_p(t) : 1/2 ≤ t ≤ 2 }.
```

The three selected public theorems say:

1. `S - T ≤ K_p (2S - P)` in every finite dimension, including dimension zero.
2. Every admissible constant in a dimension at least three is at least `K_p`.
3. Some `t ∈ [1/2, 2]` satisfies `R_p(t) = K_p`.

The interval is part of the complete public definition. Its ratio has a
strictly positive denominator for `p > 1`, so compactness gives an actual
maximum. The global inequality also bounds cyclic triples with any `t ≥ 0`;
thus restricting the definition to this compact interval loses no larger
cyclic value in the proved exponent range.

The theorem does not determine the sharp constant for arbitrary
non-diagonal matrices or for exponents below 256. It neither assumes equal
singleton norms nor asserts that every maximizing triple has equal norms.

## Proof dependencies

All module links below are under `HlawkaSchatten/DiagonalConstruction/`.
The final real and complex results are `real_hlawka_bound` and
`complex_hlawka_bound` in namespace `HlawkaSchatten.DiagonalConstruction`.

| Mathematical step | Lean source | Role |
|---|---|---|
| Coordinate norms and cyclic witnesses | [Basic](../HlawkaSchatten/DiagonalConstruction/Basic.lean), [Cyclic](../HlawkaSchatten/DiagonalConstruction/Cyclic.lean), [CyclicWitness](../HlawkaSchatten/DiagonalConstruction/CyclicWitness.lean) | Norm laws, positive cyclic denominator, compact maximum, and sharpness by embedding |
| Weighted scalar convexity | [WeightedConvex](../HlawkaSchatten/DiagonalConstruction/WeightedConvex.lean), [ScalarBounds](../HlawkaSchatten/DiagonalConstruction/ScalarBounds.lean), [ScalarEnvelope](../HlawkaSchatten/DiagonalConstruction/ScalarEnvelope.lean) | The total-norm-dependent bound and the rough bound `K_p ≤ p` |
| Reduction to three coordinates | [WeightedCoordinates](../HlawkaSchatten/DiagonalConstruction/WeightedCoordinates.lean), [Sparsification](../HlawkaSchatten/DiagonalConstruction/Sparsification.lean), [DimensionReduction](../HlawkaSchatten/DiagonalConstruction/DimensionReduction.lean) | Preserve all three pair power sums while minimizing a concave objective |
| Normalize and confine a strict failure | [Normalization](../HlawkaSchatten/DiagonalConstruction/Normalization.lean), [TailEstimates](../HlawkaSchatten/DiagonalConstruction/TailEstimates.lean), [Confinement](../HlawkaSchatten/DiagonalConstruction/Confinement.lean) | Relabel the zero-sum quadruple, then bound total norm, singleton norms, and pair deficits |
| Recover the shared coordinate pattern | [Coordinates](../HlawkaSchatten/DiagonalConstruction/Coordinates.lean), [Localization](../HlawkaSchatten/DiagonalConstruction/Localization.lean) | Distinct pair-maximizing coordinates force the radius-`19/100` cyclic box |
| Differentiate and compare curvature | [NormHessian](../HlawkaSchatten/DiagonalConstruction/NormHessian.lean), [BoxGeometry](../HlawkaSchatten/DiagonalConstruction/BoxGeometry.lean), [HessianBounds](../HlawkaSchatten/DiagonalConstruction/HessianBounds.lean), [CurvatureEstimate](../HlawkaSchatten/DiagonalConstruction/CurvatureEstimate.lean) | Control joint radial residuals and prove the uniform scalar curvature margin |
| Convexity and permutation averaging | [BoxCoordinates](../HlawkaSchatten/DiagonalConstruction/BoxCoordinates.lean), [BoxHessian](../HlawkaSchatten/DiagonalConstruction/BoxHessian.lean), [BoxConvexity](../HlawkaSchatten/DiagonalConstruction/BoxConvexity.lean), [OrbitAveraging](../HlawkaSchatten/DiagonalConstruction/OrbitAveraging.lean) | Convex sharp deficit; its orbit average is cyclic, proving the real bound |
| Transfer to complex coordinates | [CircleProjection](../HlawkaSchatten/DiagonalConstruction/CircleProjection.lean), [ComplexTransfer](../HlawkaSchatten/DiagonalConstruction/ComplexTransfer.lean) | Circle integration reproduces all seven norm powers with one positive factor |
| Identify the Schatten norm | [DiagonalNorm](../HlawkaSchatten/DiagonalConstruction/DiagonalNorm.lean) | A diagonal operator's singular-value power sum equals its coordinate power sum |

The existing repository contributes the gap definitions and the spectral
functional-calculus trace identity used in the last step. Its general
existence theorem is not a premise of the sharp construction. Earlier
equal-norm theorems, per-exponent polynomial certificates, stationarity
classifications, and numerical searches are not proof inputs.

## Formalization choices and exact estimates

The proof follows the scalar/diagonal tail argument developed on
2026-09-21/22. These implementation choices change intermediate estimates,
without changing the exponent range or the sharp constant.

**Weighted convexity.** An elementary ordered-chord argument proves the
weighted three-point inequality for every convex real function. It avoids
representing convex functions as integrals of absolute-value functions.

**Sparse minimization.** On the compact feasible weight set, first minimize
the concave objective, then maximize the sum of squared weights among its
minimizers. If more than three weights are positive, a supported kernel
direction gives feasible opposite perturbations and contradicts the second
maximization. This proves the needed support bound directly.

**Scalar separation.** Set `q₀ = 53/150` and
`f_p(q) = (1-q) / (2(1-((1+q^p)/2)^(1/p)))`. Uniform estimates for
`t = exp(-log(p)/p)` give

```text
f_p(q₀) < (939/2000) p < K_p ≤ p,     p ≥ 256.
```

Consequently a normalized strict counterexample has
`1/3 ≤ T < 53/150`, singleton norms in `(22/75,53/150)`, and pair-deficit
sum below `2/p`. All logarithmic and exponential estimates are proved for
real exponents, using exact rational arithmetic and Mathlib inequalities.

**Joint geometry and Hessian bounds.** Inside the box, the formal proof
uses the radial residual constant `300`, in place of `110` in the written
argument. Its lower and upper Hessian coefficients are

```text
b_p = (p-1) (43/100)^(p-2) / (3 (157/100)^(p-1))
d_p = 2 (p-1) (38/100)^(p-2) / (162/100)^(p-1).
```

The proved comparisons are

```text
d_p < 8 b_p (6/7)^(p-2)
9600 p (6/7)^(p-2) < 1
1200 p d_p < b_p,                    p ≥ 256.
```

These looser constants still make the complete deficit Hessian
nonnegative. The total-norm term is essential: it controls relative radial
motions of the three columns that the singleton Hessians alone miss.

**Complex transfer.** The proof applies the real inequality to finite
weighted circle projections. It then uses the closed convex hull of their
seven simultaneous power sums to include the circle integral. Continuity
passes the inequality to that integral, and its common positive factor
cancels. No choice of separate approximations for the seven norms is used.

## Cutoff and scope of further work

The formal theorem retains `p ≥ 256`. Its localization puts the normalized
configuration inside an entrywise error bound
`6/50 + 84/(5p)`, which is `0.185625` at 256, below the box radius `0.19`.
This enclosure has much less room than the curvature comparison. Lowering
the cutoff therefore requires revisiting scalar confinement and coordinate
localization, alongside rechecking the uniform arithmetic lemmas. The
written discussion of a possible cutoff of 242 is not a Lean theorem here.

The coordinate-selection argument retains the joint geometry: a shared
vector forces consistent signs when two nearly saturated pairs choose the
same coordinate, contradicting the total-norm bound. Averaging is justified
only after that geometry places the whole triple in a convex region where
the complete deficit has the required curvature.
