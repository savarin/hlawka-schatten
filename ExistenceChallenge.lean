/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Dimension-independent Hlawka constants for Schatten norms (Challenge)

For every real exponent `p > 1`, a finite dimension-independent Hlawka
constant exists for the Schatten `p`-norm on linear maps between
finite-dimensional complex inner product spaces. No such constant exists
at the trace norm (`p = 1`, dimension 2) or the operator norm
(`p = ∞`, dimension 3).

The Schatten `p`-norm is the `p`-th root of the sum of `p`-th powers of
the singular values, listed in descending order with multiplicity and
zero-padded. At `p = ∞` the Schatten norm is the largest singular value,
represented by Mathlib's spectral L2 operator norm via
`Matrix.instNormedAddCommGroupMatrix`.
-/

namespace PalomarHlawkaSchatten

open scoped Matrix.Norms.L2Operator

/-- Sum of the p-th powers of the singular values. -/
noncomputable def singularValuePowerSum
    {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (p : ℝ) (T : E →ₗ[𝕜] F) : ℝ :=
  ∑ i ∈ T.singularValues.support, (T.singularValues i) ^ p

/-- The Schatten p-norm: the p-th root of `singularValuePowerSum`. -/
noncomputable def schattenPNorm
    {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (p : ℝ) (T : E →ₗ[𝕜] F) : ℝ :=
  (singularValuePowerSum p T) ^ (1 / p)

/-- The pair deficit: `N(x) + N(y) - N(x + y)`. -/
def pairGap {E : Type*} [Add E] (size : E → ℝ) (x y : E) : ℝ :=
  size x + size y - size (x + y)

/-- The triple deficit: `N(x) + N(y) + N(z) - N(x + y + z)`. -/
def tripleGap {E : Type*} [Add E] (size : E → ℝ) (x y z : E) : ℝ :=
  size x + size y + size z - size (x + y + z)

/-- Sum of the three pair deficits. -/
def pairGapSum {E : Type*} [Add E] (size : E → ℝ) (x y z : E) : ℝ :=
  pairGap size x y + pairGap size x z + pairGap size y z

/-- `C` is a Hlawka constant for `size` if the triple deficit never exceeds
`C` times the sum of pair deficits. -/
def HasHlawkaConstant {E : Type*} [Add E] (size : E → ℝ) (C : ℝ) : Prop :=
  ∀ x y z, tripleGap size x y z ≤ C * pairGapSum size x y z

/-- For every Schatten exponent `1 < p`, there exist positive constants
`m ≤ M` such that `M / m` is a dimension-independent Hlawka constant.
No finite constant exists at the trace norm (`p = 1`, dimension 2) or the
operator norm (`p = ∞`, dimension 3). -/
theorem dimension_independent_hlawka_constant_for_schatten_norms :
    (∀ p : ℝ, 1 < p →
      ∃ m M : ℝ, 0 < m ∧ m ≤ M ∧
        ∀ {E F : Type*}
          [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
          [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F],
          HasHlawkaConstant
            (schattenPNorm p : (E →ₗ[ℂ] F) → ℝ) (M / m)) ∧
      (∀ C : ℝ, ¬HasHlawkaConstant
        (schattenPNorm 1 :
          (EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2)) → ℝ) C) ∧
      (∀ C : ℝ, ¬HasHlawkaConstant
        (norm : Matrix (Fin 3) (Fin 3) ℂ → ℝ) C) := by
  sorry

end PalomarHlawkaSchatten
