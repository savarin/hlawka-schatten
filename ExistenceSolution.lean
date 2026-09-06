/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import HlawkaSchatten.Classification

/-! # Dimension-independent Hlawka constants for Schatten norms (Solution) -/

namespace PalomarHlawkaSchatten

open scoped Matrix.Norms.L2Operator

noncomputable def singularValuePowerSum
    {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (p : ℝ) (T : E →ₗ[𝕜] F) : ℝ :=
  ∑ i ∈ T.singularValues.support, (T.singularValues i) ^ p

noncomputable def schattenPNorm
    {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (p : ℝ) (T : E →ₗ[𝕜] F) : ℝ :=
  (singularValuePowerSum p T) ^ (1 / p)

def pairGap {E : Type*} [Add E] (size : E → ℝ) (x y : E) : ℝ :=
  size x + size y - size (x + y)

def tripleGap {E : Type*} [Add E] (size : E → ℝ) (x y z : E) : ℝ :=
  size x + size y + size z - size (x + y + z)

def pairGapSum {E : Type*} [Add E] (size : E → ℝ) (x y z : E) : ℝ :=
  pairGap size x y + pairGap size x z + pairGap size y z

def HasHlawkaConstant {E : Type*} [Add E] (size : E → ℝ) (C : ℝ) : Prop :=
  ∀ x y z, tripleGap size x y z ≤ C * pairGapSum size x y z

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
        (norm : Matrix (Fin 3) (Fin 3) ℂ → ℝ) C) :=
  HlawkaSchatten.dimension_independent_hlawka_constant_for_schatten_norms

end PalomarHlawkaSchatten
