import HlawkaSchatten.Classification
import HlawkaSchatten.GapComparison
import HlawkaSchatten.SchattenNorm

/-!
Manifest-driven boundary for the landed Hlawka-Schatten surface.

The declaration below has an explicit type and delegates to the production
declaration. A changed source signature therefore breaks elaboration.
-/

open scoped Matrix.Norms.L2Operator

namespace HlawkaSchattenBoundary

noncomputable def singularValuePowerSum_boundary
    {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (p : ℝ) (T : E →ₗ[𝕜] F) : ℝ :=
  HlawkaSchatten.singularValuePowerSum p T

noncomputable def schattenPNorm_boundary
    {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (p : ℝ) (T : E →ₗ[𝕜] F) : ℝ :=
  HlawkaSchatten.schattenPNorm p T

def HasHlawkaConstant_boundary {E : Type*} [Add E] (size : E → ℝ) (C : ℝ) : Prop :=
  HlawkaSchatten.HasHlawkaConstant size C

theorem existence_boundary :
    (∀ p : ℝ, 1 < p →
      ∃ m M : ℝ, 0 < m ∧ m ≤ M ∧
        ∀ {E F : Type*}
          [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
          [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F],
          HlawkaSchatten.HasHlawkaConstant
            (HlawkaSchatten.schattenPNorm p : (E →ₗ[ℂ] F) → ℝ) (M / m)) ∧
      (∀ C : ℝ, ¬HlawkaSchatten.HasHlawkaConstant
        (HlawkaSchatten.schattenPNorm 1 :
          (EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2)) → ℝ) C) ∧
      (∀ C : ℝ, ¬HlawkaSchatten.HasHlawkaConstant
        (norm : Matrix (Fin 3) (Fin 3) ℂ → ℝ) C) :=
  HlawkaSchatten.dimension_independent_hlawka_constant_for_schatten_norms

end HlawkaSchattenBoundary
