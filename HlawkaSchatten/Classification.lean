/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import HlawkaSchatten.Final
import HlawkaSchatten.TraceEndpoint
import HlawkaSchatten.EndpointObstruction

/-! # Complete dimension-independent Schatten Hlawka classification -/

namespace HlawkaSchatten

open scoped Matrix.Norms.L2Operator

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
  exact ⟨fun _ hp => exists_uniform_schattenPNorm_hlawkaConstant hp,
    no_hlawkaConstant_schattenPNorm_one_fin2,
    no_hlawkaConstant_operatorNorm_matrix_fin3⟩

end HlawkaSchatten
