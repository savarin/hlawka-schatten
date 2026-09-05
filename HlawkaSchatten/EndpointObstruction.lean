/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.CStarAlgebra.Matrix
import HlawkaSchatten.GapComparison

/-!
# The three-coordinate infinity-norm obstruction

This is the scalar diagonal core of the operator-norm endpoint example from
the proof source. Every pair deficit vanishes, while the three-body deficit
is positive, so no finite multiplicative constant can satisfy Hlawka.
-/

namespace HlawkaSchatten

open scoped Matrix.Norms.L2Operator

private def infinityX : Fin 3 → ℝ := ![-1, 1, 1]
private def infinityY : Fin 3 → ℝ := ![1, -1, 1]
private def infinityZ : Fin 3 → ℝ := ![1, 1, -1]

private theorem univ_fin3 : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide

private theorem norm_infinityX : ‖infinityX‖ = 1 := by
  norm_num [infinityX, Pi.norm_def, univ_fin3, Finset.sup_insert, Matrix.cons_val_two]

private theorem norm_infinityY : ‖infinityY‖ = 1 := by
  norm_num [infinityY, Pi.norm_def, univ_fin3, Finset.sup_insert, Matrix.cons_val_two]

private theorem norm_infinityZ : ‖infinityZ‖ = 1 := by
  norm_num [infinityZ, Pi.norm_def, univ_fin3, Finset.sup_insert, Matrix.cons_val_two]

private theorem norm_infinityX_add_Y : ‖infinityX + infinityY‖ = 2 := by
  norm_num [infinityX, infinityY, Pi.norm_def, univ_fin3, Finset.sup_insert,
    Matrix.cons_val_two]

private theorem norm_infinityX_add_Z : ‖infinityX + infinityZ‖ = 2 := by
  norm_num [infinityX, infinityZ, Pi.norm_def, univ_fin3, Finset.sup_insert,
    Matrix.cons_val_two]

private theorem norm_infinityY_add_Z : ‖infinityY + infinityZ‖ = 2 := by
  norm_num [infinityY, infinityZ, Pi.norm_def, univ_fin3, Finset.sup_insert,
    Matrix.cons_val_two]

private theorem norm_infinity_sum : ‖infinityX + infinityY + infinityZ‖ = 1 := by
  norm_num [infinityX, infinityY, infinityZ, Pi.norm_def, univ_fin3, Finset.sup_insert,
    Matrix.cons_val_two]

/-- No constant gives the Hlawka inequality on three-dimensional real `ℓ∞`. -/
theorem no_hlawkaConstant_pi_fin3 :
    ∀ C : ℝ, ¬HasHlawkaConstant (norm : (Fin 3 → ℝ) → ℝ) C := by
  apply no_hlawkaConstant_of_pairGapSum_eq_zero
      (norm : (Fin 3 → ℝ) → ℝ) infinityX infinityY infinityZ
  · simp only [tripleGap, norm_infinityX, norm_infinityY, norm_infinityZ,
      norm_infinity_sum]
    norm_num
  · simp only [pairGapSum, pairGap, norm_infinityX, norm_infinityY, norm_infinityZ,
      norm_infinityX_add_Y, norm_infinityX_add_Z, norm_infinityY_add_Z]
    norm_num

private def infinityMatrixX : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal ![-1, 1, 1]

private def infinityMatrixY : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal ![1, -1, 1]

private def infinityMatrixZ : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal ![1, 1, -1]

private theorem norm_infinityMatrixX : ‖infinityMatrixX‖ = 1 := by
  rw [infinityMatrixX, Matrix.l2_opNorm_diagonal]
  norm_num [Pi.norm_def, univ_fin3, Finset.sup_insert, Matrix.cons_val_two]

private theorem norm_infinityMatrixY : ‖infinityMatrixY‖ = 1 := by
  rw [infinityMatrixY, Matrix.l2_opNorm_diagonal]
  norm_num [Pi.norm_def, univ_fin3, Finset.sup_insert, Matrix.cons_val_two]

private theorem norm_infinityMatrixZ : ‖infinityMatrixZ‖ = 1 := by
  rw [infinityMatrixZ, Matrix.l2_opNorm_diagonal]
  norm_num [Pi.norm_def, univ_fin3, Finset.sup_insert, Matrix.cons_val_two]

private theorem norm_infinityMatrixX_add_Y : ‖infinityMatrixX + infinityMatrixY‖ = 2 := by
  rw [infinityMatrixX, infinityMatrixY, Matrix.diagonal_add, Matrix.l2_opNorm_diagonal]
  norm_num [Pi.norm_def, univ_fin3, Finset.sup_insert, Matrix.cons_val_two]

private theorem norm_infinityMatrixX_add_Z : ‖infinityMatrixX + infinityMatrixZ‖ = 2 := by
  rw [infinityMatrixX, infinityMatrixZ, Matrix.diagonal_add, Matrix.l2_opNorm_diagonal]
  norm_num [Pi.norm_def, univ_fin3, Finset.sup_insert, Matrix.cons_val_two]

private theorem norm_infinityMatrixY_add_Z : ‖infinityMatrixY + infinityMatrixZ‖ = 2 := by
  rw [infinityMatrixY, infinityMatrixZ, Matrix.diagonal_add, Matrix.l2_opNorm_diagonal]
  norm_num [Pi.norm_def, univ_fin3, Finset.sup_insert, Matrix.cons_val_two]

private theorem norm_infinityMatrix_sum :
    ‖infinityMatrixX + infinityMatrixY + infinityMatrixZ‖ = 1 := by
  rw [infinityMatrixX, infinityMatrixY, infinityMatrixZ, Matrix.diagonal_add,
    Matrix.diagonal_add, Matrix.l2_opNorm_diagonal]
  norm_num [Pi.norm_def, univ_fin3, Finset.sup_insert, Matrix.cons_val_two]

/--
No constant gives the Hlawka inequality for the spectral operator norm on
complex `3 x 3` matrices. This is the full `p = infinity` endpoint obstruction.
-/
theorem no_hlawkaConstant_operatorNorm_matrix_fin3 :
    ∀ C : ℝ, ¬HasHlawkaConstant
      (norm : Matrix (Fin 3) (Fin 3) ℂ → ℝ) C := by
  apply no_hlawkaConstant_of_pairGapSum_eq_zero
      (norm : Matrix (Fin 3) (Fin 3) ℂ → ℝ)
      infinityMatrixX infinityMatrixY infinityMatrixZ
  · simp only [tripleGap, norm_infinityMatrixX, norm_infinityMatrixY,
      norm_infinityMatrixZ, norm_infinityMatrix_sum]
    norm_num
  · simp only [pairGapSum, pairGap, norm_infinityMatrixX, norm_infinityMatrixY,
      norm_infinityMatrixZ, norm_infinityMatrixX_add_Y, norm_infinityMatrixX_add_Z,
      norm_infinityMatrixY_add_Z]
    norm_num

end HlawkaSchatten
