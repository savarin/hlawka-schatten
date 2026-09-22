/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import HlawkaSchatten.DiagonalConstruction.Basic
import HlawkaSchatten.HermitianDilation

/-!
# Diagonal operators and coordinate power sums

This connects the coordinate proof to the singular-value Schatten norm
used in the publication boundary. The Gram operator has the coordinate
basis as an eigenbasis, with eigenvalues equal to squared entry norms.
-/

namespace HlawkaSchatten.DiagonalConstruction

open scoped InnerProductSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The complex operator with the prescribed diagonal. -/
noncomputable def diagonalOperator (d : ι → ℂ) :
    EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι :=
  Matrix.toEuclideanLin (Matrix.diagonal d)

@[simp]
theorem diagonalOperator_apply (d : ι → ℂ) (x : EuclideanSpace ℂ ι) (i : ι) :
    diagonalOperator d x i = d i * x i := by
  exact Matrix.mulVec_diagonal d (WithLp.ofLp x) i

theorem diagonalOperator_adjoint (d : ι → ℂ) :
    (diagonalOperator d).adjoint = diagonalOperator (fun i ↦ star (d i)) := by
  unfold diagonalOperator
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  congr 1
  ext i j
  simp [Matrix.conjTranspose_apply, Matrix.diagonal_apply]
  split_ifs with h <;> simp_all

theorem diagonalOperator_gram (d : ι → ℂ) :
    (diagonalOperator d).adjoint.comp (diagonalOperator d) =
      diagonalOperator (fun i ↦ (‖d i‖ ^ 2 : ℝ)) := by
  rw [diagonalOperator_adjoint]
  ext x i
  simp only [LinearMap.comp_apply, diagonalOperator_apply]
  rw [← mul_assoc]
  congr 1
  exact Complex.normSq_eq_conj_mul_self.symm.trans
    (congrArg Complex.ofReal (Complex.normSq_eq_norm_sq (d i)))

theorem diagonalOperator_apply_basis (d : ι → ℂ) (i : ι) :
    diagonalOperator d (EuclideanSpace.basisFun ι ℂ i) =
      d i • EuclideanSpace.basisFun ι ℂ i := by
  ext j
  simp [EuclideanSpace.basisFun_apply]
  split_ifs with h <;> simp_all

/-- The Schatten power sum of a diagonal operator is the coordinate power sum. -/
theorem singularValuePowerSum_diagonal {p : ℝ} (hp : 0 < p) (d : ι → ℂ) :
    singularValuePowerSum p (diagonalOperator d) = ∑ i, ‖d i‖ ^ p := by
  rw [singularValuePowerSum_eq_re_trace_gramFunctionalCalculus hp,
    LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun ι ℂ), Complex.re_sum]
  apply Fintype.sum_congr
  intro i
  rw [hermitianFunctionalCalculus_apply_of_apply_eq_smul
    (fun y ↦ y ^ (p / 2)) _ _ _ (‖d i‖ ^ 2)
    (by rw [diagonalOperator_gram, diagonalOperator_apply_basis])]
  rw [inner_smul_right, (EuclideanSpace.basisFun ι ℂ).inner_eq_one, mul_one,
    Complex.ofReal_re]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  congr 1
  ring

/-- Exact agreement with the existing singular-value definition. -/
theorem schattenPNorm_diagonal {p : ℝ} (hp : 0 < p) (d : ι → ℂ) :
    schattenPNorm p (diagonalOperator d) = lpNorm p d := by
  rw [schattenPNorm, singularValuePowerSum_diagonal hp]
  rfl

end HlawkaSchatten.DiagonalConstruction
