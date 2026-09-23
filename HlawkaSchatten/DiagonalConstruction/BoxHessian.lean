/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import HlawkaSchatten.DiagonalConstruction.CurvatureEstimate
import HlawkaSchatten.DiagonalConstruction.BoxCoordinates

/-! # Nonnegative second variation on the entire cyclic box -/

namespace HlawkaSchatten.DiagonalConstruction

/-- The Hessian of the deficit functional at `X` in direction `Z`. -/
noncomputable def deficitHessian (p K : ℝ) (X Z : Triple) : ℝ :=
  (2 * K - 1) * (∑ j, normHessian p (X j) (Z j)) +
    normHessian p (totalTriple X) (totalTriple Z) -
      K * (∑ j, normHessian p (pairTriple X j) (pairTriple Z j))

/-- Scaling the pair triple by subtraction. -/
theorem pairTriple_sub_smul (X Z : Triple) (a : ℝ) :
    pairTriple (Z - a • X) = pairTriple Z - a • pairTriple X := by
  ext j i
  fin_cases j <;> simp [pairTriple] <;> ring

/-- Upper bound on the sum of pair Hessians inside the box. -/
theorem pair_hessian_sum_upper {p : ℝ} (hp : 2 < p) {X : Triple} (hX : X ∈ entryBox)
    (Z : Triple) (a : ℝ) :
    (∑ j, normHessian p (pairTriple X j) (pairTriple Z j)) ≤
      4 * upperHessianCoefficient p * frobeniusSq (Z - a • X) := by
  have hi (j : Fin 3) : normHessian p (pairTriple X j) (pairTriple Z j) ≤
      upperHessianCoefficient p * euclideanSq (pairTriple (Z - a • X) j) := by
    rw [pairTriple_sub_smul]
    change normHessian p (pairTriple X j) (pairTriple Z j) ≤
      upperHessianCoefficient p * euclideanSq (pairTriple Z j - a • pairTriple X j)
    rw [← normHessian_sub_smul hp _ _ (entryBox_pair_ne_zero hX j) a]
    exact normHessian_upper hp _ _ j (entryBox_pair_large hX j) (entryBox_pair_small hX j)
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hi j)
  rw [← Finset.mul_sum] at hh
  have hm := mul_le_mul_of_nonneg_left (euclideanSq_pairs_le (Z - a • X))
    (upperHessianCoefficient_pos (by linarith : 1 < p)).le
  nlinarith

/-- The deficit Hessian is nonneg inside the box for `p ≥ 256`. -/
theorem deficitHessian_nonneg {p K : ℝ} (hp : 256 ≤ p) (hK : 1 ≤ K) (hKp : K ≤ p)
    {X : Triple} (hX : X ∈ entryBox) (Z : Triple) : 0 ≤ deficitHessian p K X Z := by
  have hp1 : 1 < p := by linarith
  have hp2 : 2 < p := by linarith
  let a : Fin 3 → ℝ := fun j ↦ radialCoefficient p (X j) (Z j)
  let b := radialCoefficient p (totalTriple X) (totalTriple Z)
  let U : Triple := fun j ↦ Z j - a j • X j
  let D := totalTriple Z - b • totalTriple X
  have hcol (j : Fin 3) : lowerHessianCoefficient p * euclideanSq (U j) ≤
      normHessian p (X j) (Z j) := by
    exact normHessian_lower hp2 _ _
      (fun i ↦ by linarith [(entryBox_column_bounds hX j i).1])
      (fun i ↦ by linarith [(entryBox_column_bounds hX j i).2])
  have hcols : lowerHessianCoefficient p * frobeniusSq U ≤
      ∑ j, normHessian p (X j) (Z j) := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hcol j)
    rwa [← Finset.mul_sum] at hh
  have htotal : lowerHessianCoefficient p * euclideanSq D ≤
      normHessian p (totalTriple X) (totalTriple Z) := by
    apply normHessian_lower hp2
    · intro i
      have hi := entryBox_total_bounds hX i
      rw [abs_of_pos (by linarith : 0 < totalTriple X i)]
      exact hi.1
    · intro i
      have hi := entryBox_total_bounds hX i
      rw [abs_of_pos (by linarith : 0 < totalTriple X i)]
      exact hi.2
  have hcols0 : 0 ≤ ∑ j, normHessian p (X j) (Z j) :=
    Finset.sum_nonneg fun j _ ↦ normHessian_nonneg hp1.le _ _
  have hpositive : lowerHessianCoefficient p * (frobeniusSq U + euclideanSq D) ≤
      (2 * K - 1) * (∑ j, normHessian p (X j) (Z j)) +
        normHessian p (totalTriple X) (totalTriple Z) := by
    have hm := mul_nonneg (by linarith : 0 ≤ 2 * K - 2) hcols0
    nlinarith
  have hgeom : frobeniusSq (Z - b • X) ≤ 300 * (frobeniusSq U + euclideanSq D) :=
    joint_radial_residual_bound hX Z a b
  have hpairs := pair_hessian_sum_upper hp2 hX Z b
  have hpair0 : 0 ≤ ∑ j, normHessian p (pairTriple X j) (pairTriple Z j) :=
    Finset.sum_nonneg fun j _ ↦ normHessian_nonneg hp1.le _ _
  have hd := (upperHessianCoefficient_pos hp1).le
  have hneg1 := mul_le_mul_of_nonneg_left hpairs (show 0 ≤ p by linarith)
  have hneg2 := mul_le_mul_of_nonneg_left hgeom
    (show 0 ≤ 4 * p * upperHessianCoefficient p by positivity)
  have hneg3 := mul_le_mul_of_nonneg_right hKp hpair0
  have hcurv := mul_le_mul_of_nonneg_right (hessian_curvature_margin hp).le
    (add_nonneg (frobeniusSq_nonneg U) (euclideanSq_nonneg D))
  dsimp only [deficitHessian]
  nlinarith

end HlawkaSchatten.DiagonalConstruction
