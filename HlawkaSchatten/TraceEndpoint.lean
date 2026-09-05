/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import HlawkaSchatten.SchattenNorm
import HlawkaSchatten.HilbertSchmidt
import Mathlib.Analysis.InnerProductSpace.NormDet

/-! # The Schatten-one endpoint -/

namespace HlawkaSchatten

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

private theorem singularValuePowerSum_one_eq_sum_range
    (T : E →ₗ[𝕜] F) :
    singularValuePowerSum 1 T =
      ∑ i ∈ Finset.range (Module.finrank 𝕜 E), T.singularValues i := by
  have hrank : Module.finrank 𝕜 T.range ≤ Module.finrank 𝕜 E :=
    T.finrank_range_le
  unfold singularValuePowerSum
  rw [T.support_singularValues]
  simp_rw [Real.rpow_one]
  apply Finset.sum_subset (Finset.range_mono hrank)
  intro i hi hi'
  have hirank : Module.finrank 𝕜 T.range ≤ i := by
    exact Nat.le_of_not_gt (fun hlt => hi' (Finset.mem_range.mpr hlt))
  rw [T.singularValues_eq_zero_iff_le_finrank_range.mpr hirank]

private theorem singularValuePowerSum_two_eq_sum_range
    (T : E →ₗ[𝕜] F) :
    singularValuePowerSum 2 T =
      ∑ i ∈ Finset.range (Module.finrank 𝕜 E), T.singularValues i ^ 2 := by
  have hrank : Module.finrank 𝕜 T.range ≤ Module.finrank 𝕜 E :=
    T.finrank_range_le
  unfold singularValuePowerSum
  rw [T.support_singularValues]
  simp_rw [Real.rpow_two]
  apply Finset.sum_subset (Finset.range_mono hrank)
  intro i hi hi'
  have hirank : Module.finrank 𝕜 T.range ≤ i := by
    exact Nat.le_of_not_gt (fun hlt => hi' (Finset.mem_range.mpr hlt))
  rw [T.singularValues_eq_zero_iff_le_finrank_range.mpr hirank]
  norm_num

/-- In domain dimension two, the square of the Schatten-one norm is the
Hilbert--Schmidt square plus twice the norm determinant. -/
theorem schattenPNorm_one_sq_eq_singularValuePowerSum_two_add_normDet
    (T : E →ₗ[𝕜] F) (hdim : Module.finrank 𝕜 E = 2) :
    schattenPNorm 1 T ^ 2 = singularValuePowerSum 2 T + 2 * T.normDet := by
  have hsum1 := singularValuePowerSum_one_eq_sum_range T
  have hsum2 := singularValuePowerSum_two_eq_sum_range T
  have hdet := T.normDet_eq_prod_singularValues
  rw [hdim] at hsum1 hsum2 hdet
  norm_num [Finset.sum_range_succ, Finset.prod_range_succ] at hsum1 hsum2 hdet
  unfold schattenPNorm
  norm_num
  rw [hsum1, hsum2, hdet]
  ring

/-- Concrete `2 × 2` trace-norm formula in Euclidean coordinates. -/
theorem schattenPNorm_one_toEuclideanLin_sq
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    schattenPNorm 1 A.toEuclideanLin ^ 2 =
      (∑ j, ‖A 0 j‖ ^ 2) + (∑ j, ‖A 1 j‖ ^ 2) + 2 * ‖A.det‖ := by
  rw [schattenPNorm_one_sq_eq_singularValuePowerSum_two_add_normDet
    A.toEuclideanLin (by simp)]
  rw [singularValuePowerSum_two_eq_sum_norm_sq
    (EuclideanSpace.basisFun (Fin 2) ℂ)]
  have hdet : A.toEuclideanLin.normDet = ‖A.det‖ := by
    rw [A.toEuclideanLin.normDet_eq_norm_det_toMatrix
      (EuclideanSpace.basisFun (Fin 2) ℂ)
      (EuclideanSpace.basisFun (Fin 2) ℂ)]
    simp only [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.toMatrix_toLin]
  rw [hdet]
  simp only [Fin.sum_univ_two,
    EuclideanSpace.basisFun_apply, PiLp.norm_sq_eq_of_L2]
  norm_num [Matrix.mulVec, dotProduct]
  ring

private noncomputable def traceEndpointX (c s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(c ^ 2 : ℂ), (c * s : ℂ); (c * s : ℂ), (s ^ 2 : ℂ)]

private noncomputable def traceEndpointY (c s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(c ^ 2 : ℂ), (-c * s : ℂ); (-c * s : ℂ), (s ^ 2 : ℂ)]

private noncomputable def traceEndpointZ (s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 0; 0, (-2 * s ^ 2 : ℂ)]

private theorem traceEndpoint_X_add_Y (c s : ℝ) :
    traceEndpointX c s + traceEndpointY c s =
      !![(2 * c ^ 2 : ℂ), 0; 0, (2 * s ^ 2 : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [traceEndpointX, traceEndpointY] <;> ring

private theorem traceEndpoint_X_add_Y_add_Z (c s : ℝ) :
    traceEndpointX c s + traceEndpointY c s + traceEndpointZ s =
      !![(2 * c ^ 2 : ℂ), 0; 0, 0] := by
  rw [traceEndpoint_X_add_Y]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [traceEndpointZ]

private theorem traceEndpoint_X_add_Z (c s : ℝ) :
    traceEndpointX c s + traceEndpointZ s =
      !![(c ^ 2 : ℂ), (c * s : ℂ); (c * s : ℂ), (-s ^ 2 : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [traceEndpointX, traceEndpointZ]; ring

private theorem traceEndpoint_Y_add_Z (c s : ℝ) :
    traceEndpointY c s + traceEndpointZ s =
      !![(c ^ 2 : ℂ), (-c * s : ℂ); (-c * s : ℂ), (-s ^ 2 : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [traceEndpointY, traceEndpointZ]; ring

private theorem traceEndpoint_norm_X {c s : ℝ} (hc : 0 ≤ c) (hs : 0 ≤ s)
    (hunit : c ^ 2 + s ^ 2 = 1) :
    schattenPNorm 1 (traceEndpointX c s).toEuclideanLin = 1 := by
  have hdet : (traceEndpointX c s).det = 0 := by
    simp [traceEndpointX, Matrix.det_fin_two]
    ring
  apply (sq_eq_sq₀ (schattenPNorm_nonneg 1 _) zero_le_one).mp
  rw [schattenPNorm_one_toEuclideanLin_sq]
  rw [hdet, norm_zero]
  simp [traceEndpointX, Fin.sum_univ_two,
    abs_of_nonneg hc, abs_of_nonneg hs]
  nlinarith [sq_nonneg (c * s)]

private theorem traceEndpoint_norm_Y {c s : ℝ} (hc : 0 ≤ c) (hs : 0 ≤ s)
    (hunit : c ^ 2 + s ^ 2 = 1) :
    schattenPNorm 1 (traceEndpointY c s).toEuclideanLin = 1 := by
  have hdet : (traceEndpointY c s).det = 0 := by
    simp [traceEndpointY, Matrix.det_fin_two]
    ring
  apply (sq_eq_sq₀ (schattenPNorm_nonneg 1 _) zero_le_one).mp
  rw [schattenPNorm_one_toEuclideanLin_sq, hdet, norm_zero]
  simp [traceEndpointY, Fin.sum_univ_two, abs_of_nonneg hc, abs_of_nonneg hs]
  nlinarith [sq_nonneg (c * s)]

private theorem traceEndpoint_norm_Z {s : ℝ} (hs : 0 ≤ s) :
    schattenPNorm 1 (traceEndpointZ s).toEuclideanLin = 2 * s ^ 2 := by
  apply (sq_eq_sq₀ (schattenPNorm_nonneg 1 _) (mul_nonneg (by norm_num) (sq_nonneg s))).mp
  rw [schattenPNorm_one_toEuclideanLin_sq]
  simp [traceEndpointZ, Fin.sum_univ_two, Matrix.det_fin_two, abs_of_nonneg hs]

private theorem traceEndpoint_norm_X_add_Y {c s : ℝ} (hc : 0 ≤ c) (hs : 0 ≤ s)
    (hunit : c ^ 2 + s ^ 2 = 1) :
    schattenPNorm 1 ((traceEndpointX c s + traceEndpointY c s).toEuclideanLin) = 2 := by
  rw [traceEndpoint_X_add_Y]
  apply (sq_eq_sq₀ (schattenPNorm_nonneg 1 _) (by norm_num)).mp
  rw [schattenPNorm_one_toEuclideanLin_sq]
  simp [Fin.sum_univ_two, Matrix.det_fin_two, abs_of_nonneg hc, abs_of_nonneg hs]
  nlinarith [sq_nonneg c, sq_nonneg s]

private theorem traceEndpoint_norm_sum {c s : ℝ} (hc : 0 ≤ c) (_hs : 0 ≤ s)
    (_hunit : c ^ 2 + s ^ 2 = 1) :
    schattenPNorm 1
      ((traceEndpointX c s + traceEndpointY c s + traceEndpointZ s).toEuclideanLin) =
        2 * c ^ 2 := by
  rw [traceEndpoint_X_add_Y_add_Z]
  apply (sq_eq_sq₀ (schattenPNorm_nonneg 1 _) (mul_nonneg (by norm_num) (sq_nonneg c))).mp
  rw [schattenPNorm_one_toEuclideanLin_sq]
  simp [Fin.sum_univ_two, Matrix.det_fin_two, abs_of_nonneg hc]

private theorem traceEndpoint_norm_X_add_Z {c s : ℝ} (hc : 0 ≤ c) (hs : 0 ≤ s)
    (hunit : c ^ 2 + s ^ 2 = 1) :
    schattenPNorm 1 ((traceEndpointX c s + traceEndpointZ s).toEuclideanLin) =
      √(1 + 4 * c ^ 2 * s ^ 2) := by
  rw [traceEndpoint_X_add_Z]
  have hdet : (!![(c ^ 2 : ℂ), (c * s : ℂ); (c * s : ℂ), (-s ^ 2 : ℂ)] :
      Matrix (Fin 2) (Fin 2) ℂ).det = (-2 * c ^ 2 * s ^ 2 : ℝ) := by
    simp [Matrix.det_fin_two]
    ring
  have hrad : 0 ≤ 1 + 4 * c ^ 2 * s ^ 2 := by positivity
  apply (sq_eq_sq₀ (schattenPNorm_nonneg 1 _) (Real.sqrt_nonneg _)).mp
  rw [schattenPNorm_one_toEuclideanLin_sq, Real.sq_sqrt hrad, hdet]
  simp [Fin.sum_univ_two, abs_of_nonneg hc, abs_of_nonneg hs]
  nlinarith [sq_nonneg (c * s)]

private theorem traceEndpoint_norm_Y_add_Z {c s : ℝ} (hc : 0 ≤ c) (hs : 0 ≤ s)
    (hunit : c ^ 2 + s ^ 2 = 1) :
    schattenPNorm 1 ((traceEndpointY c s + traceEndpointZ s).toEuclideanLin) =
      √(1 + 4 * c ^ 2 * s ^ 2) := by
  rw [traceEndpoint_Y_add_Z]
  have hdet : (!![(c ^ 2 : ℂ), (-c * s : ℂ); (-c * s : ℂ), (-s ^ 2 : ℂ)] :
      Matrix (Fin 2) (Fin 2) ℂ).det = (-2 * c ^ 2 * s ^ 2 : ℝ) := by
    simp [Matrix.det_fin_two]
    ring
  have hrad : 0 ≤ 1 + 4 * c ^ 2 * s ^ 2 := by positivity
  apply (sq_eq_sq₀ (schattenPNorm_nonneg 1 _) (Real.sqrt_nonneg _)).mp
  rw [schattenPNorm_one_toEuclideanLin_sq, Real.sq_sqrt hrad, hdet]
  simp [Fin.sum_univ_two, abs_of_nonneg hc, abs_of_nonneg hs]
  nlinarith [sq_nonneg (c * s)]

private noncomputable def traceEndpointLinearX (c s : ℝ) :=
  (traceEndpointX c s).toEuclideanLin

private noncomputable def traceEndpointLinearY (c s : ℝ) :=
  (traceEndpointY c s).toEuclideanLin

private noncomputable def traceEndpointLinearZ (s : ℝ) :=
  (traceEndpointZ s).toEuclideanLin

private theorem traceEndpoint_tripleGap {c s : ℝ} (hc : 0 ≤ c) (hs : 0 ≤ s)
    (hunit : c ^ 2 + s ^ 2 = 1) :
    tripleGap (schattenPNorm 1)
      (traceEndpointLinearX c s) (traceEndpointLinearY c s) (traceEndpointLinearZ s) =
        4 * s ^ 2 := by
  unfold tripleGap traceEndpointLinearX traceEndpointLinearY traceEndpointLinearZ
  rw [traceEndpoint_norm_X hc hs hunit, traceEndpoint_norm_Y hc hs hunit,
    traceEndpoint_norm_Z hs]
  rw [← map_add, ← map_add, traceEndpoint_norm_sum hc hs hunit]
  nlinarith

private theorem traceEndpoint_pairGapSum {c s : ℝ} (hc : 0 ≤ c) (hs : 0 ≤ s)
    (hunit : c ^ 2 + s ^ 2 = 1) :
    pairGapSum (schattenPNorm 1)
      (traceEndpointLinearX c s) (traceEndpointLinearY c s) (traceEndpointLinearZ s) =
        2 * (1 + 2 * s ^ 2 - √(1 + 4 * c ^ 2 * s ^ 2)) := by
  unfold pairGapSum pairGap traceEndpointLinearX traceEndpointLinearY traceEndpointLinearZ
  rw [traceEndpoint_norm_X hc hs hunit, traceEndpoint_norm_Y hc hs hunit,
    traceEndpoint_norm_Z hs]
  rw [← map_add, traceEndpoint_norm_X_add_Y hc hs hunit,
    ← map_add, traceEndpoint_norm_X_add_Z hc hs hunit,
    ← map_add, traceEndpoint_norm_Y_add_Z hc hs hunit]
  ring

private theorem traceEndpoint_pairGapSum_bounds {c s : ℝ}
    (hc : 0 ≤ c) (hs : 0 ≤ s) (hunit : c ^ 2 + s ^ 2 = 1)
    (hsq : s ^ 2 ≤ 1 / 2) :
    0 ≤ pairGapSum (schattenPNorm 1)
        (traceEndpointLinearX c s) (traceEndpointLinearY c s) (traceEndpointLinearZ s) ∧
      pairGapSum (schattenPNorm 1)
        (traceEndpointLinearX c s) (traceEndpointLinearY c s) (traceEndpointLinearZ s) ≤
          8 * (s ^ 2) ^ 2 := by
  let q := √(1 + 4 * c ^ 2 * s ^ 2)
  have hrad : 0 ≤ 1 + 4 * c ^ 2 * s ^ 2 := by positivity
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq2 : q ^ 2 = 1 + 4 * c ^ 2 * s ^ 2 := Real.sq_sqrt hrad
  have hs2 : 0 ≤ s ^ 2 := sq_nonneg s
  have hupper : q ≤ 1 + 2 * s ^ 2 := by
    nlinarith [sq_nonneg (q + (1 + 2 * s ^ 2))]
  have hlowerTerm : 0 ≤ 1 + 2 * s ^ 2 - 4 * (s ^ 2) ^ 2 := by
    nlinarith [sq_nonneg (s ^ 2 - 1 / 2)]
  have hlower : 1 + 2 * s ^ 2 - 4 * (s ^ 2) ^ 2 ≤ q := by
    nlinarith [sq_nonneg (q + (1 + 2 * s ^ 2 - 4 * (s ^ 2) ^ 2)),
      mul_nonneg hs2 (sub_nonneg.mpr hsq)]
  rw [traceEndpoint_pairGapSum hc hs hunit]
  exact ⟨by linarith, by linarith⟩

/-- No finite Hlawka constant exists for the Schatten-one norm already on
complex `2 × 2` operators. -/
theorem no_hlawkaConstant_schattenPNorm_one_fin2 :
    ∀ C : ℝ, ¬HasHlawkaConstant
      (schattenPNorm 1 :
        (EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2)) → ℝ) C := by
  intro C hC
  let d : ℝ := 16 * (|C| + 1)
  let u : ℝ := d⁻¹
  have hd : 0 < d := by
    dsimp only [d]
    positivity
  have hu : 0 < u := inv_pos.mpr hd
  have hdu : d * u = 1 := by
    dsimp only [u]
    exact mul_inv_cancel₀ hd.ne'
  have hu_le : u ≤ 1 / 16 := by
    dsimp only [u, d]
    rw [inv_le_iff_one_le_mul₀' hd]
    nlinarith [abs_nonneg C]
  let s : ℝ := √u
  let c : ℝ := √(1 - u)
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = u := Real.sq_sqrt hu.le
  have hcu : 0 ≤ 1 - u := by nlinarith
  have hc : 0 ≤ c := Real.sqrt_nonneg _
  have hc2 : c ^ 2 = 1 - u := Real.sq_sqrt hcu
  have hunit : c ^ 2 + s ^ 2 = 1 := by rw [hc2, hs2]; ring
  have hpair := traceEndpoint_pairGapSum_bounds hc hs hunit (by rw [hs2]; linarith)
  have htriple := traceEndpoint_tripleGap hc hs hunit
  have hH := hC (traceEndpointLinearX c s)
    (traceEndpointLinearY c s) (traceEndpointLinearZ s)
  rw [htriple, hs2] at hH
  have hCpair : C * pairGapSum (schattenPNorm 1)
      (traceEndpointLinearX c s) (traceEndpointLinearY c s) (traceEndpointLinearZ s) ≤
      |C| * (8 * u ^ 2) := calc
    _ ≤ |C| * pairGapSum (schattenPNorm 1)
        (traceEndpointLinearX c s) (traceEndpointLinearY c s) (traceEndpointLinearZ s) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) hpair.1
    _ ≤ |C| * (8 * (s ^ 2) ^ 2) :=
      mul_le_mul_of_nonneg_left hpair.2 (abs_nonneg C)
    _ = |C| * (8 * u ^ 2) := by rw [hs2]
  have hsmall : |C| * (8 * u ^ 2) < 4 * u := by
    have hAu : 8 * |C| * u < 4 := by
      dsimp only [d] at hdu
      nlinarith [abs_nonneg C]
    nlinarith
  linarith

end HlawkaSchatten
