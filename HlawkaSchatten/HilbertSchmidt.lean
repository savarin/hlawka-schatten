/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import HlawkaSchatten.SchattenNorm
import HlawkaSchatten.HilbertHlawka
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The Schatten-2 quantity as a Hilbert norm

This file realizes a finite-dimensional linear map by its values on an
orthonormal basis.  At exponent two, this coordinate map is an isometry for
the Schatten quantity defined from singular values.  Consequently the
Schatten-2 quantity satisfies Hlawka's inequality with constant one.
-/

namespace HlawkaSchatten

open scoped InnerProductSpace

variable {𝕜 E F ι : Type*} [RCLike 𝕜] [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- Hilbert--Schmidt coordinates of a linear map, obtained by evaluating it
on an orthonormal basis of its domain. -/
noncomputable def hilbertSchmidtCoordinates
    (e : OrthonormalBasis ι 𝕜 E) (T : E →ₗ[𝕜] F) :
    PiLp 2 (fun _ : ι => F) :=
  WithLp.toLp 2 (fun i => T (e i))

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
@[simp]
theorem hilbertSchmidtCoordinates_add
    (e : OrthonormalBasis ι 𝕜 E) (S T : E →ₗ[𝕜] F) :
    hilbertSchmidtCoordinates e (S + T) =
      hilbertSchmidtCoordinates e S + hilbertSchmidtCoordinates e T := by
  rfl

/-- Evaluation on an orthonormal basis is a linear equivalence from linear
maps to their finite family of columns. -/
noncomputable def hilbertSchmidtLinearEquiv
    (e : OrthonormalBasis ι 𝕜 E) :
    (E →ₗ[𝕜] F) ≃ₗ[𝕜] PiLp 2 (fun _ : ι => F) where
  toFun := hilbertSchmidtCoordinates e
  invFun x := e.toBasis.constr 𝕜 (WithLp.ofLp x)
  left_inv T := by
    apply e.toBasis.ext
    intro i
    change (e.toBasis.constr 𝕜 (fun j => T (e j))) (e i) = T (e i)
    exact e.toBasis.constr_basis 𝕜 _ i
  right_inv x := by
    apply WithLp.ofLp_injective 2
    funext i
    change (e.toBasis.constr 𝕜 (WithLp.ofLp x)) (e i) = WithLp.ofLp x i
    exact e.toBasis.constr_basis 𝕜 _ i
  map_add' := hilbertSchmidtCoordinates_add e
  map_smul' _ _ := rfl

/-- The exponent-two singular-value power sum is the sum of the squared
norms of the columns in any orthonormal basis. -/
theorem singularValuePowerSum_two_eq_sum_norm_sq
    (e : OrthonormalBasis ι 𝕜 E) (T : E →ₗ[𝕜] F) :
    singularValuePowerSum 2 T = ∑ i, ‖T (e i)‖ ^ 2 := by
  rw [singularValuePowerSum_two_eq_re_trace,
    LinearMap.trace_eq_sum_inner (T.adjoint.comp T) e, map_sum]
  apply Fintype.sum_congr
  intro i
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right]
  exact (norm_sq_eq_re_inner (𝕜 := 𝕜) (T (e i))).symm

/-- The Schatten-2 quantity is exactly the Hilbert norm of the column
coordinate family. -/
theorem schattenPNorm_two_eq_norm_hilbertSchmidtCoordinates
    (e : OrthonormalBasis ι 𝕜 E) (T : E →ₗ[𝕜] F) :
    schattenPNorm 2 T = ‖hilbertSchmidtCoordinates e T‖ := by
  rw [← sq_eq_sq₀ (schattenPNorm_nonneg 2 T) (norm_nonneg _),
    schattenPNorm_two_sq, PiLp.norm_sq_eq_of_L2]
  exact singularValuePowerSum_two_eq_sum_norm_sq e T

/-- The exponent-two power sum is the square of the Hilbert coordinate
norm. -/
theorem singularValuePowerSum_two_eq_norm_hilbertSchmidtCoordinates_sq
    (e : OrthonormalBasis ι 𝕜 E) (T : E →ₗ[𝕜] F) :
    singularValuePowerSum 2 T = ‖hilbertSchmidtCoordinates e T‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  exact singularValuePowerSum_two_eq_sum_norm_sq e T

/-- The Schatten-2 power sphere is exactly the ordinary unit sphere of the
Hilbert column-coordinate space. -/
noncomputable def schattenTwoPowerSphereEquivUnitSphere
    (e : OrthonormalBasis ι 𝕜 E) :
    schattenPowerSphere (𝕜 := 𝕜) (E := E) (F := F) 2 ≃
      unitSphere (PiLp 2 (fun _ : ι => F)) where
  toFun T := ⟨hilbertSchmidtCoordinates e T.1, by
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    rw [← singularValuePowerSum_two_eq_norm_hilbertSchmidtCoordinates_sq e,
      T.property, one_pow]⟩
  invFun x := ⟨(hilbertSchmidtLinearEquiv e).symm x.1, by
    rw [singularValuePowerSum_two_eq_norm_hilbertSchmidtCoordinates_sq e,
      show hilbertSchmidtCoordinates e ((hilbertSchmidtLinearEquiv e).symm x.1) =
          x.1 from (hilbertSchmidtLinearEquiv e).apply_symm_apply x.1,
      x.property, one_pow]⟩
  left_inv T := Subtype.ext ((hilbertSchmidtLinearEquiv e).symm_apply_apply T.1)
  right_inv x := Subtype.ext ((hilbertSchmidtLinearEquiv e).apply_symm_apply x.1)

/-- The finite-dimensional Schatten-2 quantity has Hlawka constant one. -/
theorem schattenPNorm_two_hasHlawkaConstant :
    HasHlawkaConstant (schattenPNorm 2 : (E →ₗ[𝕜] F) → ℝ) 1 := by
  let e := stdOrthonormalBasis 𝕜 E
  intro x y z
  have h := norm_hasHlawkaConstant (𝕜 := 𝕜)
    (E := PiLp 2 (fun _ : Fin (Module.finrank 𝕜 E) => F))
    (hilbertSchmidtCoordinates e x)
    (hilbertSchmidtCoordinates e y)
    (hilbertSchmidtCoordinates e z)
  dsimp only [tripleGap, pairGapSum, pairGap] at h ⊢
  simp only [← hilbertSchmidtCoordinates_add] at h
  simpa only [schattenPNorm_two_eq_norm_hilbertSchmidtCoordinates e] using h

end HlawkaSchatten
