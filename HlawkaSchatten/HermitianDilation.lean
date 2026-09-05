/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import HlawkaSchatten.HermitianSpectral
import HlawkaSchatten.SchattenNorm
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Rectangular Hermitian dilation

This file begins the passage from rectangular maps to the Hermitian spectral
comparison by constructing the standard off-diagonal dilation.
-/

namespace HlawkaSchatten

open scoped InnerProductSpace

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- The off-diagonal Hermitian dilation `(x,y) ↦ (T†y, Tx)` of a rectangular
complex-linear map. -/
private noncomputable def productOffDiagonal (T : E →ₗ[ℂ] F) :
    E × F →ₗ[ℂ] E × F :=
  LinearMap.prod
    (T.adjoint.comp (LinearMap.snd ℂ E F))
    (T.comp (LinearMap.fst ℂ E F))

private def productDiagonal (A : E →ₗ[ℂ] E) (B : F →ₗ[ℂ] F) :
    E × F →ₗ[ℂ] E × F :=
  LinearMap.prod
    (A.comp (LinearMap.fst ℂ E F))
    (B.comp (LinearMap.snd ℂ E F))

/-- The off-diagonal dilation, transported to the Hilbert `L²` product. -/
noncomputable def hermitianDilation (T : E →ₗ[ℂ] F) :
    WithLp 2 (E × F) →ₗ[ℂ] WithLp 2 (E × F) :=
  (WithLp.linearEquiv 2 ℂ (E × F)).symm.toLinearMap.comp
    ((productOffDiagonal T).comp
      (WithLp.linearEquiv 2 ℂ (E × F)).toLinearMap)

/-- A block-diagonal endomorphism transported to the Hilbert `L²` product. -/
noncomputable def hermitianBlockDiagonal (A : E →ₗ[ℂ] E) (B : F →ₗ[ℂ] F) :
    WithLp 2 (E × F) →ₗ[ℂ] WithLp 2 (E × F) :=
  (WithLp.linearEquiv 2 ℂ (E × F)).symm.toLinearMap.comp
    ((productDiagonal A B).comp
      (WithLp.linearEquiv 2 ℂ (E × F)).toLinearMap)

/-- The grading involution which is positive on the domain summand and
negative on the codomain summand. -/
noncomputable def hermitianSignature :
    WithLp 2 (E × F) →ₗ[ℂ] WithLp 2 (E × F) :=
  hermitianBlockDiagonal LinearMap.id (-LinearMap.id)

@[simp]
theorem hermitianDilation_apply (T : E →ₗ[ℂ] F) (x : E) (y : F) :
    hermitianDilation T (WithLp.toLp 2 (x, y)) =
      WithLp.toLp 2 (T.adjoint y, T x) := by
  rfl

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] in
@[simp]
theorem hermitianBlockDiagonal_apply
    (A : E →ₗ[ℂ] E) (B : F →ₗ[ℂ] F) (x : E) (y : F) :
    hermitianBlockDiagonal A B (WithLp.toLp 2 (x, y)) =
      WithLp.toLp 2 (A x, B y) := by
  rfl

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] in
@[simp]
theorem hermitianSignature_apply (x : E) (y : F) :
    hermitianSignature (WithLp.toLp 2 (x, y)) =
      WithLp.toLp 2 (x, -y) := by
  simp [hermitianSignature]

/-- The off-diagonal dilation anticommutes with the product grading. -/
theorem hermitianDilation_comp_signature (T : E →ₗ[ℂ] F) :
    (hermitianDilation T).comp hermitianSignature =
      -(hermitianSignature.comp (hermitianDilation T)) := by
  apply LinearMap.ext
  intro z
  rw [← WithLp.toLp_ofLp 2 z]
  rcases WithLp.ofLp z with ⟨x, y⟩
  simp only [LinearMap.comp_apply, hermitianSignature_apply,
    hermitianDilation_apply, LinearMap.neg_apply]
  rw [← WithLp.toLp_neg]
  simp

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] in
/-- Trace of a block-diagonal map is the sum of the block traces. -/
theorem trace_hermitianBlockDiagonal
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : OrthonormalBasis ι ℂ E) (f : OrthonormalBasis κ ℂ F)
    (A : E →ₗ[ℂ] E) (B : F →ₗ[ℂ] F) :
    (hermitianBlockDiagonal A B).trace ℂ (WithLp 2 (E × F)) =
      A.trace ℂ E + B.trace ℂ F := by
  rw [LinearMap.trace_eq_sum_inner _ (e.prod f), Fintype.sum_sum_type]
  simp only [OrthonormalBasis.prod_apply, Sum.elim_inl, Sum.elim_inr,
    Function.comp_apply, LinearMap.inl_apply, LinearMap.inr_apply,
    hermitianBlockDiagonal_apply, WithLp.prod_inner_apply,
    inner_zero_left, add_zero, zero_add]
  rw [← LinearMap.trace_eq_sum_inner A e,
    ← LinearMap.trace_eq_sum_inner B f]

/-- The rectangular off-diagonal dilation is symmetric. -/
theorem hermitianDilation_isSymmetric (T : E →ₗ[ℂ] F) :
    (hermitianDilation T).IsSymmetric := by
  intro u v
  rw [← WithLp.toLp_ofLp 2 u, ← WithLp.toLp_ofLp 2 v]
  rcases WithLp.ofLp u with ⟨x₁, y₁⟩
  rcases WithLp.ofLp v with ⟨x₂, y₂⟩
  simp only [hermitianDilation_apply, WithLp.prod_inner_apply]
  rw [T.adjoint_inner_left, T.adjoint_inner_right]
  ring

/-- Hermitian dilation preserves addition. -/
theorem hermitianDilation_add (S T : E →ₗ[ℂ] F) :
    hermitianDilation (S + T) = hermitianDilation S + hermitianDilation T := by
  apply LinearMap.ext
  intro u
  rw [← WithLp.toLp_ofLp 2 u]
  rcases WithLp.ofLp u with ⟨x, y⟩
  simp only [hermitianDilation_apply, map_add, LinearMap.add_apply]
  rw [← WithLp.toLp_add]
  apply WithLp.toLp_injective 2
  rfl

/-- Real scaling commutes with Hermitian dilation. -/
theorem hermitianDilation_real_smul (r : ℝ) (T : E →ₗ[ℂ] F) :
    hermitianDilation ((r : ℂ) • T) =
      (r : ℂ) • hermitianDilation T := by
  apply LinearMap.ext
  intro u
  rw [← WithLp.toLp_ofLp 2 u]
  rcases WithLp.ofLp u with ⟨x, y⟩
  simp only [hermitianDilation_apply, LinearMap.smul_apply]
  apply WithLp.ofLp_injective 2
  simp only [Complex.coe_smul, WithLp.ofLp_smul, Prod.smul_mk,
    Prod.mk.injEq, and_true]
  apply ext_inner_right ℂ
  intro z
  rw [LinearMap.adjoint_inner_left]
  change ⟪y, (r : ℂ) • T z⟫_ℂ =
    ⟪(r : ℂ) • T.adjoint y, z⟫_ℂ
  rw [inner_smul_right, inner_smul_left]
  rw [LinearMap.adjoint_inner_left]
  have hr : (starRingEnd ℂ) (r : ℂ) = (r : ℂ) := by
    apply Complex.ext <;> simp
  rw [hr]

@[simp]
theorem hermitianDilation_neg (T : E →ₗ[ℂ] F) :
    hermitianDilation (-T) = -hermitianDilation T := by
  simpa using hermitianDilation_real_smul (-1) T

theorem hermitianDilation_sub (S T : E →ₗ[ℂ] F) :
    hermitianDilation (S - T) = hermitianDilation S - hermitianDilation T := by
  rw [sub_eq_add_neg, hermitianDilation_add, hermitianDilation_neg, sub_eq_add_neg]

@[simp]
theorem hermitianDilation_zero :
    hermitianDilation (0 : E →ₗ[ℂ] F) = 0 := by
  apply LinearMap.ext
  intro u
  rw [← WithLp.toLp_ofLp 2 u]
  rcases WithLp.ofLp u with ⟨x, y⟩
  simp

/-- The off-diagonal dilation remembers the original rectangular map. -/
theorem hermitianDilation_injective :
    Function.Injective (hermitianDilation :
      (E →ₗ[ℂ] F) → WithLp 2 (E × F) →ₗ[ℂ] WithLp 2 (E × F)) := by
  intro S T h
  apply LinearMap.ext
  intro x
  have hx := DFunLike.congr_fun h (WithLp.toLp 2 (x, 0))
  have hy := congrArg
    (fun u : WithLp 2 (E × F) ↦ (WithLp.ofLp u).2) hx
  simpa using hy

/-- Squaring the dilation produces the two Gram operators on the diagonal. -/
@[simp]
theorem hermitianDilation_sq_apply (T : E →ₗ[ℂ] F) (x : E) (y : F) :
    ((hermitianDilation T).comp (hermitianDilation T))
        (WithLp.toLp 2 (x, y)) =
      WithLp.toLp 2 (T.adjoint (T x), T (T.adjoint y)) := by
  rw [LinearMap.comp_apply, hermitianDilation_apply,
    hermitianDilation_apply]

/-- Functional calculus of the squared dilation splits into the functional
calculi of its two Gram blocks. -/
theorem hermitianDilation_sq_functionalCalculus
    (g : ℝ → ℝ) (T : E →ₗ[ℂ] F) :
    hermitianFunctionalCalculus g
        ((hermitianDilation T).comp (hermitianDilation T))
        (isSymmetric_comp_self (hermitianDilation T)
          (hermitianDilation_isSymmetric T)) =
      hermitianBlockDiagonal
        (hermitianFunctionalCalculus g (T.adjoint.comp T)
          T.isSymmetric_adjoint_comp_self)
        (hermitianFunctionalCalculus g (T.comp T.adjoint)
          T.isSymmetric_self_comp_adjoint) := by
  let hD := hermitianDilation_isSymmetric T
  let hG := T.isSymmetric_adjoint_comp_self
  let hK := T.isSymmetric_self_comp_adjoint
  apply ((hG.eigenvectorBasis rfl).prod
    (hK.eigenvectorBasis rfl)).toBasis.ext
  intro ij
  rcases ij with i | j
  · rw [OrthonormalBasis.coe_toBasis, OrthonormalBasis.prod_apply]
    simp only [Sum.elim_inl, Function.comp_apply, LinearMap.inl_apply,
      hermitianBlockDiagonal_apply]
    have hx :
        ((hermitianDilation T).comp (hermitianDilation T))
            (WithLp.toLp 2 (hG.eigenvectorBasis rfl i, 0)) =
          (hG.eigenvalues rfl i : ℂ) •
            WithLp.toLp 2 (hG.eigenvectorBasis rfl i, 0) := by
      rw [hermitianDilation_sq_apply]
      simp only [map_zero]
      change WithLp.toLp 2
        ((T.adjoint.comp T) (hG.eigenvectorBasis rfl i), 0) = _
      rw [hG.apply_eigenvectorBasis, ← WithLp.toLp_smul]
      apply WithLp.toLp_injective 2
      simp
    rw [hermitianFunctionalCalculus_apply_of_apply_eq_smul g _ _ _ _ hx,
      hermitianFunctionalCalculus_apply_eigenvectorBasis, map_zero]
    rw [← WithLp.toLp_smul]
    apply WithLp.toLp_injective 2
    simp
  · rw [OrthonormalBasis.coe_toBasis, OrthonormalBasis.prod_apply]
    simp only [Sum.elim_inr, Function.comp_apply, LinearMap.inr_apply,
      hermitianBlockDiagonal_apply]
    have hx :
        ((hermitianDilation T).comp (hermitianDilation T))
            (WithLp.toLp 2 (0, hK.eigenvectorBasis rfl j)) =
          (hK.eigenvalues rfl j : ℂ) •
            WithLp.toLp 2 (0, hK.eigenvectorBasis rfl j) := by
      rw [hermitianDilation_sq_apply]
      simp only [map_zero]
      change WithLp.toLp 2
        (0, (T.comp T.adjoint) (hK.eigenvectorBasis rfl j)) = _
      rw [hK.apply_eigenvectorBasis, ← WithLp.toLp_smul]
      apply WithLp.toLp_injective 2
      simp
    rw [hermitianFunctionalCalculus_apply_of_apply_eq_smul g _ _ _ _ hx,
      hermitianFunctionalCalculus_apply_eigenvectorBasis, map_zero]
    rw [← WithLp.toLp_smul]
    apply WithLp.toLp_injective 2
    simp

/-- Trace-level form of the Gram-block functional-calculus split. -/
theorem re_trace_hermitianDilation_sq_functionalCalculus
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : OrthonormalBasis ι ℂ E) (f : OrthonormalBasis κ ℂ F)
    (g : ℝ → ℝ) (T : E →ₗ[ℂ] F) :
    ((hermitianFunctionalCalculus g
      ((hermitianDilation T).comp (hermitianDilation T))
      (isSymmetric_comp_self (hermitianDilation T)
        (hermitianDilation_isSymmetric T))).trace ℂ
          (WithLp 2 (E × F))).re =
      ((hermitianFunctionalCalculus g (T.adjoint.comp T)
        T.isSymmetric_adjoint_comp_self).trace ℂ E).re +
      ((hermitianFunctionalCalculus g (T.comp T.adjoint)
        T.isSymmetric_self_comp_adjoint).trace ℂ F).re := by
  rw [hermitianDilation_sq_functionalCalculus,
    trace_hermitianBlockDiagonal e f, Complex.add_re]

/-- The characteristic roots of the two Gram operators agree after padding
the smaller side with zero roots. This is the rectangular `AB`/`BA`
characteristic-polynomial identity in basis-free operator form. -/
theorem gram_charpoly_roots_padded
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : OrthonormalBasis ι ℂ E) (f : OrthonormalBasis κ ℂ F)
    (T : E →ₗ[ℂ] F) :
    Fintype.card κ • ({0} : Multiset ℂ) +
        (T.adjoint.comp T).charpoly.roots =
      Fintype.card ι • ({0} : Multiset ℂ) +
        (T.comp T.adjoint).charpoly.roots := by
  classical
  open Polynomial in
    have hchar :
        X ^ Fintype.card κ * (T.adjoint.comp T).charpoly =
          X ^ Fintype.card ι * (T.comp T.adjoint).charpoly := by
      rw [← LinearMap.charpoly_toMatrix (T.adjoint.comp T) e.toBasis,
        ← LinearMap.charpoly_toMatrix (T.comp T.adjoint) f.toBasis,
        LinearMap.toMatrix_comp e.toBasis f.toBasis e.toBasis,
        LinearMap.toMatrix_comp f.toBasis e.toBasis f.toBasis]
      exact Matrix.charpoly_mul_comm'
        (LinearMap.toMatrix f.toBasis e.toBasis T.adjoint)
        (LinearMap.toMatrix e.toBasis f.toBasis T)
  have hroots := congrArg Polynomial.roots hchar
  rw [Polynomial.roots_mul (mul_ne_zero
        (pow_ne_zero _ Polynomial.X_ne_zero)
        (LinearMap.charpoly_monic _).ne_zero),
    Polynomial.roots_mul (mul_ne_zero
        (pow_ne_zero _ Polynomial.X_ne_zero)
        (LinearMap.charpoly_monic _).ne_zero),
    Polynomial.roots_X_pow, Polynomial.roots_X_pow] at hroots
  exact hroots

/-- Positive real powers have equal total spectral mass on the two Gram
operators, since the only discrepancy in their spectra consists of zeros. -/
theorem sum_gram_eigenvalues_rpow_eq
    {p : ℝ} (hp : 0 < p) (T : E →ₗ[ℂ] F) :
    (∑ i : Fin (Module.finrank ℂ E),
        T.isSymmetric_adjoint_comp_self.eigenvalues rfl i ^ (p / 2)) =
      ∑ j : Fin (Module.finrank ℂ F),
        T.isSymmetric_self_comp_adjoint.eigenvalues rfl j ^ (p / 2) := by
  let hG := T.isSymmetric_adjoint_comp_self
  let hK := T.isSymmetric_self_comp_adjoint
  have hroots := gram_charpoly_roots_padded (hG.eigenvectorBasis rfl)
    (hK.eigenvectorBasis rfl) T
  rw [hG.roots_charpoly_eq_eigenvalues rfl,
    hK.roots_charpoly_eq_eigenvalues rfl] at hroots
  have hsum := congrArg
    (fun s : Multiset ℂ ↦ (s.map (fun z ↦ z.re ^ (p / 2))).sum) hroots
  have hp2 : 0 < p / 2 := div_pos hp (by norm_num)
  rw [← List.sum_ofFn, ← List.sum_ofFn]
  simpa [Multiset.map_add, Multiset.map_nsmul, Multiset.sum_add,
    Multiset.sum_nsmul, hp2.ne', Function.comp_def] using hsum

/-- The singular-value power sum is the trace of the corresponding positive
functional calculus of the domain Gram operator. -/
theorem singularValuePowerSum_eq_re_trace_gramFunctionalCalculus
    {p : ℝ} (hp : 0 < p) (T : E →ₗ[ℂ] F) :
    singularValuePowerSum p T =
      ((hermitianFunctionalCalculus (fun y ↦ y ^ (p / 2))
        (T.adjoint.comp T) T.isSymmetric_adjoint_comp_self).trace ℂ E).re := by
  rw [re_trace_hermitianFunctionalCalculus]
  have hrank : Module.finrank ℂ T.range ≤ Module.finrank ℂ E :=
    T.finrank_range_le
  have hsum :
      (∑ i ∈ Finset.range (Module.finrank ℂ T.range),
          T.singularValues i ^ p) =
        ∑ i ∈ Finset.range (Module.finrank ℂ E),
          T.singularValues i ^ p := by
    apply Finset.sum_subset (Finset.range_mono hrank)
    intro i hi hi'
    have hirank : Module.finrank ℂ T.range ≤ i := by
      exact Nat.le_of_not_gt (fun hlt ↦ hi' (Finset.mem_range.mpr hlt))
    rw [T.singularValues_eq_zero_iff_le_finrank_range.mpr hirank]
    exact Real.zero_rpow hp.ne'
  unfold singularValuePowerSum
  rw [T.support_singularValues]
  calc
    (∑ i ∈ Finset.range (Module.finrank ℂ T.range),
        T.singularValues i ^ p) =
        ∑ i ∈ Finset.range (Module.finrank ℂ E),
          T.singularValues i ^ p := hsum
    _ = ∑ i : Fin (Module.finrank ℂ E), T.singularValues i ^ p :=
      (Fin.sum_univ_eq_sum_range
        (fun i : ℕ ↦ T.singularValues i ^ p) (Module.finrank ℂ E)).symm
    _ = ∑ i : Fin (Module.finrank ℂ E),
        T.isSymmetric_adjoint_comp_self.eigenvalues rfl i ^ (p / 2) := by
      apply Fintype.sum_congr
      intro i
      rw [T.singularValues_fin rfl]
      exact (Real.rpow_div_two_eq_sqrt p
        (T.isPositive_adjoint_comp_self.nonneg_eigenvalues rfl i)).symm

/-- Normalized power-potential trace of the domain Gram block. -/
theorem re_trace_gramPowerPotential_eq_singularValuePowerSum_div
    {p : ℝ} (hp : 0 < p) (T : E →ₗ[ℂ] F) :
    ((hermitianFunctionalCalculus (fun y ↦ y ^ (p / 2) / p)
      (T.adjoint.comp T) T.isSymmetric_adjoint_comp_self).trace ℂ E).re =
      singularValuePowerSum p T / p := by
  rw [singularValuePowerSum_eq_re_trace_gramFunctionalCalculus hp,
    re_trace_hermitianFunctionalCalculus,
    re_trace_hermitianFunctionalCalculus, Finset.sum_div]

/-- A rectangular map and its adjoint have the same positive singular-value
power sum. -/
theorem singularValuePowerSum_adjoint
    {p : ℝ} (hp : 0 < p) (T : E →ₗ[ℂ] F) :
    singularValuePowerSum p T.adjoint = singularValuePowerSum p T := by
  rw [singularValuePowerSum_eq_re_trace_gramFunctionalCalculus hp T.adjoint,
    singularValuePowerSum_eq_re_trace_gramFunctionalCalculus hp T,
    re_trace_hermitianFunctionalCalculus,
    re_trace_hermitianFunctionalCalculus]
  simp only [LinearMap.adjoint_adjoint]
  exact (sum_gram_eigenvalues_rpow_eq hp T).symm

/-- Exact general-p trace formula for the dilated power potential, before
identifying the singular-value sums of a map and its adjoint. -/
theorem re_trace_dilated_powerPotential_eq_self_add_adjoint
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : OrthonormalBasis ι ℂ E) (f : OrthonormalBasis κ ℂ F)
    {p : ℝ} (hp : 0 < p) (T : E →ₗ[ℂ] F) :
    ((hermitianFunctionalCalculus (powerPotential p) (hermitianDilation T)
      (hermitianDilation_isSymmetric T)).trace ℂ
        (WithLp 2 (E × F))).re =
      (singularValuePowerSum p T + singularValuePowerSum p T.adjoint) / p := by
  rw [hermitianFunctionalCalculus_powerPotential_comp_self,
    re_trace_hermitianDilation_sq_functionalCalculus e f]
  rw [re_trace_gramPowerPotential_eq_singularValuePowerSum_div hp T]
  have hAdj :=
    re_trace_gramPowerPotential_eq_singularValuePowerSum_div hp T.adjoint
  simp only [LinearMap.adjoint_adjoint] at hAdj
  rw [hAdj]
  ring

/-- The power-potential trace of the Hermitian dilation is exactly twice the
rectangular singular-value power sum, with the potential's normalization. -/
theorem re_trace_dilated_powerPotential_eq_two_mul_singularValuePowerSum
    {p : ℝ} (hp : 0 < p) (T : E →ₗ[ℂ] F) :
    ((hermitianFunctionalCalculus (powerPotential p) (hermitianDilation T)
      (hermitianDilation_isSymmetric T)).trace ℂ
        (WithLp 2 (E × F))).re =
      2 * singularValuePowerSum p T / p := by
  rw [re_trace_dilated_powerPotential_eq_self_add_adjoint
    (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl)
    (T.isSymmetric_self_comp_adjoint.eigenvectorBasis rfl) hp T,
    singularValuePowerSum_adjoint hp T]
  ring

/-- Positive real scaling raises the rectangular singular-value power sum
to the same exponent. -/
theorem singularValuePowerSum_real_smul
    {p c : ℝ} (hp : 0 < p) (hc : 0 < c) (T : E →ₗ[ℂ] F) :
    singularValuePowerSum p ((c : ℂ) • T) =
      c ^ p * singularValuePowerSum p T := by
  have hct := re_trace_dilated_powerPotential_eq_two_mul_singularValuePowerSum
    hp ((c : ℂ) • T)
  have ht := re_trace_dilated_powerPotential_eq_two_mul_singularValuePowerSum hp T
  have hct' :
      ((hermitianFunctionalCalculus (powerPotential p)
        ((c : ℂ) • hermitianDilation T)
        ((hermitianDilation_isSymmetric T).smul (by simp))).trace ℂ
          (WithLp 2 (E × F))).re =
        2 * singularValuePowerSum p ((c : ℂ) • T) / p := by
    simpa only [hermitianDilation_real_smul] using hct
  have hs := re_trace_powerPotential_real_smul (p := p) hc
    (hermitianDilation T) (hermitianDilation_isSymmetric T)
  rw [hs, ht] at hct'
  field_simp [hp.ne'] at hct'
  linarith

/-- Positive real homogeneity of the finite-dimensional Schatten quantity. -/
theorem schattenPNorm_real_smul
    {p c : ℝ} (hp : 0 < p) (hc : 0 < c) (T : E →ₗ[ℂ] F) :
    schattenPNorm p ((c : ℂ) • T) = c * schattenPNorm p T := by
  unfold schattenPNorm
  rw [singularValuePowerSum_real_smul hp hc]
  rw [Real.mul_rpow (Real.rpow_nonneg hc.le p)
    (singularValuePowerSum_nonneg p T)]
  rw [← Real.rpow_mul hc.le]
  rw [show p * (1 / p) = 1 by field_simp [hp.ne'], Real.rpow_one]

/-- Odd functional calculus of the dilation still anticommutes with the
product grading. -/
theorem hermitianFunctionalCalculus_odd_comp_signature
    (g : ℝ → ℝ) (hodd : ∀ x, g (-x) = -g x) (T : E →ₗ[ℂ] F) :
    (hermitianFunctionalCalculus g (hermitianDilation T)
      (hermitianDilation_isSymmetric T)).comp hermitianSignature =
      -(hermitianSignature.comp
        (hermitianFunctionalCalculus g (hermitianDilation T)
          (hermitianDilation_isSymmetric T))) := by
  let hD := hermitianDilation_isSymmetric T
  apply (hD.eigenvectorBasis rfl).toBasis.ext
  intro i
  rw [OrthonormalBasis.coe_toBasis]
  have hJi :
      hermitianDilation T (hermitianSignature (hD.eigenvectorBasis rfl i)) =
        ((-hD.eigenvalues rfl i : ℝ) : ℂ) •
          hermitianSignature (hD.eigenvectorBasis rfl i) := by
    calc
      hermitianDilation T (hermitianSignature (hD.eigenvectorBasis rfl i)) =
          ((hermitianDilation T).comp hermitianSignature)
            (hD.eigenvectorBasis rfl i) := rfl
      _ = (-(hermitianSignature.comp (hermitianDilation T)))
            (hD.eigenvectorBasis rfl i) := by
          rw [hermitianDilation_comp_signature]
      _ = ((-hD.eigenvalues rfl i : ℝ) : ℂ) •
          hermitianSignature (hD.eigenvectorBasis rfl i) := by
        rw [LinearMap.neg_apply, LinearMap.comp_apply,
          hD.apply_eigenvectorBasis, map_smul]
        simp
  rw [LinearMap.comp_apply,
    hermitianFunctionalCalculus_apply_of_apply_eq_smul g _ _ _
      (-hD.eigenvalues rfl i) hJi,
    LinearMap.neg_apply, LinearMap.comp_apply,
    hermitianFunctionalCalculus_apply_eigenvectorBasis, map_smul]
  rw [hodd]
  simp

/-- Every even spectral function of the Hermitian dilation factors through
its block-diagonal square. -/
theorem hermitianDilation_evenFunctionalCalculus
    (g : ℝ → ℝ) (T : E →ₗ[ℂ] F) :
    hermitianFunctionalCalculus (fun x ↦ g (x ^ 2)) (hermitianDilation T)
        (hermitianDilation_isSymmetric T) =
      hermitianFunctionalCalculus g
        ((hermitianDilation T).comp (hermitianDilation T))
        (isSymmetric_comp_self (hermitianDilation T)
          (hermitianDilation_isSymmetric T)) :=
  hermitianFunctionalCalculus_comp_self g (hermitianDilation T)
    (hermitianDilation_isSymmetric T)

/-- In particular, the dilated power-potential map is a functional calculus
of the block-diagonal Gram square. -/
theorem hermitianDilation_powerPotential_comp_self
    (p : ℝ) (T : E →ₗ[ℂ] F) :
    hermitianFunctionalCalculus (powerPotential p) (hermitianDilation T)
        (hermitianDilation_isSymmetric T) =
      hermitianFunctionalCalculus (fun y ↦ y ^ (p / 2) / p)
        ((hermitianDilation T).comp (hermitianDilation T))
        (isSymmetric_comp_self (hermitianDilation T)
          (hermitianDilation_isSymmetric T)) :=
  hermitianFunctionalCalculus_powerPotential_comp_self p
    (hermitianDilation T) (hermitianDilation_isSymmetric T)

/-- The trace of the squared dilation is twice the trace of the domain Gram
operator. This is the Hilbert-point instance of the two-copy singular-value
normalization. -/
theorem trace_hermitianDilation_sq
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : OrthonormalBasis ι ℂ E) (f : OrthonormalBasis κ ℂ F)
    (T : E →ₗ[ℂ] F) :
    (((hermitianDilation T).comp (hermitianDilation T)).trace ℂ
      (WithLp 2 (E × F))) =
        2 * ((T.adjoint.comp T).trace ℂ E) := by
  rw [LinearMap.trace_eq_sum_inner _ (e.prod f), Fintype.sum_sum_type]
  simp only [OrthonormalBasis.prod_apply, Sum.elim_inl, Sum.elim_inr,
    Function.comp_apply, LinearMap.inl_apply, LinearMap.inr_apply,
    hermitianDilation_sq_apply, WithLp.prod_inner_apply,
    inner_zero_left, add_zero, zero_add]
  change (∑ i, ⟪e i, (T.adjoint.comp T) (e i)⟫_ℂ) +
      (∑ j, ⟪f j, (T.comp T.adjoint) (f j)⟫_ℂ) =
    2 * ((T.adjoint.comp T).trace ℂ E)
  rw [← LinearMap.trace_eq_sum_inner (T.adjoint.comp T) e]
  rw [← LinearMap.trace_eq_sum_inner (T.comp T.adjoint) f]
  rw [LinearMap.trace_comp_comm' T T.adjoint]
  ring

/-- The squared dilation has exactly twice the Schatten-2 power sum. -/
theorem re_trace_hermitianDilation_sq_eq_two_mul_singularValuePowerSum
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : OrthonormalBasis ι ℂ E) (f : OrthonormalBasis κ ℂ F)
    (T : E →ₗ[ℂ] F) :
    ((((hermitianDilation T).comp (hermitianDilation T)).trace ℂ
      (WithLp 2 (E × F))).re) = 2 * singularValuePowerSum 2 T := by
  rw [trace_hermitianDilation_sq e f T, Complex.mul_re]
  norm_num
  rw [singularValuePowerSum_two_eq_re_trace]
  exact RCLike.re_to_complex

/-- Hermitian Bregman trace quantity after rectangular dilation. -/
noncomputable def dilatedBregmanTrace
    (p : ℝ) (S T : E →ₗ[ℂ] F) : ℝ :=
  hermitianBregmanTrace p (hermitianDilation S) (hermitianDilation T)
    (hermitianDilation_isSymmetric S) (hermitianDilation_isSymmetric T)

/-- The real trace pairing between a rectangular map and the dilated power
gradient of a second map, normalized by the two dilation copies. -/
noncomputable def dilatedGradientPairing
    (p : ℝ) (S T : E →ₗ[ℂ] F) : ℝ :=
  (((hermitianDilation S).comp
    (hermitianFunctionalCalculus (powerGradient p) (hermitianDilation T)
      (hermitianDilation_isSymmetric T))).trace ℂ
        (WithLp 2 (E × F))).re / 2

/-- The dilated gradient pairing is additive in its first argument. -/
theorem dilatedGradientPairing_add
    (p : ℝ) (R S T : E →ₗ[ℂ] F) :
    dilatedGradientPairing p (R + S) T =
      dilatedGradientPairing p R T + dilatedGradientPairing p S T := by
  unfold dilatedGradientPairing
  rw [hermitianDilation_add, LinearMap.add_comp, map_add, Complex.add_re]
  ring

/-- The dilated gradient pairing is real-homogeneous in its first argument. -/
theorem dilatedGradientPairing_real_smul
    (p r : ℝ) (S T : E →ₗ[ℂ] F) :
    dilatedGradientPairing p ((r : ℂ) • S) T =
      r * dilatedGradientPairing p S T := by
  unfold dilatedGradientPairing
  rw [hermitianDilation_real_smul, LinearMap.smul_comp, map_smul]
  rw [smul_eq_mul, Complex.re_ofReal_mul]
  ring

@[simp]
theorem dilatedGradientPairing_zero (p : ℝ) (T : E →ₗ[ℂ] F) :
    dilatedGradientPairing p 0 T = 0 := by
  unfold dilatedGradientPairing
  simp

/-- Finite real linearity of the dilated gradient pairing. -/
theorem dilatedGradientPairing_sum
    {ι : Type*} [Fintype ι] (p : ℝ) (a : ι → ℝ)
    (u : ι → E →ₗ[ℂ] F) (T : E →ₗ[ℂ] F) :
    dilatedGradientPairing p (∑ i, (a i : ℂ) • u i) T =
      ∑ i, a i * dilatedGradientPairing p (u i) T := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        dilatedGradientPairing_add, dilatedGradientPairing_real_smul, ih]

/-- Dilated Bregman divergence is nonnegative for `p > 1`. -/
theorem dilatedBregmanTrace_nonneg
    {p : ℝ} (hp : 1 < p) (S T : E →ₗ[ℂ] F) :
    0 ≤ dilatedBregmanTrace p S T := by
  unfold dilatedBregmanTrace hermitianBregmanTrace
  exact spectralBregmanTrace_nonneg hp _ _ _ _

/-- Dilated Bregman divergence vanishes on the diagonal. -/
@[simp]
theorem dilatedBregmanTrace_self (p : ℝ) (S : E →ₗ[ℂ] F) :
    dilatedBregmanTrace p S S = 0 := by
  unfold dilatedBregmanTrace
  rw [hermitianBregmanTrace_eq_functionalCalculus]
  have hcross : hermitianFunctionalCalculus
      (fun x => powerGradient p x * x) (hermitianDilation S)
        (hermitianDilation_isSymmetric S) =
      (hermitianDilation S).comp
        (hermitianFunctionalCalculus (powerGradient p) (hermitianDilation S)
          (hermitianDilation_isSymmetric S)) := by
    rw [show (fun x => powerGradient p x * x) =
        (fun x => x * powerGradient p x) by funext x; ring,
      hermitianFunctionalCalculus_mul]
    rw [show (fun x : ℝ => x) = id by rfl,
      hermitianFunctionalCalculus_id]
  rw [hcross]
  ring

/-- On the Schatten-`p` power sphere, the normalized dilated Bregman
divergence is one minus the dilated gradient pairing. -/
theorem dilatedBregmanTrace_div_two_eq_one_sub_pairing
    {p : ℝ} (hp : 0 < p) (S T : E →ₗ[ℂ] F)
    (hS : singularValuePowerSum p S = 1)
    (hT : singularValuePowerSum p T = 1) :
    dilatedBregmanTrace p S T / 2 =
      1 - dilatedGradientPairing p S T := by
  unfold dilatedBregmanTrace dilatedGradientPairing
  rw [hermitianBregmanTrace_eq_functionalCalculus]
  rw [re_trace_dilated_powerPotential_eq_two_mul_singularValuePowerSum hp S,
    re_trace_dilated_powerPotential_eq_two_mul_singularValuePowerSum hp T,
    re_trace_powerGradient_mul_self hp
      (hermitianDilation T) (hermitianDilation_isSymmetric T),
    re_trace_dilated_powerPotential_eq_two_mul_singularValuePowerSum hp T,
    hS, hT]
  field_simp [hp.ne']
  ring

/-- Hermitian Mazur Hilbert--Schmidt square after rectangular dilation. -/
noncomputable def dilatedMazurDistanceSq
    (p : ℝ) (S T : E →ₗ[ℂ] F) : ℝ :=
  hermitianMazurDistanceSq p (hermitianDilation S) (hermitianDilation T)
    (hermitianDilation_isSymmetric S) (hermitianDilation_isSymmetric T)

/-- The Hermitian Mazur map of a rectangular operator's dilation. -/
noncomputable def dilatedMazurMap (p : ℝ) (T : E →ₗ[ℂ] F) :
    WithLp 2 (E × F) →ₗ[ℂ] WithLp 2 (E × F) :=
  hermitianMazurMap p (hermitianDilation T) (hermitianDilation_isSymmetric T)

/-- Extract the lower-left rectangular block of an endomorphism of the
Hilbert `L²` product. -/
private noncomputable def lowerLeftBlock
    (A : WithLp 2 (E × F) →ₗ[ℂ] WithLp 2 (E × F)) : E →ₗ[ℂ] F :=
  (LinearMap.snd ℂ E F).comp
    ((WithLp.linearEquiv 2 ℂ (E × F)).toLinearMap.comp
      (A.comp
        ((WithLp.linearEquiv 2 ℂ (E × F)).symm.toLinearMap.comp
          (LinearMap.inl ℂ E F))))

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] in
@[simp]
private theorem lowerLeftBlock_apply
    (A : WithLp 2 (E × F) →ₗ[ℂ] WithLp 2 (E × F)) (x : E) :
    lowerLeftBlock A x = (WithLp.ofLp (A (WithLp.toLp 2 (x, 0)))).2 := by
  rfl

/-- Extract the upper-right rectangular block of an endomorphism of the
Hilbert `L²` product. -/
private noncomputable def upperRightBlock
    (A : WithLp 2 (E × F) →ₗ[ℂ] WithLp 2 (E × F)) : F →ₗ[ℂ] E :=
  (LinearMap.fst ℂ E F).comp
    ((WithLp.linearEquiv 2 ℂ (E × F)).toLinearMap.comp
      (A.comp
        ((WithLp.linearEquiv 2 ℂ (E × F)).symm.toLinearMap.comp
          (LinearMap.inr ℂ E F))))

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] in
@[simp]
private theorem upperRightBlock_apply
    (A : WithLp 2 (E × F) →ₗ[ℂ] WithLp 2 (E × F)) (y : F) :
    upperRightBlock A y =
      (WithLp.ofLp (A (WithLp.toLp 2 (0, y)))).1 := by
  rfl

/-- The two off-diagonal blocks of a symmetric product endomorphism are
adjoints of one another. -/
private theorem upperRightBlock_eq_adjoint_lowerLeftBlock
    (A : WithLp 2 (E × F) →ₗ[ℂ] WithLp 2 (E × F))
    (hA : A.IsSymmetric) :
    upperRightBlock A = (lowerLeftBlock A).adjoint := by
  rw [LinearMap.eq_adjoint_iff]
  intro y x
  have h := hA (WithLp.toLp 2 (0, y)) (WithLp.toLp 2 (x, 0))
  rw [← WithLp.toLp_ofLp 2 (A (WithLp.toLp 2 (x, 0))),
    ← WithLp.toLp_ofLp 2 (A (WithLp.toLp 2 (0, y)))] at h
  simpa only [upperRightBlock_apply, lowerLeftBlock_apply,
    WithLp.prod_inner_apply, inner_zero_left, inner_zero_right,
    zero_add, add_zero] using h

private theorem eq_zero_of_eq_neg_complex_module
    {G : Type*} [AddCommGroup G] [Module ℂ G]
    {x : G} (h : x = -x) : x = 0 := by
  have hz : x + x = 0 := eq_neg_iff_add_eq_zero.mp h
  have hs := congrArg (fun z : G ↦ (1 / 2 : ℂ) • z) hz
  simpa [smul_add, ← add_smul] using hs

/-- A symmetric product endomorphism which anticommutes with the grading is
the Hermitian dilation of its lower-left block. -/
private theorem eq_hermitianDilation_lowerLeftBlock_of_anticommute
    (A : WithLp 2 (E × F) →ₗ[ℂ] WithLp 2 (E × F))
    (hA : A.IsSymmetric)
    (hanti : A.comp hermitianSignature = -(hermitianSignature.comp A)) :
    A = hermitianDilation (lowerLeftBlock A) := by
  have hupper : upperRightBlock A = (lowerLeftBlock A).adjoint :=
    upperRightBlock_eq_adjoint_lowerLeftBlock A hA
  have hAx : ∀ x : E,
      A (WithLp.toLp 2 (x, 0)) =
        WithLp.toLp 2 (0, lowerLeftBlock A x) := by
    intro x
    have hu := LinearMap.congr_fun hanti (WithLp.toLp 2 (x, 0))
    simp only [LinearMap.comp_apply, hermitianSignature_apply,
      neg_zero, LinearMap.neg_apply] at hu
    rw [← WithLp.toLp_ofLp 2 (A (WithLp.toLp 2 (x, 0))),
      hermitianSignature_apply, ← WithLp.toLp_neg] at hu
    have hp := congrArg WithLp.ofLp hu
    simp only [Prod.neg_mk, neg_neg] at hp
    have hfirst : (WithLp.ofLp (A (WithLp.toLp 2 (x, 0)))).1 =
        -(WithLp.ofLp (A (WithLp.toLp 2 (x, 0)))).1 :=
      congrArg Prod.fst hp
    rw [← WithLp.toLp_ofLp 2 (A (WithLp.toLp 2 (x, 0)))]
    apply congrArg (WithLp.toLp 2)
    apply Prod.ext
    · simpa using eq_zero_of_eq_neg_complex_module hfirst
    · rfl
  have hAy : ∀ y : F,
      A (WithLp.toLp 2 (0, y)) =
        WithLp.toLp 2 (upperRightBlock A y, 0) := by
    intro y
    have hu := LinearMap.congr_fun hanti (WithLp.toLp 2 (0, y))
    simp only [LinearMap.comp_apply, hermitianSignature_apply,
      LinearMap.neg_apply] at hu
    rw [show WithLp.toLp 2 ((0 : E), -y) =
          -WithLp.toLp 2 ((0 : E), y) by
        rw [← WithLp.toLp_neg]
        congr 1
        simp,
      map_neg, ← WithLp.toLp_ofLp 2 (A (WithLp.toLp 2 (0, y))),
      hermitianSignature_apply, ← WithLp.toLp_neg] at hu
    have hp := congrArg WithLp.ofLp hu
    simp only [WithLp.ofLp_neg, Prod.neg_mk, neg_neg] at hp
    have hsecond : -(WithLp.ofLp (A (WithLp.toLp 2 (0, y)))).2 =
        (WithLp.ofLp (A (WithLp.toLp 2 (0, y)))).2 :=
      congrArg Prod.snd hp
    rw [← WithLp.toLp_ofLp 2 (A (WithLp.toLp 2 (0, y)))]
    apply congrArg (WithLp.toLp 2)
    apply Prod.ext
    · rfl
    · exact eq_zero_of_eq_neg_complex_module hsecond.symm
  apply LinearMap.ext
  intro z
  rw [← WithLp.toLp_ofLp 2 z]
  rcases WithLp.ofLp z with ⟨x, y⟩
  rw [show WithLp.toLp 2 (x, y) =
      WithLp.toLp 2 (x, 0) + WithLp.toLp 2 (0, y) by
        rw [← WithLp.toLp_add]
        apply WithLp.toLp_injective 2
        simp,
    map_add, hAx, hAy, hermitianDilation_apply, hupper]
  rw [← WithLp.toLp_add]
  simp

/-- The rectangular Mazur map obtained as the lower-left block of the odd
spectral map of the Hermitian dilation. -/
noncomputable def rectangularMazurMap (p : ℝ) (T : E →ₗ[ℂ] F) : E →ₗ[ℂ] F :=
  lowerLeftBlock (dilatedMazurMap p T)

@[simp]
theorem dilatedMazurMap_two (T : E →ₗ[ℂ] F) :
    dilatedMazurMap 2 T = hermitianDilation T := by
  unfold dilatedMazurMap hermitianMazurMap
  rw [show scalarMazur 2 = id by funext x; exact scalarMazur_two x]
  exact hermitianFunctionalCalculus_id (hermitianDilation T)
    (hermitianDilation_isSymmetric T)

@[simp]
theorem rectangularMazurMap_two (T : E →ₗ[ℂ] F) :
    rectangularMazurMap 2 T = T := by
  apply LinearMap.ext
  intro x
  simp [rectangularMazurMap]

@[simp]
theorem dilatedMazurMap_zero (p : ℝ) :
    dilatedMazurMap p (0 : E →ₗ[ℂ] F) = 0 := by
  unfold dilatedMazurMap hermitianMazurMap
  simpa only [hermitianDilation_zero] using
    (hermitianFunctionalCalculus_zero (E := WithLp 2 (E × F))
      (scalarMazur p) (scalarMazur_zero p))

@[simp]
theorem rectangularMazurMap_zero (p : ℝ) :
    rectangularMazurMap p (0 : E →ₗ[ℂ] F) = 0 := by
  apply LinearMap.ext
  intro x
  simp [rectangularMazurMap]

/-- The exact off-diagonal form needed to identify the Hermitian spectral
Mazur map with a rectangular one. The lower-left block is pinned by
`rectangularMazurMap`; the content is that no diagonal blocks remain and the
upper-right block is its adjoint. -/
def HasRectangularMazurDilation (p : ℝ) (T : E →ₗ[ℂ] F) : Prop :=
  dilatedMazurMap p T = hermitianDilation (rectangularMazurMap p T)

/-- The odd scalar Mazur functional calculus of a Hermitian dilation is the
Hermitian dilation of its extracted rectangular block. -/
theorem hasRectangularMazurDilation (p : ℝ) (T : E →ₗ[ℂ] F) :
    HasRectangularMazurDilation p T := by
  unfold HasRectangularMazurDilation rectangularMazurMap
  apply eq_hermitianDilation_lowerLeftBlock_of_anticommute
  · exact hermitianMazurMap_isSymmetric p (hermitianDilation T)
      (hermitianDilation_isSymmetric T)
  · exact hermitianFunctionalCalculus_odd_comp_signature
      (scalarMazur p) (scalarMazur_neg p) T

/-- Rectangular Mazur maps with exponents `p` and `4 / p` are inverse. -/
theorem rectangularMazurMap_four_div_comp
    {p : ℝ} (hp : 0 < p) (T : E →ₗ[ℂ] F) :
    rectangularMazurMap (4 / p) (rectangularMazurMap p T) = T := by
  apply hermitianDilation_injective
  rw [← hasRectangularMazurDilation (4 / p) (rectangularMazurMap p T)]
  unfold dilatedMazurMap
  have hpD : hermitianDilation (rectangularMazurMap p T) =
      dilatedMazurMap p T := (hasRectangularMazurDilation p T).symm
  simp only [hpD]
  unfold dilatedMazurMap
  exact hermitianMazurMap_four_div_comp hp (hermitianDilation T)
    (hermitianDilation_isSymmetric T)

/-- For every positive exponent, the rectangular Mazur map is a bijection. -/
theorem rectangularMazurMap_bijective {p : ℝ} (hp : 0 < p) :
    Function.Bijective
      (rectangularMazurMap p : (E →ₗ[ℂ] F) → (E →ₗ[ℂ] F)) := by
  let inv : (E →ₗ[ℂ] F) → (E →ₗ[ℂ] F) :=
    fun T ↦ rectangularMazurMap (E := E) (F := F) (4 / p) T
  let mazur : (E →ₗ[ℂ] F) → (E →ₗ[ℂ] F) :=
    fun T ↦ rectangularMazurMap (E := E) (F := F) p T
  have hleft : Function.LeftInverse inv mazur :=
    fun T ↦ rectangularMazurMap_four_div_comp hp T
  have hright : Function.RightInverse inv mazur := by
    intro T
    have h := rectangularMazurMap_four_div_comp
      (p := 4 / p) (div_pos (by norm_num) hp) T
    simpa only [show 4 / (4 / p) = p by field_simp] using h
  exact ⟨hleft.injective, hright.surjective⟩

@[simp]
theorem hasRectangularMazurDilation_two (T : E →ₗ[ℂ] F) :
    HasRectangularMazurDilation 2 T := by
  exact hasRectangularMazurDilation 2 T

theorem dilatedMazurMap_isSymmetric (p : ℝ) (T : E →ₗ[ℂ] F) :
    (dilatedMazurMap p T).IsSymmetric :=
  hermitianMazurMap_isSymmetric p (hermitianDilation T)
    (hermitianDilation_isSymmetric T)

/-- The dilated Mazur square is exactly the real trace-square distance
between the corresponding dilated Mazur maps. -/
theorem dilatedMazurDistanceSq_eq_re_trace_sq_sub
    (p : ℝ) (S T : E →ₗ[ℂ] F) :
    dilatedMazurDistanceSq p S T =
      ((((dilatedMazurMap p S - dilatedMazurMap p T).comp
        (dilatedMazurMap p S - dilatedMazurMap p T)).trace ℂ
          (WithLp 2 (E × F))).re) :=
  hermitianMazurDistanceSq_eq_re_trace_sq_sub p
    (hermitianDilation S) (hermitianDilation T)
    (hermitianDilation_isSymmetric S) (hermitianDilation_isSymmetric T)

/-- Explicit Hilbert--Schmidt coordinate formula for the dilated Mazur
distance in a product orthonormal basis. -/
theorem dilatedMazurDistanceSq_eq_sum_norm_sq
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : OrthonormalBasis ι ℂ E) (f : OrthonormalBasis κ ℂ F)
    (p : ℝ) (S T : E →ₗ[ℂ] F) :
    dilatedMazurDistanceSq p S T =
      ∑ i, ‖(dilatedMazurMap p S - dilatedMazurMap p T) ((e.prod f) i)‖ ^ 2 :=
  hermitianMazurDistanceSq_eq_sum_norm_sq (e.prod f) p
    (hermitianDilation S) (hermitianDilation T)
    (hermitianDilation_isSymmetric S) (hermitianDilation_isSymmetric T)

/-- Once the odd functional calculus is known to retain off-diagonal form,
the dilated Mazur distance has exactly the expected two-copy rectangular
Hilbert--Schmidt normalization. -/
theorem dilatedMazurDistanceSq_eq_two_mul_singularValuePowerSum
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : OrthonormalBasis ι ℂ E) (f : OrthonormalBasis κ ℂ F)
    (p : ℝ) (S T : E →ₗ[ℂ] F) :
    dilatedMazurDistanceSq p S T =
      2 * singularValuePowerSum 2
        (rectangularMazurMap p S - rectangularMazurMap p T) := by
  rw [dilatedMazurDistanceSq_eq_re_trace_sq_sub,
    hasRectangularMazurDilation p S, hasRectangularMazurDilation p T,
    ← hermitianDilation_sub]
  exact re_trace_hermitianDilation_sq_eq_two_mul_singularValuePowerSum e f _

/-- Basis-free form of the two-copy rectangular Hilbert--Schmidt formula. -/
theorem dilatedMazurDistanceSq_eq_two_mul_singularValuePowerSum'
    (p : ℝ) (S T : E →ₗ[ℂ] F) :
    dilatedMazurDistanceSq p S T =
      2 * singularValuePowerSum 2
        (rectangularMazurMap p S - rectangularMazurMap p T) :=
  dilatedMazurDistanceSq_eq_two_mul_singularValuePowerSum
    (stdOrthonormalBasis ℂ E) (stdOrthonormalBasis ℂ F) p S T

/-- Against zero, the dilated Mazur square is exactly twice the rectangular
Schatten-`p` power sum. -/
theorem dilatedMazurDistanceSq_zero_eq_two_mul_singularValuePowerSum
    {p : ℝ} (hp : 0 < p) (T : E →ₗ[ℂ] F) :
    dilatedMazurDistanceSq p T 0 = 2 * singularValuePowerSum p T := by
  unfold dilatedMazurDistanceSq
  calc
    hermitianMazurDistanceSq p (hermitianDilation T) (hermitianDilation 0)
        (hermitianDilation_isSymmetric T) (hermitianDilation_isSymmetric 0) =
      p * ((hermitianFunctionalCalculus (powerPotential p)
        (hermitianDilation T) (hermitianDilation_isSymmetric T)).trace ℂ
          (WithLp 2 (E × F))).re := by
      simpa only [hermitianDilation_zero] using
        hermitianMazurDistanceSq_zero_eq_powerPotentialTrace hp
          (hermitianDilation T) (hermitianDilation_isSymmetric T)
    _ = 2 * singularValuePowerSum p T := by
      rw [re_trace_dilated_powerPotential_eq_two_mul_singularValuePowerSum hp T]
      field_simp

/-- The rectangular Mazur map sends the Schatten-`p` power sum exactly to
the Hilbert--Schmidt power sum. -/
theorem singularValuePowerSum_two_rectangularMazurMap
    {p : ℝ} (hp : 0 < p) (T : E →ₗ[ℂ] F) :
    singularValuePowerSum 2 (rectangularMazurMap p T) =
      singularValuePowerSum p T := by
  have htwo :=
    dilatedMazurDistanceSq_eq_two_mul_singularValuePowerSum
      (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl)
      (T.isSymmetric_self_comp_adjoint.eigenvectorBasis rfl) p T 0
  rw [rectangularMazurMap_zero, sub_zero,
    dilatedMazurDistanceSq_zero_eq_two_mul_singularValuePowerSum hp] at htwo
  linarith

/-- For every positive `p`, the rectangular Mazur map is an exact
equivalence from the Schatten-`p` power sphere to the Hilbert--Schmidt
power sphere.  Its inverse is the Mazur map with exponent `4 / p`. -/
noncomputable def rectangularMazurPowerSphereEquiv
    {p : ℝ} (hp : 0 < p) :
    schattenPowerSphere (𝕜 := ℂ) (E := E) (F := F) p ≃
      schattenPowerSphere (𝕜 := ℂ) (E := E) (F := F) 2 where
  toFun T := ⟨rectangularMazurMap p T.1, by
    exact (singularValuePowerSum_two_rectangularMazurMap hp T.1).trans T.property⟩
  invFun S := ⟨rectangularMazurMap (4 / p) S.1, by
    have hnorm := singularValuePowerSum_two_rectangularMazurMap hp
      (rectangularMazurMap (4 / p) S.1)
    have hcomp := rectangularMazurMap_four_div_comp
      (p := 4 / p) (div_pos (by norm_num) hp) S.1
    have hquot : 4 / (4 / p) = p := by field_simp
    simp only [hquot] at hcomp
    rw [hcomp] at hnorm
    exact hnorm.symm.trans S.property⟩
  left_inv T := Subtype.ext (rectangularMazurMap_four_div_comp hp T.1)
  right_inv S := by
    apply Subtype.ext
    have h := rectangularMazurMap_four_div_comp
      (p := 4 / p) (div_pos (by norm_num) hp) S.1
    simpa only [show 4 / (4 / p) = p by field_simp] using h

/-- The exact Hilbert-exponent normalization survives rectangular dilation. -/
theorem dilatedBregmanTrace_two_eq (S T : E →ₗ[ℂ] F) :
    dilatedBregmanTrace 2 S T = dilatedMazurDistanceSq 2 S T / 2 :=
  hermitianBregmanTrace_two_eq (hermitianDilation S) (hermitianDilation T)
    (hermitianDilation_isSymmetric S) (hermitianDilation_isSymmetric T)

/-- One pair of positive finite constants compares the dilated rectangular
quantities in every finite pair of complex Hilbert spaces. -/
theorem exists_uniform_dilatedBregmanTrace_two_sided
    {p : ℝ} (hp : 1 < p) :
    ∃ m M : ℝ, 0 < m ∧ m ≤ M ∧
      ∀ {G H : Type*}
        [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G]
        [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
        (S T : G →ₗ[ℂ] H),
        m * dilatedMazurDistanceSq p S T ≤ dilatedBregmanTrace p S T ∧
          dilatedBregmanTrace p S T ≤ M * dilatedMazurDistanceSq p S T := by
  obtain ⟨m, M, hm, hmM, hbound⟩ :=
    exists_uniform_hermitianBregmanTrace_two_sided hp
  refine ⟨m, M, hm, hmM, ?_⟩
  intro G H _ _ _ _ _ _ S T
  simpa only [dilatedBregmanTrace, dilatedMazurDistanceSq] using
    hbound (hermitianDilation S) (hermitianDilation T)
      (hermitianDilation_isSymmetric S) (hermitianDilation_isSymmetric T)

end HlawkaSchatten
