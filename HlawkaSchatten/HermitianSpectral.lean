/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import HlawkaSchatten.SpectralLift
import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Finite Hermitian spectral trace expansions

This file connects the overlap-weighted scalar comparison to traces of
finite-dimensional symmetric complex-linear maps.
-/

namespace HlawkaSchatten

open scoped InnerProductSpace
open RCLike
open ComplexConjugate

variable {ι κ E : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem sum_left_mul_orthonormalBasisOverlap
    (e : OrthonormalBasis ι ℂ E) (f : OrthonormalBasis κ ℂ E)
    (c : ι → ℝ) :
    ∑ ij : ι × κ, c ij.1 * orthonormalBasisOverlap e f ij = ∑ i, c i := by
  rw [Fintype.sum_prod_type]
  apply Fintype.sum_congr
  intro i
  change (∑ j, c i * orthonormalBasisOverlap e f (i, j)) = c i
  rw [← Finset.mul_sum, sum_orthonormalBasisOverlap_right, mul_one]

theorem sum_right_mul_orthonormalBasisOverlap
    (e : OrthonormalBasis ι ℂ E) (f : OrthonormalBasis κ ℂ E)
    (c : κ → ℝ) :
    ∑ ij : ι × κ, c ij.2 * orthonormalBasisOverlap e f ij = ∑ j, c j := by
  rw [Fintype.sum_prod_type_right]
  apply Fintype.sum_congr
  intro j
  change (∑ i, c j * orthonormalBasisOverlap e f (i, j)) = c j
  rw [← Finset.mul_sum, sum_orthonormalBasisOverlap_left, mul_one]

/-- The self-adjoint operator with prescribed real diagonal in an
orthonormal basis. -/
noncomputable def spectralDiagonal
    (e : OrthonormalBasis ι ℂ E) (a : ι → ℝ) : E →ₗ[ℂ] E :=
  ∑ i, (a i : ℂ) •
    (InnerProductSpace.rankOne ℂ (e i) (e i)).toLinearMap

@[simp]
theorem spectralDiagonal_apply_basis
    (e : OrthonormalBasis ι ℂ E) (a : ι → ℝ) (i : ι) :
    spectralDiagonal e a (e i) = (a i : ℂ) • e i := by
  classical
  simp [spectralDiagonal, OrthonormalBasis.inner_eq_ite]

/-- Coordinate formula for a spectral diagonal map in its defining basis. -/
theorem spectralDiagonal_repr_apply
    (e : OrthonormalBasis ι ℂ E) (a : ι → ℝ) (x : E) (i : ι) :
    e.repr (spectralDiagonal e a x) i = (a i : ℂ) * e.repr x i := by
  classical
  calc
    e.repr (spectralDiagonal e a x) i =
        e.repr (spectralDiagonal e a (∑ j, e.repr x j • e j)) i := by
      rw [e.sum_repr]
    _ = (a i : ℂ) * e.repr x i := by
      simp only [map_sum, spectralDiagonal_apply_basis, map_smul]
      simp_rw [e.repr_apply_apply]
      simp [Pi.single_apply, mul_comm]

theorem spectralDiagonal_isSymmetric
    (e : OrthonormalBasis ι ℂ E) (a : ι → ℝ) :
    (spectralDiagonal e a).IsSymmetric := by
  classical
  rw [spectralDiagonal]
  apply LinearMap.isSymmetric_sum Finset.univ
  intro i _
  apply InnerProductSpace.isSymmetric_rankOne_self (e i) |>.smul
  apply Complex.ext <;> simp

/-- Reconstructing a symmetric map from Mathlib's canonical eigenbasis and
eigenvalue list returns the original map. -/
theorem spectralDiagonal_eigenvectorBasis_eq [FiniteDimensional ℂ E]
    (A : E →ₗ[ℂ] E) (hA : A.IsSymmetric) :
    spectralDiagonal (hA.eigenvectorBasis rfl) (hA.eigenvalues rfl) = A := by
  apply (hA.eigenvectorBasis rfl).toBasis.ext
  intro i
  simpa only [OrthonormalBasis.coe_toBasis] using
    (spectralDiagonal_apply_basis (hA.eigenvectorBasis rfl)
      (hA.eigenvalues rfl) i).trans (hA.apply_eigenvectorBasis rfl i).symm

/-- The trace of a real diagonal operator is the sum of its diagonal. -/
theorem re_trace_spectralDiagonal [FiniteDimensional ℂ E]
    (e : OrthonormalBasis ι ℂ E) (a : ι → ℝ) :
    (spectralDiagonal e a |>.trace ℂ E).re = ∑ i, a i := by
  rw [LinearMap.trace_eq_sum_inner (spectralDiagonal e a) e, Complex.re_sum]
  apply Fintype.sum_congr
  intro i
  rw [spectralDiagonal_apply_basis, inner_smul_right, e.inner_eq_one,
    mul_one]
  exact Complex.ofReal_re (a i)

/-- Apply a real scalar function to a symmetric map through Mathlib's
canonical finite-dimensional spectral resolution. -/
noncomputable def hermitianFunctionalCalculus [FiniteDimensional ℂ E]
    (f : ℝ → ℝ) (A : E →ₗ[ℂ] E) (hA : A.IsSymmetric) : E →ₗ[ℂ] E :=
  spectralDiagonal (hA.eigenvectorBasis rfl) (f ∘ hA.eigenvalues rfl)

@[simp]
theorem hermitianFunctionalCalculus_apply_eigenvectorBasis
    [FiniteDimensional ℂ E] (f : ℝ → ℝ) (A : E →ₗ[ℂ] E)
    (hA : A.IsSymmetric) (i : Fin (Module.finrank ℂ E)) :
    hermitianFunctionalCalculus f A hA (hA.eigenvectorBasis rfl i) =
      (f (hA.eigenvalues rfl i) : ℂ) • hA.eigenvectorBasis rfl i := by
  exact spectralDiagonal_apply_basis (hA.eigenvectorBasis rfl)
    (f ∘ hA.eigenvalues rfl) i

/-- The canonical functional calculus acts by `f μ` on every `μ`-eigenvector,
not only on the chosen canonical eigenbasis. -/
theorem hermitianFunctionalCalculus_apply_of_apply_eq_smul
    [FiniteDimensional ℂ E] (f : ℝ → ℝ) (A : E →ₗ[ℂ] E)
    (hA : A.IsSymmetric) (x : E) (μ : ℝ)
    (hx : A x = (μ : ℂ) • x) :
    hermitianFunctionalCalculus f A hA x = (f μ : ℂ) • x := by
  apply (hA.eigenvectorBasis rfl).repr.injective
  ext i
  unfold hermitianFunctionalCalculus
  rw [spectralDiagonal_repr_apply]
  simp only [Function.comp_apply, map_smul]
  have hi := congrArg (fun y ↦ (hA.eigenvectorBasis rfl).repr y i) hx
  rw [hA.eigenvectorBasis_apply_self_apply] at hi
  simp only [map_smul] at hi
  by_cases hcoord : (hA.eigenvectorBasis rfl).repr x i = 0
  · simp [hcoord]
  · have heigen : hA.eigenvalues rfl i = μ := by
      apply Complex.ofReal_injective
      exact mul_right_cancel₀ hcoord hi
    rw [heigen]
    simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]

theorem hermitianFunctionalCalculus_isSymmetric [FiniteDimensional ℂ E]
    (f : ℝ → ℝ) (A : E →ₗ[ℂ] E) (hA : A.IsSymmetric) :
    (hermitianFunctionalCalculus f A hA).IsSymmetric :=
  spectralDiagonal_isSymmetric (hA.eigenvectorBasis rfl)
    (f ∘ hA.eigenvalues rfl)

@[simp]
theorem hermitianFunctionalCalculus_id [FiniteDimensional ℂ E]
    (A : E →ₗ[ℂ] E) (hA : A.IsSymmetric) :
    hermitianFunctionalCalculus id A hA = A := by
  simpa only [hermitianFunctionalCalculus, Function.id_comp] using
    spectralDiagonal_eigenvectorBasis_eq A hA

/-- Functional calculus of the zero operator vanishes when the scalar
function vanishes at zero. -/
@[simp]
theorem hermitianFunctionalCalculus_zero [FiniteDimensional ℂ E]
    (f : ℝ → ℝ) (hf : f 0 = 0) :
    hermitianFunctionalCalculus f (0 : E →ₗ[ℂ] E)
      LinearMap.IsSymmetric.zero = 0 := by
  apply LinearMap.ext
  intro x
  rw [hermitianFunctionalCalculus_apply_of_apply_eq_smul
    f _ _ x 0 (by simp)]
  simp [hf]

theorem re_trace_hermitianFunctionalCalculus [FiniteDimensional ℂ E]
    (f : ℝ → ℝ) (A : E →ₗ[ℂ] E) (hA : A.IsSymmetric) :
    ((hermitianFunctionalCalculus f A hA).trace ℂ E).re =
      ∑ i, f (hA.eigenvalues rfl i) := by
  exact re_trace_spectralDiagonal (hA.eigenvectorBasis rfl)
    (f ∘ hA.eigenvalues rfl)

/-- Trace of Hermitian functional calculus after real scaling, evaluated in
an eigenbasis of the original operator. -/
theorem re_trace_hermitianFunctionalCalculus_real_smul
    [FiniteDimensional ℂ E] (f : ℝ → ℝ) (c : ℝ)
    (A : E →ₗ[ℂ] E) (hA : A.IsSymmetric) :
    ((hermitianFunctionalCalculus f ((c : ℂ) • A)
      (hA.smul (by simp))).trace ℂ E).re =
      ∑ i, f (c * hA.eigenvalues rfl i) := by
  rw [LinearMap.trace_eq_sum_inner _ (hA.eigenvectorBasis rfl), Complex.re_sum]
  apply Fintype.sum_congr
  intro i
  have heig : ((c : ℂ) • A) (hA.eigenvectorBasis rfl i) =
      ((c * hA.eigenvalues rfl i : ℝ) : ℂ) •
        hA.eigenvectorBasis rfl i := by
    rw [LinearMap.smul_apply, hA.apply_eigenvectorBasis]
    simp only [smul_smul]
    congr 1
    exact (map_mul (algebraMap ℝ ℂ) c (hA.eigenvalues rfl i)).symm
  rw [hermitianFunctionalCalculus_apply_of_apply_eq_smul f _ _ _ _ heig,
    inner_smul_right, (hA.eigenvectorBasis rfl).inner_eq_one]
  simp

/-- The trace of the power potential is homogeneous under positive real
scaling. -/
theorem re_trace_powerPotential_real_smul [FiniteDimensional ℂ E]
    {p c : ℝ} (hc : 0 < c) (A : E →ₗ[ℂ] E) (hA : A.IsSymmetric) :
    ((hermitianFunctionalCalculus (powerPotential p) ((c : ℂ) • A)
      (hA.smul (by simp))).trace ℂ E).re =
      c ^ p *
        ((hermitianFunctionalCalculus (powerPotential p) A hA).trace ℂ E).re := by
  rw [re_trace_hermitianFunctionalCalculus_real_smul,
    re_trace_hermitianFunctionalCalculus, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    exact powerPotential_mul_of_pos p _ hc

/-- Trace-level Euler identity for the Hermitian power functional calculus. -/
theorem re_trace_powerGradient_mul_self [FiniteDimensional ℂ E]
    {p : ℝ} (hp : 0 < p) (A : E →ₗ[ℂ] E) (hA : A.IsSymmetric) :
    ((hermitianFunctionalCalculus
      (fun x => powerGradient p x * x) A hA).trace ℂ E).re =
      p * ((hermitianFunctionalCalculus
        (powerPotential p) A hA).trace ℂ E).re := by
  rw [re_trace_hermitianFunctionalCalculus,
    re_trace_hermitianFunctionalCalculus, Finset.mul_sum]
  apply Fintype.sum_congr
  intro i
  exact powerGradient_mul_self hp _

/-- For a symmetric map, the real trace of its square is its
Hilbert--Schmidt coordinate square in any orthonormal basis. -/
theorem re_trace_sq_eq_sum_norm_sq [FiniteDimensional ℂ E]
    (e : OrthonormalBasis ι ℂ E) (A : E →ₗ[ℂ] E) (hA : A.IsSymmetric) :
    ((A.comp A).trace ℂ E).re = ∑ i, ‖A (e i)‖ ^ 2 := by
  rw [LinearMap.trace_eq_sum_inner (A.comp A) e, Complex.re_sum]
  apply Fintype.sum_congr
  intro i
  rw [LinearMap.comp_apply, ← hA (e i) (A (e i))]
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) (A (e i))).symm

/-- Pointwise multiplication of real functions becomes composition of their
Hermitian functional-calculus maps. -/
theorem hermitianFunctionalCalculus_mul [FiniteDimensional ℂ E]
    (f g : ℝ → ℝ) (A : E →ₗ[ℂ] E) (hA : A.IsSymmetric) :
    hermitianFunctionalCalculus (fun x ↦ f x * g x) A hA =
      (hermitianFunctionalCalculus f A hA).comp
        (hermitianFunctionalCalculus g A hA) := by
  apply (hA.eigenvectorBasis rfl).toBasis.ext
  intro i
  simp only [OrthonormalBasis.coe_toBasis,
    hermitianFunctionalCalculus_apply_eigenvectorBasis,
    LinearMap.comp_apply, map_smul, smul_smul]
  rw [mul_comm, Complex.ofReal_mul]

/-- Applying functional calculus twice composes the scalar functions. -/
theorem hermitianFunctionalCalculus_comp [FiniteDimensional ℂ E]
    (f g : ℝ → ℝ) (A : E →ₗ[ℂ] E) (hA : A.IsSymmetric) :
    hermitianFunctionalCalculus f (hermitianFunctionalCalculus g A hA)
        (hermitianFunctionalCalculus_isSymmetric g A hA) =
      hermitianFunctionalCalculus (f ∘ g) A hA := by
  apply (hA.eigenvectorBasis rfl).toBasis.ext
  intro i
  rw [OrthonormalBasis.coe_toBasis,
    hermitianFunctionalCalculus_apply_of_apply_eq_smul f _ _ _
      (g (hA.eigenvalues rfl i))
      (hermitianFunctionalCalculus_apply_eigenvectorBasis g A hA i),
    hermitianFunctionalCalculus_apply_eigenvectorBasis]
  rfl

theorem isSymmetric_comp_self (A : E →ₗ[ℂ] E) (hA : A.IsSymmetric) :
    (A.comp A).IsSymmetric := by
  intro x y
  simp only [LinearMap.comp_apply]
  rw [hA (A x) y, hA x (A y)]

/-- Even functional calculus factors through the square of a symmetric map. -/
theorem hermitianFunctionalCalculus_comp_self [FiniteDimensional ℂ E]
    (g : ℝ → ℝ) (A : E →ₗ[ℂ] E) (hA : A.IsSymmetric) :
    hermitianFunctionalCalculus (fun x ↦ g (x ^ 2)) A hA =
      hermitianFunctionalCalculus g (A.comp A) (isSymmetric_comp_self A hA) := by
  apply (hA.eigenvectorBasis rfl).toBasis.ext
  intro i
  rw [OrthonormalBasis.coe_toBasis,
    hermitianFunctionalCalculus_apply_eigenvectorBasis]
  rw [hermitianFunctionalCalculus_apply_of_apply_eq_smul]
  simp only [LinearMap.comp_apply, hA.apply_eigenvectorBasis, map_smul,
    smul_smul, Complex.ofReal_pow]
  rw [pow_two]
  rfl

/-- The Hermitian power-potential map factors through the nonnegative square
of the symmetric operator. -/
theorem hermitianFunctionalCalculus_powerPotential_comp_self
    [FiniteDimensional ℂ E] (p : ℝ) (A : E →ₗ[ℂ] E)
    (hA : A.IsSymmetric) :
    hermitianFunctionalCalculus (powerPotential p) A hA =
      hermitianFunctionalCalculus (fun y ↦ y ^ (p / 2) / p)
        (A.comp A) (isSymmetric_comp_self A hA) := by
  rw [show powerPotential p = (fun x ↦ (x ^ 2) ^ (p / 2) / p) by
    funext x
    exact powerPotential_eq_sq_rpow_div_two p x]
  exact hermitianFunctionalCalculus_comp_self (fun y ↦ y ^ (p / 2) / p) A hA

/-- The real quadratic form of a symmetric map is the overlap-weighted sum
of its real eigenvalues in any orthonormal eigenbasis. -/
theorem re_inner_apply_eq_sum_eigenbasis
    (A : E →ₗ[ℂ] E) (hA : A.IsSymmetric)
    (e : OrthonormalBasis ι ℂ E) (a : ι → ℝ)
    (he : ∀ i, A (e i) = (a i : ℂ) • e i) (x : E) :
    (⟪x, A x⟫_ℂ).re = ∑ i, a i * ‖(⟪e i, x⟫_ℂ)‖ ^ 2 := by
  rw [← e.sum_inner_mul_inner x (A x), Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← hA (e i) x, he i, inner_smul_left]
  have ha : (starRingEnd ℂ) (a i : ℂ) = (a i : ℂ) := by
    apply Complex.ext <;> simp
  rw [ha]
  rw [show ⟪x, e i⟫_ℂ * ((a i : ℂ) * ⟪e i, x⟫_ℂ) =
      (a i : ℂ) * (⟪x, e i⟫_ℂ * ⟪e i, x⟫_ℂ) by ring]
  rw [Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hinner : (⟪x, e i⟫_ℂ * ⟪e i, x⟫_ℂ).re =
      ‖(⟪e i, x⟫_ℂ)‖ ^ 2 := by
    calc
      _ = ‖(⟪x, e i⟫_ℂ * ⟪e i, x⟫_ℂ)‖ :=
        inner_mul_symm_re_eq_norm x (e i)
      _ = ‖(⟪e i, x⟫_ℂ)‖ ^ 2 := by
        rw [norm_mul, norm_inner_symm]
        ring
  rw [hinner]

/-- The real trace of a product of symmetric maps is a double sum of the
products of their eigenvalues against the overlaps of eigenbases. -/
theorem re_trace_comp_eq_sum_eigenbasis_overlap [FiniteDimensional ℂ E]
    (A B : E →ₗ[ℂ] E) (hA : A.IsSymmetric)
    (e : OrthonormalBasis ι ℂ E) (f : OrthonormalBasis κ ℂ E)
    (a : ι → ℝ) (b : κ → ℝ)
    (he : ∀ i, A (e i) = (a i : ℂ) • e i)
    (hf : ∀ j, B (f j) = (b j : ℂ) • f j) :
    ((A.comp B).trace ℂ E).re =
      ∑ ij : ι × κ, a ij.1 * b ij.2 * orthonormalBasisOverlap e f ij := by
  calc
    ((A.comp B).trace ℂ E).re =
        ∑ j, (⟪f j, (A.comp B) (f j)⟫_ℂ).re := by
      rw [LinearMap.trace_eq_sum_inner (A.comp B) f, Complex.re_sum]
    _ = ∑ j, b j * ∑ i, a i * orthonormalBasisOverlap e f (i, j) := by
      apply Fintype.sum_congr
      intro j
      rw [LinearMap.comp_apply, hf j, map_smul, inner_smul_right,
        Complex.mul_re]
      simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      rw [re_inner_apply_eq_sum_eigenbasis A hA e a he]
      rfl
    _ = ∑ j, ∑ i, a i * b j * orthonormalBasisOverlap e f (i, j) := by
      apply Fintype.sum_congr
      intro j
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ ij : ι × κ,
        a ij.1 * b ij.2 * orthonormalBasisOverlap e f ij := by
      rw [Fintype.sum_prod_type_right]

/-- Trace-product expansion for two explicitly diagonal spectral maps. -/
theorem re_trace_spectralDiagonal_comp [FiniteDimensional ℂ E]
    (e : OrthonormalBasis ι ℂ E) (f : OrthonormalBasis κ ℂ E)
    (a : ι → ℝ) (b : κ → ℝ) :
    (((spectralDiagonal e a).comp (spectralDiagonal f b)).trace ℂ E).re =
      ∑ ij : ι × κ,
        a ij.1 * b ij.2 * orthonormalBasisOverlap e f ij := by
  exact re_trace_comp_eq_sum_eigenbasis_overlap
    (spectralDiagonal e a) (spectralDiagonal f b)
    (spectralDiagonal_isSymmetric e a) e f a b
    (spectralDiagonal_apply_basis e a)
    (spectralDiagonal_apply_basis f b)

/-- The trace form of the power-potential Bregman divergence for two finite
Hermitian spectral resolutions. -/
noncomputable def spectralBregmanTrace [FiniteDimensional ℂ E]
    (p : ℝ) (e : OrthonormalBasis ι ℂ E) (a : ι → ℝ)
    (f : OrthonormalBasis κ ℂ E) (b : κ → ℝ) : ℝ :=
  (spectralDiagonal e (powerPotential p ∘ a) |>.trace ℂ E).re -
    (spectralDiagonal f (powerPotential p ∘ b) |>.trace ℂ E).re -
    (((spectralDiagonal e a).comp
      (spectralDiagonal f (powerGradient p ∘ b))).trace ℂ E).re +
    (spectralDiagonal f (fun j ↦ powerGradient p (b j) * b j) |>.trace ℂ E).re

/-- Exact equation (4), first line: the Hermitian trace Bregman divergence is
the overlap-weighted sum of scalar Bregman divergences. -/
theorem spectralBregmanTrace_eq_sum [FiniteDimensional ℂ E]
    (p : ℝ) (e : OrthonormalBasis ι ℂ E) (a : ι → ℝ)
    (f : OrthonormalBasis κ ℂ E) (b : κ → ℝ) :
    spectralBregmanTrace p e a f b =
      ∑ ij : ι × κ, orthonormalBasisOverlap e f ij *
        scalarBregman p (a ij.1) (b ij.2) := by
  classical
  unfold spectralBregmanTrace
  rw [re_trace_spectralDiagonal, re_trace_spectralDiagonal,
    re_trace_spectralDiagonal_comp, re_trace_spectralDiagonal]
  rw [← sum_left_mul_orthonormalBasisOverlap e f (powerPotential p ∘ a)]
  rw [← sum_right_mul_orthonormalBasisOverlap e f (powerPotential p ∘ b)]
  rw [← sum_right_mul_orthonormalBasisOverlap e f
    (fun j ↦ powerGradient p (b j) * b j)]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Fintype.sum_congr
  intro ij
  simp only [Function.comp_apply]
  unfold scalarBregman
  ring

theorem spectralBregmanTrace_nonneg [FiniteDimensional ℂ E]
    {p : ℝ} (hp : 1 < p) (e : OrthonormalBasis ι ℂ E) (a : ι → ℝ)
    (f : OrthonormalBasis κ ℂ E) (b : κ → ℝ) :
    0 ≤ spectralBregmanTrace p e a f b := by
  rw [spectralBregmanTrace_eq_sum]
  exact Finset.sum_nonneg fun ij _ ↦
    mul_nonneg (orthonormalBasisOverlap_nonneg e f ij)
      (scalarBregman_nonneg hp (a ij.1) (b ij.2))

/-- The expanded Hilbert--Schmidt square of the difference of the two
spectral Mazur maps. -/
noncomputable def spectralMazurDistanceSq [FiniteDimensional ℂ E]
    (p : ℝ) (e : OrthonormalBasis ι ℂ E) (a : ι → ℝ)
    (f : OrthonormalBasis κ ℂ E) (b : κ → ℝ) : ℝ :=
  (spectralDiagonal e (fun i ↦ scalarMazur p (a i) ^ 2) |>.trace ℂ E).re -
    2 * (((spectralDiagonal e (scalarMazur p ∘ a)).comp
      (spectralDiagonal f (scalarMazur p ∘ b))).trace ℂ E).re +
    (spectralDiagonal f (fun j ↦ scalarMazur p (b j) ^ 2) |>.trace ℂ E).re

/-- Exact equation (4), second line: the Hilbert--Schmidt Mazur square is
the overlap-weighted sum of squared scalar Mazur differences. -/
theorem spectralMazurDistanceSq_eq_sum [FiniteDimensional ℂ E]
    (p : ℝ) (e : OrthonormalBasis ι ℂ E) (a : ι → ℝ)
    (f : OrthonormalBasis κ ℂ E) (b : κ → ℝ) :
    spectralMazurDistanceSq p e a f b =
      ∑ ij : ι × κ, orthonormalBasisOverlap e f ij *
        (scalarMazur p (a ij.1) - scalarMazur p (b ij.2)) ^ 2 := by
  classical
  unfold spectralMazurDistanceSq
  rw [re_trace_spectralDiagonal, re_trace_spectralDiagonal_comp,
    re_trace_spectralDiagonal]
  rw [← sum_left_mul_orthonormalBasisOverlap e f
    (fun i ↦ scalarMazur p (a i) ^ 2)]
  rw [← sum_right_mul_orthonormalBasisOverlap e f
    (fun j ↦ scalarMazur p (b j) ^ 2)]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Fintype.sum_congr
  intro ij
  simp only [Function.comp_apply]
  ring

theorem spectralMazurDistanceSq_nonneg [FiniteDimensional ℂ E]
    (p : ℝ) (e : OrthonormalBasis ι ℂ E) (a : ι → ℝ)
    (f : OrthonormalBasis κ ℂ E) (b : κ → ℝ) :
    0 ≤ spectralMazurDistanceSq p e a f b := by
  rw [spectralMazurDistanceSq_eq_sum]
  exact Finset.sum_nonneg fun ij _ ↦
    mul_nonneg (orthonormalBasisOverlap_nonneg e f ij) (sq_nonneg _)

/-- At the Hilbert exponent, the spectral Bregman trace is exactly half the
spectral Mazur square. -/
theorem spectralBregmanTrace_two_eq [FiniteDimensional ℂ E]
    (e : OrthonormalBasis ι ℂ E) (a : ι → ℝ)
    (f : OrthonormalBasis κ ℂ E) (b : κ → ℝ) :
    spectralBregmanTrace 2 e a f b =
      spectralMazurDistanceSq 2 e a f b / 2 := by
  rw [spectralBregmanTrace_eq_sum, spectralMazurDistanceSq_eq_sum]
  simp_rw [scalarBregman_two, scalarMazur_two]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ij _
  ring

/-- The scalar compactified bounds lift to the exact Hermitian spectral trace
quantities. -/
theorem spectralBregmanTrace_two_sided [FiniteDimensional ℂ E]
    {p m M : ℝ} (hp : 1 < p)
    (hbound : ∀ x : OnePoint ℝ, m ≤ compactifiedScalarRatio p x ∧
      compactifiedScalarRatio p x ≤ M)
    (e : OrthonormalBasis ι ℂ E) (a : ι → ℝ)
    (f : OrthonormalBasis κ ℂ E) (b : κ → ℝ) :
    m * spectralMazurDistanceSq p e a f b ≤ spectralBregmanTrace p e a f b ∧
      spectralBregmanTrace p e a f b ≤
        M * spectralMazurDistanceSq p e a f b := by
  rw [spectralBregmanTrace_eq_sum, spectralMazurDistanceSq_eq_sum]
  exact orthonormalBasisOverlap_sum_scalarBregman_two_sided
    hp hbound e f a b

/-- Canonical trace Bregman quantity for two symmetric maps, using Mathlib's
eigenvalue lists and eigenvector bases. -/
noncomputable def hermitianBregmanTrace [FiniteDimensional ℂ E]
    (p : ℝ) (A B : E →ₗ[ℂ] E) (hA : A.IsSymmetric) (hB : B.IsSymmetric) : ℝ :=
  spectralBregmanTrace p (hA.eigenvectorBasis rfl) (hA.eigenvalues rfl)
    (hB.eigenvectorBasis rfl) (hB.eigenvalues rfl)

/-- Canonical expanded Hilbert--Schmidt square between the spectral Mazur
maps of two symmetric operators. -/
noncomputable def hermitianMazurDistanceSq [FiniteDimensional ℂ E]
    (p : ℝ) (A B : E →ₗ[ℂ] E) (hA : A.IsSymmetric) (hB : B.IsSymmetric) : ℝ :=
  spectralMazurDistanceSq p (hA.eigenvectorBasis rfl) (hA.eigenvalues rfl)
    (hB.eigenvectorBasis rfl) (hB.eigenvalues rfl)

/-- The Hermitian Mazur map obtained from the canonical spectral calculus. -/
noncomputable def hermitianMazurMap [FiniteDimensional ℂ E]
    (p : ℝ) (A : E →ₗ[ℂ] E) (hA : A.IsSymmetric) : E →ₗ[ℂ] E :=
  hermitianFunctionalCalculus (scalarMazur p) A hA

theorem hermitianMazurMap_isSymmetric [FiniteDimensional ℂ E]
    (p : ℝ) (A : E →ₗ[ℂ] E) (hA : A.IsSymmetric) :
    (hermitianMazurMap p A hA).IsSymmetric :=
  hermitianFunctionalCalculus_isSymmetric (scalarMazur p) A hA

/-- The Hermitian Mazur maps with exponents `p` and `4 / p` are inverse. -/
theorem hermitianMazurMap_four_div_comp [FiniteDimensional ℂ E]
    {p : ℝ} (hp : 0 < p) (A : E →ₗ[ℂ] E) (hA : A.IsSymmetric) :
    hermitianMazurMap (4 / p) (hermitianMazurMap p A hA)
        (hermitianMazurMap_isSymmetric p A hA) = A := by
  unfold hermitianMazurMap
  rw [hermitianFunctionalCalculus_comp]
  rw [show scalarMazur (4 / p) ∘ scalarMazur p = id by
    funext x
    unfold scalarMazur
    simp only [Function.comp_apply]
    rw [signedPower_comp]
    rw [show (4 / p / 2) * (p / 2) = 1 by field_simp; norm_num]
    exact signedPower_one x]
  exact hermitianFunctionalCalculus_id A hA

/-- Operator-functional-calculus form of the canonical Hermitian Bregman
quantity. This is the form used by the rectangular dilation step. -/
theorem hermitianBregmanTrace_eq_functionalCalculus [FiniteDimensional ℂ E]
    (p : ℝ) (A B : E →ₗ[ℂ] E) (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
    hermitianBregmanTrace p A B hA hB =
      ((hermitianFunctionalCalculus (powerPotential p) A hA).trace ℂ E).re -
      ((hermitianFunctionalCalculus (powerPotential p) B hB).trace ℂ E).re -
      ((A.comp (hermitianFunctionalCalculus (powerGradient p) B hB)).trace ℂ E).re +
      ((hermitianFunctionalCalculus
        (fun x ↦ powerGradient p x * x) B hB).trace ℂ E).re := by
  unfold hermitianBregmanTrace spectralBregmanTrace hermitianFunctionalCalculus
  rw [spectralDiagonal_eigenvectorBasis_eq A hA]
  congr 3

/-- Operator-functional-calculus form of the canonical Hermitian Mazur
square. -/
theorem hermitianMazurDistanceSq_eq_functionalCalculus
    [FiniteDimensional ℂ E]
    (p : ℝ) (A B : E →ₗ[ℂ] E) (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
    hermitianMazurDistanceSq p A B hA hB =
      ((hermitianFunctionalCalculus
        (fun x ↦ scalarMazur p x ^ 2) A hA).trace ℂ E).re -
      2 * (((hermitianFunctionalCalculus (scalarMazur p) A hA).comp
        (hermitianFunctionalCalculus (scalarMazur p) B hB)).trace ℂ E).re +
      ((hermitianFunctionalCalculus
        (fun x ↦ scalarMazur p x ^ 2) B hB).trace ℂ E).re := by
  rfl

/-- Against the zero operator, the Mazur Hilbert--Schmidt square is `p`
times the power-potential trace. -/
theorem hermitianMazurDistanceSq_zero_eq_powerPotentialTrace
    [FiniteDimensional ℂ E] {p : ℝ} (hp : 0 < p)
    (A : E →ₗ[ℂ] E) (hA : A.IsSymmetric) :
    hermitianMazurDistanceSq p A 0 hA LinearMap.IsSymmetric.zero =
      p * ((hermitianFunctionalCalculus
        (powerPotential p) A hA).trace ℂ E).re := by
  rw [hermitianMazurDistanceSq_eq_functionalCalculus,
    hermitianFunctionalCalculus_zero
      (scalarMazur p) (scalarMazur_zero p),
    hermitianFunctionalCalculus_zero
      (fun x ↦ scalarMazur p x ^ 2) (by simp)]
  simp only [LinearMap.comp_zero, map_zero, Complex.zero_re,
    mul_zero, sub_zero, add_zero]
  rw [re_trace_hermitianFunctionalCalculus,
    re_trace_hermitianFunctionalCalculus, Finset.mul_sum]
  apply Fintype.sum_congr
  intro i
  rw [scalarMazur_sq hp]
  unfold powerPotential
  field_simp

/-- The expanded spectral Mazur quantity is the real trace of the square of
the difference of the two Hermitian Mazur maps. -/
theorem hermitianMazurDistanceSq_eq_re_trace_sq_sub
    [FiniteDimensional ℂ E]
    (p : ℝ) (A B : E →ₗ[ℂ] E) (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
    hermitianMazurDistanceSq p A B hA hB =
      ((((hermitianMazurMap p A hA - hermitianMazurMap p B hB).comp
        (hermitianMazurMap p A hA - hermitianMazurMap p B hB)).trace ℂ E).re) := by
  rw [hermitianMazurDistanceSq_eq_functionalCalculus]
  have hA_sq :
      hermitianFunctionalCalculus (fun x ↦ scalarMazur p x ^ 2) A hA =
        (hermitianMazurMap p A hA).comp (hermitianMazurMap p A hA) := by
    rw [show (fun x ↦ scalarMazur p x ^ 2) =
        (fun x ↦ scalarMazur p x * scalarMazur p x) by funext x; ring]
    exact hermitianFunctionalCalculus_mul (scalarMazur p) (scalarMazur p) A hA
  have hB_sq :
      hermitianFunctionalCalculus (fun x ↦ scalarMazur p x ^ 2) B hB =
        (hermitianMazurMap p B hB).comp (hermitianMazurMap p B hB) := by
    rw [show (fun x ↦ scalarMazur p x ^ 2) =
        (fun x ↦ scalarMazur p x * scalarMazur p x) by funext x; ring]
    exact hermitianFunctionalCalculus_mul (scalarMazur p) (scalarMazur p) B hB
  rw [hA_sq, hB_sq]
  unfold hermitianMazurMap
  simp only [LinearMap.sub_comp, LinearMap.comp_sub, map_sub, Complex.sub_re]
  rw [LinearMap.trace_comp_comm'
    (hermitianFunctionalCalculus (scalarMazur p) B hB)
    (hermitianFunctionalCalculus (scalarMazur p) A hA)]
  ring

/-- Coordinate Hilbert--Schmidt form of the Hermitian Mazur distance, valid
in every orthonormal basis. -/
theorem hermitianMazurDistanceSq_eq_sum_norm_sq
    [FiniteDimensional ℂ E] (e : OrthonormalBasis ι ℂ E)
    (p : ℝ) (A B : E →ₗ[ℂ] E) (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
    hermitianMazurDistanceSq p A B hA hB =
      ∑ i, ‖(hermitianMazurMap p A hA - hermitianMazurMap p B hB) (e i)‖ ^ 2 := by
  rw [hermitianMazurDistanceSq_eq_re_trace_sq_sub]
  exact re_trace_sq_eq_sum_norm_sq e _
    ((hermitianMazurMap_isSymmetric p A hA).sub
      (hermitianMazurMap_isSymmetric p B hB))

/-- Canonical operator form of the exact Hilbert-exponent normalization. -/
theorem hermitianBregmanTrace_two_eq [FiniteDimensional ℂ E]
    (A B : E →ₗ[ℂ] E) (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
    hermitianBregmanTrace 2 A B hA hB =
      hermitianMazurDistanceSq 2 A B hA hB / 2 :=
  spectralBregmanTrace_two_eq (hA.eigenvectorBasis rfl) (hA.eigenvalues rfl)
    (hB.eigenvectorBasis rfl) (hB.eigenvalues rfl)

/-- Positive finite constants compare the Hermitian trace Bregman quantity to
the spectral Mazur Hilbert--Schmidt square. -/
theorem exists_hermitianBregmanTrace_two_sided [FiniteDimensional ℂ E]
    {p : ℝ} (hp : 1 < p) :
    ∃ m M : ℝ, 0 < m ∧ m ≤ M ∧
      ∀ (A B : E →ₗ[ℂ] E) (hA : A.IsSymmetric) (hB : B.IsSymmetric),
        m * hermitianMazurDistanceSq p A B hA hB ≤
            hermitianBregmanTrace p A B hA hB ∧
          hermitianBregmanTrace p A B hA hB ≤
            M * hermitianMazurDistanceSq p A B hA hB := by
  obtain ⟨m, M, hm, hmM, hbound⟩ := exists_compactifiedScalarRatio_bounds hp
  refine ⟨m, M, hm, hmM, ?_⟩
  intro A B hA hB
  exact spectralBregmanTrace_two_sided hp hbound
    (hA.eigenvectorBasis rfl) (hA.eigenvalues rfl)
    (hB.eigenvectorBasis rfl) (hB.eigenvalues rfl)

/-- The constants in the Hermitian comparison are independent of the complex
finite-dimensional Hilbert space. -/
theorem exists_uniform_hermitianBregmanTrace_two_sided
    {p : ℝ} (hp : 1 < p) :
    ∃ m M : ℝ, 0 < m ∧ m ≤ M ∧
      ∀ {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
        [FiniteDimensional ℂ F]
        (A B : F →ₗ[ℂ] F) (hA : A.IsSymmetric) (hB : B.IsSymmetric),
        m * hermitianMazurDistanceSq p A B hA hB ≤
            hermitianBregmanTrace p A B hA hB ∧
          hermitianBregmanTrace p A B hA hB ≤
            M * hermitianMazurDistanceSq p A B hA hB := by
  obtain ⟨m, M, hm, hmM, hbound⟩ := exists_compactifiedScalarRatio_bounds hp
  refine ⟨m, M, hm, hmM, ?_⟩
  intro F _ _ _ A B hA hB
  exact spectralBregmanTrace_two_sided hp hbound
    (hA.eigenvectorBasis rfl) (hA.eigenvalues rfl)
    (hB.eigenvectorBasis rfl) (hB.eigenvalues rfl)

/-- The trace-product formula instantiated with Mathlib's canonical
eigenvalue lists and eigenvector bases. -/
theorem re_trace_comp_eq_sum_symmetric_eigenvalues_overlap
    [FiniteDimensional ℂ E] (A B : E →ₗ[ℂ] E)
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
    ((A.comp B).trace ℂ E).re =
      ∑ ij : Fin (Module.finrank ℂ E) × Fin (Module.finrank ℂ E),
        hA.eigenvalues rfl ij.1 * hB.eigenvalues rfl ij.2 *
          orthonormalBasisOverlap (hA.eigenvectorBasis rfl)
            (hB.eigenvectorBasis rfl) ij := by
  exact re_trace_comp_eq_sum_eigenbasis_overlap A B hA
    (hA.eigenvectorBasis rfl) (hB.eigenvectorBasis rfl)
    (hA.eigenvalues rfl) (hB.eigenvalues rfl)
    (hA.apply_eigenvectorBasis rfl) (hB.apply_eigenvectorBasis rfl)

end HlawkaSchatten
