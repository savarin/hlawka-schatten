/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import HlawkaSchatten.ScalarRatio
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Nonnegative weighted lift of the scalar comparison

The Hermitian spectral argument writes both divergences as finite sums with
weights `Tr(Pᵢ Qⱼ) ≥ 0`.  This file isolates the ordered-algebraic step which
lifts the pointwise scalar bounds through those sums.
-/

namespace HlawkaSchatten

open scoped InnerProductSpace

/-- A two-sided scalar Bregman comparison survives every finite nonnegative
weighted sum. -/
theorem finset_sum_scalarBregman_two_sided {ι : Type*} {p m M : ℝ}
    (hp : 1 < p)
    (hbound : ∀ x : OnePoint ℝ, m ≤ compactifiedScalarRatio p x ∧
      compactifiedScalarRatio p x ≤ M) (s : Finset ι) (w a b : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    m * ∑ i ∈ s, w i * (scalarMazur p (a i) - scalarMazur p (b i)) ^ 2 ≤
        ∑ i ∈ s, w i * scalarBregman p (a i) (b i) ∧
      ∑ i ∈ s, w i * scalarBregman p (a i) (b i) ≤
        M * ∑ i ∈ s, w i * (scalarMazur p (a i) - scalarMazur p (b i)) ^ 2 := by
  have hpoint (i : ι) :
      m * (scalarMazur p (a i) - scalarMazur p (b i)) ^ 2 ≤
          scalarBregman p (a i) (b i) ∧
        scalarBregman p (a i) (b i) ≤
          M * (scalarMazur p (a i) - scalarMazur p (b i)) ^ 2 :=
    scalarBregman_two_sided_of_compactified_bounds hp hbound (a i) (b i)
  constructor
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left (hpoint i).1 (hw i hi)
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left (hpoint i).2 (hw i hi)

/-- Uniform positive finite constants work simultaneously for all finite
nonnegative weighted scalar families. -/
theorem exists_finset_sum_scalarBregman_two_sided {p : ℝ} (hp : 1 < p) :
    ∃ m M : ℝ, 0 < m ∧ m ≤ M ∧
      ∀ {ι : Type} (s : Finset ι) (w a b : ι → ℝ),
        (∀ i ∈ s, 0 ≤ w i) →
        m * ∑ i ∈ s, w i * (scalarMazur p (a i) - scalarMazur p (b i)) ^ 2 ≤
            ∑ i ∈ s, w i * scalarBregman p (a i) (b i) ∧
          ∑ i ∈ s, w i * scalarBregman p (a i) (b i) ≤
            M * ∑ i ∈ s, w i * (scalarMazur p (a i) - scalarMazur p (b i)) ^ 2 := by
  obtain ⟨m, M, hm, hmM, hbound⟩ := exists_compactifiedScalarRatio_bounds hp
  refine ⟨m, M, hm, hmM, ?_⟩
  intro ι s w a b hw
  exact finset_sum_scalarBregman_two_sided hp hbound s w a b hw

section SpectralOverlap

variable {ι κ E : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The nonnegative coefficient relating two orthonormal spectral bases.
For rank-one spectral projections this is `Tr(Pᵢ Qⱼ)`. -/
noncomputable def orthonormalBasisOverlap
    (e : OrthonormalBasis ι ℂ E) (f : OrthonormalBasis κ ℂ E)
    (ij : ι × κ) : ℝ :=
  ‖(⟪e ij.1, f ij.2⟫_ℂ)‖ ^ 2

theorem orthonormalBasisOverlap_nonneg
    (e : OrthonormalBasis ι ℂ E) (f : OrthonormalBasis κ ℂ E)
    (ij : ι × κ) :
    0 ≤ orthonormalBasisOverlap e f ij := by
  exact sq_nonneg _

/-- Completeness of the second spectral basis makes each row of overlap
weights sum to one. -/
theorem sum_orthonormalBasisOverlap_right
    (e : OrthonormalBasis ι ℂ E) (f : OrthonormalBasis κ ℂ E) (i : ι) :
    ∑ j, orthonormalBasisOverlap e f (i, j) = 1 := by
  simp only [orthonormalBasisOverlap]
  rw [f.sum_sq_norm_inner_left, e.norm_eq_one, one_pow]

/-- Completeness of the first spectral basis makes each column of overlap
weights sum to one. -/
theorem sum_orthonormalBasisOverlap_left
    (e : OrthonormalBasis ι ℂ E) (f : OrthonormalBasis κ ℂ E) (j : κ) :
    ∑ i, orthonormalBasisOverlap e f (i, j) = 1 := by
  simp only [orthonormalBasisOverlap]
  rw [e.sum_sq_norm_inner_right, f.norm_eq_one, one_pow]

/-- The scalar comparison specialized to the overlap weights of two
orthonormal spectral bases.  Supplying the two trace expansion identities
turns this statement into the Hermitian Bregman--Mazur comparison. -/
theorem orthonormalBasisOverlap_sum_scalarBregman_two_sided
    {p m M : ℝ} (hp : 1 < p)
    (hbound : ∀ x : OnePoint ℝ, m ≤ compactifiedScalarRatio p x ∧
      compactifiedScalarRatio p x ≤ M)
    (e : OrthonormalBasis ι ℂ E) (f : OrthonormalBasis κ ℂ E)
    (a : ι → ℝ) (b : κ → ℝ) :
    m * ∑ ij : ι × κ, orthonormalBasisOverlap e f ij *
          (scalarMazur p (a ij.1) - scalarMazur p (b ij.2)) ^ 2 ≤
        ∑ ij : ι × κ, orthonormalBasisOverlap e f ij *
          scalarBregman p (a ij.1) (b ij.2) ∧
      (∑ ij : ι × κ, orthonormalBasisOverlap e f ij *
          scalarBregman p (a ij.1) (b ij.2)) ≤
        M * ∑ ij : ι × κ, orthonormalBasisOverlap e f ij *
          (scalarMazur p (a ij.1) - scalarMazur p (b ij.2)) ^ 2 := by
  simpa only [Finset.sum_filter, Finset.mem_univ, if_true] using
    finset_sum_scalarBregman_two_sided hp hbound
      (Finset.univ : Finset (ι × κ)) (orthonormalBasisOverlap e f)
      (fun ij ↦ a ij.1) (fun ij ↦ b ij.2)
      (fun ij _ ↦ orthonormalBasisOverlap_nonneg e f ij)

end SpectralOverlap

end HlawkaSchatten
