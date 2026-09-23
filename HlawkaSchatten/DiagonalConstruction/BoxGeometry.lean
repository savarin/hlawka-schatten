/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import HlawkaSchatten.DiagonalConstruction.Localization

/-!
# Quadratic geometry of the cyclic box

The joint radial estimate bounds the squared Frobenius residual by `300`
times the sum of squared singleton-norm residuals. This constant controls
the trade-off between singleton and total-norm Hessians; its looseness is
absorbed by the curvature margin, which has order 10¹¹ at p = 256.
-/

namespace HlawkaSchatten.DiagonalConstruction

/-- The squared Euclidean norm of a 3-vector. -/
def euclideanSq (v : Fin 3 → ℝ) : ℝ := ∑ i, (v i) ^ 2

/-- The squared Frobenius norm of a triple. -/
def frobeniusSq (X : Triple) : ℝ := ∑ j, euclideanSq (X j)

/-- Applying a coefficient vector to a triple: `Σ a_j X_j`. -/
def applyTriple (X : Triple) (a : Fin 3 → ℝ) : Fin 3 → ℝ := fun i ↦ ∑ j, a j * X j i

/-- The column-sum vector `X_0 + X_1 + X_2`. -/
def totalTriple (X : Triple) : Fin 3 → ℝ := ∑ j, X j

/-- The squared Euclidean norm is nonneg. -/
theorem euclideanSq_nonneg (v : Fin 3 → ℝ) : 0 ≤ euclideanSq v :=
  Finset.sum_nonneg fun i _ ↦ sq_nonneg (v i)

/-- The squared Frobenius norm is nonneg. -/
theorem frobeniusSq_nonneg (X : Triple) : 0 ≤ frobeniusSq X :=
  Finset.sum_nonneg fun j _ ↦ euclideanSq_nonneg (X j)

/-- Triangle inequality for squared Euclidean norms. -/
theorem euclideanSq_add_le (u v : Fin 3 → ℝ) :
    euclideanSq (u + v) ≤ 2 * euclideanSq u + 2 * euclideanSq v := by
  simp only [euclideanSq, Finset.mul_sum, ← Finset.sum_add_distrib, Pi.add_apply]
  exact Finset.sum_le_sum fun i _ ↦ by nlinarith [sq_nonneg (u i - v i)]

/-- The squared norm is invariant under negation. -/
theorem euclideanSq_neg (v : Fin 3 → ℝ) : euclideanSq (-v) = euclideanSq v := by
  simp [euclideanSq]

/-- Bound on `‖u - v‖²` in terms of `‖u‖²` and `‖v‖²`. -/
theorem euclideanSq_sub_le (u v : Fin 3 → ℝ) :
    euclideanSq (u - v) ≤ 2 * euclideanSq u + 2 * euclideanSq v := by
  simpa only [sub_eq_add_neg, euclideanSq_neg] using euclideanSq_add_le u (-v)

/-- The squared norm scales quadratically. -/
theorem euclideanSq_smul (a : ℝ) (v : Fin 3 → ℝ) :
    euclideanSq (a • v) = a ^ 2 * euclideanSq v := by
  simp only [euclideanSq, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

/-- The total vector's squared norm is at most `3 · ‖X‖_F²`. -/
theorem euclideanSq_total_le (X : Triple) : euclideanSq (totalTriple X) ≤ 3 * frobeniusSq X := by
  have hi (i : Fin 3) : ((∑ j, X j i) ^ 2) ≤ 3 * ∑ j, (X j i) ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin 3 ↦ (1 : ℝ)) (fun j ↦ X j i)
  calc
    _ ≤ ∑ i, 3 * ∑ j, (X j i) ^ 2 := Finset.sum_le_sum fun i _ ↦ hi i
    _ = _ := by
      simp only [frobeniusSq, euclideanSq, ← Finset.mul_sum]
      rw [Finset.sum_comm]

/-- Lower bound on the squared norm of a signed combination at the center. -/
theorem euclideanSq_center_lower (a : Fin 3 → ℝ) :
    euclideanSq a ≤ euclideanSq (applyTriple cyclicCenter a) := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin 3 ↦ (1 : ℝ)) a
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_ofNat, mul_one] at hc
  have he : euclideanSq (applyTriple cyclicCenter a) = 4 * euclideanSq a - (∑ i, a i) ^ 2 := by
    have heq : applyTriple cyclicCenter a =
        ![-a 0 + a 1 + a 2, a 0 - a 1 + a 2, a 0 + a 1 - a 2] := by
      ext i
      fin_cases i <;>
        norm_num [applyTriple, cyclicCenter, Fin.sum_univ_three, Fin.ext_iff] <;> ring!
    rw [heq]
    simp only [euclideanSq, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    ring!
  rw [he]
  change (∑ i, a i) ^ 2 ≤ 3 * euclideanSq a at hc
  linarith

/-- Upper bound on the perturbation squared norm inside the box. -/
theorem euclideanSq_perturbation_upper {X : Triple} (hX : X ∈ entryBox) (a : Fin 3 → ℝ) :
    euclideanSq (applyTriple (X - cyclicCenter) a) ≤ (57 / 100 : ℝ) ^ 2 * euclideanSq a := by
  have hrow (i : Fin 3) : (∑ j, (X j i - cyclicCenter j i) ^ 2) ≤ 3 * (19 / 100 : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ _ : Fin 3, (19 / 100 : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by norm_num)).mpr (hX j i)
      _ = _ := by simp
  have hi (i : Fin 3) : (∑ j, a j * (X j i - cyclicCenter j i)) ^ 2 ≤
      euclideanSq a * (3 * (19 / 100 : ℝ) ^ 2) := by
    exact (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a (fun j ↦ X j i - cyclicCenter j i)).trans
      (mul_le_mul_of_nonneg_left (hrow i) (euclideanSq_nonneg a))
  calc
    _ ≤ ∑ _ : Fin 3, euclideanSq a * (3 * (19 / 100 : ℝ) ^ 2) :=
      Finset.sum_le_sum fun i _ ↦ hi i
    _ = _ := by simp; ring

/-- Uniform invertibility, expressed entirely with sums of squares. -/
theorem euclideanSq_apply_lower {X : Triple} (hX : X ∈ entryBox) (a : Fin 3 → ℝ) :
    (43 / 100 : ℝ) ^ 2 * euclideanSq a ≤ euclideanSq (applyTriple X a) := by
  let u := applyTriple cyclicCenter a
  let v := applyTriple (X - cyclicCenter) a
  have heq : applyTriple X a = u + v := by
    ext i
    simp only [u, v, applyTriple, Pi.sub_apply, Pi.add_apply, mul_sub, Finset.sum_sub_distrib]
    ring
  have hid : (57 / 100 : ℝ) * euclideanSq (u + v) - (2451 / 10000 : ℝ) * euclideanSq u +
      (43 / 100 : ℝ) * euclideanSq v = euclideanSq ((57 / 100 : ℝ) • u + v) := by
    simp only [euclideanSq, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have hnon := euclideanSq_nonneg ((57 / 100 : ℝ) • u + v)
  have hu : euclideanSq a ≤ euclideanSq u := euclideanSq_center_lower a
  have hv : euclideanSq v ≤ (57 / 100 : ℝ) ^ 2 * euclideanSq a :=
    euclideanSq_perturbation_upper hX a
  rw [heq]
  nlinarith

/-- Upper bound on `‖X_j‖²` inside the box. -/
theorem euclideanSq_column_upper {X : Triple} (hX : X ∈ entryBox) (j : Fin 3) :
    euclideanSq (X j) ≤ 3 * (119 / 100 : ℝ) ^ 2 := by
  have hi (i : Fin 3) : |X j i| ≤ 119 / 100 := by
    have hh := abs_le.mp (hX j i)
    have hc : cyclicCenter j i = -1 ∨ cyclicCenter j i = 1 := by
      simp only [cyclicCenter]; split_ifs <;> simp
    apply abs_le.mpr
    rcases hc with hc | hc <;> rw [hc] at hh <;> constructor <;> linarith
  calc
    _ ≤ ∑ _ : Fin 3, (119 / 100 : ℝ) ^ 2 := Finset.sum_le_sum fun i _ ↦ by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by norm_num)).mpr (hi i)
    _ = _ := by simp

/-- The total residual controls the independent radial directions of the columns. -/
theorem joint_radial_residual_bound {X : Triple} (hX : X ∈ entryBox) (Z : Triple)
    (a : Fin 3 → ℝ) (b : ℝ) :
    frobeniusSq (Z - b • X) ≤ 300 *
      (frobeniusSq (fun j ↦ Z j - a j • X j) +
        euclideanSq (totalTriple Z - b • totalTriple X)) := by
  let U : Triple := fun j ↦ Z j - a j • X j
  let c : Fin 3 → ℝ := fun j ↦ a j - b
  let D := totalTriple Z - b • totalTriple X
  have he : applyTriple X c = D - totalTriple U := by
    ext i
    simp only [applyTriple, c, D, totalTriple, U, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  have hinv := euclideanSq_apply_lower hX c
  rw [he] at hinv
  have hD := euclideanSq_sub_le D (totalTriple U)
  have hU := euclideanSq_total_le U
  have hcol (j : Fin 3) : euclideanSq ((Z - b • X) j) ≤
      2 * euclideanSq (U j) + 2 * ((a j - b) ^ 2 * (3 * (119 / 100 : ℝ) ^ 2)) := by
    have hh : (Z - b • X) j = U j + (a j - b) • X j := by
      ext i
      simp only [U, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply]
      ring
    rw [hh]
    have h := euclideanSq_add_le (U j) ((a j - b) • X j)
    rw [euclideanSq_smul] at h
    have hm := mul_le_mul_of_nonneg_left (euclideanSq_column_upper hX j) (sq_nonneg (a j - b))
    linarith
  have hbound : frobeniusSq (Z - b • X) ≤
      2 * frobeniusSq U + (6 * (119 / 100 : ℝ) ^ 2) * euclideanSq c := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hcol j)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul] at hh
    change frobeniusSq (Z - b • X) ≤
      2 * frobeniusSq U + 2 * (euclideanSq c * (3 * (119 / 100 : ℝ) ^ 2)) at hh
    nlinarith
  have hUne := frobeniusSq_nonneg U
  have hDne := euclideanSq_nonneg D
  change frobeniusSq (Z - b • X) ≤ 300 * (frobeniusSq U + euclideanSq D)
  nlinarith

end HlawkaSchatten.DiagonalConstruction
