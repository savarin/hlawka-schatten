/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import HlawkaSchatten.DiagonalConstruction.BoxGeometry

/-! # Coordinate ranges of the seven vectors on the cyclic box -/

namespace HlawkaSchatten.DiagonalConstruction

/-- Pair sums indexed by the omitted column. -/
def pairTriple (X : Triple) : Triple := ![X 1 + X 2, X 0 + X 2, X 0 + X 1]

theorem totalTriple_eq (X : Triple) : totalTriple X = X 0 + X 1 + X 2 := by
  simp [totalTriple, Fin.sum_univ_three]

theorem entryBox_column_bounds {X : Triple} (hX : X ∈ entryBox) (j i : Fin 3) :
    81 / 100 ≤ |X j i| ∧ |X j i| ≤ 119 / 100 := by
  have h := abs_le.mp (hX j i)
  by_cases hij : i = j
  · simp only [cyclicCenter, if_pos hij] at h
    rw [abs_of_neg (by linarith : X j i < 0)]
    constructor <;> linarith
  · simp only [cyclicCenter, if_neg hij] at h
    rw [abs_of_pos (by linarith : 0 < X j i)]
    constructor <;> linarith

theorem entryBox_total_bounds {X : Triple} (hX : X ∈ entryBox) (i : Fin 3) :
    43 / 100 ≤ totalTriple X i ∧ totalTriple X i ≤ 157 / 100 := by
  have h0 := abs_le.mp (hX 0 i)
  have h1 := abs_le.mp (hX 1 i)
  have h2 := abs_le.mp (hX 2 i)
  rw [totalTriple_eq]
  simp only [Pi.add_apply]
  fin_cases i <;> norm_num [cyclicCenter, Fin.ext_iff] at h0 h1 h2 ⊢ <;>
    constructor <;> linarith!

theorem entryBox_pair_large {X : Triple} (hX : X ∈ entryBox) (j : Fin 3) :
    81 / 50 ≤ |pairTriple X j j| := by
  have h0 := abs_le.mp (hX 0 j)
  have h1 := abs_le.mp (hX 1 j)
  have h2 := abs_le.mp (hX 2 j)
  have hl : 81 / 50 ≤ pairTriple X j j := by
    fin_cases j <;> norm_num [pairTriple, cyclicCenter, Fin.ext_iff] at h0 h1 h2 ⊢ <;>
      linarith!
  exact hl.trans (le_abs_self _)

theorem entryBox_pair_small {X : Triple} (hX : X ∈ entryBox) (j i : Fin 3) (hij : i ≠ j) :
    |pairTriple X j i| ≤ 19 / 50 := by
  have h0 := abs_le.mp (hX 0 i)
  have h1 := abs_le.mp (hX 1 i)
  have h2 := abs_le.mp (hX 2 i)
  fin_cases j <;> fin_cases i <;> first
  | exact (hij rfl).elim
  | norm_num [pairTriple, cyclicCenter, Fin.ext_iff, abs_le] at h0 h1 h2 ⊢
    constructor <;> linarith!

theorem entryBox_column_ne_zero {X : Triple} (hX : X ∈ entryBox) (j : Fin 3) : X j ≠ 0 := by
  intro he
  have h := (entryBox_column_bounds hX j 0).1
  norm_num [he] at h

theorem entryBox_total_ne_zero {X : Triple} (hX : X ∈ entryBox) : totalTriple X ≠ 0 := by
  intro he
  have h := (entryBox_total_bounds hX 0).1
  norm_num [he] at h

theorem entryBox_pair_ne_zero {X : Triple} (hX : X ∈ entryBox) (j : Fin 3) :
    pairTriple X j ≠ 0 := by
  intro he
  have h := entryBox_pair_large hX j
  norm_num [he] at h

theorem euclideanSq_pairs_le (X : Triple) :
    (∑ j, euclideanSq (pairTriple X j)) ≤ 4 * frobeniusSq X := by
  have he : (∑ j, euclideanSq (pairTriple X j)) = frobeniusSq X + euclideanSq (totalTriple X) := by
    rw [totalTriple_eq]
    simp only [pairTriple, frobeniusSq, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    simp only [euclideanSq, Pi.add_apply, Fin.sum_univ_three]
    ring
  rw [he]
  linarith [euclideanSq_total_le X]

end HlawkaSchatten.DiagonalConstruction
