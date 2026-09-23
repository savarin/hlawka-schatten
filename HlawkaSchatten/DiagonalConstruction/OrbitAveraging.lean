/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import HlawkaSchatten.DiagonalConstruction.Localization
import HlawkaSchatten.DiagonalConstruction.DimensionReduction

/-! # Simultaneous permutation averaging on the cyclic box -/

namespace HlawkaSchatten.DiagonalConstruction

/-- The entry box is convex. -/
theorem convex_entryBox : Convex ℝ entryBox := by
  intro X hX Y hY a b ha hb hab j i
  have heq : (a • X + b • Y) j i - cyclicCenter j i =
      a * (X j i - cyclicCenter j i) + b * (Y j i - cyclicCenter j i) := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [congrArg (fun t : ℝ ↦ t * cyclicCenter j i) hab]
  rw [heq]
  calc
    _ ≤ |a * (X j i - cyclicCenter j i)| + |b * (Y j i - cyclicCenter j i)| := abs_add_le _ _
    _ = a * |X j i - cyclicCenter j i| + b * |Y j i - cyclicCenter j i| := by
      rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * (19 / 100) + b * (19 / 100) :=
      add_le_add (mul_le_mul_of_nonneg_left (hX j i) ha)
        (mul_le_mul_of_nonneg_left (hY j i) hb)
    _ = 19 / 100 := by nlinarith

/-- Permute both row and column indices of a triple. -/
def conjugate (e : Equiv.Perm (Fin 3)) (X : Triple) : Triple :=
  fun j i ↦ X (e j) (e i)

/-- Conjugation preserves the entry box. -/
theorem conjugate_mem_entryBox (e : Equiv.Perm (Fin 3)) {X : Triple} (hX : X ∈ entryBox) :
    conjugate e X ∈ entryBox := by
  intro j i
  simpa [conjugate, cyclicCenter, e.injective.eq_iff] using hX (e j) (e i)

private def permutations : Fin 6 → Equiv.Perm (Fin 3) :=
  ![Equiv.refl _, Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 1 2,
    (Equiv.swap 0 1).trans (Equiv.swap 1 2), (Equiv.swap 1 2).trans (Equiv.swap 0 1)]

private theorem tripleDeficit_conjugate_six (p K : ℝ) (X : Triple) (k : Fin 6) :
    tripleDeficit p K (conjugate (permutations k) X) = tripleDeficit p K X := by
  have he (e : Equiv.Perm (Fin 3)) :
      tripleDeficit p K (conjugate e X) = hlawkaDeficit p K (X (e 0)) (X (e 1)) (X (e 2)) := by
    have hsum (u v : Fin 3 → ℝ) : u ∘ e + v ∘ e = (u + v) ∘ e := rfl
    change hlawkaDeficit p K (X (e 0) ∘ e) (X (e 1) ∘ e) (X (e 2) ∘ e) = _
    simp only [hlawkaDeficit, hsum, lpNorm_comp_equiv]
  rw [he]
  fin_cases k <;> simp [permutations, tripleDeficit, hlawkaDeficit, Equiv.swap_apply_def,
    add_comm, add_left_comm, add_assoc]

/-- The orbit average over the six column permutations. -/
noncomputable def orbitAverage (X : Triple) : Triple :=
  ∑ k : Fin 6, (1 / 6 : ℝ) • conjugate (permutations k) X

/-- The average diagonal entry of a triple. -/
noncomputable def averageDiagonal (X : Triple) : ℝ := (X 0 0 + X 1 1 + X 2 2) / 3

/-- The average off-diagonal entry of a triple. -/
noncomputable def averageOffDiagonal (X : Triple) : ℝ :=
  (X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1) / 6

/-- The orbit average is constant on diagonal and off-diagonal entries. -/
theorem orbitAverage_apply (X : Triple) (j i : Fin 3) :
    orbitAverage X j i = if i = j then averageDiagonal X else averageOffDiagonal X := by
  fin_cases j <;> fin_cases i <;>
    norm_num [orbitAverage, permutations, conjugate, Fin.sum_univ_succ, Equiv.swap_apply_def,
      averageDiagonal, averageOffDiagonal, Fin.ext_iff] <;> ring!

/-- The orbit average stays in the entry box. -/
theorem orbitAverage_mem_entryBox {X : Triple} (hX : X ∈ entryBox) : orbitAverage X ∈ entryBox := by
  apply convex_entryBox.sum_mem (t := Finset.univ)
  · intros; norm_num
  · norm_num
  · intro k _
    exact conjugate_mem_entryBox _ hX

/-- Averaging does not increase the deficit when it is convex. -/
theorem tripleDeficit_orbitAverage_le {p K : ℝ}
    (hc : ConvexOn ℝ entryBox (tripleDeficit p K)) {X : Triple} (hX : X ∈ entryBox) :
    tripleDeficit p K (orbitAverage X) ≤ tripleDeficit p K X := by
  have h := hc.map_sum_le (t := Finset.univ) (w := fun _ : Fin 6 ↦ (1 / 6 : ℝ))
    (p := fun k ↦ conjugate (permutations k) X) (by intros; norm_num) (by norm_num)
    (fun _ _ ↦ conjugate_mem_entryBox _ hX)
  change tripleDeficit p K (orbitAverage X) ≤ _ at h
  simp only [tripleDeficit_conjugate_six, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, nsmul_eq_mul] at h
  norm_num at h
  linarith

/-- The orbit average's parameter `t = -d/o` lies in `[1/2, 2]`. -/
theorem average_parameter_bounds {X : Triple} (hX : X ∈ entryBox) :
    0 < averageOffDiagonal X ∧ -averageDiagonal X / averageOffDiagonal X ∈ Set.Icc (1 / 2) 2 := by
  have hbar := orbitAverage_mem_entryBox hX
  have hd := hbar 0 0
  have ho := hbar 0 1
  rw [orbitAverage_apply] at hd ho
  norm_num [cyclicCenter, abs_le] at hd ho
  have hop : 0 < averageOffDiagonal X := by linarith
  exact ⟨hop, (le_div_iff₀ hop).mpr (by linarith), (div_le_iff₀ hop).mpr (by linarith)⟩

/-- The orbit average is a scaled cyclic triple. -/
theorem orbitAverage_eq_cyclic (X : Triple) (ho : averageOffDiagonal X ≠ 0) :
    orbitAverage X = ![averageOffDiagonal X • cyclicX (-averageDiagonal X / averageOffDiagonal X),
      averageOffDiagonal X • cyclicY (-averageDiagonal X / averageOffDiagonal X),
      averageOffDiagonal X • cyclicZ (-averageDiagonal X / averageOffDiagonal X)] := by
  ext j i
  rw [orbitAverage_apply]
  fin_cases j <;> fin_cases i <;> norm_num [cyclicX, cyclicY, cyclicZ] <;> field_simp

/-- The deficit of the orbit average is nonneg. -/
theorem tripleDeficit_orbitAverage_nonneg {p : ℝ} (hp : 1 < p) {X : Triple} (hX : X ∈ entryBox) :
    0 ≤ tripleDeficit p (cyclicConstant p) (orbitAverage X) := by
  obtain ⟨ho, ht⟩ := average_parameter_bounds hX
  let t := -averageDiagonal X / averageOffDiagonal X
  have ht0 : 0 ≤ t := by dsimp [t]; linarith [ht.1]
  have hratio := cyclicRatio_le_constant hp ht
  have hD := cyclic_denominator_pos hp ht0
  rw [cyclicRatio, div_le_iff₀ hD] at hratio
  have hcyclic : 0 ≤ hlawkaDeficit p (cyclicConstant p) (cyclicX t) (cyclicY t) (cyclicZ t) := by
    rw [hlawkaDeficit_eq, cyclic_tripleGap (zero_lt_one.trans hp) ht0, cyclic_pairGapSum ht0]
    exact sub_nonneg.mpr hratio
  rw [orbitAverage_eq_cyclic X ho.ne']
  change 0 ≤ hlawkaDeficit p (cyclicConstant p) (averageOffDiagonal X • cyclicX t)
    (averageOffDiagonal X • cyclicY t) (averageOffDiagonal X • cyclicZ t)
  rw [hlawkaDeficit_smul (zero_lt_one.trans hp)]
  exact mul_nonneg (abs_nonneg _) hcyclic

/-- Nonnegativity of the deficit from convexity and orbit averaging. -/
theorem tripleDeficit_nonneg_of_convex {p : ℝ} (hp : 1 < p)
    (hc : ConvexOn ℝ entryBox (tripleDeficit p (cyclicConstant p)))
    {X : Triple} (hX : X ∈ entryBox) : 0 ≤ tripleDeficit p (cyclicConstant p) X :=
  (tripleDeficit_orbitAverage_nonneg hp hX).trans (tripleDeficit_orbitAverage_le hc hX)

/-- This isolates the remaining analytic input: convexity on the fixed box. -/
theorem real_bound_of_box_convex {p : ℝ} (hp : 256 ≤ p)
    (hc : ConvexOn ℝ entryBox (tripleDeficit p (cyclicConstant p)))
    {ι : Type*} [Fintype ι] : HasHlawkaConstant (lpNorm p : (ι → ℝ) → ℝ) (cyclicConstant p) := by
  have hp1 : 1 < p := by linarith
  apply real_bound_of_fin_three hp1 (by linarith [one_le_cyclicConstant hp1])
  intro x y z
  by_contra hn
  have hf : hlawkaDeficit p (cyclicConstant p) x y z < 0 := by
    rw [hlawkaDeficit_eq]
    linarith
  obtain ⟨X, hX, hneg⟩ := exists_failure_in_entryBox hp x y z hf
  exact (not_lt_of_ge (tripleDeficit_nonneg_of_convex hp1 hc hX)) hneg

end HlawkaSchatten.DiagonalConstruction
