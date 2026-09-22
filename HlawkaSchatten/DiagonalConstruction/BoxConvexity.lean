/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import HlawkaSchatten.DiagonalConstruction.BoxHessian
import HlawkaSchatten.DiagonalConstruction.OrbitAveraging
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.Module

/-! # Convexity of the sharp deficit on the cyclic box -/

namespace HlawkaSchatten.DiagonalConstruction

noncomputable def deficitSlope (p K : ℝ) (X Z : Triple) : ℝ :=
  (2 * K - 1) * (∑ j, normSlope p (X j) (Z j)) +
    normSlope p (totalTriple X) (totalTriple Z) -
      K * (∑ j, normSlope p (pairTriple X j) (pairTriple Z j))

theorem tripleDeficit_eq_sums (p K : ℝ) (X : Triple) :
    tripleDeficit p K X = (2 * K - 1) * (∑ j, lpNorm p (X j)) +
      lpNorm p (totalTriple X) - K * (∑ j, lpNorm p (pairTriple X j)) := by
  simp only [tripleDeficit, hlawkaDeficit, totalTriple_eq, pairTriple, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  ring

theorem totalTriple_add_smul (X Z : Triple) (t : ℝ) :
    totalTriple (X + t • Z) = totalTriple X + t • totalTriple Z := by
  simp [totalTriple, Finset.sum_add_distrib, Finset.smul_sum]

theorem pairTriple_add_smul (X Z : Triple) (t : ℝ) :
    pairTriple (X + t • Z) = pairTriple X + t • pairTriple Z := by
  ext j i
  fin_cases j <;> simp [pairTriple] <;> ring

theorem hasDerivAt_tripleDeficit_line {p : ℝ} (hp : 1 < p) (K : ℝ) (X Z : Triple) (t : ℝ)
    (ht : X + t • Z ∈ entryBox) :
    HasDerivAt (fun s : ℝ ↦ tripleDeficit p K (X + s • Z))
      (deficitSlope p K (X + t • Z) Z) t := by
  have hcol (j : Fin 3) := hasDerivAt_lpNorm_line hp (X j) (Z j) t
    (entryBox_column_ne_zero ht j)
  have htotal := hasDerivAt_lpNorm_line hp (totalTriple X) (totalTriple Z) t
    (by rw [← totalTriple_add_smul]; exact entryBox_total_ne_zero ht)
  have hpair (j : Fin 3) := hasDerivAt_lpNorm_line hp (pairTriple X j) (pairTriple Z j) t
    (by change (pairTriple X + t • pairTriple Z) j ≠ 0
        rw [← pairTriple_add_smul]; exact entryBox_pair_ne_zero ht j)
  have h := (((HasDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦ hcol j)).const_mul (2 * K - 1)).add
    htotal).sub ((HasDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦ hpair j)).const_mul K)
  convert! h using 1 <;>
    simp only [tripleDeficit_eq_sums, deficitSlope, totalTriple_add_smul, pairTriple_add_smul,
      Pi.add_apply, Pi.smul_apply]
  rfl

theorem hasDerivAt_deficitSlope_line {p : ℝ} (hp : 4 < p) (K : ℝ) (X Z : Triple) (t : ℝ)
    (ht : X + t • Z ∈ entryBox) :
    HasDerivAt (fun s : ℝ ↦ deficitSlope p K (X + s • Z) Z)
      (deficitHessian p K (X + t • Z) Z) t := by
  have hcol (j : Fin 3) := hasDerivAt_normSlope_line hp (X j) (Z j) t
    (entryBox_column_ne_zero ht j)
  have htotal := hasDerivAt_normSlope_line hp (totalTriple X) (totalTriple Z) t
    (by rw [← totalTriple_add_smul]; exact entryBox_total_ne_zero ht)
  have hpair (j : Fin 3) := hasDerivAt_normSlope_line hp (pairTriple X j) (pairTriple Z j) t
    (by change (pairTriple X + t • pairTriple Z) j ≠ 0
        rw [← pairTriple_add_smul]; exact entryBox_pair_ne_zero ht j)
  have h := (((HasDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦ hcol j)).const_mul (2 * K - 1)).add
    htotal).sub ((HasDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦ hpair j)).const_mul K)
  convert! h using 1 <;>
    simp only [deficitSlope, deficitHessian, totalTriple_add_smul, pairTriple_add_smul,
      Pi.add_apply, Pi.smul_apply]
  rfl

theorem continuous_tripleDeficit {p : ℝ} (hp : 0 < p) (K : ℝ) :
    Continuous (tripleDeficit p K) := by
  have hc (j : Fin 3) : Continuous (fun X : Triple ↦ lpNorm p (X j)) :=
    (continuous_lpNorm hp).comp (continuous_apply j)
  have ht : Continuous (fun X : Triple ↦ lpNorm p (X 0 + X 1 + X 2)) :=
    (continuous_lpNorm hp).comp
      (((continuous_apply 0).add (continuous_apply 1)).add (continuous_apply 2))
  have hpairs (j k : Fin 3) : Continuous (fun X : Triple ↦ lpNorm p (X j + X k)) :=
    (continuous_lpNorm hp).comp ((continuous_apply j).add (continuous_apply k))
  exact ((continuous_const.mul (((hc 0).add (hc 1)).add (hc 2))).add ht).sub
    (continuous_const.mul (((hpairs 0 1).add (hpairs 0 2)).add (hpairs 1 2)))

theorem convexOn_tripleDeficit {p K : ℝ} (hp : 256 ≤ p) (hK : 1 ≤ K) (hKp : K ≤ p) :
    ConvexOn ℝ entryBox (tripleDeficit p K) := by
  refine ⟨convex_entryBox, ?_⟩
  intro X hX Y hY a b ha hb hab
  let Z := Y - X
  have hline (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : X + t • Z ∈ entryBox := by
    have he : X + t • Z = (1 - t) • X + t • Y := by
      dsimp [Z]
      module
    rw [he]
    exact convex_entryBox hX hY (by linarith [ht.2]) ht.1 (by ring)
  have hcont : Continuous (fun t : ℝ ↦ tripleDeficit p K (X + t • Z)) :=
    (continuous_tripleDeficit (by linarith : 0 < p) K).comp
      (continuous_const.add (continuous_id.smul continuous_const))
  have hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun t : ℝ ↦ tripleDeficit p K (X + t • Z)) := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 1) hcont.continuousOn
      (f' := fun t ↦ deficitSlope p K (X + t • Z) Z)
      (f'' := fun t ↦ deficitHessian p K (X + t • Z) Z)
    · intro t ht
      exact (hasDerivAt_tripleDeficit_line (by linarith : 1 < p) K X Z t
        (hline t (interior_subset ht))).hasDerivWithinAt
    · intro t ht
      exact (hasDerivAt_deficitSlope_line (by linarith : 4 < p) K X Z t
        (hline t (interior_subset ht))).hasDerivWithinAt
    · intro t ht
      exact deficitHessian_nonneg hp hK hKp (hline t (interior_subset ht)) Z
  have h := hconv.2 (show (0 : ℝ) ∈ Set.Icc 0 1 by norm_num)
    (show (1 : ℝ) ∈ Set.Icc 0 1 by norm_num) ha hb hab
  have hpoint : X + b • Z = a • X + b • Y := by
    have haeq : a = 1 - b := by linarith
    rw [haeq]
    dsimp [Z]
    module
  simpa only [smul_eq_mul, mul_zero, mul_one, zero_add, zero_smul, add_zero, one_smul,
    Z, add_sub_cancel, hpoint] using h

/-- The sharp cyclic constant bounds every finite real coordinate space. -/
theorem real_hlawka_bound {p : ℝ} (hp : 256 ≤ p) {ι : Type*} [Fintype ι] :
    HasHlawkaConstant (lpNorm p : (ι → ℝ) → ℝ) (cyclicConstant p) := by
  have hp1 : 1 < p := by linarith
  exact real_bound_of_box_convex hp
    (convexOn_tripleDeficit hp (one_le_cyclicConstant hp1) (cyclicConstant_le_exponent hp1))

end HlawkaSchatten.DiagonalConstruction
