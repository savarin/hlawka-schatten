/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.SideConeAlgebra

/-! Move from the two SC row coordinates back to arbitrary nonzero scale. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

noncomputable section

private theorem signedPower_positive_scale {q ρ x : ℝ} (hρ : 0 < ρ) :
    signedPower q (ρ*x) = ρ^(q-1) * signedPower q x := by
  have hsg := mul_nonneg_iff_of_pos_left hρ (b := x)
  have hp : |ρ*x|^(q-1) = ρ^(q-1)*|x|^(q-1) := by
    rw [abs_mul, abs_of_pos hρ, Real.mul_rpow hρ.le (abs_nonneg x)]
  by_cases hx : 0 ≤ x <;> simp only [signedPower, hsg, hp, hx, ite_true, ite_false, mul_neg]

private theorem signedPower_negate {q : ℝ} (hq : 1 < q) (x : ℝ) :
    signedPower q (-x) = -signedPower q x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · simp [signedPower, hx.not_ge, neg_nonneg.mpr hx.le]
  · simp [signedPower, Real.zero_rpow (sub_pos.mpr hq).ne']
  · simp [signedPower, hx.le, (neg_lt_zero.mpr hx).not_ge]

private theorem linearRow_scale (e z : Row) (ρ : ℝ) :
    linearRow e (fun i => ρ*z i) = ρ * linearRow e z := by
  simp only [linearRow, Fin.sum_univ_three]
  ring

private theorem argument_scale (η : ℝ) (e z : Row) (ρ : ℝ) :
    argument η e (fun i => ρ*z i) = ρ * argument η e z := by
  simp only [argument, linearRow_scale, Fin.sum_univ_three]
  ring

private theorem feature_positive_scale {q η ρ : ℝ} (hq : 1 < q) (hρ : 0 < ρ)
    (e R d z : Row) : feature q η e R d (fun i => ρ*z i) = ρ^q * feature q η e R d z := by
  have hρq : ρ*ρ^(q-1) = ρ^q := by
    rw [mul_comm, ← Real.rpow_add_one' hρ.le (show q-1+1 ≠ 0 by linarith only [hq])]
    congr 1
    ring
  simp only [feature, linearRow_scale, signedPower_positive_scale hρ, Fin.sum_univ_three,
    abs_mul, abs_of_pos hρ, Real.mul_rpow hρ.le (abs_nonneg _)]
  linear_combination
    (q * linearRow e z *
      (rowWeight η R d 0 * signedPower q (z 0) + rowWeight η R d 1 * signedPower q (z 1) +
        rowWeight η R d 2 * signedPower q (z 2))) * hρq

private theorem feature_negate {q η : ℝ} (hq : 1 < q) (e R d z : Row) :
    feature q η e R d (fun i => -z i) = feature q η e R d z := by
  have hL : linearRow e (fun i => -z i) = -linearRow e z := by
    simpa only [neg_one_mul] using linearRow_scale e z (-1)
  simp only [feature, hL, signedPower_negate hq, Fin.sum_univ_three, abs_neg]
  ring

theorem parameterGap_scale {q a b η ρ : ℝ} (hq : 1 < q) (hρ : ρ ≠ 0) (z : Row) :
    parameterGap q (fun i => ρ*z i) a b η = |ρ|^q * parameterGap q z a b η := by
  have pos {s : ℝ} (hs : 0 < s) (v : Row) :
      parameterGap q (fun i => s*v i) a b η = s^q * parameterGap q v a b η := by
    simp only [parameterGap, parameterArgument, argument_scale, feature_positive_scale hq hs,
      abs_mul, abs_of_pos hs, Real.mul_rpow hs.le (abs_nonneg _), mul_sub]
  rcases hρ.lt_or_gt with hn | hp
  · have harg : parameterArgument (fun i => -z i) a b η = -parameterArgument z a b η := by
      simpa only [parameterArgument, parameterDirection, neg_one_mul] using
        argument_scale η (parameterDirection a b) z (-1)
    have hneg : parameterGap q (fun i => -z i) a b η = parameterGap q z a b η := by
      simp only [parameterGap, feature_negate hq, harg, abs_neg]
    have hscale := pos (neg_pos.mpr hn) (fun i => -z i)
    simpa only [hneg, neg_mul_neg, abs_of_neg hn] using hscale
  · simpa only [abs_of_pos hp] using pos hp z

theorem parameterGap_of_near_ratios {q a b η : ℝ} {z : Row} (hq : 1 < q) (hz : z 0 ≠ 0)
    (h : 0 ≤ parameterGap q (sideRow (-z 1/z 0-1) (-z 2/z 0-1)) a b η) :
    0 ≤ parameterGap q z a b η := by
  let u := -z 1/z 0-1
  let v := -z 2/z 0-1
  have hrow : (fun j => z 0 * sideRow u v j) = z := by
    funext j
    fin_cases j <;> norm_num [sideRow, u, v] <;> field_simp [hz]
  have hscale := parameterGap_scale (a := a) (b := b) (η := η) hq hz (sideRow u v)
  rw [hrow] at hscale
  rw [hscale]
  exact mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) h

end

end HlawkaSchatten.BelowExponent.Vertex
