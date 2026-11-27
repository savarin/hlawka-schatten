/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.VertexWeights

/-! From coefficient second derivatives to the real curvature used on all three vertex collars. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

noncomputable section

def linearFeature (q : ℝ) (d : Row) (h : Fin 3 → Row) (z : Row) : ℝ :=
  (∑ j, d j * |z j|^q) + ∑ i, ∑ j, q * h i j * z i * signedPower q (z j)

theorem feature_eq_linear (q η : ℝ) (e R d z : Row) :
    feature q η e R d z = linearFeature q d (fun i j => (1-e i)*rowWeight η R d j) z := by
  simp only [feature, linearFeature, linearRow, Fin.sum_univ_three]
  ring

private theorem abs_signedPower (q x : ℝ) : |signedPower q x| = |x|^(q-1) := by
  have hp := Real.rpow_nonneg (abs_nonneg x) (q-1)
  unfold signedPower
  split <;> simp [abs_of_nonneg hp]

private theorem pow_mul_abs {q : ℝ} (hq : 1 < q) (x : ℝ) :
    |x|^(q-1) * |x| = |x|^q := by
  rw [← Real.rpow_add_one' (abs_nonneg x) (show q-1+1 ≠ 0 by linarith)]
  congr 1
  ring

private theorem mul_signedPower {q : ℝ} (hq : 1 < q) (x : ℝ) :
    x * signedPower q x = |x|^q := by
  rw [← pow_mul_abs hq x]
  by_cases hx : 0 ≤ x
  · simp [signedPower, hx, abs_of_nonneg hx, mul_comm]
  · simp [signedPower, hx, abs_of_neg (lt_of_not_ge hx), mul_comm]

private theorem row_young {q : ℝ} (hq : 1 < q) (x y : ℝ) :
    q * |x| * |y|^(q-1) ≤ |x|^q + (q-1)*|y|^q := by
  have ht := tangent_signed hq |x| |y|
  simp only [signedPower, ite_eq_left (abs_nonneg y), abs_abs] at ht
  have he := congrArg (fun v : ℝ => q*v) (pow_mul_abs hq y)
  linarith only [ht, he]

private theorem off_diagonal_bound {q : ℝ} (hq : 1 < q) (h x y : ℝ) :
    q*h*x*signedPower q y ≤ |h| * (|x|^q + (q-1)*|y|^q) := calc
  _ = q*(h*x*signedPower q y) := by ring
  _ ≤ q*|h*x*signedPower q y| := mul_le_mul_of_nonneg_left (le_abs_self _) (by linarith)
  _ = |h| * (q * |x| * |y|^(q-1)) := by rw [abs_mul, abs_mul, abs_signedPower]; ring
  _ ≤ _ := mul_le_mul_of_nonneg_left (row_young hq x y) (abs_nonneg h)

/-- For one parameter derivative, its three coefficient upper bounds, before clipping at zero. -/
def curvatureBudget (q : ℝ) (d : Row) (h : Fin 3 → Row) (i : Fin 3) : ℝ :=
  d i + q * h i i + |h i (i+1)| + |h i (i+2)| +
    (q-1) * (|h (i+1) i| + |h (i+2) i|)

theorem linearFeature_le_budget {q : ℝ} (hq : 1 < q) {d K : Row} {h : Fin 3 → Row}
    (hc : ∀ i, curvatureBudget q d h i ≤ K i) (z : Row) :
    linearFeature q d h z ≤ ∑ i, K i * |z i|^q := by
  have diag (i : Fin 3) : q*h i i*z i*signedPower q (z i) = q*h i i*|z i|^q := by
    rw [mul_assoc (q*h i i), mul_signedPower hq]
  have off (i j : Fin 3) := off_diagonal_bound hq (h i j) (z i) (z j)
  have budget (i : Fin 3) := mul_le_mul_of_nonneg_right (hc i) (Real.rpow_nonneg (abs_nonneg (z i)) q)
  have h₀ := budget 0
  have h₁ := budget 1
  have h₂ := budget 2
  norm_num only [curvatureBudget, Fin.reduceAdd] at h₀ h₁ h₂
  simp only [linearFeature, Fin.sum_univ_three, diag]
  linarith only [h₀, h₁, h₂, off 0 1, off 0 2, off 1 0, off 1 2, off 2 0, off 2 1]

/-- Along any coordinate of a parameter box the row depends linearly on its coefficients. -/
theorem hasDerivAt_linearFeature (q x : ℝ) (z : Row) {d : ℝ → Row} {h : ℝ → Fin 3 → Row}
    {d' : Row} {h' : Fin 3 → Row}
    (hd : ∀ i, HasDerivAt (fun t => d t i) (d' i) x)
    (hh : ∀ i j, HasDerivAt (fun t => h t i j) (h' i j) x) :
    HasDerivAt (fun t => linearFeature q (d t) (h t) z) (linearFeature q d' h' z) x := by
  unfold linearFeature
  apply HasDerivAt.add
  · exact HasDerivAt.fun_sum fun i _ => (hd i).mul_const _
  · apply HasDerivAt.fun_sum
    intro i _
    exact HasDerivAt.fun_sum fun j _ => (((hh i j).const_mul q).mul_const _).mul_const _

end
end HlawkaSchatten.BelowExponent.Vertex
