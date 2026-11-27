/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Bulk
public import HlawkaSchatten.BelowExponent.Coverage
public import HlawkaSchatten.BelowExponent.VertexCurvature

/-! The normalized coefficient inequality gives the physical row inequality in all three vertex
collars. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

noncomputable section

/-- The arguments e are in row order, so the profile coordinates use their reverse order. -/
def profile (ε : ℝ) (e : Row) : Profile := ![1-ε, ε * e 2, ε * e 1, ε * e 0]

def linearRow (e z : Row) : ℝ := ∑ j, (1-e j) * z j

def shift (ε : ℝ) (e x : Row) : Row := fun j => x j - ε * linearRow e x

def signedPower (q z : ℝ) : ℝ := if 0 ≤ z then |z|^(q-1) else -|z|^(q-1)

def rowWeight (η : ℝ) (R d : Row) (j : Fin 3) : ℝ := (1+2*η) * R j + η * d j

def argument (η : ℝ) (e z : Row) : ℝ := (∑ j, z j) + 2 * η * linearRow e z

def feature (q η : ℝ) (e R d z : Row) : ℝ :=
  (∑ j, d j * |z j|^q) + q * linearRow e z * ∑ j, rowWeight η R d j * signedPower q (z j)

/-- The supporting line on the whole real axis, including its zero anchor. -/
theorem tangent_signed {q : ℝ} (hq : 1 < q) (x z : ℝ) :
    |z|^q + q * (x-z) * signedPower q z ≤ |x|^q := by
  rcases lt_trichotomy z 0 with hz | rfl | hz
  · have h := tangent_le_rpow hq.le (abs_pos.mpr hz.ne) (abs_nonneg x)
    have hc := mul_nonneg (show 0 ≤ q * |z|^(q-1) by positivity) (show 0 ≤ |x| + x by linarith only [neg_le_abs x])
    simp only [signedPower, ite_eq_right (not_le.mpr hz)]
    rw [abs_of_neg hz] at *
    nlinarith only [h, hc]
  · simp [signedPower, Real.zero_rpow (ne_of_gt (sub_pos.mpr hq)),
      Real.zero_rpow (ne_of_gt (zero_lt_one.trans hq)), Real.rpow_nonneg (abs_nonneg x)]
  · have h := tangent_le_rpow hq.le (abs_pos.mpr hz.ne') (abs_nonneg x)
    have hc := mul_nonneg (show 0 ≤ q * |z|^(q-1) by positivity) (sub_nonneg.mpr (le_abs_self x))
    simp only [signedPower, ite_eq_left hz.le]
    rw [abs_of_pos hz] at *
    nlinarith only [h, hc]

private theorem shift_inverse {η ε : ℝ} {e : Row} (he : ∑ j, e j = 1)
    (hdepth : η * (1-2*ε) = ε) (x : Row) :
    η * linearRow e (shift ε e x) = ε * linearRow e x := by
  have hs : ∑ j : Fin 3, (1-e j) = 2 := by
    rw [Finset.sum_sub_distrib, he]
    norm_num
  have h : linearRow e (shift ε e x) = (1-2*ε) * linearRow e x := by
    unfold shift linearRow
    simp_rw [mul_sub, ← mul_assoc]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul, hs]
    ring
  rw [h, ←mul_assoc, hdepth]

/-- The three light rows share a translation. The heavy row is affine in the shifted variables. -/
theorem rowEval_eq {η ε : ℝ} {e : Row} (he : ∑ j, e j = 1)
    (hdepth : η * (1-2*ε) = ε) (x : Row) (s : Fin 4) :
    rowEval (profile ε e) s x =
      ![argument η e (shift ε e x), shift ε e x 2, shift ε e x 1, shift ε e x 0] s := by
  have he₂ : e 2 = 1 - e 0 - e 1 := by
    rw [Fin.sum_univ_three] at he
    linarith
  have harg : argument η e (shift ε e x) = (∑ j, x j) - ε * linearRow e x := by
    unfold argument
    rw [mul_assoc, shift_inverse he hdepth]
    simp [Fin.sum_univ_three, shift]
    ring
  rw [harg]
  fin_cases s <;> norm_num [rowEval, partner, sign, shift, profile, linearRow, Fin.sum_univ_three, he₂] <;> ring

/-- Exact normalized coefficient and row tests suffice for the original, unshifted row condition. -/
theorem rowAt_of_normalized {q ε η lam : ℝ} {e R d : Row}
    (hq : 1 < q) (he : ∑ j, e j = 1) (hη : 0 ≤ η) (hlam : 0 < lam)
    (hdepth : η * (1-2*ε) = ε) (hR : ∀ j, 0 ≤ R j)
    (hd : ∑ j, d j = 1) (hG : ∀ j, 0 ≤ rowWeight η R d j)
    (hn : lam * (η + (1+2*η) * ∑ j, R j) = 1)
    (hcoeff : ∀ z : Row, |argument η e z|^q ≤ feature q η e R d z) :
    RowAt q (profile ε e) := by
  let n := 1+2*η
  let π : Profile := ![lam*η, lam*n*R 2, lam*n*R 1, lam*n*R 0]
  have hn₀ : 0 ≤ n := by dsimp [n]; positivity
  refine ⟨π, ⟨?_, ?_⟩, fun j => lam*rowWeight η R d j, ?_, ?_, ?_⟩
  · intro s
    fin_cases s
    · exact mul_nonneg hlam.le hη
    · exact mul_nonneg (mul_nonneg hlam.le hn₀) (hR 2)
    · exact mul_nonneg (mul_nonneg hlam.le hn₀) (hR 1)
    · exact mul_nonneg (mul_nonneg hlam.le hn₀) (hR 0)
  · simp [π, Fin.sum_univ_four]
    rw [Fin.sum_univ_three] at hn
    dsimp [n]
    linarith only [hn]
  · intro j
    exact mul_nonneg hlam.le (hG j)
  · rw [← Finset.mul_sum]
    simp only [rowWeight, Finset.sum_add_distrib, ← Finset.mul_sum, hd, mul_one]
    linarith only [hn]
  · intro x
    let z := shift ε e x
    have hinv := shift_inverse he hdepth x
    have hx (j : Fin 3) : x j - z j = η * linearRow e z := by
      change x j - (x j - ε * linearRow e x) = _
      linarith only [hinv]
    have hsupport (j : Fin 3) := mul_le_mul_of_nonneg_left (tangent_signed hq (x j) (z j)) (hG j)
    simp_rw [hx] at hsupport
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hsupport j)
    have hcert := mul_le_mul_of_nonneg_left (hcoeff z) hη
    have hrow : η * |argument η e z|^q + (∑ j, n * R j * |z j|^q) ≤
        ∑ j, rowWeight η R d j * |x j|^q := by
      simp only [feature, Fin.sum_univ_three, rowWeight, n] at *
      linarith only [hcert, hsum]
    unfold WeightedRow
    simp only [rowEval_eq he hdepth, Fin.sum_univ_four, Fin.sum_univ_three, π,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three]
    change lam*η*|argument η e z|^q + lam*n*R 2*|z 2|^q + lam*n*R 1*|z 1|^q +
      lam*n*R 0*|z 0|^q ≤ _
    have h := mul_le_mul_of_nonneg_left hrow hlam.le
    rw [Fin.sum_univ_three, Fin.sum_univ_three] at h
    linarith only [h]

end
end HlawkaSchatten.BelowExponent.Vertex
