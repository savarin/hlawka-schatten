/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Interpolation
public import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import all HlawkaSchatten.BelowExponent.Interpolation
import Batteries.Tactic.OpenPrivate

/-! Parameter interpolation for the vertex and side collars, after dividing by λ. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open Set
open private abs_rpow_lerp_le from HlawkaSchatten.BelowExponent.Interpolation

/-- The upper second derivative controls the loss below the chord on a closed interval. -/
theorem vertex_chord_of_second_le {f d dd : ℝ → ℝ} {a b u M : ℝ}
    (hab : a ≤ b) (hu : u ∈ Icc 0 1) (hM : 0 ≤ M) (hc : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ interior (Icc a b), HasDerivAt f (d x) x)
    (hdd : ∀ x ∈ interior (Icc a b), HasDerivAt d (dd x) x)
    (hbound : ∀ x ∈ interior (Icc a b), dd x ≤ M) :
    (1-u) * f a + u * f b - M * (b-a)^2 / 8 ≤ f ((1-u)*a+u*b) := by
  let g := fun x : ℝ => f x - (M/2)*x^2
  have hg : ConcaveOn ℝ (Icc a b) g := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc a b)
      (f' := fun x => d x - M*x) (f'' := fun x => dd x - M)
    · exact hc.sub (continuous_const.mul (continuous_id.pow 2)).continuousOn
    · intro x hx
      have hsq := ((hasDerivAt_id x).pow 2).const_mul (M/2)
      convert! ((hd x hx).sub hsq).hasDerivWithinAt using 1
      simp
      ring
    · intro x hx
      convert! ((hdd x hx).sub ((hasDerivAt_id x).const_mul M)).hasDerivWithinAt using 1
      simp
    · intro x hx
      exact sub_nonpos.mpr (hbound x hx)
  have h := hg.2 (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
    (sub_nonneg.mpr hu.2) hu.1 (sub_add_cancel 1 u)
  simp only [g, smul_eq_mul] at h
  nlinarith only [h, mul_nonneg (mul_nonneg hM (sq_nonneg (b-a))) (sq_nonneg (u-1/2))]

/-- After dividing by positive λ, the negative absolute power loses no interpolation
margin, even when its affine argument vanishes inside the parameter cell. -/
theorem vertex_normalized_gap_of_vertices {ι : Type*} {s : Finset ι}
    {w A y : ι → ℝ} {q lam a l err : ℝ} (hq : 1 ≤ q) (hlam : 0 < lam)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hs : ∑ i ∈ s, w i = 1)
    (hl : l = ∑ i ∈ s, w i * y i)
    (hfeature : ∑ i ∈ s, w i * A i - err ≤ a)
    (hmargin : err ≤ ∑ i ∈ s, w i * (A i - |y i| ^ q)) :
    0 ≤ lam * (a - |l| ^ q) := by
  have hconv : ConvexOn ℝ univ (fun x : ℝ => |x|^q) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ z _ r t hr ht hrt
    have hrt' : r = 1-t := by linarith
    simp only [smul_eq_mul, hrt']
    exact abs_rpow_lerp_le hq ht (by linarith) _ _
  have h := hconv.map_sum_le hw hs (fun i _ => mem_univ (y i))
  simp only [smul_eq_mul, ←hl] at h
  simp only [mul_sub, Finset.sum_sub_distrib] at hmargin
  exact mul_nonneg hlam.le (by linarith)

/-- The derivatives of a fifth power introduce only integral powers. -/
theorem vertex_fifth_derivatives {r v : ℝ → ℝ} {x a : ℝ}
    (hr : HasDerivAt r (v x) x) (hv : HasDerivAt v a x) :
    HasDerivAt (fun y => r y ^ 5) (5 * r x ^ 4 * v x) x ∧
    HasDerivAt (fun y => 5 * r y ^ 4 * v y)
      (20 * r x ^ 3 * (v x)^2 + 5 * r x ^ 4 * a) x := by
  constructor
  · convert! hr.pow 5 using 1
  · convert! (((hr.pow 4).const_mul 5).mul hv) using 1
    simp
    ring

/-- For a positive fifth root of B, its two derivatives need only one root value. -/
theorem vertex_radical_derivatives {r B v B₁ a B₂ : ℝ} (hr : 0 < r) (hB : r^5 = B)
    (hd : 5 * r^4 * v = B₁) (hdd : 20 * r^3 * v^2 + 5 * r^4 * a = B₂) :
    v = r * B₁ / (5 * B) ∧ a = r * (5 * B * B₂ - 4 * B₁^2) / (25 * B^2) := by
  subst B
  subst B₁
  subst B₂
  constructor
  · field_simp [hr.ne']
  · field_simp [hr.ne']
    ring

end HlawkaSchatten.BelowExponent
