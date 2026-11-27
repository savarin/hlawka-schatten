/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.ParameterBounds

/-! Exact nonnegativity of a rational quadratic on a closed interval. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

def sidePoly (A G V x : ℚ) : ℚ := A * x^2 + G*x + V

def sideIntervalOK (A G V : ℚ) (I : RatBounds) : Bool :=
  let z := -G / (2*A)
  decide (I.lo ≤ I.hi → 0 ≤ sidePoly A G V I.lo ∧ 0 ≤ sidePoly A G V I.hi ∧
    (0 < A → I.lo ≤ z → z ≤ I.hi → 0 ≤ sidePoly A G V z))

noncomputable section

theorem sideQuadratic_interval_nonneg {A G V x l r : ℝ}
    (hl : l ≤ x) (hr : x ≤ r)
    (hleft : 0 ≤ A*l^2+G*l+V) (hright : 0 ≤ A*r^2+G*r+V)
    (hvertex : 0 < A → l ≤ -G/(2*A) → -G/(2*A) ≤ r →
      0 ≤ A*(-G/(2*A))^2+G*(-G/(2*A))+V) : 0 ≤ A*x^2+G*x+V := by
  by_cases hA : 0 < A
  · let z := -G/(2*A)
    have hstat : 2*A*z+G = 0 := by
      dsimp only [z]
      field_simp [hA.ne']
      ring
    have shift (u v : ℝ) :
        A*v^2+G*v+V - (A*u^2+G*u+V) = A*((v-z)^2-(u-z)^2) := by
      linear_combination (v-u)*hstat
    by_cases hz₁ : z < l
    · have hdiff : 0 ≤ (x-z)^2-(l-z)^2 := by
        nlinarith only [mul_nonneg (sub_nonneg.mpr hl) (show 0 ≤ x+l-2*z by linarith only [hz₁, hl])]
      linarith only [shift l x, hleft, mul_nonneg hA.le hdiff]
    by_cases hz₂ : r < z
    · have hdiff : 0 ≤ (x-z)^2-(r-z)^2 := by
        nlinarith only [mul_nonneg (sub_nonneg.mpr hr) (show 0 ≤ 2*z-x-r by linarith only [hz₂, hr])]
      linarith only [shift r x, hright, mul_nonneg hA.le hdiff]
    have hdiff : 0 ≤ (x-z)^2-(z-z)^2 := by simpa using sq_nonneg (x-z)
    linarith only [shift z x, hvertex hA (le_of_not_gt hz₁) (le_of_not_gt hz₂),
      mul_nonneg hA.le hdiff]
  · obtain hwidth | hwidth := (hl.trans hr).eq_or_lt
    · have hx : x = l := le_antisymm (hr.trans_eq hwidth.symm) hl
      simpa only [hx] using hleft
    have hsum := sub_nonneg.mpr (show A*(r-l)*(x-l)*(r-x) ≤
      (r-x)*(A*l^2+G*l+V)+(x-l)*(A*r^2+G*r+V) from
      (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hA) (sub_nonneg.mpr hwidth.le))
          (sub_nonneg.mpr hl)) (sub_nonneg.mpr hr)).trans
        (add_nonneg (mul_nonneg (sub_nonneg.mpr hr) hleft) (mul_nonneg (sub_nonneg.mpr hl) hright)))
    have heq : (r-l)*(A*x^2+G*x+V) =
        (r-x)*(A*l^2+G*l+V)+(x-l)*(A*r^2+G*r+V)-A*(r-l)*(x-l)*(r-x) := by ring
    rw [← heq] at hsum
    exact nonneg_of_mul_nonneg_right hsum (sub_pos.mpr hwidth)

theorem sideIntervalOK_sound {A G V : ℚ} {I : RatBounds} {x : ℝ}
    (h : sideIntervalOK A G V I = true) (hx : I.Contains x) :
    0 ≤ (A : ℝ)*x^2+(G : ℝ)*x+V := by
  have ht : I.lo ≤ I.hi := by exact_mod_cast hx.1.trans hx.2
  obtain ⟨hl, hr, hz⟩ := of_decide_eq_true h ht
  apply sideQuadratic_interval_nonneg hx.1 hx.2
  · exact_mod_cast (show 0 ≤ A * I.lo^2 + G*I.lo+V from hl)
  · exact_mod_cast (show 0 ≤ A * I.hi^2 + G*I.hi+V from hr)
  intro hA hleft hright
  have hA' : 0 < A := by exact_mod_cast hA
  have hleft' : I.lo ≤ -G/(2*A) := by exact_mod_cast hleft
  have hright' : -G/(2*A) ≤ I.hi := by exact_mod_cast hright
  exact_mod_cast (show 0 ≤ A*(-G/(2*A))^2+G*(-G/(2*A))+V from hz hA' hleft' hright')

end

end HlawkaSchatten.BelowExponent.Vertex
