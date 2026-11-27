/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.SideConeExpansion
public import HlawkaSchatten.BelowExponent.Vertex.ParameterBounds

/-! Transport signed endpoint bounds and exact determinant tests to the normalized SC row. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

structure SideCoefficientIntervals where
  value : RatBounds
  first : RatBounds
  second : RatBounds
  diagonalFirst : RatBounds
  mixed : RatBounds
  diagonalSecond : RatBounds

structure SideLowerCoefficients where
  value : ℚ
  first : ℚ
  second : ℚ
  diagonalFirst : ℚ
  mixed : ℚ
  diagonalSecond : ℚ

def SideLowerCoefficients.detOK (B : SideLowerCoefficients) (cap : ℚ) : Bool :=
  let A := B.diagonalFirst
  let C := B.diagonalSecond
  let D := A * C - B.mixed ^ 2
  let X := C * B.first ^ 2 - 2 * B.mixed * B.first * B.second + A * B.second ^ 2
  decide (0 < A ∧ 0 < D ∧ cap * X ≤ 4 * D * B.value)

def signEndpoint (s : Bool) (I : RatBounds) : ℚ := if s then I.lo else I.hi

def SideCoefficientIntervals.lower (I : SideCoefficientIntervals) (first second : Bool) :
    SideLowerCoefficients :=
  ⟨I.value.lo, signEndpoint first I.first, signEndpoint second I.second, I.diagonalFirst.lo,
    signEndpoint (first == second) I.mixed, I.diagonalSecond.lo⟩

noncomputable section

def SideLowerCoefficients.eval (c : SideLowerCoefficients) (a u v : ℝ) : ℝ :=
  sideQuadratic c.diagonalFirst c.mixed c.diagonalSecond c.value c.first c.second a u v

structure SideCoefficientIntervals.Contains (I : SideCoefficientIntervals)
    (c : SideCoefficients) : Prop where
  value : I.value.Contains c.value
  first : I.first.Contains c.first
  second : I.second.Contains c.second
  diagonalFirst : I.diagonalFirst.Contains c.diagonalFirst
  mixed : I.mixed.Contains c.mixed
  diagonalSecond : I.diagonalSecond.Contains c.diagonalSecond

def HasSideSign (positive : Bool) (x : ℝ) : Prop := if positive then 0 ≤ x else x ≤ 0

private theorem signEndpoint_mul_le {s : Bool} {x r : ℝ} {I : RatBounds}
    (h : I.Contains r) (hx : HasSideSign s x) :
    (signEndpoint s I : ℝ) * x ≤ r * x := by
  cases s
  · exact mul_le_mul_of_nonpos_right h.2 hx
  · exact mul_le_mul_of_nonneg_right h.1 hx

private theorem hasSideSign_mul {p q : Bool} {u v : ℝ} (hu : HasSideSign p u)
    (hv : HasSideSign q v) : HasSideSign (p == q) (u*v) := by
  cases p <;> cases q
  · exact mul_nonneg_of_nonpos_of_nonpos hu hv
  · exact mul_nonpos_of_nonpos_of_nonneg hu hv
  · exact mul_nonpos_of_nonneg_of_nonpos hu hv
  · exact mul_nonneg hu hv

theorem SideCoefficientIntervals.lower_le {I : SideCoefficientIntervals} {c : SideCoefficients}
    {a u v : ℝ} {p q : Bool} (h : I.Contains c) (ha : 0 ≤ a)
    (hu : HasSideSign p u) (hv : HasSideSign q v) :
    (I.lower p q).eval a u v ≤ c.eval a u v := by
  have h₀ := mul_le_mul_of_nonneg_left h.value.1 ha
  have h₁ := mul_le_mul_of_nonneg_left (signEndpoint_mul_le h.first hu) ha
  have h₂ := mul_le_mul_of_nonneg_left (signEndpoint_mul_le h.second hv) ha
  have hd₁ := mul_le_mul_of_nonneg_right h.diagonalFirst.1 (sq_nonneg u)
  have hd₂ := mul_le_mul_of_nonneg_right h.diagonalSecond.1 (sq_nonneg v)
  have hm := signEndpoint_mul_le h.mixed (hasSideSign_mul hu hv)
  unfold SideLowerCoefficients.eval SideCoefficients.eval SideCoefficientIntervals.lower sideQuadratic
  dsimp only
  linarith only [h₀, h₁, h₂, hd₁, hm, hd₂]

theorem SideLowerCoefficients.detOK_sound {B : SideLowerCoefficients} {cap : ℚ}
    (h : B.detOK cap = true) {a u v : ℝ} (ha : 0 ≤ a) (hcap : a ≤ (cap : ℝ)) :
    0 ≤ B.eval a u v := by
  unfold SideLowerCoefficients.detOK at h
  obtain ⟨hA, hD, hX⟩ := of_decide_eq_true h
  have hAr : (0 : ℝ) < B.diagonalFirst := by exact_mod_cast hA
  have hDr : 0 < (B.diagonalFirst : ℝ) * (B.diagonalSecond : ℝ) - (B.mixed : ℝ) ^ 2 := by
    exact_mod_cast hD
  have hXr := (Rat.cast_le (K := ℝ)).2 hX
  push_cast at hXr
  unfold SideLowerCoefficients.eval
  apply sideQuadratic_det_nonneg hAr hDr ha hcap
  simpa only [adjugateCost] using hXr

theorem side_gap_nonneg_of_interval_det {q a b η u v : ℝ} {cap : ℚ}
    {I : SideCoefficientIntervals} {p r : Bool}
    (ha : 0 ≤ a) (hcap : a ≤ (cap : ℝ)) (hη : 0 ≤ η)
    (hu : -1 < u) (hv : -1 < v) (hY : 0 < sideY a b η u v)
    (hsu : HasSideSign p u) (hsv : HasSideSign r v)
    (hbox : I.Contains (sideCoefficients q a b η u v))
    (hdet : (I.lower p r).detOK cap = true) :
    0 ≤ parameterGap q (sideRow u v) a b η := by
  rw [side_gap_eq_quadratic ha hη hu hv hY]
  exact (SideLowerCoefficients.detOK_sound hdet ha hcap).trans
    (SideCoefficientIntervals.lower_le hbox ha hsu hsv)

end

end HlawkaSchatten.BelowExponent.Vertex
