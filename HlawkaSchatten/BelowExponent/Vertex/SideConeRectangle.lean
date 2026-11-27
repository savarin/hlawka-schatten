/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.SideConeBox
public import HlawkaSchatten.BelowExponent.Vertex.SideConeUnivariate

/-! The exact second branch of the SC check, minimizing a quadratic on a rectangle. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

def sideAffinePreimage (s t : ℚ) (U V : RatBounds) : RatBounds :=
  if s = 0 then
    if U.lo ≤ t ∧ t ≤ U.hi then V else ⟨1, 0⟩
  else
    let l := (U.lo-t)/s
    let r := (U.hi-t)/s
    ⟨max V.lo (min l r), min V.hi (max l r)⟩

def SideLowerCoefficients.rectangleEndpointOK (I : SideLowerCoefficients)
    (a : ℚ) (U V : RatBounds) : Bool :=
  let A := I.diagonalFirst
  let B := I.mixed
  let C := I.diagonalSecond
  let G := a*I.first
  let K := a*I.second
  let J := a*I.value
  let edge (u : ℚ) := sideIntervalOK C (K+2*B*u) (J+G*u+A*u^2) V
  edge U.lo && edge U.hi &&
    (if 0 < A then
      sideIntervalOK (C-B^2/A) (K-B*G/A) (J-G^2/(4*A))
        (sideAffinePreimage (-B/A) (-G/(2*A)) U V)
    else true)

def SideLowerCoefficients.rectangleOK (I : SideLowerCoefficients)
    (a U V : RatBounds) : Bool :=
  I.rectangleEndpointOK a.lo U V && I.rectangleEndpointOK a.hi U V

noncomputable section

theorem sideAffinePreimage_mem {s t : ℚ} {U V : RatBounds} {y : ℝ}
    (hy : V.Contains y) (hx : U.Contains ((s : ℝ)*y+(t : ℝ))) :
    (sideAffinePreimage s t U V).Contains y := by
  by_cases hzero : s = 0
  · subst s
    have hs : U.lo ≤ t ∧ t ≤ U.hi := by
      have hr : U.Contains (t : ℝ) := by simpa only [Rat.cast_zero, zero_mul, zero_add] using hx
      exact ⟨by exact_mod_cast hr.1, by exact_mod_cast hr.2⟩
    simpa [sideAffinePreimage, hs] using hy
  have hs : (s : ℝ) ≠ 0 := by exact_mod_cast hzero
  simp only [sideAffinePreimage, ite_eq_right hzero, RatBounds.Contains, Rat.cast_max, Rat.cast_min,
    Rat.cast_div, Rat.cast_sub, max_le_iff, le_min_iff]
  refine ⟨⟨hy.1, ?_⟩, ⟨hy.2, ?_⟩⟩
  · rcases hs.lt_or_gt with hn | hp
    · apply min_le_of_right_le
      exact (div_le_iff_of_neg hn).2 (by linarith only [hx.2])
    · apply min_le_of_left_le
      exact (div_le_iff₀ hp).2 (by linarith only [hx.1])
  · rcases hs.lt_or_gt with hn | hp
    · apply le_max_of_le_left
      exact (le_div_iff_of_neg hn).2 (by linarith only [hx.1])
    · apply le_max_of_le_right
      exact (le_div_iff₀ hp).2 (by linarith only [hx.2])

theorem SideLowerCoefficients.rectangleEndpointOK_sound {I : SideLowerCoefficients}
    {a : ℚ} {U V : RatBounds} {x y : ℝ} (h : I.rectangleEndpointOK a U V = true)
    (hx : U.Contains x) (hy : V.Contains y) : 0 ≤ I.eval a x y := by
  let A : ℝ := I.diagonalFirst
  let B : ℝ := I.mixed
  let C : ℝ := I.diagonalSecond
  let G : ℝ := (a : ℝ)*(I.first : ℝ)
  let K : ℝ := (a : ℝ)*(I.second : ℝ)
  let J : ℝ := (a : ℝ)*(I.value : ℝ)
  let L := G+2*B*y
  let N := J+K*y+C*y^2
  have heval (z : ℝ) : I.eval a z y = A*z^2+L*z+N := by
    simp only [SideLowerCoefficients.eval, sideQuadratic, A, B, C, G, K, J, L, N]
    ring
  unfold SideLowerCoefficients.rectangleEndpointOK at h
  simp only [Bool.and_eq_true, and_assoc] at h
  have edge {z : ℚ} (hcheck : sideIntervalOK I.diagonalSecond (a*I.second+2*I.mixed*z)
      (a*I.value+a*I.first*z+I.diagonalFirst*z^2) V = true) :
      0 ≤ A*(z : ℝ)^2+L*(z : ℝ)+N := by
    have hval := sideIntervalOK_sound hcheck hy
    push_cast at hval
    dsimp only [A, L, N, G, B, J, K, C]
    linear_combination hval
  have hl := edge h.1
  have hr := edge h.2.1
  rw [heval]
  apply sideQuadratic_interval_nonneg hx.1 hx.2 hl hr
  intro hA hz₁ hz₂
  have hAq : 0 < I.diagonalFirst := by
    change (0 : ℝ) < (I.diagonalFirst : ℝ) at hA
    exact_mod_cast hA
  have hstation := h.2.2
  simp only [ite_eq_left hAq] at hstation
  let s := -I.mixed/I.diagonalFirst
  let t := -(a*I.first)/(2*I.diagonalFirst)
  have hz : (s : ℝ)*y+(t : ℝ) = -L/(2*A) := by
    dsimp only [s,t,L,A,B,G]
    push_cast
    field_simp [hA.ne']
    ring
  have pre := sideAffinePreimage_mem hy (show U.Contains ((s : ℝ)*y+(t : ℝ)) from hz ▸ ⟨hz₁,hz₂⟩)
  have hval := sideIntervalOK_sound hstation pre
  push_cast at hval
  have hred : A*(-L/(2*A))^2+L*(-L/(2*A))+N =
      (C-B^2/A)*y^2+(K-B*G/A)*y+(J-G^2/(4*A)) := by
    dsimp only [L,N]
    field_simp [hA.ne']
    ring
  rw [hred]
  exact hval

theorem SideLowerCoefficients.rectangleOK_sound {I : SideLowerCoefficients}
    {P U V : RatBounds} {a u v : ℝ} (h : I.rectangleOK P U V = true)
    (ha : P.Contains a) (hu : U.Contains u) (hv : V.Contains v) : 0 ≤ I.eval a u v := by
  have hends := Bool.and_eq_true_iff.mp h
  exact sideQuadratic_of_endpoints ha.1 ha.2 (rectangleEndpointOK_sound hends.1 hu hv)
    (rectangleEndpointOK_sound hends.2 hu hv)

theorem SideNearBox.gap_nonneg_rectangle {B : SideNearBox} {W : SideNearSamples} (h : B.OK W)
    {q a b η u v : ℝ} {s t : Bool} (hq : B.exponent.Contains q) (hp : B.cell.Contains a b η)
    (hu : B.u.Contains u) (hv : B.v.Contains v) (hs : HasSideSign s u) (ht : HasSideSign t v)
    (hrect : ((B.input W).evaluate.lower s t).rectangleOK B.cell.a B.u B.v = true) :
    0 ≤ parameterGap q (sideRow u v) a b η := by
  obtain ⟨hbox, ha, hη, hu₀, hv₀, hY⟩ := B.evaluate_sound h hq hp hu hv
  rw [side_gap_eq_quadratic ha hη hu₀ hv₀ hY]
  exact (SideLowerCoefficients.rectangleOK_sound hrect hp.first hu hv).trans
    (SideCoefficientIntervals.lower_le hbox ha hs ht)

end

end HlawkaSchatten.BelowExponent.Vertex
