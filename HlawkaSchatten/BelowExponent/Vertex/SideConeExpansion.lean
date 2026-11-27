/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.SideConePowers
public import HlawkaSchatten.BelowExponent.Vertex.SideConeQuadratic

/-! Exact quadratic representation of the normalized SC row. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

noncomputable section

structure SideCoefficients where
  value : ℝ
  first : ℝ
  second : ℝ
  diagonalFirst : ℝ
  mixed : ℝ
  diagonalSecond : ℝ

def SideCoefficients.eval (c : SideCoefficients) (a u v : ℝ) : ℝ :=
  sideQuadratic c.diagonalFirst c.mixed c.diagonalSecond c.value c.first c.second a u v

def sideCoefficients (q a b η u v : ℝ) : SideCoefficients :=
  let e := parameterDirection a b
  let R := radical (η / (1 + 2 * η)) e
  let d := parameterD a b η
  let W := rowWeight η R d
  let J := sideWeightDifference η R d
  let r := q - 1
  let A := 1 - b
  let B := a + b
  let C := 1 + 2 * η * A
  let D := 1 + 2 * η * B
  let X := 4 * η * a
  let Y := 1 + X
  let F := Y ^ (q - 2) * sideSecondFactor q ((C * u + D * v) / Y)
  let n₁ := sideFirstFactor r u
  let n₂ := sideFirstFactor r v
  let k := q * r / 2
  ⟨-2 * q * J - 4 * η * q * sideFirstFactor q X,
    q * (sideGradientFactor η e R 1 + 2 * r * W 1 - 4 * η * r * C * sideFirstFactor r X),
    q * (sideGradientFactor η e R 2 + 2 * r * W 2 - 4 * η * r * D * sideFirstFactor r X),
    k * (d 1 * sideSecondFactor q u + 2 * A * W 1 * n₁ +
      2 * a * (r - 1) * W 1 * sideSecondFactor r u - C ^ 2 * F),
    k * (A * W 2 * n₂ + B * W 1 * n₁ - C * D * F),
    k * (d 2 * sideSecondFactor q v + 2 * B * W 2 * n₂ +
      2 * a * (r - 1) * W 2 * sideSecondFactor r v - D ^ 2 * F)⟩

/-- The normalized SC row equals the exact quadratic with local real coefficients. -/
theorem side_gap_eq_quadratic {q a b η u v : ℝ} (ha : 0 ≤ a) (hη : 0 ≤ η)
    (hu : -1 < u) (hv : -1 < v) (hy : 0 < sideY a b η u v) :
    parameterGap q (sideRow u v) a b η = (sideCoefficients q a b η u v).eval a u v := by
  let e := parameterDirection a b
  let R := radical (η / (1 + 2 * η)) e
  let d := parameterD a b η
  let W := rowWeight η R d
  let J := sideWeightDifference η R d
  let r := q - 1
  let A := 1 - b
  let B := a + b
  let C := 1 + 2 * η * A
  let D := 1 + 2 * η * B
  let X := 4 * η * a
  let Y := 1 + X
  let ℓ := C * u + D * v
  have hX : 0 ≤ X := mul_nonneg (mul_nonneg (by norm_num) hη) ha
  have hX₀ : -1 < X := by linarith only [hX]
  have hY : 0 < Y := by dsimp only [Y]; linarith only [hX]
  have hYe : sideY a b η u v = Y + ℓ := by
    unfold sideY
    dsimp only [Y, X, ℓ, C, D, A, B]
    ring
  have hYplus : 0 < Y+ℓ := hYe ▸ hy
  have hYres := side_scaled_second_eq (q := q) hY hYplus
  rw [← hYe] at hYres
  have hV : parameterGap q (sideRow 0 0) a b η =
      a * (-2 * q * J - 4 * η * q * sideFirstFactor q X) := by
    rw [side_gap_at_equality ha hη]
    have hf := side_first_factor_eq (p := q) hX₀
    change 1 - 2 * q * a * J - (1+X)^q = _
    dsimp only [X] at hf ⊢
    linear_combination -hf
  have hYfirst : Y ^ r - 1 = r * X * sideFirstFactor r X := side_first_factor_eq hX₀
  have hu' : 0 < 1+u := by linarith only [hu]
  have hv' : 0 < 1+v := by linarith only [hv]
  rw [side_gap_expansion ha hη hu' hv' hy.le]
  change parameterGap q (sideRow 0 0) a b η +
    q * a * ((sideGradientFactor η e R 1 + 2 * r * W 1) * u +
      (sideGradientFactor η e R 2 + 2 * r * W 2) * v) -
    q * (Y ^ r - 1) * ℓ +
    d 1 * powerRemainder q u + d 2 * powerRemainder q v +
    2 * q * a * (W 1 * powerRemainder r u + W 2 * powerRemainder r v) +
    q * (A*u+B*v) * (W 1 * ((1 + u) ^ r - 1) + W 2 * ((1 + v) ^ r - 1)) -
    ((sideY a b η u v) ^ q - Y ^ q - q * Y ^ r * ℓ) = _
  rw [hV, hYfirst, side_second_factor_eq (p := q) hu, side_second_factor_eq (p := q) hv,
    side_second_factor_eq (p := r) hu, side_second_factor_eq (p := r) hv,
    side_first_factor_eq (p := r) hu, side_first_factor_eq (p := r) hv]
  have hres : (sideY a b η u v)^q - Y^q - q * Y^r * ℓ =
      (q * (q - 1) / 2) * Y ^ (q - 2) * ℓ ^ 2 * sideSecondFactor q (ℓ / Y) := hYres
  rw [hres]
  simp only [SideCoefficients.eval, sideCoefficients, sideQuadratic]
  dsimp only [e, R, d, W, J, r, A, B, C, D, X, Y, ℓ]
  ring

end

end HlawkaSchatten.BelowExponent.Vertex
