/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.VertexRegion

/-! The normalized SC near-cone identity and its vanishing linear coefficients. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

noncomputable section

def sideRow (u v : ℝ) : Row := ![1, -(1 + u), -(1 + v)]

def sideWeightDifference (η : ℝ) (R d : Row) : ℝ :=
  rowWeight η R d 0 - rowWeight η R d 1 - rowWeight η R d 2

def sideY (a b η u v : ℝ) : ℝ :=
  1 + 4 * η * a + (1 + 2 * η * (1 - b)) * u + (1 + 2 * η * (a + b)) * v

private theorem parameter_coefficient_sum {a b η : ℝ} (hη : 0 ≤ η) :
    ∑ j, parameterD a b η j = 1 := by
  let ε := η / (1 + 2 * η)
  have hε : ε * (1 + 2 * η) = η :=
    div_mul_cancel₀ _ (show (1 + 2 * η : ℝ) ≠ 0 by positivity)
  exact coefficient_sum (by simp [parameterDirection, Fin.sum_univ_three])
    (beta_sum hη hε _) _

theorem side_gap_eval {q a b η u v : ℝ} (hη : 0 ≤ η)
    (hu : 0 < 1 + u) (hv : 0 < 1 + v) (hY : 0 ≤ sideY a b η u v) :
    let d := parameterD a b η
    let R := radical (η / (1 + 2 * η)) (parameterDirection a b)
    let j := sideWeightDifference η R d
    parameterGap q (sideRow u v) a b η =
      1 + d 1 * ((1 + u) ^ q - 1) + d 2 * ((1 + v) ^ q - 1) -
        q * (2 * a + (1 - b) * u + (a + b) * v) *
          (j - rowWeight η R d 1 * ((1 + u) ^ (q - 1) - 1) -
            rowWeight η R d 2 * ((1 + v) ^ (q - 1) - 1)) -
        (sideY a b η u v) ^ q := by
  intro d R j
  have hsum : d 0 + d 1 + d 2 = 1 :=
    by simpa only [Fin.sum_univ_three] using parameter_coefficient_sum (a := a) (b := b) hη
  have hlin : linearRow (parameterDirection a b) (sideRow u v) =
      -(2 * a + (1 - b) * u + (a + b) * v) := by
    simp [linearRow, parameterDirection, sideRow, Fin.sum_univ_three]
    ring
  have hArg : parameterArgument (sideRow u v) a b η = -sideY a b η u v := by
    change argument η (parameterDirection a b) (sideRow u v) = _
    rw [argument, hlin]
    simp [sideRow, sideY, Fin.sum_univ_three]
    ring
  have hS {x : ℝ} (hx : 0 < x) : signedPower q (-x) = -(x ^ (q - 1)) := by
    unfold signedPower
    rw [ite_eq_right (not_le.mpr (neg_lt_zero.mpr hx)), abs_neg, abs_of_pos hx]
  change feature q η (parameterDirection a b) R d (sideRow u v) - |parameterArgument (sideRow u v) a b η| ^ q = _
  rw [hArg, abs_neg, abs_of_nonneg hY]
  simp only [feature, hlin, Fin.sum_univ_three]
  change d 0 * |(1 : ℝ)| ^ q + d 1 * |-(1 + u)| ^ q + d 2 * |-(1 + v)| ^ q +
      q * (-(2 * a + (1 - b) * u + (a + b) * v)) *
        (rowWeight η R d 0 * signedPower q 1 +
          rowWeight η R d 1 * signedPower q (-(1 + u)) +
          rowWeight η R d 2 * signedPower q (-(1 + v))) - (sideY a b η u v) ^ q = _
  simp only [abs_one, abs_neg, abs_of_pos hu, abs_of_pos hv, Real.one_rpow, mul_one,
    hS hu, hS hv]
  have hs : signedPower q 1 = 1 := by simp [signedPower]
  rw [hs]
  dsimp only [j, sideWeightDifference]
  linear_combination hsum

theorem side_gap_at_equality {q a b η : ℝ} (ha : 0 ≤ a) (hη : 0 ≤ η) :
    let d := parameterD a b η
    let R := radical (η / (1 + 2 * η)) (parameterDirection a b)
    parameterGap q (sideRow 0 0) a b η =
      1 - 2 * q * a * sideWeightDifference η R d - (1 + 4 * η * a) ^ q := by
  have hY : 0 ≤ sideY a b η 0 0 := by
    simp only [sideY, mul_zero, add_zero]
    nlinarith only [mul_nonneg hη ha]
  have h := side_gap_eval (q := q) hη (u := 0) (v := 0) (by norm_num) (by norm_num) hY
  simp [sideY] at h
  exact h.trans (by ring)

def sideBetaFactor (η : ℝ) (e : Row) (j : Fin 3) : ℝ :=
  (e 0 / (e j) ^ 2) / betaDen η e

def sideHeavyFactor (η : ℝ) (e : Row) : ℝ :=
  (e 0 * (1 + η / (1 + η)) ^ 2) / betaDen η e

private theorem side_beta_factor {η : ℝ} {e : Row} {j : Fin 3} (h : j ≠ 0) :
    beta η e j = e 0 * sideBetaFactor η e j := by
  have he (k : Fin 3) : (e 0 / e k) ^ 2 / betaDen η e = e 0 * sideBetaFactor η e k := by
    unfold sideBetaFactor
    rw [div_pow, ← mul_div_assoc, ← mul_div_assoc, pow_two]
  fin_cases j
  · contradiction
  · exact he 1
  · exact he 2

private theorem side_heavy_factor (η : ℝ) (e : Row) :
    betaHeavy η e = e 0 * sideHeavyFactor η e := by
  unfold betaHeavy sideHeavyFactor
  rw [mul_pow, ← mul_div_assoc]
  ring

private def sideFace (ε : ℝ) (e R : Row) : Row :=
  let Δ := (∑ i, R i) - 2 * R 0
  ![-1 + ε + Δ, 1 - (1 - e 1) * (ε + Δ), 1 - (1 - e 2) * (ε + Δ)]

/-- The exact coefficient correction divided by the first direction, written without that division. -/
def sideCorrection (ε β₀ β₁ β₂ βh : ℝ) (e R : Row) : Row :=
  let T := ∑ i, R i
  let Δ := fun i => T - 2 * R i
  let a := fun j => 1 - e j
  let B := β₁ + β₂ + ε ^ 2 * βh
  let X := (2 / 3) * (ε * βh * (1 - ε) * (T - ε) +
    β₀ * (ε + Δ 0) + β₁ * e 1 * (ε + Δ 1) + β₂ * e 2 * (ε + Δ 2))
  ![-(ε + Δ 0) + 2 * (1 - ε * a 0) * B -
        2 * ε * βh * R 0 * (1 - ε * a 0) - 2 * a 0 * (β₁ * R 2 + β₂ * R 1) + X,
    -2 * (1 - ε * a 1) * β₁ + 2 * a 1 * R 2 * B -
        2 * ε * βh * R 1 * (1 - ε * a 1) - 2 * a 1 * β₂ * R 0 + X,
    -2 * (1 - ε * a 2) * β₂ + 2 * a 2 * R 1 * B -
        2 * ε * βh * R 2 * (1 - ε * a 2) - 2 * a 2 * β₁ * R 0 + X]

private theorem side_coefficient_split {ε bh β₁ β₂ βh : ℝ} {e b R : Row}
    (hB : (∑ j, b j) + ε ^ 2 * bh = 1)
    (hb₁ : b 1 = e 0 * β₁) (hb₂ : b 2 = e 0 * β₂) (hh : bh = e 0 * βh) (j : Fin 3) :
    coefficient ε bh e b R j =
      sideFace ε e R j + e 0 * sideCorrection ε (b 0) β₁ β₂ βh e R j := by
  have hB₀ : b 0 = 1 - e 0 * (β₁ + β₂ + ε ^ 2 * βh) := by
    simp only [Fin.sum_univ_three, hb₁, hb₂, hh] at hB
    linear_combination hB
  fin_cases j <;>
    norm_num [coefficient, sideFace, sideCorrection, Fin.sum_univ_three, Fin.reduceAdd] <;>
    rw [hB₀, hb₁, hb₂, hh] <;> ring

/-- Division-free factor of the normalized SC linear coefficient along a free row coordinate. -/
def sideGradientFactor (η : ℝ) (e R : Row) (j : Fin 3) : ℝ :=
  let C := sideCorrection (η / (1 + 2 * η)) (beta η e 0)
    (sideBetaFactor η e 1) (sideBetaFactor η e 2) (sideHeavyFactor η e) e R
  C j - 2 * η * (1 - e j) * C 0

theorem side_linear_factor {a b η : ℝ} (hη : 0 ≤ η) {j : Fin 3} (hj : j ≠ 0) :
    let e := parameterDirection a b
    let R := radical (η / (1 + 2 * η)) e
    let d := parameterD a b η
    d j - (1 - e j) * sideWeightDifference η R d - (1 + 2 * η * (1 - e j)) =
      a * sideGradientFactor η e R j := by
  intro e R d
  let ε := η / (1 + 2 * η)
  have hε : ε * (1 + 2 * η) = η :=
    div_mul_cancel₀ _ (show (1 + 2 * η : ℝ) ≠ 0 by positivity)
  have hsum : d 0 + d 1 + d 2 = 1 :=
    by simpa only [Fin.sum_univ_three] using parameter_coefficient_sum (a := a) (b := b) hη
  let C := sideCorrection ε (beta η e 0)
    (sideBetaFactor η e 1) (sideBetaFactor η e 2) (sideHeavyFactor η e) e R
  have hd (i : Fin 3) : d i = sideFace ε e R i + e 0 * C i :=
    side_coefficient_split (beta_sum hη hε e) (side_beta_factor (by decide : (1 : Fin 3) ≠ 0))
      (side_beta_factor (by decide : (2 : Fin 3) ≠ 0)) (side_heavy_factor η e) i
  have hJ : sideWeightDifference η R d =
      -(1 + 2 * η) * ((∑ i, R i) - 2 * R 0) + η * (2 * d 0 - 1) := by
    simp only [sideWeightDifference, rowWeight, Fin.sum_univ_three]
    linear_combination -η * hsum
  change _ = a * (C j - 2 * η * (1 - e j) * C 0)
  rw [hJ, hd j, hd 0]
  change _ = e 0 * (C j - 2 * η * (1 - e j) * C 0)
  fin_cases j
  · contradiction
  · norm_num [sideFace]
    linear_combination -(1 - e 1) * hε
  · norm_num [sideFace]
    linear_combination -(1 - e 2) * hε

def powerRemainder (q x : ℝ) : ℝ := (1 + x) ^ q - 1 - q * x

/-- The exact SC expansion with unscaled power remainders, including the face at a = 0. -/
theorem side_gap_expansion {q a b η u v : ℝ} (ha : 0 ≤ a) (hη : 0 ≤ η)
    (hu : 0 < 1 + u) (hv : 0 < 1 + v) (hY : 0 ≤ sideY a b η u v) :
    let e := parameterDirection a b
    let R := radical (η / (1 + 2 * η)) e
    let d := parameterD a b η
    let W := rowWeight η R d
    let r := q - 1
    let A := 1 - b
    let B := a + b
    let L := A * u + B * v
    let Y₀ := 1 + 4 * η * a
    let ℓ := (1 + 2 * η * A) * u + (1 + 2 * η * B) * v
    let resY := (sideY a b η u v) ^ q - Y₀ ^ q - q * Y₀ ^ r * ℓ
    parameterGap q (sideRow u v) a b η =
      parameterGap q (sideRow 0 0) a b η +
        q * a * ((sideGradientFactor η e R 1 + 2 * r * W 1) * u +
          (sideGradientFactor η e R 2 + 2 * r * W 2) * v) -
        q * (Y₀ ^ r - 1) * ℓ +
        d 1 * powerRemainder q u + d 2 * powerRemainder q v +
        2 * q * a * (W 1 * powerRemainder r u + W 2 * powerRemainder r v) +
        q * L * (W 1 * ((1 + u) ^ r - 1) + W 2 * ((1 + v) ^ r - 1)) - resY := by
  intro e R d W r A B L Y₀ ℓ resY
  let J := sideWeightDifference η R d
  have h₁ := side_linear_factor (a := a) (b := b) hη (by decide : (1 : Fin 3) ≠ 0)
  have h₂ := side_linear_factor (a := a) (b := b) hη (by decide : (2 : Fin 3) ≠ 0)
  change d 1 - A * J - (1 + 2 * η * A) = a * sideGradientFactor η e R 1 at h₁
  have hB : 1 - e 2 = B := by simp [e, parameterDirection, B]; ring
  change d 2 - (1 - e 2) * J - (1 + 2 * η * (1 - e 2)) =
    a * sideGradientFactor η e R 2 at h₂
  rw [hB] at h₂
  rw [side_gap_eval hη hu hv hY, side_gap_at_equality ha hη]
  change 1 + d 1 * ((1 + u) ^ q - 1) + d 2 * ((1 + v) ^ q - 1) -
    q * (2*a + A*u + B*v) *
      (J - W 1 * ((1 + u) ^ r - 1) - W 2 * ((1 + v) ^ r - 1)) -
    (sideY a b η u v) ^ q = _
  dsimp only [resY, ℓ, L, powerRemainder]
  dsimp only [J, Y₀, R, d] at h₁ h₂ ⊢
  linear_combination q * u * h₁ + q * v * h₂

theorem side_gap_equality_lower {q a b η : ℝ} (hq : 1 ≤ q) (ha : 0 ≤ a) (hη : 0 ≤ η) :
    let d := parameterD a b η
    let R := radical (η / (1 + 2 * η)) (parameterDirection a b)
    a * (-2 * q * sideWeightDifference η R d - 4 * η * q * (1 + 4 * η * a) ^ (q - 1)) ≤
      parameterGap q (sideRow 0 0) a b η := by
  intro d R
  have hY : 0 < 1 + 4 * η * a := by nlinarith only [mul_nonneg hη ha]
  have h := tangent_le_rpow hq hY (show (0 : ℝ) ≤ 1 by norm_num)
  rw [Real.one_rpow] at h
  rw [side_gap_at_equality ha hη]
  change _ ≤ 1 - 2 * q * a * sideWeightDifference η R d - (1 + 4 * η * a) ^ q
  linarith only [h]

end

end HlawkaSchatten.BelowExponent.Vertex
