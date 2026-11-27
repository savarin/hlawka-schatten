/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.RouteT
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! The averaging step of exponent transfer. The moment representation used here
is constructed in StableLaw. The published mission definitions are used throughout. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.mathlibStandardSet true

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction MeasureTheory

/-- A positive mean of pullbacks by additive maps preserves constant-one Hlawka. -/
theorem hlawka_of_mean {E F Ω : Type*} [AddCommGroup E] [AddCommGroup F] [MeasurableSpace Ω]
    (μ : Measure Ω) (D : Ω → E →+ F) (N : F → ℝ) (M : E → ℝ) {c : ℝ} (hc : 0 < c)
    (hN : HasHlawkaConstant N 1)
    (hi : ∀ v, Integrable (fun w => N (D w v)) μ)
    (hmean : ∀ v, (∫ w, N (D w v) ∂μ) = c * M v) :
    HasHlawkaConstant M 1 := by
  apply (hasHlawkaConstant_one_iff M).2
  intro x y z
  have hwise (w : Ω) :
      N (D w (x+y)) + N (D w (x+z)) + N (D w (y+z)) ≤
        N (D w x) + N (D w y) + N (D w z) + N (D w (x+y+z)) := by
    simpa only [map_add] using (hasHlawkaConstant_one_iff N).1 hN (D w x) (D w y) (D w z)
  have hInt := integral_mono (((hi (x+y)).add (hi (x+z))).add (hi (y+z)))
    ((((hi x).add (hi y)).add (hi z)).add (hi (x+y+z))) hwise
  change (∫ w, N (D w (x+y)) + N (D w (x+z)) + N (D w (y+z)) ∂μ) ≤
    (∫ w, N (D w x) + N (D w y) + N (D w z) + N (D w (x+y+z)) ∂μ) at hInt
  have i₂ (a b : E) : Integrable (fun w => N (D w a) + N (D w b)) μ := (hi a).add (hi b)
  have i₃ (a b d : E) : Integrable (fun w => N (D w a) + N (D w b) + N (D w d)) μ :=
    (i₂ a b).add (hi d)
  rw [integral_add (i₂ (x+y) (x+z)) (hi (y+z)),
    integral_add (hi (x+y)) (hi (x+z)),
    integral_add (i₃ x y z) (hi (x+y+z)),
    integral_add (i₂ x y) (hi z), integral_add (hi x) (hi y)] at hInt
  apply (mul_le_mul_iff_right₀ hc).mp
  simpa only [hmean, mul_add] using hInt

def diagonalScale {n : ℕ} (w : Fin n → ℝ) : (Fin n → ℝ) →+ (Fin n → ℝ) where
  toFun x i := w i * x i
  map_zero' := by ext; simp
  map_add' x y := by ext; simp [mul_add]

/-- A positive multiple of the smaller-exponent norm equals the integral of larger-exponent
norms over diagonal scalings. -/
def HasDiagonalMean (r p : ℝ) (n : ℕ) : Prop :=
  ∃ μ : Measure (Fin n → ℝ), ∃ c : ℝ, 0 < c ∧
    (∀ x, Integrable (fun w => lpNorm p (diagonalScale w x)) μ) ∧
    ∀ x, (∫ w, lpNorm p (diagonalScale w x) ∂μ) = c * lpNorm r x

theorem hlawka_of_diagonalMean {p r : ℝ} {n : ℕ} (hm : HasDiagonalMean r p n)
    (hp : HasHlawkaConstant (lpNorm p : (Fin n → ℝ) → ℝ) 1) :
    HasHlawkaConstant (lpNorm r : (Fin n → ℝ) → ℝ) 1 := by
  obtain ⟨μ, c, hc, hi, hmean⟩ := hm
  exact hlawka_of_mean μ diagonalScale _ _ hc hp hi hmean

/-- The exact mission conclusion from row certificates and diagonal means. -/
theorem hlawka_below_of_regions_and_means
    (hregions : ∀ t : Profile, OrderedInterior t → InRegion t → RowAt criticalQ t)
    (hmeans : ∀ r : ℝ, 2 ≤ r → r < criticalP → ∀ n, HasDiagonalMean r criticalP n) :
    ∀ p : ℝ, 2 ≤ p → p ≤ Real.log 3 / Real.log (3 / 2) → ∀ n : ℕ,
      HasHlawkaConstant (lpNorm p : (Fin n → ℝ) → ℝ) 1 := by
  intro p hp hpW n
  change p ≤ criticalP at hpW
  rcases hpW.lt_or_eq with hlt | rfl
  · exact hlawka_of_diagonalMean (hmeans p hp hlt n) (critical_hlawka_of_regions hregions n)
  · exact critical_hlawka_of_regions hregions n

end HlawkaSchatten.BelowExponent
