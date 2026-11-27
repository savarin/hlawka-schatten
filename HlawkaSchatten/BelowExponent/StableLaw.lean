/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.ParetoApproximation
public import HlawkaSchatten.BelowExponent.StableLimit

/-! The positive stable probability law and its diagonal mean in finite dimensions. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

/-- For every index strictly between zero and one, there is a probability law
on the nonnegative reals with Laplace transform exp(−t^α) for all t ≥ 0. -/
theorem positiveStable_exists {α : ℝ} (hα : 0 < α) (hα₁ : α < 1) : HasPositiveStable α := by
  obtain ⟨ν, hν⟩ := exists_pareto_approximants hα hα₁
  exact positiveStable_of_unitInterval_approximants hα ν hν

theorem diagonalMean_exists {r p : ℝ} (hr : 1 < r) (hrp : r < p) (n : ℕ) :
    HasDiagonalMean r p n := by
  have hr₀ : 0 < r := zero_lt_one.trans hr
  have hp : 0 < p := hr₀.trans hrp
  exact diagonalMean_of_positiveStable hr hrp
    (positiveStable_exists (div_pos hr₀ hp) ((div_lt_one hp).2 hrp)) n

end HlawkaSchatten.BelowExponent
