/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Euclidean
public import HlawkaSchatten.BelowExponent.StableLaw

/-! Assembly of leaf (A) from its regional row certificates. Intermediate
statements expose the diagonal means and the one-dimensional probability law. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

/-- The mission statement from critical row certificates and interior moment representations.
The left endpoint and the dimensions zero and one are unconditional. -/
theorem hlawka_below_of_certificates
    (hregions : ∀ t : Profile, OrderedInterior t → InRegion t → RowAt criticalQ t)
    (hmeans : ∀ r : ℝ, 2 < r → r < criticalP → ∀ n : ℕ, 2 ≤ n → HasDiagonalMean r criticalP n) :
    ∀ p : ℝ, 2 ≤ p → p ≤ Real.log 3 / Real.log (3 / 2) → ∀ n : ℕ,
      HasHlawkaConstant (lpNorm p : (Fin n → ℝ) → ℝ) 1 := by
  intro p hp hpW n
  change p ≤ criticalP at hpW
  rcases hp.eq_or_lt with rfl | hp
  · exact hlawka_two n
  rcases hpW.lt_or_eq with hl | rfl
  · cases n with
    | zero => exact hlawka_fin_zero p
    | succ k =>
      cases k with
      | zero => exact hlawka_fin_one (by linarith)
      | succ k =>
        exact hlawka_of_diagonalMean (hmeans p hp hl _ (by omega)) (critical_hlawka_of_regions hregions _)
  · exact critical_hlawka_of_regions hregions n

/-- Transfer using the positive stable probability laws at the needed indices. -/
theorem hlawka_below_of_regions_and_stable
    (hregions : ∀ t : Profile, OrderedInterior t → InRegion t → RowAt criticalQ t)
    (hstable : ∀ r : ℝ, 2 < r → r < criticalP → HasPositiveStable (r/criticalP)) :
    ∀ p : ℝ, 2 ≤ p → p ≤ Real.log 3 / Real.log (3 / 2) → ∀ n : ℕ,
      HasHlawkaConstant (lpNorm p : (Fin n → ℝ) → ℝ) 1 :=
  hlawka_below_of_certificates hregions (fun r hr hp n _ =>
    diagonalMean_of_positiveStable (by linarith) hp (hstable r hr hp) n)

/-- Leaf (A) from the regional weighted-row certificates alone. -/
theorem hlawka_below_of_regions
    (hregions : ∀ t : Profile, OrderedInterior t → InRegion t → RowAt criticalQ t) :
    ∀ p : ℝ, 2 ≤ p → p ≤ Real.log 3 / Real.log (3 / 2) → ∀ n : ℕ,
      HasHlawkaConstant (lpNorm p : (Fin n → ℝ) → ℝ) 1 :=
  hlawka_below_of_certificates hregions (fun r hr hp n _ =>
    diagonalMean_exists (by linarith) hp n)

end HlawkaSchatten.BelowExponent
