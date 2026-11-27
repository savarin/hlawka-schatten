/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FSlabCheckSound
import all HlawkaSchatten.BelowExponent.FacetArchive.NearChecker
import Batteries.Tactic.OpenPrivate

/-! The rational near-equality branch for all three F comparisons. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FSlabCheck

open Tangent
open FacetNumeric (ctx nearAxis nearAnchor nearMagnitude nearIntercept nearSlope nearUpper nearShiftedMag
  rpow_le_nearUpper nearTangent_le_rpow)
open private cast_nearMagnitude from HlawkaSchatten.BelowExponent.FacetArchive.NearChecker

private theorem rawPowers_le_near (P : Band) (A B : ℕ) (ts : List TC.Tm)
    (hvalid : ts.all (fun t => decide (-1 < movement P A B t)) = true) :
    rawPowers P A B ts ≤ ((ts.map fun t => (t.p : ℚ)*nearUpper (movement P A B t)).sum : ℝ) := by
  induction ts with
  | nil => simp [rawPowers]
  | cons head tail ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hvalid
    simp only [rawPowers, List.map_cons, List.sum_cons, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast]
    refine add_le_add (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)) (ih hvalid.2)
    have ht : -1 < movement P A B head := of_decide_eq_true hvalid.1
    have h := rpow_le_nearUpper ht
    have heq : 1 + (movement P A B head : ℝ) =
        |(TC.gInt head (Nat.ble ctx.Da A) (nearShiftedMag A) (Nat.ble ctx.Da B) (nearShiftedMag B) : ℝ) /
          ↑(profileDen P*ctx.Da : ℕ)| := by
      unfold movement
      push_cast
      ring
    rwa [heq] at h

theorem nearGroup_sound (P : Band) (hW : P.weight ≤ 100) (j : Fin 3) (A B : ℕ) (r s : ℚ)
    (i : Fin 3) (h : nearGroup P j A B r s (groups P j i) = true) :
    fPairOutput (len P) (mu P) (imbalanceAt P false) (imbalanceAt P true) i
      (chartRow j (chartCoord ctx A) (chartCoord ctx B)) ≤
    cornerInput (fDoubleGamma (mu P) (len P)) j (fun x => (nearIntercept r : ℝ)-(nearSlope r : ℝ)*|x|)
      (fun x => (nearIntercept s : ℝ)-(nearSlope s : ℝ)*|x|) (chartCoord ctx A) (chartCoord ctx B) := by
  simp only [nearGroup, Bool.and_eq_true] at h
  have hupper := rawPowers_le_near P A B (groups P j i) h.1
  have hn := (Rat.cast_le (K := ℝ)).2 (of_decide_eq_true h.2)
  push_cast at hn
  push_cast at hupper
  simp only [cast_nearMagnitude] at hn
  have hp := hupper.trans hn
  rw [rawPowers_groups P hW] at hp
  have hh : (0 : ℝ) < commonDen P := by exact_mod_cast commonDen_pos P
  apply (mul_le_mul_iff_right₀ hh).mp
  unfold cornerInput
  have hg₀ := rawGamma_agrees P hW j
  have hg₁ := rawGamma_agrees P hW (chartA j)
  have hg₂ := rawGamma_agrees P hW (chartB j)
  have ha := congrArg (fun a : ℝ => a*((nearIntercept r : ℝ)-(nearSlope r : ℝ)*|chartCoord ctx A|)) hg₁
  have hb := congrArg (fun a : ℝ => a*((nearIntercept s : ℝ)-(nearSlope s : ℝ)*|chartCoord ctx B|)) hg₂
  linarith only [hp,hg₀,ha,hb]

end HlawkaSchatten.BelowExponent.FSlabCheck
