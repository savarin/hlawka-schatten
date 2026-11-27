/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PowerCore
public import HlawkaSchatten.BelowExponent.G3Power

/-! Soundness for power comparisons without rational normalization. -/

set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3Power.Kernel

theorem crossNatLE_upper {xn xd yn yd m n : ℕ}
    (hxd : 0 < xd) (hyd : 0 < yd) (hn : 0 < n)
    (h : crossNatLE xn xd yn yd m n = true) :
    ((xn : ℝ) / xd) ^ ((m : ℝ) / n) ≤ (yn : ℝ) / yd := by
  apply (natRat_rpow_le_iff hxd hyd hn).mpr
  simpa [crossNatLE, Nat.ble_eq] using h

theorem crossNatLE_lower {xn xd yn yd m n : ℕ}
    (hxd : 0 < xd) (hyd : 0 < yd) (hn : 0 < n)
    (h : crossNatLE yn yd xn xd n m = true) :
    (yn : ℝ) / yd ≤ ((xn : ℝ) / xd) ^ ((m : ℝ) / n) := by
  apply (le_natRat_rpow_iff hxd hyd hn).mpr
  simpa [crossNatLE, Nat.ble_eq] using h

private theorem abs_fraction (xn : ℤ) (xd : ℕ) :
    |(xn : ℝ) / xd| = (xn.natAbs : ℝ) / xd := by
  rw [abs_div, ← Int.cast_abs, ← Int.natCast_natAbs,
    abs_of_nonneg (Nat.cast_nonneg _)]
  simp

theorem crossIntLE_upper {xn yn : ℤ} {xd yd m n : ℕ}
    (hxd : 0 < xd) (hyd : 0 < yd) (hn : 0 < n)
    (h : crossIntLE xn xd yn yd m n = true) :
    |(xn : ℝ) / xd| ^ ((m : ℝ) / n) ≤ |(yn : ℝ) / yd| := by
  rw [abs_fraction, abs_fraction]
  apply crossNatLE_upper hxd hyd hn
  simpa only [crossIntLE, Int.natAbs_k_eq] using h

theorem crossIntLE_lower {xn yn : ℤ} {xd yd m n : ℕ}
    (hxd : 0 < xd) (hyd : 0 < yd) (hn : 0 < n)
    (h : crossIntLE yn yd xn xd n m = true) :
    |(yn : ℝ) / yd| ≤ |(xn : ℝ) / xd| ^ ((m : ℝ) / n) := by
  rw [abs_fraction, abs_fraction]
  apply crossNatLE_lower hxd hyd hn
  simpa only [crossIntLE, Int.natAbs_k_eq] using h

theorem crossIntLE_rat_eq (x y : ℚ) (m n : ℕ) :
    crossIntLE x.num x.den y.num y.den m n = G3Power.crossLE x y m n := by
  apply Bool.eq_iff_iff.mpr
  simp [crossIntLE, crossNatLE, G3Power.crossLE, Int.natAbs_k_eq]

end HlawkaSchatten.BelowExponent.G3Power.Kernel
