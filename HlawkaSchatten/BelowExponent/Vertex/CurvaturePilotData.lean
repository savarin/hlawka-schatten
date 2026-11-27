/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCheck
public import HlawkaSchatten.BelowExponent.Vertex.RootData.VcM000
public import HlawkaSchatten.BelowExponent.Vertex.RootData.ScS000
import Mathlib.Tactic.FinCases

/-! Exact curvature caps and positive weight floors for the two vertex pilots. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

def vcM0Caps : Fin 3 → Fin 3 → ℚ := ![
  ![1130427409/4000000, 23375286071/100000000, 725273113/10000000],
  ![10746905379/50000000, 11256223943/50000000, 1827647131/25000000],
  ![329190657/50000000, 355134971/50000000, 13677413/5000000]]

def vcM0WeightFloor : ℚ := 51405381/50000000

def vcM0Margins : Fin 3 → ℚ := ![395057129/10000000000, 365348519/10000000000, 4656573/400000000]

theorem vcM0_caps_nonneg (k i : Fin 3) : 0 ≤ vcM0Caps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM0_margin_le (i : Fin 3) : curvatureLoss vcM0Cell vcM0Caps i ≤ vcM0Margins i := by
  fin_cases i <;> decide +kernel

def scS0Caps : Fin 3 → Fin 3 → ℚ := ![
  ![19524839287/100000000, 146706531/1000000, 2851180657/100000000],
  ![5667312763/50000000, 2366555863/20000000, 638926083/50000000],
  ![59335987/12500000, 47945681/10000000, 37849591/20000000]]

def scS0WeightFloor : ℚ := 53203041/50000000

def scS0Margins : Fin 3 → ℚ := ![15995223/2500000000, 55510273/10000000000, 9543017/10000000000]

theorem scS0_caps_nonneg (k i : Fin 3) : 0 ≤ scS0Caps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS0_margin_le (i : Fin 3) : curvatureLoss scS0Cell scS0Caps i ≤ scS0Margins i := by
  fin_cases i <;> decide +kernel

end HlawkaSchatten.BelowExponent.Vertex
