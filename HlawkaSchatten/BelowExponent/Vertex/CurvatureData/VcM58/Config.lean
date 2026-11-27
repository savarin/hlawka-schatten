/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCheck
public import HlawkaSchatten.BelowExponent.Vertex.RootData.VcM048
meta import Mathlib.Tactic.FinCases

/-! Curvature caps and floor for vcM58. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def vcM58Caps : Fin 3 → Fin 3 → ℚ := ![![19559359249/100000000, 3562955687/20000000, 4933164707/100000000], ![27541343219/100000000, 937366509/3125000, 1372389169/12500000], ![98287817/20000000, 247007041/50000000, 109279879/50000000]]
def vcM58WeightFloor : ℚ := 26180443/25000000
def vcM58Margins : Fin 3 → ℚ := ![372714199/10000000000, 378284381/10000000000, 25284539/2000000000]

theorem vcM58_caps_nonneg (k i : Fin 3) : 0 ≤ vcM58Caps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM58_margin_le (i : Fin 3) : curvatureLoss vcM58Cell vcM58Caps i ≤ vcM58Margins i := by
  fin_cases i <;> decide +kernel


end HlawkaSchatten.BelowExponent.Vertex
