/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CurvatureData.VcM58.Config
meta import Mathlib.Tactic.FinCases

/-! The exact caps from the 16 by 18 by 1 cover of the original VC-M 58 box. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def vcM58PilotCaps : Fin 3 → Fin 3 → ℚ := ![![4904360149/25000000, 17815485397/100000000, 492491249/10000000], ![6659326657/25000000, 14564111073/50000000, 2624996857/25000000], ![102789637/12500000, 206292291/25000000, 365604909/100000000]]
def vcM58PilotFloor : ℚ := 51731319/50000000

theorem vcM58Pilot_caps_nonneg (k j : Fin 3) : 0 ≤ vcM58PilotCaps k j := by
  fin_cases k <;> fin_cases j <;> decide +kernel

theorem vcM58Pilot_margins (j : Fin 3) : curvatureLoss vcM58Cell vcM58PilotCaps j ≤ vcM58Margins j := by
  fin_cases j <;> decide +kernel


end HlawkaSchatten.BelowExponent.Vertex
