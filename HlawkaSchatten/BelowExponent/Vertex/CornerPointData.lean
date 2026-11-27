/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.RadicalCheck

/-! Rational coordinates and margin budgets for shared VC and SC corners. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

structure SideCornerEntry where
  a : ℚ
  b : ℚ
  eta : ℚ
  margin : Vector ℚ 3

def SideCornerEntry.cell (p : SideCornerEntry) : ParameterCell :=
  ⟨.point p.a, .point p.b, .point p.eta⟩

end HlawkaSchatten.BelowExponent.Vertex
