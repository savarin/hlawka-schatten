/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual

/-! # Basic definitions for Hlawka inequalities -/

namespace HlawkaSchatten

/-- The unit sphere of a normed additive group, as a type. -/
abbrev unitSphere (E : Type*) [NormedAddCommGroup E] :=
  {x : E // ‖x‖ = 1}

end HlawkaSchatten
