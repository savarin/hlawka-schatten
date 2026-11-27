/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Tangent.TreeData
public import HlawkaSchatten.BelowExponent.Tangent.FineTable
public import HlawkaSchatten.BelowExponent.Tangent.Sound

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[expose] public section

namespace HlawkaSchatten.BelowExponent.TC

set_option maxRecDepth 100000 in
theorem R002_tree_ok : treeOK R002_hdr R002_tree R002_geoms = true := by decide +kernel

/-- The fine header satisfies the positivity guard for the real exponent bracket. -/
theorem R002_exponent_denominators_pos : 0 < R002_hdr.prof.k1 ∧ 0 < R002_hdr.prof.k2 := by
  decide

/-- Every certified partition leaf occurs exactly in its traversal position. -/
theorem R002_walkCT_eq : walkCT R002_hdr R002_tree (root R002_hdr) = some R002_geoms :=
  walkCT_eq_of_treeOK R002_tree_ok

set_option maxRecDepth 10000 in
theorem R002_geoms_length : R002_geoms.length = 167 := by rfl

end HlawkaSchatten.BelowExponent.TC
