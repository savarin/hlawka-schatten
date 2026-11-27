/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Tangent.ProfileTree
public import HlawkaSchatten.BelowExponent.Tangent.Root

/-! The exact E2 profile-tree cover, with only the partition and centre geometry as inputs. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Tangent

private theorem fine_root_geometry : CellGeometry (TC.root TC.R002_hdr) := by
  constructor <;> decide

/-- Every ordered point in the E2 domain belongs to a checked leaf, including the cube surface. -/
theorem mem_fine_leaf_of_outside_cube {t : Profile} (ht : OrderedInterior t) (hd : 1 / 500 ≤ t 3)
    (hOut : ∃ i, 1 / 500 ≤ |t i - 1 / 4|) : ∃ G ∈ TC.R002_geoms, t ∈ cellSet G := by
  apply walkCT_covers_outside_cube (by decide : 0 < TC.R002_hdr.rcD) fine_root_geometry
    TC.R002_walkCT_eq (mem_fine_root ht hd)
  have hrad : (TC.R002_hdr.rcN : ℝ) / TC.R002_hdr.rcD = 1 / 500 := by norm_num [TC.R002_hdr]
  rwa [hrad]

end HlawkaSchatten.BelowExponent.Tangent
