/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Tangent.FineData

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[expose] public section

namespace HlawkaSchatten.BelowExponent.TC

set_option maxRecDepth 100000 in
theorem fine_tab_ok : tabOK fine_prof fine_tab = true := by decide +kernel

end HlawkaSchatten.BelowExponent.TC
