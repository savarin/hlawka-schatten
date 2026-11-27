/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3HeadDataCore

/-! Exact endpoint comparisons for depth band 1 of the G3 head chart. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

public section

namespace HlawkaSchatten.BelowExponent

open G3HeadData

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem headCornerChecksBand1 : ∀ upper j, headPairOK 1 upper j := by
  decide +kernel

end HlawkaSchatten.BelowExponent
