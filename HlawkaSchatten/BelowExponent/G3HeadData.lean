/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3HeadDataCore
import HlawkaSchatten.BelowExponent.G3HeadDepths.Band0
import HlawkaSchatten.BelowExponent.G3HeadDepths.Band1
import HlawkaSchatten.BelowExponent.G3HeadDepths.Band2
import HlawkaSchatten.BelowExponent.G3HeadDepths.Band3

/-! All four certified G3 head depth bands. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

public section

namespace HlawkaSchatten.BelowExponent

open G3HeadData

private theorem headCornerChecks (i : Fin 4) : ∀ upper j, headPairOK i upper j := by
  fin_cases i
  · exact headCornerChecksBand0
  · exact headCornerChecksBand1
  · exact headCornerChecksBand2
  · exact headCornerChecksBand3

end HlawkaSchatten.BelowExponent
