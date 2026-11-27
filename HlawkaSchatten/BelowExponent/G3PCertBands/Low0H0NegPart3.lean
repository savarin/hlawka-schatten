/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCertData

/-! Generated central G3 row witnesses. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def Low0H0NegPart3Box : Box := (((((⟨![0, 7/10000, 0, -8], ![9/17, 1/20, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).upperChild 2 (1/2)

def Low0H0NegPart3Tree : CertTree :=
  .row ⟨8409823756, 65259754745, (.direct 30541785600 32536707074), (.chord .universal 91625974997 274877906944)⟩

set_option maxRecDepth 16000 in
theorem Low0H0NegPart3_ok : Low0H0NegPart3Tree.ok Low0H0NegPart3Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
