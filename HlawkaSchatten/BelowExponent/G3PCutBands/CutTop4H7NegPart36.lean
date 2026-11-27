/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H7NegPart36`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H7NegPart36Box : Box := ((((((((⟨![63/136, 19/100, 0, -8], ![9/17, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).upperChild 2 (1/2)).lowerChild 2 (3/4)).lowerChild 3 (0)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutTop4H7NegPart36Tree : CertTree :=
  .cut 0 (135/272)
    (.cut 3 (-3/16)
      (.row ⟨123862991199, 126950446638, (.direct 19358451269 9797767092), (.chord (.midpoint ⟨454867404036, 130806058099, 159483090083, 404469934755, 208982365950, 294521615362⟩) 91625974997 174227471798)⟩)
      (.row ⟨123862991199, 126950446638, (.direct 10180561190 3433189219), (.chord (.midpoint ⟨496866369589, 105702804617, 139998894149, 443646981069, 193176906087, 312348888093⟩) 91625974997 174227471798)⟩))
    (.cut 3 (-3/16)
      (.row ⟨123862991199, 126950446638, (.direct 19358451269 9247956506), (.chord (.midpoint ⟨440644192175, 139952159602, 162006020820, 399990659574, 214260717140, 290768038917⟩) 91625974997 174227471798)⟩)
      (.row ⟨123862991199, 126950446638, (.direct 10180561190 3082652371), (.chord (.midpoint ⟨482003012289, 114268821763, 142840786428, 437366160319, 198813131255, 308685887107⟩) 91625974997 174227471798)⟩))

set_option maxRecDepth 16000 in
theorem CutTop4H7NegPart36_checked : CutTop4H7NegPart36Tree.commonOK CutTop4H7NegPart36Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
