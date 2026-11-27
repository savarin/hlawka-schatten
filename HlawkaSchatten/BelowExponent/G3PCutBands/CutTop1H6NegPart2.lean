/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H6NegPart2`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H6NegPart2Box : Box := (((((((((⟨![27/68, 4/25, 0, -8], ![63/136, 17/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 3 (0)).lowerChild 2 (5/16)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutTop1H6NegPart2Tree : CertTree :=
  .cut 2 (7/32)
    (.cut 3 (-3/16)
      (.row ⟨114055813619, 117423580140, (.direct 19358451269 11690844908), (.variance 628385699313)⟩)
      (.row ⟨114055813619, 117423580140, (.direct 10180561190 4683575983), (.chord (.midpoint ⟨392909412243, 173188565694, 193479884069, 352649440621, 231790882392, 152382538768⟩) 10180665226 24716235638)⟩))
    (.cut 3 (-3/16)
      (.row ⟨114055813619, 117423580140, (.direct 19358451269 11690844908), (.chord (.midpoint ⟨350856693453, 205970998101, 210752050146, 331890472288, 247105625488, 202122005131⟩) 24716235638 43500686443)⟩)
      (.row ⟨114055813619, 117423580140, (.direct 10180561190 4683575983), (.chord (.midpoint ⟨446385685926, 136219750831, 170863647112, 385165158535, 212133776261, 252870788554⟩) 24716235638 43500686443)⟩))

set_option maxRecDepth 16000 in
theorem CutTop1H6NegPart2_checked : CutTop1H6NegPart2Tree.commonOK CutTop1H6NegPart2Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
