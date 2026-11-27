/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H7NegPart2`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H7NegPart2Box : Box := ((((((((⟨![63/136, 9/50, 0, -8], ![9/17, 19/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 3 (0)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutTop3H7NegPart2Tree : CertTree :=
  .cut 2 (5/16)
    (.cut 2 (7/32)
      (.cut 3 (-3/16)
        (.row ⟨120689819474, 123862991200, (.direct 19358451269 9733377167), (.variance 659273611795)⟩)
        (.row ⟨120689819474, 123862991200, (.direct 10180561190 3391807444), (.chord (.midpoint ⟨392074252368, 173806467800, 186921830816, 361383814146, 232095756097, 162192708682⟩) 10180665226 24716235638)⟩))
      (.row ⟨120689819474, 123862991200, (.direct 10180561190 3391807444), (.chord (.midpoint ⟨435478093534, 143357821617, 168131203167, 389596040435, 216170450543, 201786673985⟩) 24716235638 43500686443)⟩))
    (.cut 3 (-3/16)
      (.row ⟨120689819474, 123862991200, (.direct 19358451269 9733377167), (.chord (.midpoint ⟨413447229172, 158395176412, 177754235538, 374510913852, 224277001010, 250610440127⟩) 43500686443 91625974997)⟩)
      (.cut 0 (135/272)
        (.row ⟨120689819474, 123862991200, (.direct 10180561190 3734116759), (.chord (.midpoint ⟨470659820704, 121038550783, 152290961496, 417931610883, 203081508453, 287188289845⟩) 43500686443 91625974997)⟩)
        (.row ⟨120689819474, 123862991200, (.direct 10180561190 3391807444), (.chord (.midpoint ⟨457302321880, 129273734823, 154414506271, 413845503291, 208075473659, 283956167006⟩) 43500686443 91625974997)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop3H7NegPart2_checked : CutTop3H7NegPart2Tree.commonOK CutTop3H7NegPart2Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
