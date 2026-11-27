/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H3NegPart8`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H3NegPart8Box : Box := ((((((((((⟨![27/68, 11/100, 0, -8], ![9/17, 13/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 2 (5/16)).lowerChild 3 (0)).lowerChild 1 (3/25)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutMid3H3NegPart8Tree : CertTree :=
  .cut 2 (7/32)
    (.cut 3 (-3/16)
      (.row ⟨95281442640, 99345187400, (.direct 19358451269 13216227450), (.variance 608526129614)⟩)
      (.row ⟨95281442640, 99345187400, (.direct 10180561190 5730453280), (.chord (.midpoint ⟨369550448072, 190969534573, 203113836194, 340698237550, 240304315623, 104088499379⟩) 10180665226 24716235638)⟩))
    (.cut 0 (63/136)
      (.row ⟨95281442640, 99345187400, (.direct 10180561190 6234514579), (.chord (.midpoint ⟨421394330878, 152873578642, 181549181660, 368939520942, 221359168784, 188758483376⟩) 24716235638 43500686443)⟩)
      (.row ⟨95281442640, 99345187400, (.direct 10180561190 5730453280), (.chord (.midpoint ⟨395693031063, 171138420460, 185379726313, 363514191671, 230774394241, 179317813337⟩) 24716235638 43500686443)⟩))

set_option maxRecDepth 16000 in
theorem CutMid3H3NegPart8_checked : CutMid3H3NegPart8Tree.commonOK CutMid3H3NegPart8Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
