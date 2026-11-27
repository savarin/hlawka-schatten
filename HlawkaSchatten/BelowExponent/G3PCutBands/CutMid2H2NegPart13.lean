/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H2NegPart13`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H2NegPart13Box : Box := (((((((((((((⟨![9/34, 9/100, 0, -8], ![27/68, 11/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)).upperChild 3 (0)).lowerChild 3 (1/8)).lowerChild 3 (1/16)).upperChild 1 (1/10)).upperChild 1 (21/200)).upperChild 0 (45/136)).upperChild 3 (1/32)

set_option maxRecDepth 16000 in
def CutMid2H2NegPart13Tree : CertTree :=
  .cut 2 (1/16)
    (.row ⟨93177423804, 95281442641, (.direct 3393509060 5438924473), (.variance 960987072524)⟩)
    (.cut 2 (3/32)
      (.row ⟨93177423804, 95281442641, (.direct 3393509060 5438924473), (.chord (.secant 1581128677165 281774039607 10274321865 98330605209) 3393555298 6452870597)⟩)
      (.row ⟨93177423804, 95281442641, (.direct 3393509060 5438924473), (.chord (.secant 1224710403322 111796290756 61398302 62325374623) 6452870597 10180665226)⟩))

set_option maxRecDepth 16000 in
theorem CutMid2H2NegPart13_checked : CutMid2H2NegPart13Tree.commonOK CutMid2H2NegPart13Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
