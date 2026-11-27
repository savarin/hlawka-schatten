/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H0NegPart8`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H0NegPart8Box : Box := (((((((((((⟨![0, 9/100, 0, -8], ![9/68, 11/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 2 (5/16)).lowerChild 3 (0)).lowerChild 2 (7/32)).upperChild 1 (1/10)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutMid2H0NegPart8Tree : CertTree :=
  .cut 1 (21/200)
    (.row ⟨91020629597, 93177423805, (.direct 10180561190 9136412464), (.chord .universal 10180665226 24716235638)⟩)
    (.cut 0 (9/136)
      (.row ⟨93177423804, 95281442641, (.direct 10180561190 9627028444), (.chord .universal 10180665226 24716235638)⟩)
      (.row ⟨93177423804, 95281442641, (.direct 10180561190 9084901347), (.variance 671284535891)⟩))

set_option maxRecDepth 16000 in
theorem CutMid2H0NegPart8_checked : CutMid2H0NegPart8Tree.commonOK CutMid2H0NegPart8Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
