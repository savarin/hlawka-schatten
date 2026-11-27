/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H3NegPart22`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H3NegPart22Box : Box := (((((((((⟨![27/136, 9/50, 0, -8], ![9/34, 19/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).upperChild 3 (0)).upperChild 2 (5/16)).upperChild 3 (1/8)

set_option maxRecDepth 16000 in
def CutTop3H3NegPart22Tree : CertTree :=
  .cut 3 (3/16)
    (.cut 2 (13/32)
      (.cut 3 (5/32)
        (.row ⟨120689819474, 123862991200, (.direct 14500097491 18097052962), (.chord (.secant 1083895799298 58442930356 5553238247 52055707956) 43500686443 65931360876)⟩)
        (.row ⟨120689819474, 123862991200, (.direct 19358451269 23181125599), (.chord (.secant 1155012149411 84109870420 15158615775 70923210272) 43500686443 65931360876)⟩))
      (.row ⟨120689819474, 123862991200, (.direct 19358451269 23181125599), (.chord (.secant 1042331097516 44850072896 542447834 37457720530) 65931360876 91625974997)⟩))
    (.cut 2 (13/32)
      (.row ⟨120689819474, 123862991200, (.direct 30541785600 34674581032), (.chord (.secant 1302181259700 145070796553 27895025432 91860459769) 43500686443 65931360876)⟩)
      (.row ⟨120689819474, 123862991200, (.direct 30541785600 34674581032), (.chord (.secant 1150898471009 82549917074 12488796593 66100021783) 65931360876 91625974997)⟩))

set_option maxRecDepth 16000 in
theorem CutTop3H3NegPart22_checked : CutTop3H3NegPart22Tree.commonOK CutTop3H3NegPart22Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
