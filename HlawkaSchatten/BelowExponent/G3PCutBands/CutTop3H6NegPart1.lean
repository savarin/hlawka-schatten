/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H6NegPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H6NegPart1Box : Box := ((((((⟨![27/68, 9/50, 0, -8], ![63/136, 19/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutTop3H6NegPart1Tree : CertTree :=
  .cut 3 (0)
    (.row ⟨120689819474, 123862991200, (.direct 0 2279757842), (.chord .universal 0 10180665226)⟩)
    (.cut 3 (1/8)
      (.cut 3 (1/16)
        (.cut 3 (1/32)
          (.cut 3 (1/64)
            (.row ⟨120689819474, 123862991200, (.direct 377054043 3479330686), (.chord .universal 0 10180665226)⟩)
            (.row ⟨120689819474, 123862991200, (.direct 1131165907 4856210701), (.variance 921103982926)⟩))
          (.row ⟨120689819474, 123862991200, (.direct 3393509060 8085590294), (.variance 832336507559)⟩))
        (.row ⟨120689819474, 123862991200, (.direct 10180561190 16196901941), (.variance 716829722510)⟩))
      (.cut 3 (3/16)
        (.row ⟨120689819474, 123862991200, (.direct 19358451269 26211593380), (.variance 589089701317)⟩)
        (.row ⟨120689819474, 123862991200, (.direct 30541785600 37899295126), (.variance 515876864776)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop3H6NegPart1_checked : CutTop3H6NegPart1Tree.commonOK CutTop3H6NegPart1Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
