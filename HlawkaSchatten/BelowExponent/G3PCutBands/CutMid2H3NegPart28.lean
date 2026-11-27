/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H3NegPart28`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H3NegPart28Box : Box := ((((⟨![27/68, 9/100, 0, -8], ![9/17, 11/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).upperChild 3 (1/4)

set_option maxRecDepth 16000 in
def CutMid2H3NegPart28Tree : CertTree :=
  .cut 2 (1/2)
    (.cut 2 (1/8)
      (.cut 3 (1/2)
        (.cut 3 (3/8)
          (.row ⟨86531900008, 95281442641, (.direct 58075547817 62873353995), (.variance 477720609253)⟩)
          (.row ⟨86531900008, 95281442641, (.direct 91625662891 96140811507), (.variance 407753879984)⟩))
        (.cut 3 (5/8)
          (.row ⟨86531900008, 95281442641, (.direct 130501749339 134346623517), (.variance 363695046526)⟩)
          (.row ⟨86531900008, 95281442641, (.direct 174227225485 177072192555), (.variance 332540963073)⟩)))
      (.cut 3 (1/2)
        (.cut 3 (3/8)
          (.row ⟨86531900008, 95281442641, (.direct 58075547817 62873353995), (.variance 477720609253)⟩)
          (.row ⟨86531900008, 95281442641, (.direct 91625662891 96140811507), (.variance 407753879984)⟩))
        (.row ⟨86531900008, 95281442641, (.direct 174227225485 177072192555), (.variance 363695046526)⟩)))
    (.row ⟨86531900008, 95281442641, (.direct 174227225485 177072192555), (.variance 477720609253)⟩)

set_option maxRecDepth 16000 in
theorem CutMid2H3NegPart28_checked : CutMid2H3NegPart28Tree.commonOK CutMid2H3NegPart28Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
