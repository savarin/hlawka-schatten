/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H1NegPart17`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H1NegPart17Box : Box := ((((⟨![9/68, 9/100, 0, -8], ![9/34, 11/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).upperChild 3 (1/4)

set_option maxRecDepth 16000 in
def CutMid2H1NegPart17Tree : CertTree :=
  .cut 2 (1/2)
    (.cut 2 (1/8)
      (.cut 3 (1/2)
        (.cut 3 (3/8)
          (.cut 3 (5/16)
            (.row ⟨86531900008, 95281442641, (.direct 43500437793 45860602400), (.variance 484926760535)⟩)
            (.row ⟨86531900008, 95281442641, (.direct 58075547817 60457026107), (.variance 442934801897)⟩))
          (.row ⟨86531900008, 95281442641, (.direct 91625662891 93873375423), (.variance 411215050867)⟩))
        (.cut 3 (5/8)
          (.row ⟨86531900008, 95281442641, (.direct 130501749339 132419187593), (.variance 365559408948)⟩)
          (.row ⟨86531900008, 95281442641, (.direct 174227225485 175647706695), (.variance 333567773154)⟩)))
      (.cut 3 (1/2)
        (.cut 3 (3/8)
          (.cut 0 (27/136)
            (.row ⟨86531900008, 95281442641, (.direct 58075547817 59858418833), (.variance 484926760535)⟩)
            (.row ⟨86531900008, 95281442641, (.direct 58075547817 60457026107), (.variance 483090487935)⟩))
          (.row ⟨86531900008, 95281442641, (.direct 91625662891 93873375423), (.variance 411215050867)⟩))
        (.row ⟨86531900008, 95281442641, (.direct 174227225485 175647706695), (.variance 365559408948)⟩)))
    (.row ⟨86531900008, 95281442641, (.direct 174227225485 175647706695), (.variance 484926760535)⟩)

set_option maxRecDepth 16000 in
theorem CutMid2H1NegPart17_checked : CutMid2H1NegPart17Tree.commonOK CutMid2H1NegPart17Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
