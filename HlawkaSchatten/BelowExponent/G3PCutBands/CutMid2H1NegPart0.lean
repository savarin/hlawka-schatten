/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H1NegPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H1NegPart0Box : Box := (((⟨![9/68, 9/100, 0, -8], ![9/34, 11/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutMid2H1NegPart0Tree : CertTree :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.row ⟨86531900008, 95281442641, (.direct 3523554676644 3420894547120), (.variance 142039101150)⟩)
          (.row ⟨86531900008, 95281442641, (.direct 824633666698 794637000009), (.variance 208169352427)⟩))
        (.cut 3 (-5)
          (.row ⟨86531900008, 95281442641, (.direct 3523554676644 3420894547120), (.variance 142039101150)⟩)
          (.cut 3 (-7/2)
            (.row ⟨86531900008, 95281442641, (.direct 2002014560937 1939538576460), (.variance 164793454543)⟩)
            (.row ⟨86531900008, 95281442641, (.direct 824633666698 794637000009), (.variance 208169352427)⟩))))
      (.cut 3 (-5)
        (.row ⟨86531900008, 95281442641, (.direct 3523554676644 3420894547120), (.variance 142039101150)⟩)
        (.row ⟨86531900008, 95281442641, (.direct 824633666698 794637000009), (.variance 208169352427)⟩)))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-9/8)
          (.row ⟨86531900008, 95281442641, (.direct 331294831298 316145161818), (.variance 264992123994)⟩)
          (.row ⟨86531900008, 95281442641, (.direct 30541785600 26898025938), (.variance 505203074715)⟩))
        (.cut 3 (-9/8)
          (.row ⟨86531900008, 95281442641, (.direct 331294831298 316145161818), (.variance 264992123994)⟩)
          (.cut 3 (-11/16)
            (.row ⟨86531900008, 95281442641, (.direct 151782739331 142786970144), (.variance 326306798782)⟩)
            (.cut 0 (27/136)
              (.row ⟨86531900008, 95281442641, (.direct 30541785600 27792960709), (.variance 500891667114)⟩)
              (.row ⟨86531900008, 95281442641, (.direct 30541785600 26898025938), (.variance 505203074715)⟩)))))
      (.cut 3 (-9/8)
        (.row ⟨86531900008, 95281442641, (.direct 331294831298 316145161818), (.variance 264992123994)⟩)
        (.cut 3 (-11/16)
          (.row ⟨86531900008, 95281442641, (.direct 151782739331 142786970144), (.variance 326306798782)⟩)
          (.row ⟨86531900008, 95281442641, (.direct 30541785600 26898025938), (.chord .universal 91625974997 274877906944)⟩))))

set_option maxRecDepth 16000 in
theorem CutMid2H1NegPart0_checked : CutMid2H1NegPart0Tree.commonOK CutMid2H1NegPart0Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
