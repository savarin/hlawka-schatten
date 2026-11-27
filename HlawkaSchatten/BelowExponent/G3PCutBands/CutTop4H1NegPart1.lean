/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H1NegPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H1NegPart1Box : Box := ((((((⟨![9/136, 19/100, 0, -8], ![9/68, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutTop4H1NegPart1Tree : CertTree :=
  .cut 3 (0)
    (.row ⟨123862991199, 126950446638, (.direct 0 342516976), (.chord .universal 0 10180665226)⟩)
    (.cut 3 (1/8)
      (.cut 3 (1/16)
        (.cut 1 (39/200)
          (.cut 0 (27/272)
            (.row ⟨123862991199, 125417011706, (.direct 3393509060 4298605156), (.chord .universal 0 10180665226)⟩)
            (.row ⟨123862991199, 125417011706, (.direct 3393509060 4617524614), (.chord .universal 0 10180665226)⟩))
          (.row ⟨125417011705, 126950446638, (.direct 3393509060 4654401306), (.chord .universal 0 10180665226)⟩))
        (.cut 3 (3/32)
          (.cut 2 (1/16)
            (.row ⟨123862991199, 126950446638, (.direct 6452795533 7966106447), (.variance 833735663771)⟩)
            (.row ⟨123862991199, 126950446638, (.direct 6452795533 7966106447), (.chord (.secant 2136981480793 606199575017 69436828886 107212820014) 3393555298 10180665226)⟩))
          (.cut 3 (7/64)
            (.row ⟨123862991199, 126950446638, (.direct 8238656156 9856321484), (.variance 714653505468)⟩)
            (.row ⟨123862991199, 126950446638, (.direct 10180561190 11891045277), (.variance 673142434426)⟩))))
      (.cut 3 (3/16)
        (.cut 3 (5/32)
          (.row ⟨123862991199, 126950446638, (.direct 14500097491 16367232989), (.variance 638848149465)⟩)
          (.row ⟨123862991199, 126950446638, (.direct 19358451269 21350007720), (.variance 584920779177)⟩))
        (.cut 3 (7/32)
          (.row ⟨123862991199, 126950446638, (.direct 24716051037 26805089813), (.variance 543908433932)⟩)
          (.row ⟨123862991199, 126950446638, (.direct 30541785600 32705028659), (.variance 511291853767)⟩))))

set_option maxRecDepth 16000 in
theorem CutTop4H1NegPart1_checked : CutTop4H1NegPart1Tree.commonOK CutTop4H1NegPart1Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
