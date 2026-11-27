/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid1H1NegRestPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid1H1NegRestPart0Box : Box := (((⟨![9/68, 7/100, 0, -8], ![9/34, 9/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutMid1H1NegRestPart0Tree : RatioRemainder :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.original (.row ⟨76698504228, 86531900009, (.direct 3523554676644 3440358400461), (.variance 141828236449)⟩))
          (.original (.row ⟨76698504228, 86531900009, (.direct 824633666698 800316814064), (.variance 207781477512)⟩)))
        (.cut 3 (-5)
          (.original (.row ⟨76698504228, 86531900009, (.direct 3523554676644 3440358400461), (.variance 141828236449)⟩))
          (.original (.row ⟨76698504228, 86531900009, (.direct 824633666698 800316814064), (.variance 207781477512)⟩))))
      (.cut 3 (-5)
        (.original (.row ⟨76698504228, 86531900009, (.direct 3523554676644 3440358400461), (.variance 141828236449)⟩))
        (.original (.row ⟨76698504228, 86531900009, (.direct 824633666698 800316814064), (.variance 207781477512)⟩))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-9/8)
          (.original (.row ⟨76698504228, 86531900009, (.direct 331294831298 319009280992), (.variance 264367056495)⟩))
          (.original (.row ⟨76698504228, 86531900009, (.direct 30541785600 27578575652), (.variance 501908366984)⟩)))
        (.cut 3 (-9/8)
          (.original (.row ⟨76698504228, 86531900009, (.direct 331294831298 319009280992), (.variance 264367056495)⟩))
          (.original (.row ⟨76698504228, 86531900009, (.direct 30541785600 27578575652), (.variance 501908366984)⟩))))
      (.cut 3 (-9/8)
        (.original (.row ⟨76698504228, 86531900009, (.direct 331294831298 319009280992), (.variance 264367056495)⟩))
        (.original (.row ⟨76698504228, 86531900009, (.direct 30541785600 27578575652), (.chord .universal 91625974997 274877906944)⟩))))

set_option maxRecDepth 16000 in
theorem CutMid1H1NegRestPart0_ok : CutMid1H1NegRestPart0Tree.ok CutMid1H1NegRestPart0Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
