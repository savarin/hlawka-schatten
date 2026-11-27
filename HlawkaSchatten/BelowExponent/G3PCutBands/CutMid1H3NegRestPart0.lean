/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H3NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid1H3NegRestPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid1H3NegRestPart0Box : Box := (((⟨![27/68, 7/100, 0, -8], ![9/17, 9/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutMid1H3NegRestPart0Tree : RatioRemainder :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.original (.row ⟨76698504228, 86531900009, (.direct 3523554676644 3357870746848), (.variance 142732405878)⟩))
          (.original (.row ⟨76698504228, 86531900009, (.direct 824633666698 776266898129), (.variance 209448206883)⟩)))
        (.cut 3 (-5)
          (.original (.row ⟨76698504228, 86531900009, (.direct 3523554676644 3357870746848), (.variance 142732405878)⟩))
          (.original (.row ⟨76698504228, 86531900009, (.direct 824633666698 776266898129), (.variance 209448206883)⟩))))
      (.cut 3 (-5)
        (.original (.row ⟨76698504228, 86531900009, (.direct 3523554676644 3357870746848), (.variance 142732405878)⟩))
        (.original (.row ⟨76698504228, 86531900009, (.direct 824633666698 776266898129), (.variance 209448206883)⟩))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-9/8)
          (.original (.row ⟨76698504228, 86531900009, (.direct 331294831298 306895739647), (.variance 267060570977)⟩))
          (.original (.row ⟨76698504228, 86531900009, (.direct 30541785600 24728301493), (.variance 516452875501)⟩)))
        (.cut 3 (-9/8)
          (.original (.row ⟨76698504228, 86531900009, (.direct 331294831298 306895739647), (.variance 267060570977)⟩))
          (.original (.row ⟨76698504228, 86531900009, (.direct 30541785600 24728301493), (.variance 516452875501)⟩))))
      (.cut 3 (-9/8)
        (.original (.row ⟨76698504228, 86531900009, (.direct 331294831298 306895739647), (.variance 267060570977)⟩))
        (.original (.row ⟨76698504228, 86531900009, (.direct 30541785600 24728301493), (.variance 516452875501)⟩))))

set_option maxRecDepth 16000 in
theorem CutMid1H3NegRestPart0_ok : CutMid1H3NegRestPart0Tree.geometryOK CutMid1H3NegPowerCache CutMid1H3NegRestPart0Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
