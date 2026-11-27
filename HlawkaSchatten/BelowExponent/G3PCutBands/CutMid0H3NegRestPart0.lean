/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid0H3NegRestPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid0H3NegRestPart0Box : Box := (((⟨![27/68, 1/20, 0, -8], ![9/17, 7/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutMid0H3NegRestPart0Tree : RatioRemainder :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.original (.row ⟨65259754744, 76698504229, (.direct 3523554676644 3395769820676), (.variance 142313543113)⟩))
          (.original (.row ⟨65259754744, 76698504229, (.direct 824633666698 787309783186), (.variance 208674927782)⟩)))
        (.cut 3 (-5)
          (.original (.row ⟨65259754744, 76698504229, (.direct 3523554676644 3395769820676), (.variance 142313543113)⟩))
          (.original (.row ⟨65259754744, 76698504229, (.direct 824633666698 787309783186), (.variance 208674927782)⟩))))
      (.original (.row ⟨65259754744, 76698504229, (.direct 824633666698 787309783186), (.variance 208674927782)⟩)))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.original (.row ⟨65259754744, 76698504229, (.direct 30541785600 26026778923), (.variance 509577886408)⟩))
        (.cut 3 (-9/8)
          (.original (.row ⟨65259754744, 76698504229, (.direct 331294831298 312453301389), (.variance 265808461943)⟩))
          (.original (.row ⟨65259754744, 76698504229, (.direct 30541785600 26026778923), (.variance 509577886408)⟩))))
      (.original (.row ⟨65259754744, 76698504229, (.direct 30541785600 26026778923), (.variance 509577886408)⟩)))

set_option maxRecDepth 16000 in
theorem CutMid0H3NegRestPart0_ok : CutMid0H3NegRestPart0Tree.ok CutMid0H3NegRestPart0Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
