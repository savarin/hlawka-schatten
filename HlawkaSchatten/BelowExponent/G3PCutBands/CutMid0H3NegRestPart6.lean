/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid0H3NegRestPart6`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid0H3NegRestPart6Box : Box := ((⟨![27/68, 1/20, 0, -8], ![9/17, 7/100, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutMid0H3NegRestPart6Tree : RatioRemainder :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.original (.cone))
          (.original (.row ⟨65259754744, 76698504229, .zero, (.variance 309302507133)⟩)))
        (.original (.row ⟨65259754744, 76698504229, .zero, (.variance 309302507133)⟩)))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (13/8)
            (.cut 3 (23/16)
              (.original (.row ⟨65259754744, 76698504229, (.direct 391506126583 389126236032), (.variance 250964645209)⟩))
              (.original (.row ⟨65259754744, 76698504229, (.direct 488587506629 484070604924), (.variance 237019382086)⟩)))
            (.original (.row ⟨65259754744, 76698504229, (.direct 593382169971 586452891497), (.variance 225405697577)⟩)))
          (.original (.row ⟨65259754744, 76698504229, (.direct 391506126583 389126236032), (.variance 250964645209)⟩)))
        (.original (.row ⟨65259754744, 76698504229, (.direct 391506126583 389126236032), (.variance 250964645209)⟩))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.cut 3 (11/4)
              (.original (.row ⟨65259754744, 76698504229, (.direct 824633666698 812123393169), (.variance 206986207536)⟩))
              (.original (.row ⟨65259754744, 76698504229, (.direct 1366046989981 1339692273724), (.variance 181559269947)⟩)))
            (.original (.row ⟨65259754744, 76698504229, (.direct 2002014560937 1958681039983), (.variance 164370193180)⟩)))
          (.original (.row ⟨65259754744, 76698504229, (.direct 3523554676644 3438180308380), (.variance 141851758260)⟩)))
        (.cut 3 (5)
          (.original (.row ⟨65259754744, 76698504229, (.direct 824633666698 812123393169), (.variance 206986207536)⟩))
          (.original (.row ⟨65259754744, 76698504229, (.direct 3523554676644 3438180308380), (.variance 141851758260)⟩))))
      (.original (.row ⟨65259754744, 76698504229, (.direct 824633666698 812123393169), (.variance 206986207536)⟩)))

set_option maxRecDepth 16000 in
theorem CutMid0H3NegRestPart6_ok : CutMid0H3NegRestPart6Tree.ok CutMid0H3NegRestPart6Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
