/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid0H2NegRestPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid0H2NegRestPart1Box : Box := ((⟨![9/34, 1/20, 0, -8], ![27/68, 7/100, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutMid0H2NegRestPart1Tree : RatioRemainder :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.original (.cone))
          (.original (.row ⟨65259754744, 76698504229, .zero, (.variance 309447348912)⟩)))
        (.original (.row ⟨65259754744, 76698504229, .zero, (.variance 309447348912)⟩)))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (13/8)
            (.original (.row ⟨65259754744, 76698504229, (.direct 391506126583 389720813662), (.variance 250864328291)⟩))
            (.original (.row ⟨65259754744, 76698504229, (.direct 593382169971 588182746936), (.variance 225231918953)⟩)))
          (.original (.row ⟨65259754744, 76698504229, (.direct 391506126583 389720813662), (.variance 250864328291)⟩)))
        (.original (.row ⟨65259754744, 76698504229, (.direct 391506126583 389720813662), (.variance 250864328291)⟩))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.original (.row ⟨65259754744, 76698504229, (.direct 824633666698 815245041515), (.variance 206778374835)⟩))
            (.original (.row ⟨65259754744, 76698504229, (.direct 2002014560937 1969484657631), (.variance 164133610574)⟩)))
          (.original (.row ⟨65259754744, 76698504229, (.direct 3523554676644 3459458327159), (.variance 141622772719)⟩)))
        (.cut 3 (5)
          (.original (.row ⟨65259754744, 76698504229, (.direct 824633666698 815245041515), (.variance 206778374835)⟩))
          (.original (.row ⟨65259754744, 76698504229, (.direct 3523554676644 3459458327159), (.variance 141622772719)⟩))))
      (.original (.row ⟨65259754744, 76698504229, (.direct 824633666698 815245041515), (.variance 206778374835)⟩)))

set_option maxRecDepth 16000 in
theorem CutMid0H2NegRestPart1_ok : CutMid0H2NegRestPart1Tree.ok CutMid0H2NegRestPart1Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
