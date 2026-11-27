/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid1H3NegRestPart15`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid1H3NegRestPart15Box : Box := ((⟨![27/68, 7/100, 0, -8], ![9/17, 9/100, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutMid1H3NegRestPart15Tree : RatioRemainder :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.original (.cone))
          (.original (.row ⟨76698504228, 86531900009, .zero, (.variance 309122715000)⟩)))
        (.original (.row ⟨76698504228, 86531900009, .zero, (.variance 309122715000)⟩)))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (13/8)
            (.cut 3 (23/16)
              (.original (.row ⟨76698504228, 86531900009, (.direct 391506126583 388415140089), (.variance 251084875346)⟩))
              (.original (.row ⟨76698504228, 86531900009, (.direct 488587506629 482722002125), (.variance 237192597087)⟩)))
            (.original (.row ⟨76698504228, 86531900009, (.direct 593382169971 584385230578), (.variance 225614262192)⟩)))
          (.original (.row ⟨76698504228, 86531900009, (.direct 391506126583 388415140089), (.variance 251084875346)⟩)))
        (.original (.row ⟨76698504228, 86531900009, (.direct 391506126583 388415140089), (.variance 251084875346)⟩))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.cut 3 (11/4)
              (.original (.row ⟨76698504228, 86531900009, (.direct 824633666698 808393501364), (.variance 207235861578)⟩))
              (.original (.row ⟨76698504228, 86531900009, (.direct 1366046989981 1331842404806), (.variance 181838876562)⟩)))
            (.original (.row ⟨76698504228, 86531900009, (.direct 2002014560937 1945781104987), (.variance 164654848111)⟩)))
          (.original (.row ⟨76698504228, 86531900009, (.direct 3523554676644 3412780453796), (.variance 142127454051)⟩)))
        (.cut 3 (5)
          (.original (.row ⟨76698504228, 86531900009, (.direct 824633666698 808393501364), (.variance 207235861578)⟩))
          (.original (.row ⟨76698504228, 86531900009, (.direct 3523554676644 3412780453796), (.variance 142127454051)⟩))))
      (.original (.row ⟨76698504228, 86531900009, (.direct 824633666698 808393501364), (.variance 207235861578)⟩)))

set_option maxRecDepth 16000 in
theorem CutMid1H3NegRestPart15_ok : CutMid1H3NegRestPart15Tree.ok CutMid1H3NegRestPart15Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
