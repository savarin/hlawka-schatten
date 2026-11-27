/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H1NegRestPart12`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H1NegRestPart12Box : Box := ((⟨![9/68, 11/100, 0, -8], ![9/34, 13/100, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutMid3H1NegRestPart12Tree : RatioRemainder :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.original (.cone))
          (.original (.row ⟨95281442640, 103236350716, .zero, (.variance 309408241841)⟩)))
        (.original (.row ⟨95281442640, 103236350716, .zero, (.variance 309408241841)⟩)))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (13/8)
            (.original (.row ⟨95281442640, 103236350716, (.direct 391506126583 389225233346), (.variance 250947929002)⟩))
            (.original (.row ⟨95281442640, 103236350716, (.direct 593382169971 586740849968), (.variance 225376724869)⟩)))
          (.original (.row ⟨95281442640, 103236350716, (.direct 391506126583 389225233346), (.variance 250947929002)⟩)))
        (.original (.row ⟨95281442640, 103236350716, (.direct 391506126583 389225233346), (.variance 250947929002)⟩))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.original (.row ⟨95281442640, 103236350716, (.direct 824633666698 812642963642), (.variance 206951545778)⟩))
            (.original (.row ⟨95281442640, 103236350716, (.direct 2002014560937 1960478744956), (.variance 164330712160)⟩)))
          (.original (.row ⟨95281442640, 103236350716, (.direct 3523554676644 3441720572437), (.variance 141813535531)⟩)))
        (.cut 3 (5)
          (.original (.row ⟨95281442640, 103236350716, (.direct 824633666698 812642963642), (.variance 206951545778)⟩))
          (.original (.row ⟨95281442640, 103236350716, (.direct 3523554676644 3441720572437), (.variance 141813535531)⟩))))
      (.original (.row ⟨95281442640, 103236350716, (.direct 824633666698 812642963642), (.variance 206951545778)⟩)))

set_option maxRecDepth 16000 in
theorem CutMid3H1NegRestPart12_ok : CutMid3H1NegRestPart12Tree.ok CutMid3H1NegRestPart12Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
