/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H3NegRestPart24`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H3NegRestPart24Box : Box := ((⟨![27/68, 9/100, 0, -8], ![9/17, 11/100, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutMid2H3NegRestPart24Tree : RatioRemainder :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.original (.cone))
          (.original (.row ⟨86531900008, 95281442641, .zero, (.variance 308939524654)⟩)))
        (.original (.row ⟨86531900008, 95281442641, .zero, (.variance 308939524654)⟩)))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (13/8)
            (.cut 3 (23/16)
              (.original (.row ⟨86531900008, 95281442641, (.direct 391506126583 387689490001), (.variance 251207852934)⟩))
              (.original (.row ⟨86531900008, 95281442641, (.direct 488587506629 481346290990), (.variance 237369924202)⟩)))
            (.original (.row ⟨86531900008, 95281442641, (.direct 593382169971 582276592390), (.variance 225827921414)⟩)))
          (.original (.row ⟨86531900008, 95281442641, (.direct 391506126583 387689490001), (.variance 251207852934)⟩)))
        (.original (.row ⟨86531900008, 95281442641, (.direct 391506126583 387689490001), (.variance 251207852934)⟩))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.cut 3 (11/4)
              (.original (.row ⟨86531900008, 95281442641, (.direct 824633666698 804591213603), (.variance 207491861910)⟩))
              (.original (.row ⟨86531900008, 95281442641, (.direct 1366046989981 1323843984892), (.variance 182125921572)⟩)))
            (.original (.row ⟨86531900008, 95281442641, (.direct 2002014560937 1932640649632), (.variance 164947269344)⟩)))
          (.original (.row ⟨86531900008, 95281442641, (.direct 3523554676644 3386914840243), (.variance 142410878982)⟩)))
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.original (.row ⟨86531900008, 95281442641, (.direct 824633666698 804591213603), (.variance 207491861910)⟩))
            (.original (.row ⟨86531900008, 95281442641, (.direct 2002014560937 1932640649632), (.variance 164947269344)⟩)))
          (.original (.row ⟨86531900008, 95281442641, (.direct 3523554676644 3386914840243), (.variance 142410878982)⟩))))
      (.original (.row ⟨86531900008, 95281442641, (.direct 824633666698 804591213603), (.variance 207491861910)⟩)))

set_option maxRecDepth 16000 in
theorem CutMid2H3NegRestPart24_ok : CutMid2H3NegRestPart24Tree.geometryOK CutMid2H3NegPowerCache CutMid2H3NegRestPart24Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
