/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H3NegRestPart19`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H3NegRestPart19Box : Box := (((((((((⟨![27/68, 9/100, 0, -8], ![9/17, 11/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)).upperChild 3 (0)).lowerChild 3 (1/8)).upperChild 3 (1/16)

set_option maxRecDepth 16000 in
def CutMid2H3NegRestPart19Tree : RatioRemainder :=
  .cut 1 (1/10)
    (.cut 3 (3/32)
      (.cut 1 (19/200)
        (.cut 0 (63/136)
          (.original (.row ⟨86531900008, 88806993133, (.direct 6452795533 8881671835), (.variance 783985642657)⟩))
          (.original (.row ⟨86531900008, 88806993133, (.direct 6452795533 9251563474), (.variance 772399754274)⟩)))
        (.cut 0 (63/136)
          (.original (.row ⟨88806993132, 91020629598, (.direct 6452795533 9024458654), (.variance 779863908153)⟩))
          (.original (.row ⟨88806993132, 91020629598, (.direct 6452795533 9417279864), (.variance 767834190641)⟩))))
      (.original (.row ⟨86531900008, 91020629598, (.direct 10180561190 13502933456), (.variance 685244347676)⟩)))
    (.cut 3 (3/32)
      (.cut 0 (63/136)
        (.cut 1 (21/200)
          (.original (.row ⟨91020629597, 93177423805, (.direct 6452795533 9168844330), (.variance 775794010747)⟩))
          (.original (.row ⟨93177423804, 95281442641, (.direct 6452795533 9314844735), (.variance 771774715911)⟩)))
        (.original (.row ⟨91020629597, 95281442641, (.direct 6452795533 9754631025), (.variance 763336026995)⟩)))
      (.original (.row ⟨91020629597, 95281442641, (.direct 10180561190 13874427330), (.variance 680213407856)⟩)))

set_option maxRecDepth 16000 in
theorem CutMid2H3NegRestPart19_ok : CutMid2H3NegRestPart19Tree.geometryOK CutMid2H3NegPowerCache CutMid2H3NegRestPart19Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
