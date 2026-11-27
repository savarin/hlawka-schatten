/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H2NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H2NegRestPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H2NegRestPart0Box : Box := (((⟨![9/34, 9/100, 0, -8], ![27/68, 11/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutMid2H2NegRestPart0Tree : RatioRemainder :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.original (.row ⟨86531900008, 95281442641, (.direct 3523554676644 3369971974709), (.variance 142598016759)⟩))
          (.original (.row ⟨86531900008, 95281442641, (.direct 824633666698 779791620156), (.variance 209199887431)⟩)))
        (.cut 3 (-5)
          (.original (.row ⟨86531900008, 95281442641, (.direct 3523554676644 3369971974709), (.variance 142598016759)⟩))
          (.cut 3 (-7/2)
            (.original (.row ⟨86531900008, 95281442641, (.direct 2002014560937 1908569423760), (.variance 165489502159)⟩))
            (.original (.row ⟨86531900008, 95281442641, (.direct 824633666698 779791620156), (.variance 209199887431)⟩)))))
      (.cut 3 (-5)
        (.original (.row ⟨86531900008, 95281442641, (.direct 3523554676644 3369971974709), (.variance 142598016759)⟩))
        (.original (.row ⟨86531900008, 95281442641, (.direct 824633666698 779791620156), (.variance 209199887431)⟩))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-9/8)
          (.original (.row ⟨86531900008, 95281442641, (.direct 331294831298 308668776471), (.variance 266658021181)⟩))
          (.original (.row ⟨86531900008, 95281442641, (.direct 30541785600 25140822935), (.variance 514220262554)⟩)))
        (.cut 3 (-9/8)
          (.original (.row ⟨86531900008, 95281442641, (.direct 331294831298 308668776471), (.variance 266658021181)⟩))
          (.cut 0 (45/136)
            (.cut 3 (-11/16)
              (.original (.row ⟨86531900008, 95281442641, (.direct 151782739331 140569779521), (.variance 327646762711)⟩))
              (.original (.row ⟨86531900008, 95281442641, (.direct 30541785600 26013948199), (.variance 509643689284)⟩)))
            (.cut 3 (-11/16)
              (.original (.row ⟨86531900008, 95281442641, (.direct 151782739331 138365421402), (.variance 329005674542)⟩))
              (.original (.row ⟨86531900008, 95281442641, (.direct 30541785600 25140822935), (.variance 514220262554)⟩))))))
      (.cut 3 (-9/8)
        (.original (.row ⟨86531900008, 95281442641, (.direct 331294831298 308668776471), (.variance 266658021181)⟩))
        (.cut 0 (45/136)
          (.cut 3 (-11/16)
            (.original (.row ⟨86531900008, 95281442641, (.direct 151782739331 140569779521), (.variance 327646762711)⟩))
            (.original (.row ⟨86531900008, 95281442641, (.direct 30541785600 26013948199), (.variance 509643689284)⟩)))
          (.cut 3 (-11/16)
            (.original (.row ⟨86531900008, 95281442641, (.direct 151782739331 138365421402), (.variance 329005674542)⟩))
            (.original (.row ⟨86531900008, 95281442641, (.direct 30541785600 25140822935), (.variance 514220262554)⟩))))))

set_option maxRecDepth 16000 in
theorem CutMid2H2NegRestPart0_ok : CutMid2H2NegRestPart0Tree.geometryOK CutMid2H2NegPowerCache CutMid2H2NegRestPart0Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
