/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H0NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H0NegRestPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H0NegRestPart0Box : Box := (((⟨![0, 11/100, 0, -8], ![9/68, 13/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutMid3H0NegRestPart0Tree : RatioRemainder :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.original (.row ⟨95281442640, 103236350716, (.direct 3523554676644 3462119450297), (.variance 141594259829)⟩))
          (.original (.row ⟨95281442640, 103236350716, (.direct 824633666698 806670557967), (.variance 207351675197)⟩)))
        (.cut 3 (-5)
          (.original (.row ⟨95281442640, 103236350716, (.direct 3523554676644 3462119450297), (.variance 141594259829)⟩))
          (.cut 3 (-7/2)
            (.original (.row ⟨95281442640, 103236350716, (.direct 2002014560937 1964619077466), (.variance 164239956095)⟩))
            (.original (.row ⟨95281442640, 103236350716, (.direct 824633666698 806670557967), (.variance 207351675197)⟩)))))
      (.cut 3 (-5)
        (.cut 3 (-13/2)
          (.original (.row ⟨95281442640, 103236350716, (.direct 5340438828596 5250903663652), (.variance 126963255871)⟩))
          (.original (.row ⟨95281442640, 103236350716, (.direct 3523554676644 3462119450297), (.variance 141594259829)⟩)))
        (.cut 3 (-7/2)
          (.original (.row ⟨95281442640, 103236350716, (.direct 2002014560937 1964619077466), (.variance 164239956095)⟩))
          (.original (.row ⟨95281442640, 103236350716, (.direct 824633666698 806670557967), (.variance 207351675197)⟩)))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.original (.row ⟨95281442640, 103236350716, (.direct 30541785600 28345145725), (.variance 498317925345)⟩))
        (.cut 3 (-9/8)
          (.original (.row ⟨95281442640, 103236350716, (.direct 331294831298 322215598114), (.variance 263675654679)⟩))
          (.cut 3 (-11/16)
            (.original (.row ⟨95281442640, 103236350716, (.direct 151782739331 146385909214), (.variance 324186733298)⟩))
            (.cut 0 (9/136)
              (.cut 3 (-15/32)
                (.original (.row ⟨95281442640, 103236350716, (.direct 82716570280 80835021937), (.variance 378729164407)⟩))
                (.cut 0 (9/272)
                  (.original (.row ⟨95281442640, 103236350716, (.direct 30541785600 29987117627), (.variance 491023710944)⟩))
                  (.original (.row ⟨95281442640, 103236350716, (.direct 30541785600 29436005352), (.variance 493414565585)⟩))))
              (.cut 3 (-15/32)
                (.original (.row ⟨95281442640, 103236350716, (.direct 82716570280 78969197562), (.variance 381052211518)⟩))
                (.cut 0 (27/272)
                  (.original (.row ⟨95281442640, 103236350716, (.direct 30541785600 28888675173), (.variance 495845581970)⟩))
                  (.original (.row ⟨95281442640, 103236350716, (.direct 30541785600 28345145725), (.variance 498317925345)⟩))))))))
      (.cut 3 (-9/8)
        (.original (.row ⟨95281442640, 103236350716, (.direct 331294831298 322215598114), (.variance 263675654679)⟩))
        (.cut 3 (-11/16)
          (.original (.row ⟨95281442640, 103236350716, (.direct 151782739331 146385909214), (.variance 324186733298)⟩))
          (.cut 3 (-15/32)
            (.original (.row ⟨95281442640, 103236350716, (.direct 82716570280 78969197562), (.variance 381052211518)⟩))
            (.covered)))))

set_option maxRecDepth 16000 in
theorem CutMid3H0NegRestPart0_ok : CutMid3H0NegRestPart0Tree.geometryOK CutMid3H0NegPowerCache CutMid3H0NegRestPart0Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
