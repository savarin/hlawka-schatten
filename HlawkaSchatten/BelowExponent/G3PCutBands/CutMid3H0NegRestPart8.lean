/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H0NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H0NegRestPart8`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H0NegRestPart8Box : Box := ((((⟨![0, 11/100, 0, -8], ![9/68, 13/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).upperChild 3 (1/4)

set_option maxRecDepth 16000 in
def CutMid3H0NegRestPart8Tree : RatioRemainder :=
  .cut 2 (1/2)
    (.cut 2 (1/8)
      (.cut 3 (1/2)
        (.cut 3 (3/8)
          (.cut 3 (5/16)
            (.cut 1 (3/25)
              (.cut 0 (9/136)
                (.original (.row ⟨95281442640, 99345187400, (.direct 43500437793 44143140465), (.variance 488671898726)⟩))
                (.original (.row ⟨95281442640, 99345187400, (.direct 43500437793 44789064067), (.variance 486347404289)⟩)))
              (.cut 0 (9/136)
                (.original (.row ⟨99345187399, 103236350716, (.direct 43500437793 44200568773), (.variance 488671898726)⟩))
                (.original (.row ⟨99345187399, 103236350716, (.direct 43500437793 44904565310), (.variance 486124591239)⟩))))
            (.cut 0 (9/136)
              (.original (.row ⟨95281442640, 103236350716, (.direct 58075547817 58783187426), (.variance 445447029174)⟩))
              (.original (.row ⟨95281442640, 103236350716, (.direct 58075547817 59493702655), (.variance 443889820057)⟩))))
          (.cut 3 (7/16)
            (.original (.row ⟨95281442640, 103236350716, (.direct 74148400816 75543784771), (.variance 412983663964)⟩))
            (.original (.row ⟨95281442640, 103236350716, (.direct 91625662891 92965770783), (.variance 387389137214)⟩))))
        (.cut 3 (5/8)
          (.cut 3 (9/16)
            (.original (.row ⟨95281442640, 103236350716, (.direct 110431305439 111686810503), (.variance 366503899985)⟩))
            (.original (.row ⟨95281442640, 103236350716, (.direct 130501749339 131645779515), (.variance 349018446009)⟩)))
          (.cut 3 (11/16)
            (.original (.row ⟨95281442640, 103236350716, (.direct 151782739331 152790380498), (.variance 334085249950)⟩))
            (.original (.row ⟨95281442640, 103236350716, (.direct 174227225485 175075165445), (.variance 321127709228)⟩)))))
      (.cut 0 (9/136)
        (.cut 3 (1/2)
          (.cut 0 (9/272)
            (.cut 3 (3/8)
              (.cut 3 (5/16)
                (.cut 1 (3/25)
                  (.original (.row ⟨95281442640, 99345187400, (.direct 43500437793 43821478927), (.variance 488671898726)⟩))
                  (.cut 3 (9/32)
                    (.cut 0 (9/544)
                      (.cut 1 (1/8)
                        (.original (.row ⟨99345187399, 101311009181, (.direct 36810312175 36975125258), (.variance 488671898726)⟩))
                        (.original (.row ⟨101311009180, 103236350716, (.direct 36810312175 36982172312), (.variance 488671898726)⟩)))
                      (.original (.row ⟨99345187399, 103236350716, (.direct 36810312175 37154097456), (.variance 488030805763)⟩)))
                    (.original (.row ⟨99345187399, 103236350716, (.direct 43500437793 43850112261), (.variance 465357958560)⟩))))
                (.original (.row ⟨95281442640, 103236350716, (.direct 58075547817 58429112518), (.variance 445447029174)⟩)))
              (.original (.row ⟨95281442640, 103236350716, (.direct 91625662891 91960250783), (.variance 412983663964)⟩)))
            (.cut 3 (3/8)
              (.cut 3 (5/16)
                (.cut 1 (3/25)
                  (.original (.row ⟨95281442640, 99345187400, (.direct 43500437793 44143140465), (.variance 487504928027)⟩))
                  (.cut 3 (9/32)
                    (.cut 0 (27/544)
                      (.original (.row ⟨99345187399, 103236350716, (.direct 36810312175 37326316720), (.variance 487392571279)⟩))
                      (.original (.row ⟨99345187399, 103236350716, (.direct 36810312175 37498829748), (.variance 486757173588)⟩)))
                    (.original (.row ⟨99345187399, 103236350716, (.direct 43500437793 44200568773), (.variance 464319468179)⟩))))
                (.original (.row ⟨95281442640, 103236350716, (.direct 58075547817 58783187426), (.variance 444666100558)⟩)))
              (.original (.row ⟨95281442640, 103236350716, (.direct 91625662891 92294975628), (.variance 412434769631)⟩))))
          (.original (.row ⟨95281442640, 103236350716, (.direct 174227225485 174651128808), (.variance 366503899985)⟩)))
        (.cut 3 (1/2)
          (.cut 3 (3/8)
            (.cut 0 (27/272)
              (.cut 3 (5/16)
                (.cut 1 (3/25)
                  (.original (.row ⟨95281442640, 99345187400, (.direct 43500437793 44465669396), (.variance 486347404289)⟩))
                  (.cut 3 (9/32)
                    (.cut 0 (45/544)
                      (.original (.row ⟨99345187399, 103236350716, (.direct 36810312175 37671636185), (.variance 486124591239)⟩))
                      (.original (.row ⟨99345187399, 103236350716, (.direct 36810312175 37844735679), (.variance 485494803008)⟩)))
                    (.original (.row ⟨99345187399, 103236350716, (.direct 43500437793 44552053833), (.variance 463288836849)⟩))))
                (.original (.row ⟨95281442640, 103236350716, (.direct 58075547817 59138051219), (.variance 443889820057)⟩)))
              (.cut 3 (5/16)
                (.cut 1 (3/25)
                  (.original (.row ⟨95281442640, 99345187400, (.direct 43500437793 44789064067), (.variance 485199197732)⟩))
                  (.cut 3 (9/32)
                    (.original (.row ⟨99345187399, 103236350716, (.direct 36810312175 38191812430), (.variance 484867787897)⟩))
                    (.original (.row ⟨99345187399, 103236350716, (.direct 43500437793 44904565310), (.variance 462265963602)⟩))))
                (.original (.row ⟨95281442640, 103236350716, (.direct 58075547817 59493702655), (.variance 443118140652)⟩))))
            (.original (.row ⟨95281442640, 103236350716, (.direct 91625662891 92965770783), (.variance 411888354642)⟩)))
          (.original (.row ⟨95281442640, 103236350716, (.direct 174227225485 175075165445), (.variance 365919622566)⟩)))))
    (.original (.row ⟨95281442640, 103236350716, (.direct 174227225485 175075165445), (.chord .universal 91625974997 274877906944)⟩))

set_option maxRecDepth 16000 in
theorem CutMid3H0NegRestPart8_ok : CutMid3H0NegRestPart8Tree.geometryOK CutMid3H0NegPowerCache CutMid3H0NegRestPart8Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
