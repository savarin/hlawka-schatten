/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H3NegRestPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H3NegRestPart0Box : Box := (((⟨![27/68, 9/100, 0, -8], ![9/17, 11/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutMid2H3NegRestPart0Tree : RatioRemainder :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.original (.row ⟨86531900008, 95281442641, (.direct 3523554676644 3319331824465), (.variance 143164502576)⟩))
          (.original (.row ⟨86531900008, 95281442641, (.direct 824633666698 765049823158), (.variance 210248026272)⟩)))
        (.cut 3 (-5)
          (.original (.row ⟨86531900008, 95281442641, (.direct 3523554676644 3319331824465), (.variance 143164502576)⟩))
          (.original (.row ⟨86531900008, 95281442641, (.direct 824633666698 765049823158), (.variance 210248026272)⟩))))
      (.cut 3 (-5)
        (.original (.row ⟨86531900008, 95281442641, (.direct 3523554676644 3319331824465), (.variance 143164502576)⟩))
        (.original (.row ⟨86531900008, 95281442641, (.direct 824633666698 765049823158), (.variance 210248026272)⟩))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.original (.row ⟨86531900008, 95281442641, (.direct 30541785600 23427826359), (.variance 523810892788)⟩))
        (.cut 3 (-9/8)
          (.original (.row ⟨86531900008, 95281442641, (.direct 331294831298 301258636919), (.variance 268360174485)⟩))
          (.cut 0 (63/136)
            (.cut 3 (-11/16)
              (.original (.row ⟨86531900008, 95281442641, (.direct 151782739331 136173949011), (.variance 330383996176)⟩))
              (.original (.row ⟨86531900008, 95281442641, (.direct 30541785600 24278748508), (.variance 518940056205)⟩)))
            (.cut 3 (-11/16)
              (.original (.row ⟨86531900008, 95281442641, (.direct 151782739331 133995416333), (.variance 331782205599)⟩))
              (.original (.row ⟨86531900008, 95281442641, (.direct 30541785600 23427826359), (.variance 523810892788)⟩))))))
      (.cut 0 (63/136)
        (.cut 3 (-9/8)
          (.original (.row ⟨86531900008, 95281442641, (.direct 331294831298 304955399755), (.variance 267504482012)⟩))
          (.cut 3 (-11/16)
            (.original (.row ⟨86531900008, 95281442641, (.direct 151782739331 136173949011), (.variance 330383996176)⟩))
            (.original (.row ⟨86531900008, 95281442641, (.direct 30541785600 24278748508), (.variance 518940056205)⟩))))
        (.cut 3 (-9/8)
          (.original (.row ⟨86531900008, 95281442641, (.direct 331294831298 301258636919), (.variance 268360174485)⟩))
          (.cut 3 (-11/16)
            (.original (.row ⟨86531900008, 95281442641, (.direct 151782739331 133995416333), (.variance 331782205599)⟩))
            (.original (.row ⟨86531900008, 95281442641, (.direct 30541785600 23427826359), (.variance 523810892788)⟩))))))

set_option maxRecDepth 16000 in
theorem CutMid2H3NegRestPart0_ok : CutMid2H3NegRestPart0Tree.ok CutMid2H3NegRestPart0Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
