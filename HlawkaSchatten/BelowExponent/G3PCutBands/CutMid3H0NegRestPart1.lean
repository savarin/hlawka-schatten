/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H0NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H0NegRestPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H0NegRestPart1Box : Box := (((((((⟨![0, 11/100, 0, -8], ![9/68, 13/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)).lowerChild 3 (0)

set_option maxRecDepth 16000 in
def CutMid3H0NegRestPart1Tree : RatioRemainder :=
  .cut 1 (3/25)
    (.cut 3 (-1/8)
      (.original (.row ⟨95281442640, 99345187400, (.direct 10180561190 8981384302), (.variance 673301994573)⟩))
      (.cut 1 (23/200)
        (.cut 0 (9/136)
          (.original (.row ⟨95281442640, 97336292160, (.direct 0 44145112), (.chord .universal 0 10180665226)⟩))
          (.original (.row ⟨95281442640, 97336292160, (.direct 0 132435327), (.chord .universal 0 10180665226)⟩)))
        (.cut 0 (9/136)
          (.original (.row ⟨97336292159, 99345187400, (.direct 0 47424896), (.chord .universal 0 10180665226)⟩))
          (.original (.row ⟨97336292159, 99345187400, (.direct 0 142274679), (.chord .universal 0 10180665226)⟩)))))
    (.cut 3 (-1/8)
      (.original (.row ⟨99345187399, 103236350716, (.direct 10180561190 8877205668), (.variance 675362189801)⟩))
      (.cut 1 (1/8)
        (.cut 0 (9/136)
          (.original (.row ⟨99345187399, 101311009181, (.direct 0 50808801), (.chord .universal 0 10180665226)⟩))
          (.original (.row ⟨99345187399, 101311009181, (.direct 0 152426393), (.chord .universal 0 10180665226)⟩)))
        (.original (.row ⟨101311009180, 103236350716, (.direct 0 162890367), (.chord .universal 0 10180665226)⟩))))

set_option maxRecDepth 16000 in
theorem CutMid3H0NegRestPart1_ok : CutMid3H0NegRestPart1Tree.geometryOK CutMid3H0NegPowerCache CutMid3H0NegRestPart1Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
