/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H3NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid1H3NegRestPart12`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid1H3NegRestPart12Box : Box := ((((((⟨![27/68, 7/100, 0, -8], ![9/17, 9/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutMid1H3NegRestPart12Tree : RatioRemainder :=
  .cut 2 (5/16)
    (.cut 3 (0)
      (.cut 2 (7/32)
        (.cut 1 (2/25)
          (.cut 1 (3/40)
            (.cut 3 (-1/8)
              (.original (.row ⟨76698504228, 79281022314, (.direct 10180561190 7352335882), (.variance 709529075087)⟩))
              (.covered))
            (.cut 3 (-1/8)
              (.original (.row ⟨79281022313, 81775466253, (.direct 10180561190 7168719696), (.variance 714243660188)⟩))
              (.covered)))
          (.cut 3 (-1/8)
            (.cut 2 (11/64)
              (.original (.row ⟨81775466252, 86531900009, (.direct 10180561190 6803841782), (.variance 724081256540)⟩))
              (.original (.row ⟨81775466252, 86531900009, (.direct 10180561190 6803841782), (.chord (.midpoint ⟨347687454099, 208585076952, 212042034850, 330456629790, 248258484509, 85697228890⟩) 16864782083 24716235638)⟩)))
            (.covered)))
        (.cut 1 (2/25)
          (.cut 3 (-1/8)
            (.original (.row ⟨76698504228, 81775466253, (.direct 10180561190 7168719696), (.chord (.midpoint ⟨407688355831, 162466316938, 187318653912, 360840466460, 226387490816, 163171890046⟩) 24716235638 43500686443)⟩))
            (.covered))
          (.cut 3 (-1/8)
            (.original (.row ⟨81775466252, 86531900009, (.direct 10180561190 6803841782), (.chord (.midpoint ⟨412938361496, 158752531450, 185115460293, 363882311728, 224463615414, 166005201872⟩) 24716235638 43500686443)⟩))
            (.covered))))
      (.cut 2 (7/32)
        (.cut 3 (1/8)
          (.cut 1 (2/25)
            (.cut 3 (1/16)
              (.covered)
              (.cut 2 (11/64)
                (.cut 3 (3/32)
                  (.covered)
                  (.original (.row ⟨76698504228, 81775466253, (.direct 10180561190 12782493823), (.chord (.secant 1371847479399 176942276750 6260394489 129308265217) 10180665226 16864782083)⟩)))
                (.covered)))
            (.cut 3 (1/16)
              (.covered)
              (.cut 2 (11/64)
                (.cut 3 (3/32)
                  (.covered)
                  (.original (.row ⟨81775466252, 86531900009, (.direct 10180561190 13139005456), (.chord (.secant 1387819135121 184484597124 7522496149 133054919510) 10180665226 16864782083)⟩)))
                (.covered))))
          (.cut 0 (63/136)
            (.cut 1 (2/25)
              (.original (.row ⟨76698504228, 81775466253, (.direct 30541785600 33392124625), (.variance 626100874367)⟩))
              (.cut 0 (117/272)
                (.cut 3 (3/16)
                  (.original (.row ⟨81775466252, 86531900009, (.direct 19358451269 22121915184), (.variance 622593494013)⟩))
                  (.original (.row ⟨81775466252, 86531900009, (.direct 30541785600 33537409290), (.variance 535046590360)⟩)))
                (.original (.row ⟨81775466252, 86531900009, (.direct 30541785600 33772089160), (.variance 620372152549)⟩))))
            (.cut 1 (2/25)
              (.original (.row ⟨76698504228, 81775466253, (.direct 30541785600 33806907894), (.variance 622177092348)⟩))
              (.cut 0 (135/272)
                (.original (.row ⟨81775466252, 86531900009, (.direct 30541785600 34007372449), (.variance 618177602193)⟩))
                (.original (.row ⟨81775466252, 86531900009, (.direct 30541785600 34243258062), (.variance 616009296134)⟩))))))
        (.cut 3 (1/8)
          (.covered)
          (.cut 3 (3/16)
            (.covered)
            (.original (.row ⟨76698504228, 86531900009, (.direct 30541785600 34243258062), (.variance 536982703926)⟩))))))
    (.covered)

set_option maxRecDepth 16000 in
theorem CutMid1H3NegRestPart12_ok : CutMid1H3NegRestPart12Tree.geometryOK CutMid1H3NegPowerCache CutMid1H3NegRestPart12Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
