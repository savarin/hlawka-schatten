/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H1NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H1NegRestPart9`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H1NegRestPart9Box : Box := ((((((⟨![9/68, 11/100, 0, -8], ![9/34, 13/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutMid3H1NegRestPart9Tree : RatioRemainder :=
  .cut 2 (5/16)
    (.cut 3 (0)
      (.cut 1 (3/25)
        (.cut 3 (-1/8)
          (.cut 2 (7/32)
            (.cut 3 (-3/16)
              (.original (.row ⟨95281442640, 99345187400, (.direct 19358451269 16179639437), (.variance 577127672606)⟩))
              (.cut 2 (11/64)
                (.original (.row ⟨95281442640, 99345187400, (.direct 10180561190 7838508693), (.chord (.midpoint ⟨391986761321, 173871274110, 219901786402, 322032249713, 232127691969, 138149362466⟩) 10180665226 16864782083)⟩))
                (.original (.row ⟨95281442640, 99345187400, (.direct 10180561190 7838508693), (.chord (.midpoint ⟨459615364821, 127827059142, 193905369550, 352100233560, 207213025660, 222667602000⟩) 16864782083 24716235638)⟩))))
            (.cut 3 (-3/16)
              (.original (.row ⟨95281442640, 99345187400, (.direct 19358451269 16179639437), (.chord (.midpoint ⟨432911017914, 145066929800, 204267804186, 339331515245, 217118061086, 211032909798⟩) 24716235638 43500686443)⟩))
              (.covered)))
          (.covered))
        (.cut 3 (-1/8)
          (.cut 2 (7/32)
            (.cut 3 (-3/16)
              (.original (.row ⟨99345187399, 103236350716, (.direct 19358451269 15906611987), (.variance 579705395684)⟩))
              (.cut 2 (11/64)
                (.original (.row ⟨99345187399, 103236350716, (.direct 10180561190 7640863183), (.chord (.midpoint ⟨396893335687, 170258811455, 218039402810, 323981447233, 230335917432, 139994717235⟩) 10180665226 16864782083)⟩))
                (.original (.row ⟨99345187399, 103236350716, (.direct 10180561190 7640863183), (.chord (.midpoint ⟨463701060016, 125292890394, 192305565176, 354175995851, 205687293849, 223627179208⟩) 16864782083 24716235638)⟩))))
            (.cut 3 (-3/16)
              (.original (.row ⟨99345187399, 103236350716, (.direct 19358451269 15906611987), (.chord (.midpoint ⟨435862809641, 143102649657, 203129680078, 340679382723, 216028360643, 211857463489⟩) 24716235638 43500686443)⟩))
              (.covered)))
          (.covered)))
      (.cut 3 (1/8)
        (.cut 1 (3/25)
          (.cut 2 (7/32)
            (.cut 3 (1/16)
              (.covered)
              (.cut 3 (3/32)
                (.covered)
                (.cut 2 (11/64)
                  (.original (.row ⟨95281442640, 99345187400, (.direct 10180561190 12154093105), (.chord (.secant 1556407025831 268768906304 45472718468 117855075964) 10180665226 16864782083)⟩))
                  (.covered))))
            (.covered))
          (.cut 2 (7/32)
            (.cut 3 (1/16)
              (.covered)
              (.cut 3 (3/32)
                (.covered)
                (.cut 2 (11/64)
                  (.cut 2 (19/128)
                    (.original (.row ⟨99345187399, 103236350716, (.direct 10180561190 12336180585), (.chord (.secant 1565124797688 273337724496 69097170611 150265695440) 10180665226 13368036905)⟩))
                    (.covered))
                  (.covered))))
            (.covered)))
        (.cut 2 (7/32)
          (.cut 2 (11/64)
            (.cut 3 (3/16)
              (.cut 3 (5/32)
                (.cut 2 (19/128)
                  (.original (.row ⟨95281442640, 103236350716, (.direct 14500097491 16849496788), (.chord (.secant 1773095696633 387473307856 129777038584 227508898335) 10180665226 13368036905)⟩))
                  (.original (.row ⟨95281442640, 103236350716, (.direct 14500097491 16849496788), (.chord (.secant 1588716635165 285795817586 92144246219 180337056421) 13368036905 16864782083)⟩)))
                (.cut 2 (19/128)
                  (.original (.row ⟨95281442640, 103236350716, (.direct 19358451269 21861761805), (.chord (.secant 1990489064361 515663811502 205257810907 318053541655) 10180665226 13368036905)⟩))
                  (.original (.row ⟨95281442640, 103236350716, (.direct 19358451269 21861761805), (.chord (.secant 1764150157483 382377860121 149932679228 252108228959) 13368036905 16864782083)⟩))))
              (.cut 3 (7/32)
                (.cut 2 (19/128)
                  (.original (.row ⟨95281442640, 103236350716, (.direct 24716051037 27339878487), (.chord (.secant 2217023474797 656888074370 292782337881 419322378307) 10180665226 13368036905)⟩))
                  (.original (.row ⟨95281442640, 103236350716, (.direct 24716051037 27339878487), (.chord (.secant 1946273858429 488956018301 217477542196 332380045038) 13368036905 16864782083)⟩)))
                (.cut 2 (19/128)
                  (.original (.row ⟨95281442640, 103236350716, (.direct 30541785600 33257230137), (.chord (.secant 2452444262125 810341244124 391268728340 530561407802) 10180665226 13368036905)⟩))
                  (.original (.row ⟨95281442640, 103236350716, (.direct 30541785600 33257230137), (.chord (.secant 2134917664476 604903517814 293861862098 420554765841) 13368036905 16864782083)⟩)))))
            (.cut 3 (3/16)
              (.cut 3 (5/32)
                (.covered)
                (.original (.row ⟨95281442640, 103236350716, (.direct 19358451269 21861761805), (.chord (.secant 1605956024451 294984346313 85684589679 172022364817) 16864782083 24716235638)⟩)))
              (.cut 3 (7/32)
                (.original (.row ⟨95281442640, 103236350716, (.direct 24716051037 27339878487), (.chord (.secant 1757654805130 378687738347 129196713975 226794798710) 16864782083 24716235638)⟩))
                (.original (.row ⟨95281442640, 103236350716, (.direct 30541785600 33257230137), (.chord (.secant 1914348145537 469863313266 178965703799 286959737061) 16864782083 24716235638)⟩)))))
          (.cut 3 (3/16)
            (.covered)
            (.cut 2 (17/64)
              (.original (.row ⟨95281442640, 103236350716, (.direct 30541785600 33257230137), (.chord (.secant 1629461982782 307625266417 81597820388 166719823565) 24716235638 33622326476)⟩))
              (.covered))))))
    (.covered)

set_option maxRecDepth 16000 in
theorem CutMid3H1NegRestPart9_ok : CutMid3H1NegRestPart9Tree.geometryOK CutMid3H1NegPowerCache CutMid3H1NegRestPart9Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
