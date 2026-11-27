/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid0H3NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid0H3NegRestPart3`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid0H3NegRestPart3Box : Box := ((((((⟨![27/68, 1/20, 0, -8], ![9/17, 7/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutMid0H3NegRestPart3Tree : RatioRemainder :=
  .cut 2 (5/16)
    (.cut 2 (7/32)
      (.cut 3 (0)
        (.cut 1 (3/50)
          (.cut 2 (11/64)
            (.cut 1 (11/200)
              (.cut 3 (-1/8)
                (.original (.row ⟨65259754744, 68314662357, (.direct 10180561190 8093944250), (.variance 691897117218)⟩))
                (.covered))
              (.cut 3 (-1/8)
                (.original (.row ⟨68314662356, 71228276419, (.direct 10180561190 7907528276), (.variance 696131678505)⟩))
                (.covered)))
            (.cut 1 (11/200)
              (.cut 3 (-1/8)
                (.original (.row ⟨65259754744, 68314662357, (.direct 10180561190 8093944250), (.variance 691897117218)⟩))
                (.covered))
              (.cut 3 (-1/8)
                (.original (.row ⟨68314662356, 71228276419, (.direct 10180561190 7907528276), (.variance 696131678505)⟩))
                (.covered))))
          (.cut 1 (13/200)
            (.cut 2 (11/64)
              (.cut 3 (-1/8)
                (.original (.row ⟨71228276418, 74018153447, (.direct 10180561190 7721769440), (.variance 700478509374)⟩))
                (.covered))
              (.cut 3 (-1/8)
                (.original (.row ⟨71228276418, 74018153447, (.direct 10180561190 7721769440), (.chord (.midpoint ⟨330349164189, 223263475354, 219079699331, 322889165502, 254568370205, 73692021887⟩) 16864782083 24716235638)⟩))
                (.covered)))
            (.cut 3 (-1/8)
              (.original (.row ⟨74018153446, 76698504229, (.direct 10180561190 7536695702), (.variance 704942555932)⟩))
              (.covered))))
        (.cut 3 (1/8)
          (.cut 1 (3/50)
            (.cut 2 (11/64)
              (.cut 3 (1/16)
                (.covered)
                (.cut 3 (3/32)
                  (.covered)
                  (.original (.row ⟨65259754744, 71228276419, (.direct 10180561190 12091140688), (.chord (.secant 1340598090357 162433678660 4035971918 122046427346) 10180665226 16864782083)⟩))))
              (.covered))
            (.cut 3 (1/16)
              (.covered)
              (.cut 2 (11/64)
                (.cut 3 (3/32)
                  (.covered)
                  (.original (.row ⟨71228276418, 76698504229, (.direct 10180561190 12433252883), (.chord (.secant 1356108609600 169593136707 5097606354 125639268786) 10180665226 16864782083)⟩)))
                (.covered))))
          (.original (.row ⟨65259754744, 76698504229, (.direct 30541785600 33377116207), (.variance 633209548660)⟩))))
      (.cut 3 (0)
        (.cut 1 (3/50)
          (.cut 1 (11/200)
            (.cut 0 (63/136)
              (.original (.row ⟨65259754744, 68314662357, (.direct 0 285130388), (.chord .universal 24716235638 43500686443)⟩))
              (.cut 3 (-1/8)
                (.original (.row ⟨65259754744, 68314662357, (.direct 10180561190 8093944250), (.chord (.midpoint ⟨362460033857, 196576551733, 199413770620, 345171464403, 242884572460, 159790422503⟩) 24716235638 43500686443)⟩))
                (.covered)))
            (.cut 3 (-1/8)
              (.original (.row ⟨68314662356, 71228276419, (.direct 10180561190 7907528276), (.chord (.midpoint ⟨397423389334, 169871221481, 191604074927, 355095523649, 230142253808, 158911181618⟩) 24716235638 43500686443)⟩))
              (.covered)))
          (.cut 1 (13/200)
            (.cut 3 (-1/8)
              (.original (.row ⟨71228276418, 74018153447, (.direct 10180561190 7721769440), (.chord (.midpoint ⟨399960722462, 168022997414, 190547409511, 356491538429, 229214912961, 160332992337⟩) 24716235638 43500686443)⟩))
              (.covered))
            (.cut 3 (-1/8)
              (.original (.row ⟨74018153446, 76698504229, (.direct 10180561190 7536695702), (.chord (.midpoint ⟨402517203555, 166172728305, 189481062586, 357913825095, 228280076861, 161753192235⟩) 24716235638 43500686443)⟩))
              (.covered))))
        (.cut 3 (1/8)
          (.covered)
          (.original (.row ⟨65259754744, 76698504229, (.direct 30541785600 33377116207), (.variance 633209548660)⟩)))))
    (.covered)

set_option maxRecDepth 16000 in
theorem CutMid0H3NegRestPart3_ok : CutMid0H3NegRestPart3Tree.geometryOK CutMid0H3NegPowerCache CutMid0H3NegRestPart3Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
