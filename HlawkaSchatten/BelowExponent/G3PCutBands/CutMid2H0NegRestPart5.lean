/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H0NegRestPart5`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H0NegRestPart5Box : Box := ((((((((⟨![0, 9/100, 0, -8], ![9/68, 11/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)).upperChild 3 (0)).upperChild 3 (1/8)

set_option maxRecDepth 16000 in
def CutMid2H0NegRestPart5Tree : RatioRemainder :=
  .cut 3 (3/16)
    (.cut 1 (1/10)
      (.cut 0 (9/136)
        (.cut 3 (5/32)
          (.cut 1 (19/200)
            (.original (.row ⟨86531900008, 88806993133, (.direct 14500097491 14911921441), (.variance 651562574406)⟩))
            (.cut 3 (9/64)
              (.original (.row ⟨88806993132, 91020629598, (.direct 12270063068 12686693390), (.variance 651562574406)⟩))
              (.original (.row ⟨88806993132, 91020629598, (.direct 14500097491 14934854038), (.variance 620477318811)⟩))))
          (.original (.row ⟨86531900008, 91020629598, (.direct 19358451269 19823740362), (.variance 593929411221)⟩)))
        (.cut 3 (5/32)
          (.cut 1 (19/200)
            (.original (.row ⟨86531900008, 88806993133, (.direct 14500097491 15327851461), (.variance 645749412144)⟩))
            (.original (.row ⟨88806993132, 91020629598, (.direct 14500097491 15374197395), (.variance 645415782684)⟩)))
          (.original (.row ⟨86531900008, 91020629598, (.direct 19358451269 20292933420), (.variance 589827430208)⟩))))
      (.cut 0 (9/136)
        (.cut 3 (5/32)
          (.cut 1 (21/200)
            (.cut 3 (9/64)
              (.original (.row ⟨91020629597, 93177423805, (.direct 12270063068 12708815225), (.variance 651562574406)⟩))
              (.original (.row ⟨91020629597, 93177423805, (.direct 14500097491 14957920757), (.variance 620477318811)⟩)))
            (.cut 3 (9/64)
              (.cut 0 (9/272)
                (.original (.row ⟨93177423804, 95281442641, (.direct 12270063068 12499840906), (.variance 651562574406)⟩))
                (.original (.row ⟨93177423804, 95281442641, (.direct 12270063068 12731068441), (.variance 648123239061)⟩)))
              (.original (.row ⟨93177423804, 95281442641, (.direct 14500097491 14981122763), (.variance 620477318811)⟩))))
          (.cut 1 (21/200)
            (.original (.row ⟨91020629597, 93177423805, (.direct 19358451269 19848398559), (.variance 593929411221)⟩))
            (.original (.row ⟨93177423804, 95281442641, (.direct 19358451269 19873198623), (.variance 593929411221)⟩))))
        (.cut 3 (5/32)
          (.cut 1 (21/200)
            (.original (.row ⟨91020629597, 93177423805, (.direct 14500097491 15420839928), (.variance 645080988873)⟩))
            (.original (.row ⟨93177423804, 95281442641, (.direct 14500097491 15467781787), (.variance 644745024388)⟩)))
          (.original (.row ⟨91020629597, 95281442641, (.direct 19358451269 20392752152), (.variance 589353945291)⟩)))))
    (.cut 1 (1/10)
      (.original (.row ⟨86531900008, 91020629598, (.direct 30541785600 31559779622), (.variance 550644921433)⟩))
      (.cut 0 (9/136)
        (.original (.row ⟨91020629597, 95281442641, (.direct 30541785600 31103216055), (.variance 550644921433)⟩))
        (.original (.row ⟨91020629597, 95281442641, (.direct 30541785600 31668201037), (.variance 547232011331)⟩))))

set_option maxRecDepth 16000 in
theorem CutMid2H0NegRestPart5_ok : CutMid2H0NegRestPart5Tree.ok CutMid2H0NegRestPart5Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
