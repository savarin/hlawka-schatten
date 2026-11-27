/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H3NegRestPart18`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H3NegRestPart18Box : Box := (((((((((((⟨![27/68, 9/100, 0, -8], ![9/17, 11/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)).upperChild 3 (0)).lowerChild 3 (1/8)).lowerChild 3 (1/16)).upperChild 1 (1/10)).upperChild 3 (1/32)

set_option maxRecDepth 16000 in
def CutMid2H3NegRestPart18Tree : RatioRemainder :=
  .cut 1 (21/200)
    (.cut 0 (63/136)
      (.cut 3 (3/64)
        (.cut 2 (1/16)
          (.original (.row ⟨91020629597, 93177423805, (.direct 2150924658 4185125679), (.variance 941470138977)⟩))
          (.original (.row ⟨91020629597, 93177423805, (.direct 2150924658 4185125679), (.chord (.secant 1361622908295 172158449720 2479801248 67405397587) 3393555298 10180665226)⟩)))
        (.cut 2 (1/16)
          (.original (.row ⟨91020629597, 93177423805, (.direct 3393509060 5686602913), (.variance 845123168274)⟩))
          (.original (.row ⟨91020629597, 93177423805, (.direct 3393509060 5686602913), (.chord (.secant 1558086238235 269647469946 4163894473 101799925435) 3393555298 10180665226)⟩))))
      (.cut 3 (3/64)
        (.cut 1 (41/400)
          (.cut 2 (1/16)
            (.original (.row ⟨91020629597, 92105866080, (.direct 2150924658 4447804956), (.variance 916994683937)⟩))
            (.original (.row ⟨91020629597, 92105866080, (.direct 2150924658 4447804956), (.chord (.secant 1344766430626 164349502674 6097709857 74538615635) 3393555298 10180665226)⟩)))
          (.cut 0 (135/272)
            (.original (.row ⟨92105866079, 93177423805, (.direct 2150924658 4348766832), (.variance 912712075966)⟩))
            (.original (.row ⟨92105866079, 93177423805, (.direct 2150924658 4514712905), (.variance 901146469422)⟩))))
        (.original (.row ⟨91020629597, 93177423805, (.direct 3393509060 6048664026), (.variance 828279560461)⟩))))
    (.cut 0 (63/136)
      (.cut 3 (3/64)
        (.cut 2 (1/16)
          (.original (.row ⟨93177423804, 95281442641, (.direct 2150924658 4300328683), (.variance 933480654947)⟩))
          (.original (.row ⟨93177423804, 95281442641, (.direct 2150924658 4300328683), (.chord (.secant 1377166315411 179444659616 1857422587 69635246414) 3393555298 10180665226)⟩)))
        (.cut 2 (1/16)
          (.original (.row ⟨93177423804, 95281442641, (.direct 3393509060 5813371844), (.variance 839664139359)⟩))
          (.original (.row ⟨93177423804, 95281442641, (.direct 3393509060 5813371844), (.chord (.secant 1574151333884 278088253644 4970858141 104350670992) 3393555298 10180665226)⟩))))
      (.cut 3 (3/64)
        (.cut 0 (135/272)
          (.cut 2 (1/16)
            (.original (.row ⟨93177423804, 95281442641, (.direct 2150924658 4473987038), (.variance 908485866892)⟩))
            (.original (.row ⟨93177423804, 95281442641, (.direct 2150924658 4473987038), (.chord (.secant 1348212629731 165938009365 2189356240 77240040124) 3393555298 10180665226)⟩)))
          (.original (.row ⟨93177423804, 95281442641, (.direct 2150924658 4650169629), (.variance 896812378433)⟩)))
        (.original (.row ⟨93177423804, 95281442641, (.direct 3393509060 6196940868), (.variance 822340434100)⟩))))

set_option maxRecDepth 16000 in
theorem CutMid2H3NegRestPart18_ok : CutMid2H3NegRestPart18Tree.geometryOK CutMid2H3NegPowerCache CutMid2H3NegRestPart18Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
