/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid4H0NegRestPart4`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid4H0NegRestPart4Box : Box := ((((((((⟨![0, 13/100, 0, -8], ![9/68, 3/20, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)).upperChild 3 (0)).upperChild 3 (1/8)

set_option maxRecDepth 16000 in
def CutMid4H0NegRestPart4Tree : RatioRemainder :=
  .cut 3 (3/16)
    (.cut 1 (7/50)
      (.cut 3 (5/32)
        (.cut 0 (9/136)
          (.cut 1 (27/200)
            (.cut 3 (9/64)
              (.cut 0 (9/272)
                (.original (.row ⟨103236350715, 105123556200, (.direct 12270063068 12556052411), (.variance 651562574406)⟩))
                (.original (.row ⟨103236350715, 105123556200, (.direct 12270063068 12844346063), (.variance 647257259386)⟩)))
              (.original (.row ⟨103236350715, 105123556200, (.direct 14500097491 15099203753), (.variance 620477318811)⟩)))
            (.cut 3 (9/64)
              (.cut 0 (9/272)
                (.original (.row ⟨105123556199, 106974752992, (.direct 12270063068 12567487418), (.variance 651562574406)⟩))
                (.original (.row ⟨105123556199, 106974752992, (.direct 12270063068 12867412254), (.variance 647081759196)⟩)))
              (.original (.row ⟨105123556199, 106974752992, (.direct 14500097491 15123242669), (.variance 620477318811)⟩))))
          (.cut 1 (27/200)
            (.cut 3 (9/64)
              (.original (.row ⟨103236350715, 105123556200, (.direct 12270063068 13428143997), (.variance 643047417170)⟩))
              (.original (.row ⟨103236350715, 105123556200, (.direct 14500097491 15707078694), (.variance 613378143893)⟩)))
            (.cut 3 (9/64)
              (.original (.row ⟨105123556199, 106974752992, (.direct 12270063068 13475054079), (.variance 642704293148)⟩))
              (.original (.row ⟨105123556199, 106974752992, (.direct 14500097491 15755875617), (.variance 613091243376)⟩)))))
        (.cut 0 (9/136)
          (.cut 1 (27/200)
            (.cut 3 (11/64)
              (.original (.row ⟨103236350715, 105123556200, (.direct 16864636136 17485871419), (.variance 593929411221)⟩))
              (.original (.row ⟨103236350715, 105123556200, (.direct 19358451269 19999370012), (.variance 570893780246)⟩)))
            (.cut 3 (11/64)
              (.original (.row ⟨105123556199, 106974752992, (.direct 16864636136 17510777513), (.variance 593929411221)⟩))
              (.original (.row ⟨105123556199, 106974752992, (.direct 19358451269 20025047312), (.variance 570893780246)⟩))))
          (.cut 1 (27/200)
            (.original (.row ⟨103236350715, 105123556200, (.direct 19358451269 20647797607), (.variance 587911134224)⟩))
            (.original (.row ⟨105123556199, 106974752992, (.direct 19358451269 20699772357), (.variance 587667346550)⟩)))))
      (.cut 3 (5/32)
        (.cut 0 (9/136)
          (.cut 1 (29/200)
            (.cut 3 (9/64)
              (.cut 0 (9/272)
                (.original (.row ⟨106974752991, 108791878640, (.direct 12270063068 12578987940), (.variance 651562574406)⟩))
                (.original (.row ⟨106974752991, 108791878640, (.direct 12270063068 12890618185), (.variance 646905478900)⟩)))
              (.original (.row ⟨106974752991, 108791878640, (.direct 14500097491 15147425401), (.variance 620477318811)⟩)))
            (.cut 3 (9/64)
              (.cut 0 (9/272)
                (.cut 1 (59/400)
                  (.original (.row ⟨108791878639, 109688224065, (.direct 12270063068 12584762946), (.variance 651562574406)⟩))
                  (.original (.row ⟨109688224064, 110576703735, (.direct 12270063068 12590554542), (.variance 651562574406)⟩)))
                (.original (.row ⟨108791878639, 110576703735, (.direct 12270063068 12913965108), (.variance 646728413255)⟩)))
              (.cut 0 (9/272)
                (.original (.row ⟨108791878639, 110576703735, (.direct 14500097491 14834589077), (.variance 620477318811)⟩))
                (.original (.row ⟨108791878639, 110576703735, (.direct 14500097491 15171753223), (.variance 616451920757)⟩)))))
          (.cut 1 (29/200)
            (.cut 3 (9/64)
              (.original (.row ⟨106974752991, 108791878640, (.direct 12270063068 13522277884), (.variance 642359952828)⟩))
              (.original (.row ⟨106974752991, 108791878640, (.direct 14500097491 15804991889), (.variance 612803261082)⟩)))
            (.cut 3 (9/64)
              (.original (.row ⟨108791878639, 110576703735, (.direct 12270063068 13569818393), (.variance 642014389491)⟩))
              (.original (.row ⟨108791878639, 110576703735, (.direct 14500097491 15854430511), (.variance 612514190729)⟩)))))
        (.cut 0 (9/136)
          (.cut 1 (29/200)
            (.cut 3 (11/64)
              (.original (.row ⟨106974752991, 108791878640, (.direct 16864636136 17535831058), (.variance 593929411221)⟩))
              (.original (.row ⟨106974752991, 108791878640, (.direct 19358451269 20050875290), (.variance 570893780246)⟩)))
            (.cut 3 (11/64)
              (.original (.row ⟨108791878639, 110576703735, (.direct 16864636136 17561033353), (.variance 593929411221)⟩))
              (.original (.row ⟨108791878639, 110576703735, (.direct 19358451269 20076855263), (.variance 570893780246)⟩))))
          (.cut 1 (29/200)
            (.original (.row ⟨106974752991, 108791878640, (.direct 19358451269 20752075895), (.variance 587422595286)⟩))
            (.original (.row ⟨108791878639, 110576703735, (.direct 19358451269 20804711248), (.variance 587176874607)⟩))))))
    (.cut 1 (7/50)
      (.cut 3 (7/32)
        (.cut 0 (9/136)
          (.cut 1 (27/200)
            (.original (.row ⟨103236350715, 105123556200, (.direct 24716051037 25389777207), (.variance 550644921433)⟩))
            (.original (.row ⟨105123556199, 106974752992, (.direct 24716051037 25416739053), (.variance 550644921433)⟩)))
          (.original (.row ⟨103236350715, 106974752992, (.direct 24716051037 26124441576), (.variance 546152139635)⟩)))
        (.cut 0 (9/136)
          (.original (.row ⟨103236350715, 106974752992, (.direct 30541785600 31268511685), (.variance 516518883525)⟩))
          (.original (.row ⟨103236350715, 106974752992, (.direct 30541785600 32001313975), (.variance 513037038638)⟩))))
      (.cut 3 (7/32)
        (.cut 0 (9/136)
          (.cut 1 (29/200)
            (.original (.row ⟨106974752991, 108791878640, (.direct 24716051037 25443856891), (.variance 550644921433)⟩))
            (.cut 3 (13/64)
              (.original (.row ⟨108791878639, 110576703735, (.direct 21976949588 22714852128), (.variance 550644921433)⟩))
              (.original (.row ⟨108791878639, 110576703735, (.direct 24716051037 25471132070), (.variance 532652607245)⟩))))
          (.cut 1 (29/200)
            (.original (.row ⟨106974752991, 108791878640, (.direct 24716051037 26179240186), (.variance 545786095795)⟩))
            (.original (.row ⟨108791878639, 110576703735, (.direct 24716051037 26234377715), (.variance 545601910659)⟩))))
        (.cut 0 (9/136)
          (.cut 1 (29/200)
            (.original (.row ⟨106974752991, 108791878640, (.direct 30541785600 31296612860), (.variance 516518883525)⟩))
            (.original (.row ⟨108791878639, 110576703735, (.direct 30541785600 31324875325), (.variance 516518883525)⟩)))
          (.original (.row ⟨106974752991, 110576703735, (.direct 30541785600 32115045848), (.variance 512752612861)⟩)))))

set_option maxRecDepth 16000 in
theorem CutMid4H0NegRestPart4_ok : CutMid4H0NegRestPart4Tree.ok CutMid4H0NegRestPart4Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
