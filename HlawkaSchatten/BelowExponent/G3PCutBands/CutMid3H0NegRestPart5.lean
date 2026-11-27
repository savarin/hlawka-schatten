/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H0NegRestPart5`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H0NegRestPart5Box : Box := ((((((((⟨![0, 11/100, 0, -8], ![9/68, 13/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)).upperChild 3 (0)).upperChild 3 (1/8)

set_option maxRecDepth 16000 in
def CutMid3H0NegRestPart5Tree : RatioRemainder :=
  .cut 3 (3/16)
    (.cut 1 (3/25)
      (.cut 3 (5/32)
        (.cut 0 (9/136)
          (.cut 1 (23/200)
            (.cut 3 (9/64)
              (.cut 0 (9/272)
                (.original (.row ⟨95281442640, 97336292160, (.direct 12270063068 12510956537), (.variance 651562574406)⟩))
                (.original (.row ⟨95281442640, 97336292160, (.direct 12270063068 12753454190), (.variance 647951562353)⟩)))
              (.original (.row ⟨95281442640, 97336292160, (.direct 14500097491 15004461232), (.variance 620477318811)⟩)))
            (.cut 3 (9/64)
              (.cut 0 (9/272)
                (.original (.row ⟨97336292159, 99345187400, (.direct 12270063068 12522134969), (.variance 651562574406)⟩))
                (.original (.row ⟨97336292159, 99345187400, (.direct 12270063068 12775973640), (.variance 647779131068)⟩)))
              (.original (.row ⟨97336292159, 99345187400, (.direct 14500097491 15027937355), (.variance 620477318811)⟩))))
          (.cut 1 (23/200)
            (.cut 3 (9/64)
              (.original (.row ⟨95281442640, 97336292160, (.direct 12270063068 13243582502), (.variance 644407882858)⟩))
              (.original (.row ⟨95281442640, 97336292160, (.direct 14500097491 15515025730), (.variance 614515052152)⟩)))
            (.cut 3 (9/64)
              (.original (.row ⟨97336292159, 99345187400, (.direct 12270063068 13289266801), (.variance 644069557864)⟩))
              (.original (.row ⟨97336292159, 99345187400, (.direct 14500097491 15562574550), (.variance 614232416886)⟩)))))
        (.cut 0 (9/136)
          (.cut 1 (23/200)
            (.original (.row ⟨95281442640, 97336292160, (.direct 19358451269 19898141771), (.variance 593929411221)⟩))
            (.original (.row ⟨97336292159, 99345187400, (.direct 19358451269 19923229233), (.variance 593929411221)⟩)))
          (.original (.row ⟨95281442640, 99345187400, (.direct 19358451269 20493816329), (.variance 588876763919)⟩))))
      (.cut 3 (5/32)
        (.cut 0 (9/136)
          (.cut 1 (1/8)
            (.cut 3 (9/64)
              (.cut 0 (9/272)
                (.original (.row ⟨99345187399, 101311009181, (.direct 12270063068 12533376733), (.variance 651562574406)⟩))
                (.original (.row ⟨99345187399, 101311009181, (.direct 12270063068 12798627971), (.variance 647605940194)⟩)))
              (.original (.row ⟨99345187399, 101311009181, (.direct 14500097491 15051552335), (.variance 620477318811)⟩)))
            (.cut 3 (9/64)
              (.cut 0 (9/272)
                (.original (.row ⟨101311009180, 103236350716, (.direct 12270063068 12544682366), (.variance 651562574406)⟩))
                (.original (.row ⟨101311009180, 103236350716, (.direct 12270063068 12821418376), (.variance 647431984668)⟩)))
              (.original (.row ⟨101311009180, 103236350716, (.direct 14500097491 15075307390), (.variance 620477318811)⟩))))
          (.cut 1 (1/8)
            (.cut 3 (9/64)
              (.original (.row ⟨99345187399, 101311009181, (.direct 12270063068 13335253250), (.variance 643730042937)⟩))
              (.original (.row ⟨99345187399, 101311009181, (.direct 14500097491 15610431072), (.variance 613948724488)⟩)))
            (.cut 3 (9/64)
              (.original (.row ⟨101311009180, 103236350716, (.direct 12270063068 13381544691), (.variance 643389331561)⟩))
              (.original (.row ⟨101311009180, 103236350716, (.direct 14500097491 15658598156), (.variance 613663968869)⟩)))))
        (.cut 0 (9/136)
          (.cut 1 (1/8)
            (.original (.row ⟨99345187399, 101311009181, (.direct 19358451269 19948462252), (.variance 593929411221)⟩))
            (.cut 3 (11/64)
              (.original (.row ⟨101311009180, 103236350716, (.direct 16864636136 17461111495), (.variance 593929411221)⟩))
              (.original (.row ⟨101311009180, 103236350716, (.direct 19358451269 19973842088), (.variance 570893780246)⟩))))
          (.cut 1 (1/8)
            (.original (.row ⟨99345187399, 101311009181, (.direct 19358451269 20544822532), (.variance 588395841877)⟩))
            (.original (.row ⟨101311009180, 103236350716, (.direct 19358451269 20596148651), (.variance 588153964089)⟩))))))
    (.cut 1 (3/25)
      (.cut 0 (9/136)
        (.cut 3 (7/32)
          (.original (.row ⟨95281442640, 99345187400, (.direct 24716051037 25309814366), (.variance 550644921433)⟩))
          (.original (.row ⟨95281442640, 99345187400, (.direct 30541785600 31157692706), (.variance 516518883525)⟩)))
        (.cut 3 (7/32)
          (.original (.row ⟨95281442640, 99345187400, (.direct 24716051037 25908575997), (.variance 546875058915)⟩))
          (.original (.row ⟨95281442640, 99345187400, (.direct 30541785600 31777915238), (.variance 513598435862)⟩))))
      (.cut 3 (7/32)
        (.cut 0 (9/136)
          (.original (.row ⟨99345187399, 103236350716, (.direct 24716051037 25362970020), (.variance 550644921433)⟩))
          (.original (.row ⟨99345187399, 103236350716, (.direct 24716051037 26015848978), (.variance 546515114403)⟩)))
        (.cut 0 (9/136)
          (.original (.row ⟨99345187399, 103236350716, (.direct 30541785600 31212787737), (.variance 516518883525)⟩))
          (.original (.row ⟨99345187399, 103236350716, (.direct 30541785600 31888945087), (.variance 513318968669)⟩)))))

set_option maxRecDepth 16000 in
theorem CutMid3H0NegRestPart5_ok : CutMid3H0NegRestPart5Tree.ok CutMid3H0NegRestPart5Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
