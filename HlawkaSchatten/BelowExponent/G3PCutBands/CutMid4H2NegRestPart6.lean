/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid4H2NegRestPart6`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid4H2NegRestPart6Box : Box := ((((((((⟨![9/34, 13/100, 0, -8], ![27/68, 3/20, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)).upperChild 3 (0)).upperChild 3 (1/8)

set_option maxRecDepth 16000 in
def CutMid4H2NegRestPart6Tree : RatioRemainder :=
  .cut 3 (3/16)
    (.cut 1 (7/50)
      (.cut 3 (5/32)
        (.cut 0 (45/136)
          (.original (.row ⟨103236350715, 106974752992, (.direct 14500097491 17710485758), (.variance 619606331374)⟩))
          (.original (.row ⟨103236350715, 106974752992, (.direct 14500097491 18380607291), (.variance 612414672600)⟩)))
        (.original (.row ⟨103236350715, 106974752992, (.direct 19358451269 23480153096), (.variance 571029350783)⟩)))
      (.cut 3 (5/32)
        (.cut 0 (45/136)
          (.original (.row ⟨106974752991, 110576703735, (.direct 14500097491 17968130986), (.variance 617195149567)⟩))
          (.original (.row ⟨106974752991, 110576703735, (.direct 14500097491 18694192332), (.variance 609522430446)⟩)))
        (.original (.row ⟨106974752991, 110576703735, (.direct 19358451269 23810503769), (.variance 569266786807)⟩))))
    (.cut 1 (7/50)
      (.cut 3 (7/32)
        (.original (.row ⟨103236350715, 106974752992, (.direct 24716051037 29026229238), (.variance 533387185926)⟩))
        (.original (.row ⟨103236350715, 106974752992, (.direct 30541785600 34994617179), (.variance 503052164058)⟩)))
      (.cut 3 (7/32)
        (.original (.row ⟨106974752991, 110576703735, (.direct 24716051037 29369590720), (.variance 532040707840)⟩))
        (.original (.row ⟨106974752991, 110576703735, (.direct 30541785600 35347683971), (.variance 501991020807)⟩))))

set_option maxRecDepth 16000 in
theorem CutMid4H2NegRestPart6_ok : CutMid4H2NegRestPart6Tree.geometryOK CutMid4H2NegPowerCache CutMid4H2NegRestPart6Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
