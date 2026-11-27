/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid4H3NegChartPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid4H3NegChartPart1Box : Box := (((((⟨![27/68, 13/100, 0, -1], ![9/17, 3/20, 1, 1]⟩ : Box)).lowerChild 3 (1/4)).upperChild 3 (-1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutMid4H3NegChartPart1Tree : RatioChart :=
  .cut 1 (7/50)
    (.cut 0 (63/136)
      (.cut 3 (0)
        (.cut 3 (-1/8)
          (.row ⟨103236350715, 106974752992, (.direct 39278188 1573671826), 0, 10180665226, 443202712349/274877906944, .leaf (.secant 730620357551 13171657058 49313920105 10180561190)⟩)
          (.row ⟨103236350715, 106974752992, (.direct 258648757 694864745), 0, 10180665226, 484812700997/274877906944, .leaf (.secant 654056799327 34921981117 81179804332 0)⟩))
        (.row ⟨103236350715, 106974752992, (.direct 971347183 117075457), 0, 10180665226, 114387405749/68719476736, .leaf (.midpoint ⟨580667489242, 63582541603, 106756363911, 537735758958, 160133808481, 318561080555⟩)⟩))
      (.cut 3 (0)
        (.row ⟨103236350715, 106974752992, (.direct 4720743 1600670717), 0, 10180665226, 16326978053/8589934592, .leaf (.secant 689697055100 23735775456 100314348286 0)⟩)
        (.row ⟨103236350715, 106974752992, (.direct 1249531767 127901361), 0, 10180665226, 218575936205/137438953472, .leaf (.midpoint ⟨543133300087, 81179497341, 116830202263, 504409762149, 175244629181, 308872718761⟩)⟩)))
    (.cut 1 (29/200)
      (.cut 0 (63/136)
        (.row ⟨106974752991, 108791878640, (.direct 8293257 1514328593), 0, 10180665226, 2, .leaf .universal⟩)
        (.row ⟨106974752991, 108791878640, (.direct 39234112 1528736801), 0, 10180665226, 2, .leaf .universal⟩))
      (.cut 0 (63/136)
        (.row ⟨108791878639, 110576703735, (.direct 438155 1527544659), 0, 10180665226, 2, .leaf .universal⟩)
        (.row ⟨108791878639, 110576703735, (.direct 64849769 1542238342), 0, 10180665226, 2, .leaf .universal⟩)))

set_option maxRecDepth 16000 in
theorem CutMid4H3NegChartPart1_ok : CutMid4H3NegChartPart1Tree.geometryOK CutMid4H3NegPowerCache CutMid4H3NegChartPart1Box false = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
