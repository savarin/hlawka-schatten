/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H3NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H3NegRestPart2`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H3NegRestPart2Box : Box := ((⟨![27/136, 17/100, 0, -8], ![9/34, 9/50, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutTop2H3NegRestPart2Tree : RatioRemainder :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.original (.cone))
          (.original (.row ⟨117423580139, 120689819475, .zero, (.variance 308950864443)⟩)))
        (.original (.row ⟨117423580139, 120689819475, .zero, (.variance 308950864443)⟩)))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (13/8)
            (.original (.row ⟨117423580139, 120689819475, (.direct 391506126583 388262502666), (.variance 251110719071)⟩))
            (.original (.row ⟨117423580139, 120689819475, (.direct 593382169971 583941574728), (.variance 225659135037)⟩)))
          (.original (.row ⟨117423580139, 120689819475, (.direct 391506126583 388262502666), (.variance 251110719071)⟩)))
        (.original (.row ⟨117423580139, 120689819475, (.direct 391506126583 388262502666), (.variance 251110719071)⟩))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.original (.row ⟨117423580139, 120689819475, (.direct 824633666698 807593374828), (.variance 207289606084)⟩))
            (.original (.row ⟨117423580139, 120689819475, (.direct 2002014560937 1943015090574), (.variance 164716194178)⟩)))
          (.original (.row ⟨117423580139, 120689819475, (.direct 3523554676644 3407335184382), (.chord .universal 0 10180665226)⟩)))
        (.cut 3 (5)
          (.original (.row ⟨117423580139, 120689819475, (.direct 824633666698 807593374828), (.variance 207289606084)⟩))
          (.original (.row ⟨117423580139, 120689819475, (.direct 3523554676644 3407335184382), (.variance 142186895376)⟩))))
      (.original (.row ⟨117423580139, 120689819475, (.direct 824633666698 807593374828), (.variance 207289606084)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop2H3NegRestPart2_ok : CutTop2H3NegRestPart2Tree.geometryOK CutTop2H3NegPowerCache CutTop2H3NegRestPart2Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
