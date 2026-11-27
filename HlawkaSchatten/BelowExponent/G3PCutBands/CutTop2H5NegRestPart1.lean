/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H5NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H5NegRestPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H5NegRestPart1Box : Box := ((⟨![45/136, 17/100, 0, -8], ![27/68, 9/50, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutTop2H5NegRestPart1Tree : RatioRemainder :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.original (.cone))
          (.original (.row ⟨117423580139, 120689819475, .zero, (.variance 308430058377)⟩)))
        (.original (.row ⟨117423580139, 120689819475, .zero, (.variance 308430058377)⟩)))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (13/8)
            (.original (.row ⟨117423580139, 120689819475, (.direct 391506126583 386644214572), (.variance 251385509619)⟩))
            (.original (.row ⟨117423580139, 120689819475, (.direct 593382169971 579241559668), (.variance 226137168182)⟩)))
          (.original (.row ⟨117423580139, 120689819475, (.direct 391506126583 386644214572), (.variance 251385509619)⟩)))
        (.original (.row ⟨117423580139, 120689819475, (.direct 391506126583 386644214572), (.variance 251385509619)⟩))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.original (.row ⟨117423580139, 120689819475, (.direct 824633666698 799121175227), (.variance 207862838555)⟩))
            (.original (.row ⟨117423580139, 120689819475, (.direct 2002014560937 1913754190384), (.variance 165371982587)⟩)))
          (.original (.row ⟨117423580139, 120689819475, (.direct 3523554676644 3349752826757), (.variance 142822901695)⟩)))
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.original (.row ⟨117423580139, 120689819475, (.direct 824633666698 799121175227), (.variance 207862838555)⟩))
            (.original (.row ⟨117423580139, 120689819475, (.direct 2002014560937 1913754190384), (.variance 165371982587)⟩)))
          (.original (.row ⟨117423580139, 120689819475, (.direct 3523554676644 3349752826757), (.variance 142822901695)⟩))))
      (.original (.row ⟨117423580139, 120689819475, (.direct 824633666698 799121175227), (.variance 207862838555)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop2H5NegRestPart1_ok : CutTop2H5NegRestPart1Tree.geometryOK CutTop2H5NegPowerCache CutTop2H5NegRestPart1Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
