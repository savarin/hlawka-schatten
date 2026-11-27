/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H1NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H1NegRestPart3`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H1NegRestPart3Box : Box := ((⟨![9/136, 17/100, 0, -8], ![9/68, 9/50, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutTop2H1NegRestPart3Tree : RatioRemainder :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.original (.cone))
          (.original (.row ⟨117423580139, 120689819475, .zero, (.variance 309474681067)⟩)))
        (.original (.row ⟨117423580139, 120689819475, .zero, (.variance 309474681067)⟩)))
      (.original (.row ⟨117423580139, 120689819475, (.direct 391506126583 389883284016), (.variance 250836949945)⟩)))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.original (.row ⟨117423580139, 120689819475, (.direct 824633666698 816098505041), (.variance 206721727801)⟩))
          (.original (.row ⟨117423580139, 120689819475, (.direct 3523554676644 3465278954640), (.chord .universal 0 10180665226)⟩)))
        (.cut 3 (5)
          (.original (.row ⟨117423580139, 120689819475, (.direct 824633666698 816098505041), (.variance 206721727801)⟩))
          (.original (.row ⟨117423580139, 120689819475, (.direct 3523554676644 3465278954640), (.variance 141560442867)⟩))))
      (.original (.row ⟨117423580139, 120689819475, (.direct 824633666698 816098505041), (.variance 206721727801)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop2H1NegRestPart3_ok : CutTop2H1NegRestPart3Tree.geometryOK CutTop2H1NegPowerCache CutTop2H1NegRestPart3Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
