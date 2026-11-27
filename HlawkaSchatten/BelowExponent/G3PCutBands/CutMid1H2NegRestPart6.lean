/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H2NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid1H2NegRestPart6`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid1H2NegRestPart6Box : Box := ((⟨![9/34, 7/100, 0, -8], ![27/68, 9/100, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutMid1H2NegRestPart6Tree : RatioRemainder :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.original (.cone))
          (.original (.row ⟨76698504228, 86531900009, .zero, (.variance 309327256445)⟩)))
        (.original (.row ⟨76698504228, 86531900009, .zero, (.variance 309327256445)⟩)))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (13/8)
            (.original (.row ⟨76698504228, 86531900009, (.direct 391506126583 389187145931), (.variance 250954359623)⟩))
            (.original (.row ⟨76698504228, 86531900009, (.direct 593382169971 586630060212), (.variance 225387869766)⟩)))
          (.original (.row ⟨76698504228, 86531900009, (.direct 391506126583 389187145931), (.variance 250954359623)⟩)))
        (.original (.row ⟨76698504228, 86531900009, (.direct 391506126583 389187145931), (.variance 250954359623)⟩))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.original (.row ⟨76698504228, 86531900009, (.direct 824633666698 812443059617), (.variance 206964878531)⟩))
            (.original (.row ⟨76698504228, 86531900009, (.direct 2002014560937 1959787058623), (.variance 164345897498)⟩)))
          (.original (.row ⟨76698504228, 86531900009, (.direct 3523554676644 3440358400461), (.variance 141828236449)⟩)))
        (.cut 3 (5)
          (.original (.row ⟨76698504228, 86531900009, (.direct 824633666698 812443059617), (.variance 206964878531)⟩))
          (.original (.row ⟨76698504228, 86531900009, (.direct 3523554676644 3440358400461), (.variance 141828236449)⟩))))
      (.original (.row ⟨76698504228, 86531900009, (.direct 824633666698 812443059617), (.variance 206964878531)⟩)))

set_option maxRecDepth 16000 in
theorem CutMid1H2NegRestPart6_ok : CutMid1H2NegRestPart6Tree.geometryOK CutMid1H2NegPowerCache CutMid1H2NegRestPart6Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
