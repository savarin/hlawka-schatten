/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid0H1NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid0H1NegPart5`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid0H1NegPart5Box : Box := ((⟨![9/68, 1/20, 0, -8], ![9/34, 7/100, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutMid0H1NegPart5Tree : CertTree :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cone)
          (.row ⟨65259754744, 76698504229, .zero, (.variance 309592422204)⟩))
        (.row ⟨65259754744, 76698504229, .zero, (.variance 309592422204)⟩))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (13/8)
            (.row ⟨65259754744, 76698504229, (.direct 391506126583 390315726274), (.variance 250764147958)⟩)
            (.row ⟨65259754744, 76698504229, (.direct 593382169971 589914482085), (.variance 225058596267)⟩))
          (.row ⟨65259754744, 76698504229, (.direct 391506126583 390315726274), (.variance 250764147958)⟩))
        (.row ⟨65259754744, 76698504229, (.direct 391506126583 390315726274), (.variance 250764147958)⟩)))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.row ⟨65259754744, 76698504229, (.direct 824633666698 818371107657), (.variance 206571251910)⟩)
            (.row ⟨65259754744, 76698504229, (.direct 2002014560937 1980310192140), (.variance 163898184941)⟩))
          (.row ⟨65259754744, 76698504229, (.direct 3523554676644 3480784758044), (.variance 141395042571)⟩))
        (.row ⟨65259754744, 76698504229, (.direct 824633666698 818371107657), (.variance 206571251910)⟩))
      (.row ⟨65259754744, 76698504229, (.direct 824633666698 818371107657), (.variance 206571251910)⟩))

set_option maxRecDepth 16000 in
theorem CutMid0H1NegPart5_checked : CutMid0H1NegPart5Tree.geometryOK CutMid0H1NegPowerCache CutMid0H1NegPart5Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
