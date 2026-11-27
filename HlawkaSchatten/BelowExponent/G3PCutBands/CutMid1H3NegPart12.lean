/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid1H3NegPart12`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid1H3NegPart12Box : Box := (((((((((⟨![27/68, 7/100, 0, -8], ![9/17, 9/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)).upperChild 3 (0)).lowerChild 3 (1/8)).upperChild 3 (1/16)

set_option maxRecDepth 16000 in
def CutMid1H3NegPart12Tree : CertTree :=
  .cut 1 (2/25)
    (.cut 0 (63/136)
      (.cut 1 (3/40)
        (.cut 3 (3/32)
          (.row ⟨76698504228, 79281022314, (.direct 6452795533 8326203030), (.variance 801017177554)⟩)
          (.row ⟨76698504228, 79281022314, (.direct 10180561190 12293300230), (.variance 695532786764)⟩))
        (.cut 3 (3/32)
          (.row ⟨79281022313, 81775466253, (.direct 6452795533 8462748953), (.variance 796674866008)⟩)
          (.row ⟨79281022313, 81775466253, (.direct 10180561190 12445415950), (.variance 692931612813)⟩)))
      (.cut 1 (3/40)
        (.row ⟨76698504228, 79281022314, (.direct 10180561190 12606973474), (.variance 791375617674)⟩)
        (.row ⟨79281022313, 81775466253, (.direct 10180561190 12782493823), (.variance 786520446056)⟩)))
    (.cut 0 (63/136)
      (.cut 1 (17/200)
        (.cut 3 (3/32)
          (.row ⟨81775466252, 84190079492, (.direct 6452795533 8600832333), (.variance 792389776422)⟩)
          (.row ⟨81775466252, 84190079492, (.direct 10180561190 12599020726), (.variance 690350017686)⟩))
        (.cut 3 (3/32)
          (.row ⟨84190079491, 86531900009, (.direct 6452795533 8740468212), (.variance 788160491470)⟩)
          (.row ⟨84190079491, 86531900009, (.direct 10180561190 12754129472), (.variance 687787695710)⟩)))
      (.cut 1 (17/200)
        (.row ⟨81775466252, 84190079492, (.direct 10180561190 12959831787), (.variance 781740842191)⟩)
        (.cut 3 (3/32)
          (.row ⟨84190079491, 86531900009, (.direct 6452795533 9087794534), (.variance 777034638559)⟩)
          (.row ⟨84190079491, 86531900009, (.direct 10180561190 13139005456), (.variance 680978803271)⟩))))

set_option maxRecDepth 16000 in
theorem CutMid1H3NegPart12_checked : CutMid1H3NegPart12Tree.commonOK CutMid1H3NegPart12Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
