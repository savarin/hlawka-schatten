/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H6PosPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H6PosPart1Box : Box := ((⟨![27/68, 19/100, 0, -8], ![63/136, 1/5, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutTop4H6PosPart1Tree : CertTree :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cone)
          (.row ⟨123862991199, 126950446638, .zero, (.variance 307969054205)⟩))
        (.row ⟨123862991199, 126950446638, .zero, (.variance 307969054205)⟩))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (13/8)
            (.cut 3 (23/16)
              (.cut 3 (43/32)
                (.row ⟨123862991199, 126950446638, (.direct 391506126583 385138057698), (.variance 251642567031)⟩)
                (.row ⟨123862991199, 126950446638, (.direct 439055879922 429929155162), (.variance 244496429938)⟩))
              (.row ⟨123862991199, 126950446638, (.direct 488587506629 476513186548), (.variance 237998011020)⟩))
            (.row ⟨123862991199, 126950446638, (.direct 593382169971 574873316986), (.variance 226585866276)⟩))
          (.cut 3 (13/8)
            (.cut 3 (23/16)
              (.row ⟨123862991199, 126950446638, (.direct 391506126583 385138057698), (.variance 251642567031)⟩)
              (.row ⟨123862991199, 126950446638, (.direct 488587506629 476513186548), (.variance 237998011020)⟩))
            (.row ⟨123862991199, 126950446638, (.direct 593382169971 574873316986), (.variance 226585866276)⟩)))
        (.row ⟨123862991199, 126950446638, (.direct 391506126583 385138057698), (.variance 251642567031)⟩)))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.cut 3 (11/4)
              (.cut 3 (19/8)
                (.row ⟨123862991199, 126950446638, (.direct 824633666698 791253981054), (.variance 208402045334)⟩)
                (.row ⟨123862991199, 126950446638, (.direct 1082810704946 1032121460283), (.variance 194392690635)⟩))
              (.row ⟨123862991199, 126950446638, (.direct 1366046989981 1295818919105), (.variance 183149211626)⟩))
            (.row ⟨123862991199, 126950446638, (.direct 2002014560937 1886627979807), (.variance 165991331149)⟩))
          (.cut 3 (13/2)
            (.row ⟨123862991199, 126950446638, (.direct 3523554676644 3296407239956), (.variance 143424546253)⟩)
            (.row ⟨123862991199, 126950446638, (.direct 5340438828596 4976566440488), (.variance 128759831429)⟩)))
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.cut 3 (11/4)
              (.cut 3 (19/8)
                (.row ⟨123862991199, 126950446638, (.direct 824633666698 791253981054), (.variance 208402045334)⟩)
                (.row ⟨123862991199, 126950446638, (.direct 1082810704946 1032121460283), (.variance 194392690635)⟩))
              (.row ⟨123862991199, 126950446638, (.direct 1366046989981 1295818919105), (.variance 183149211626)⟩))
            (.cut 3 (17/4)
              (.row ⟨123862991199, 126950446638, (.direct 2002014560937 1886627979807), (.variance 165991331149)⟩)
              (.row ⟨123862991199, 126950446638, (.direct 2723407729414 2555495254603), (.variance 153311863015)⟩)))
          (.cut 3 (13/2)
            (.row ⟨123862991199, 126950446638, (.direct 3523554676644 3296407239956), (.variance 143424546253)⟩)
            (.cut 3 (29/4)
              (.row ⟨123862991199, 126950446638, (.direct 5340438828596 4976566440488), (.variance 128759831429)⟩)
              (.row ⟨123862991199, 126950446638, (.direct 6349554162205 5908898576615), (.variance 123098301351)⟩)))))
      (.cut 3 (5)
        (.cut 3 (7/2)
          (.row ⟨123862991199, 126950446638, (.direct 824633666698 791253981054), (.variance 208402045334)⟩)
          (.row ⟨123862991199, 126950446638, (.direct 2002014560937 1886627979807), (.variance 165991331149)⟩))
        (.cut 3 (13/2)
          (.row ⟨123862991199, 126950446638, (.direct 3523554676644 3296407239956), (.variance 143424546253)⟩)
          (.row ⟨123862991199, 126950446638, (.direct 5340438828596 4976566440488), (.variance 128759831429)⟩))))

set_option maxRecDepth 16000 in
theorem CutTop4H6PosPart1_checked : CutTop4H6PosPart1Tree.commonOK CutTop4H6PosPart1Box true = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
