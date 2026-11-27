/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H6NegPart50`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H6NegPart50Box : Box := ((⟨![27/68, 19/100, 0, -8], ![63/136, 1/5, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutTop4H6NegPart50Tree : CertTree :=
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
              (.row ⟨123862991199, 126950446638, (.direct 391506126583 385138057698), (.variance 251642567031)⟩)
              (.row ⟨123862991199, 126950446638, (.direct 488587506629 476513186548), (.variance 237998011020)⟩))
            (.row ⟨123862991199, 126950446638, (.direct 593382169971 574873316986), (.variance 226585866276)⟩))
          (.row ⟨123862991199, 126950446638, (.direct 391506126583 385138057698), (.variance 251642567031)⟩))
        (.row ⟨123862991199, 126950446638, (.direct 391506126583 385138057698), (.variance 251642567031)⟩)))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.cut 3 (11/4)
              (.row ⟨123862991199, 126950446638, (.direct 824633666698 791253981054), (.variance 208402045334)⟩)
              (.row ⟨123862991199, 126950446638, (.direct 1366046989981 1295818919105), (.variance 183149211626)⟩))
            (.row ⟨123862991199, 126950446638, (.direct 2002014560937 1886627979807), (.variance 165991331149)⟩))
          (.cut 3 (13/2)
            (.row ⟨123862991199, 126950446638, (.direct 3523554676644 3296407239956), (.variance 143424546253)⟩)
            (.row ⟨123862991199, 126950446638, (.direct 5340438828596 4976566440488), (.chord .universal 0 10180665226)⟩)))
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.row ⟨123862991199, 126950446638, (.direct 824633666698 791253981054), (.variance 208402045334)⟩)
            (.row ⟨123862991199, 126950446638, (.direct 2002014560937 1886627979807), (.variance 165991331149)⟩))
          (.row ⟨123862991199, 126950446638, (.direct 3523554676644 3296407239956), (.variance 143424546253)⟩)))
      (.cut 3 (5)
        (.row ⟨123862991199, 126950446638, (.direct 824633666698 791253981054), (.variance 208402045334)⟩)
        (.row ⟨123862991199, 126950446638, (.direct 3523554676644 3296407239956), (.variance 143424546253)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop4H6NegPart50_checked : CutTop4H6NegPart50Tree.commonOK CutTop4H6NegPart50Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
