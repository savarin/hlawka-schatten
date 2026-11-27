/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H2NegPart38`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H2NegPart38Box : Box := ((⟨![9/68, 19/100, 0, -8], ![27/136, 1/5, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutTop4H2NegPart38Tree : CertTree :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cone)
          (.row ⟨123862991199, 126950446638, .zero, (.variance 309144325836)⟩))
        (.row ⟨123862991199, 126950446638, .zero, (.variance 309144325836)⟩))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (13/8)
            (.row ⟨123862991199, 126950446638, (.direct 391506126583 388772479870), (.variance 251024422637)⟩)
            (.row ⟨123862991199, 126950446638, (.direct 593382169971 585424108671), (.variance 225509354543)⟩))
          (.row ⟨123862991199, 126950446638, (.direct 391506126583 388772479870), (.variance 251024422637)⟩))
        (.row ⟨123862991199, 126950446638, (.direct 391506126583 388772479870), (.variance 251024422637)⟩)))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.row ⟨123862991199, 126950446638, (.direct 824633666698 810267368430), (.variance 207110256167)⟩)
            (.row ⟨123862991199, 126950446638, (.direct 2002014560937 1952260733701), (.variance 164511569455)⟩))
          (.row ⟨123862991199, 126950446638, (.direct 3523554676644 3425537837915), (.chord .universal 0 10180665226)⟩))
        (.cut 3 (5)
          (.row ⟨123862991199, 126950446638, (.direct 824633666698 810267368430), (.variance 207110256167)⟩)
          (.row ⟨123862991199, 126950446638, (.direct 3523554676644 3425537837915), (.variance 141988660068)⟩)))
      (.row ⟨123862991199, 126950446638, (.direct 824633666698 810267368430), (.variance 207110256167)⟩))

set_option maxRecDepth 16000 in
theorem CutTop4H2NegPart38_checked : CutTop4H2NegPart38Tree.commonOK CutTop4H2NegPart38Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
