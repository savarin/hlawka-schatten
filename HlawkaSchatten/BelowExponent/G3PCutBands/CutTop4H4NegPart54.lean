/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H4NegPart54`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H4NegPart54Box : Box := ((⟨![9/34, 19/100, 0, -8], ![45/136, 1/5, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutTop4H4NegPart54Tree : CertTree :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cone)
          (.row ⟨123862991199, 126950446638, .zero, (.variance 308554782230)⟩))
        (.row ⟨123862991199, 126950446638, .zero, (.variance 308554782230)⟩))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (13/8)
            (.row ⟨123862991199, 126950446638, (.direct 391506126583 386953693954), (.variance 251332846912)⟩)
            (.row ⟨123862991199, 126950446638, (.direct 593382169971 580139860438), (.variance 226045425520)⟩))
          (.row ⟨123862991199, 126950446638, (.direct 391506126583 386953693954), (.variance 251332846912)⟩))
        (.row ⟨123862991199, 126950446638, (.direct 391506126583 386953693954), (.variance 251332846912)⟩)))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.row ⟨123862991199, 126950446638, (.direct 824633666698 800739846528), (.variance 207752727650)⟩)
            (.row ⟨123862991199, 126950446638, (.direct 2002014560937 1919340814641), (.variance 165245803215)⟩))
          (.row ⟨123862991199, 126950446638, (.direct 3523554676644 3360743635384), (.chord .universal 0 10180665226)⟩))
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.row ⟨123862991199, 126950446638, (.direct 824633666698 800739846528), (.variance 207752727650)⟩)
            (.row ⟨123862991199, 126950446638, (.direct 2002014560937 1919340814641), (.variance 165245803215)⟩))
          (.row ⟨123862991199, 126950446638, (.direct 3523554676644 3360743635384), (.variance 142700446006)⟩)))
      (.row ⟨123862991199, 126950446638, (.direct 824633666698 800739846528), (.variance 207752727650)⟩))

set_option maxRecDepth 16000 in
theorem CutTop4H4NegPart54_checked : CutTop4H4NegPart54Tree.commonOK CutTop4H4NegPart54Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
