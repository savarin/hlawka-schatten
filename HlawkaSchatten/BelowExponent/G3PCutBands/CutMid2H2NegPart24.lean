/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H2NegPart24`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H2NegPart24Box : Box := ((⟨![9/34, 9/100, 0, -8], ![27/68, 11/100, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutMid2H2NegPart24Tree : CertTree :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cone)
          (.row ⟨86531900008, 95281442641, .zero, (.variance 309204812723)⟩))
        (.row ⟨86531900008, 95281442641, .zero, (.variance 309204812723)⟩))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (13/8)
            (.row ⟨86531900008, 95281442641, (.direct 391506126583 388642462220), (.variance 251046410165)⟩)
            (.row ⟨86531900008, 95281442641, (.direct 593382169971 585046076117), (.variance 225547501696)⟩))
          (.row ⟨86531900008, 95281442641, (.direct 391506126583 388642462220), (.variance 251046410165)⟩))
        (.row ⟨86531900008, 95281442641, (.direct 391506126583 388642462220), (.variance 251046410165)⟩)))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.row ⟨86531900008, 95281442641, (.direct 824633666698 809585452442), (.variance 207155922570)⟩)
            (.row ⟨86531900008, 95281442641, (.direct 2002014560937 1949902463019), (.variance 164563646391)⟩))
          (.row ⟨86531900008, 95281442641, (.direct 3523554676644 3420894547120), (.variance 142039101150)⟩))
        (.cut 3 (5)
          (.row ⟨86531900008, 95281442641, (.direct 824633666698 809585452442), (.variance 207155922570)⟩)
          (.row ⟨86531900008, 95281442641, (.direct 3523554676644 3420894547120), (.variance 142039101150)⟩)))
      (.row ⟨86531900008, 95281442641, (.direct 824633666698 809585452442), (.variance 207155922570)⟩))

set_option maxRecDepth 16000 in
theorem CutMid2H2NegPart24_checked : CutMid2H2NegPart24Tree.commonOK CutMid2H2NegPart24Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
