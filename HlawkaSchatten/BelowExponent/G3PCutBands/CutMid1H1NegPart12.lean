/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid1H1NegPart12`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid1H1NegPart12Box : Box := ((⟨![9/68, 7/100, 0, -8], ![9/34, 9/100, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutMid1H1NegPart12Tree : CertTree :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cone)
          (.row ⟨76698504228, 86531900009, .zero, (.variance 309532260063)⟩))
        (.row ⟨76698504228, 86531900009, .zero, (.variance 309532260063)⟩))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (13/8)
            (.row ⟨76698504228, 86531900009, (.direct 391506126583 389959717376), (.variance 250824074919)⟩)
            (.row ⟨76698504228, 86531900009, (.direct 593382169971 588878064732), (.variance 225162250008)⟩))
          (.row ⟨76698504228, 86531900009, (.direct 391506126583 389959717376), (.variance 250824074919)⟩))
        (.row ⟨76698504228, 86531900009, (.direct 391506126583 389959717376), (.variance 250824074919)⟩)))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.row ⟨76698504228, 86531900009, (.direct 824633666698 816500081227), (.variance 206695099793)⟩)
            (.row ⟨76698504228, 86531900009, (.direct 2002014560937 1973830052749), (.variance 164038914451)⟩))
          (.row ⟨76698504228, 86531900009, (.direct 3523554676644 3468018178648), (.variance 141531155744)⟩))
        (.row ⟨76698504228, 86531900009, (.direct 824633666698 816500081227), (.variance 206695099793)⟩))
      (.row ⟨76698504228, 86531900009, (.direct 824633666698 816500081227), (.variance 206695099793)⟩))

set_option maxRecDepth 16000 in
theorem CutMid1H1NegPart12_checked : CutMid1H1NegPart12Tree.commonOK CutMid1H1NegPart12Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
