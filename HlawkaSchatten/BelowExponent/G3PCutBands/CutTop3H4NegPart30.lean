/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H4NegPart30`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H4NegPart30Box : Box := ((⟨![9/34, 9/50, 0, -8], ![45/136, 19/100, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutTop3H4NegPart30Tree : CertTree :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cone)
          (.row ⟨120689819474, 123862991200, .zero, (.variance 308622781021)⟩))
        (.row ⟨120689819474, 123862991200, .zero, (.variance 308622781021)⟩))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (13/8)
            (.row ⟨120689819474, 123862991200, (.direct 391506126583 387204720092), (.variance 251290169952)⟩)
            (.row ⟨120689819474, 123862991200, (.direct 593382169971 580868676106), (.variance 225971123836)⟩))
          (.row ⟨120689819474, 123862991200, (.direct 391506126583 387204720092), (.variance 251290169952)⟩))
        (.row ⟨120689819474, 123862991200, (.direct 391506126583 387204720092), (.variance 251290169952)⟩)))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.row ⟨120689819474, 123862991200, (.direct 824633666698 802053326042), (.variance 207663583789)⟩)
            (.row ⟨120689819474, 123862991200, (.direct 2002014560937 1923875459647), (.variance 165143724096)⟩))
          (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3369665913257), (.chord .universal 0 10180665226)⟩))
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.row ⟨120689819474, 123862991200, (.direct 824633666698 802053326042), (.variance 207663583789)⟩)
            (.row ⟨120689819474, 123862991200, (.direct 2002014560937 1923875459647), (.variance 165143724096)⟩))
          (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3369665913257), (.variance 142601408188)⟩)))
      (.row ⟨120689819474, 123862991200, (.direct 824633666698 802053326042), (.variance 207663583789)⟩))

set_option maxRecDepth 16000 in
theorem CutTop3H4NegPart30_checked : CutTop3H4NegPart30Tree.commonOK CutTop3H4NegPart30Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
