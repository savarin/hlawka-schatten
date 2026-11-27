/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H5NegPart32`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H5NegPart32Box : Box := ((⟨![45/136, 9/50, 0, -8], ![27/68, 19/100, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutTop3H5NegPart32Tree : CertTree :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cone)
          (.row ⟨120689819474, 123862991200, .zero, (.variance 308346175074)⟩))
        (.row ⟨120689819474, 123862991200, .zero, (.variance 308346175074)⟩))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (13/8)
            (.row ⟨120689819474, 123862991200, (.direct 391506126583 386346459376), (.variance 251436227505)⟩)
            (.row ⟨120689819474, 123862991200, (.direct 593382169971 578377524472), (.variance 226225580881)⟩))
          (.row ⟨120689819474, 123862991200, (.direct 391506126583 386346459376), (.variance 251436227505)⟩))
        (.row ⟨120689819474, 123862991200, (.direct 391506126583 386346459376), (.variance 251436227505)⟩)))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.row ⟨120689819474, 123862991200, (.direct 824633666698 797564515406), (.variance 207968996898)⟩)
            (.row ⟨120689819474, 123862991200, (.direct 2002014560937 1908383327056), (.variance 165493727774)⟩))
          (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3339187876970), (.chord .universal 0 10180665226)⟩))
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.row ⟨120689819474, 123862991200, (.direct 824633666698 797564515406), (.variance 207968996898)⟩)
            (.row ⟨120689819474, 123862991200, (.direct 2002014560937 1908383327056), (.variance 165493727774)⟩))
          (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3339187876970), (.variance 142941091473)⟩)))
      (.row ⟨120689819474, 123862991200, (.direct 824633666698 797564515406), (.variance 207968996898)⟩))

set_option maxRecDepth 16000 in
theorem CutTop3H5NegPart32_checked : CutTop3H5NegPart32Tree.commonOK CutTop3H5NegPart32Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
