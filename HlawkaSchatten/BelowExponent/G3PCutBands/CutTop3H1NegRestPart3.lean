/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H1NegRestPart3`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H1NegRestPart3Box : Box := ((⟨![9/136, 9/50, 0, -8], ![9/68, 19/100, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutTop3H1NegRestPart3Tree : RatioRemainder :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.original (.cone))
          (.original (.row ⟨120689819474, 123862991200, .zero, (.variance 309457703605)⟩)))
        (.original (.row ⟨120689819474, 123862991200, .zero, (.variance 309457703605)⟩)))
      (.original (.row ⟨120689819474, 123862991200, (.direct 391506126583 389783716759), (.variance 250853726601)⟩)))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.original (.row ⟨120689819474, 123862991200, (.direct 824633666698 815575450570), (.variance 206756435682)⟩))
          (.original (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3461711557547), (.chord .universal 0 10180665226)⟩)))
        (.cut 3 (5)
          (.original (.row ⟨120689819474, 123862991200, (.direct 824633666698 815575450570), (.variance 206756435682)⟩))
          (.original (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3461711557547), (.variance 141598628445)⟩))))
      (.original (.row ⟨120689819474, 123862991200, (.direct 824633666698 815575450570), (.variance 206756435682)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop3H1NegRestPart3_ok : CutTop3H1NegRestPart3Tree.ok CutTop3H1NegRestPart3Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
