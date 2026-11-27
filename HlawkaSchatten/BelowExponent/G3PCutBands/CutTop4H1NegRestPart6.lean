/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H1NegRestPart6`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H1NegRestPart6Box : Box := ((⟨![9/136, 19/100, 0, -8], ![9/68, 1/5, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutTop4H1NegRestPart6Tree : RatioRemainder :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.original (.cone))
          (.original (.row ⟨123862991199, 126950446638, .zero, (.variance 309440541774)⟩)))
        (.original (.row ⟨123862991199, 126950446638, .zero, (.variance 309440541774)⟩)))
      (.original (.row ⟨123862991199, 126950446638, (.direct 391506126583 389683052741), (.variance 250870693555)⟩)))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.original (.row ⟨123862991199, 126950446638, (.direct 824633666698 815046710230), (.variance 206791549416)⟩))
            (.original (.row ⟨123862991199, 126950446638, (.direct 2002014560937 1968798061724), (.variance 164148597192)⟩)))
          (.original (.row ⟨123862991199, 126950446638, (.direct 3523554676644 3458105901705), (.chord .universal 0 10180665226)⟩)))
        (.cut 3 (5)
          (.original (.row ⟨123862991199, 126950446638, (.direct 824633666698 815046710230), (.variance 206791549416)⟩))
          (.original (.row ⟨123862991199, 126950446638, (.direct 3523554676644 3458105901705), (.variance 141637274036)⟩))))
      (.original (.row ⟨123862991199, 126950446638, (.direct 824633666698 815046710230), (.variance 206791549416)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop4H1NegRestPart6_ok : CutTop4H1NegRestPart6Tree.ok CutTop4H1NegRestPart6Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
