/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H3NegRestPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H3NegRestPart1Box : Box := ((⟨![27/136, 4/25, 0, -8], ![9/34, 17/100, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutTop1H3NegRestPart1Tree : RatioRemainder :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.original (.cone))
          (.original (.row ⟨114055813619, 117423580140, .zero, (.variance 309000971619)⟩)))
        (.original (.row ⟨114055813619, 117423580140, .zero, (.variance 309000971619)⟩)))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (13/8)
            (.original (.row ⟨114055813619, 117423580140, (.direct 391506126583 388459185915), (.variance 251077420133)⟩))
            (.original (.row ⟨114055813619, 117423580140, (.direct 593382169971 584513265302), (.variance 225601320322)⟩)))
          (.original (.row ⟨114055813619, 117423580140, (.direct 391506126583 388459185915), (.variance 251077420133)⟩)))
        (.original (.row ⟨114055813619, 117423580140, (.direct 391506126583 388459185915), (.variance 251077420133)⟩))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.original (.row ⟨114055813619, 117423580140, (.direct 824633666698 808624422699), (.variance 207220363070)⟩))
            (.original (.row ⟨114055813619, 117423580140, (.direct 2002014560937 1946579475420), (.variance 164637161910)⟩)))
          (.original (.row ⟨114055813619, 117423580140, (.direct 3523554676644 3414352217893), (.chord .universal 0 10180665226)⟩)))
        (.cut 3 (5)
          (.original (.row ⟨114055813619, 117423580140, (.direct 824633666698 808624422699), (.variance 207220363070)⟩))
          (.original (.row ⟨114055813619, 117423580140, (.direct 3523554676644 3414352217893), (.variance 142110318708)⟩))))
      (.original (.row ⟨114055813619, 117423580140, (.direct 824633666698 808624422699), (.variance 207220363070)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop1H3NegRestPart1_ok : CutTop1H3NegRestPart1Tree.ok CutTop1H3NegRestPart1Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
