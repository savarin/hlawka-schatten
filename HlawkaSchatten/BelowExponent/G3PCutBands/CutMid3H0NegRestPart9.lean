/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H0NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H0NegRestPart9`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H0NegRestPart9Box : Box := ((⟨![0, 11/100, 0, -8], ![9/68, 13/100, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutMid3H0NegRestPart9Tree : RatioRemainder :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.original (.cone))
          (.original (.row ⟨95281442640, 103236350716, .zero, (.variance 309737727641)⟩)))
        (.original (.row ⟨95281442640, 103236350716, .zero, (.variance 309737727641)⟩)))
      (.original (.row ⟨95281442640, 103236350716, (.direct 391506126583 390365279556), (.variance 250755812125)⟩)))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.original (.row ⟨95281442640, 103236350716, (.direct 824633666698 818631613270), (.variance 206554036734)⟩))
          (.original (.row ⟨95281442640, 103236350716, (.direct 3523554676644 3482562783967), (.chord .universal 0 10180665226)⟩)))
        (.original (.row ⟨95281442640, 103236350716, (.direct 824633666698 818631613270), (.variance 206554036734)⟩)))
      (.original (.row ⟨95281442640, 103236350716, (.direct 824633666698 818631613270), (.variance 206554036734)⟩)))

set_option maxRecDepth 16000 in
theorem CutMid3H0NegRestPart9_ok : CutMid3H0NegRestPart9Tree.geometryOK CutMid3H0NegPowerCache CutMid3H0NegRestPart9Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
