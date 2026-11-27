/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H0NegRestPart5`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H0NegRestPart5Box : Box := ((⟨![0, 19/100, 0, -8], ![9/136, 1/5, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutTop4H0NegRestPart5Tree : RatioRemainder :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.original (.cone))
          (.original (.row ⟨123862991199, 126950446638, .zero, (.variance 309737727641)⟩)))
        (.original (.row ⟨123862991199, 126950446638, .zero, (.variance 309737727641)⟩)))
      (.original (.row ⟨123862991199, 126950446638, (.direct 391506126583 390594411579), (.variance 250717284982)⟩)))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.original (.row ⟨123862991199, 126950446638, (.direct 824633666698 819836417934), (.variance 206474508601)⟩))
          (.original (.row ⟨123862991199, 126950446638, (.direct 3523554676644 3490787563943), (.chord .universal 0 10180665226)⟩)))
        (.cut 3 (5)
          (.original (.row ⟨123862991199, 126950446638, (.direct 824633666698 819836417934), (.variance 206474508601)⟩))
          (.original (.row ⟨123862991199, 126950446638, (.direct 3523554676644 3490787563943), (.variance 141288835262)⟩))))
      (.original (.row ⟨123862991199, 126950446638, (.direct 824633666698 819836417934), (.variance 206474508601)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop4H0NegRestPart5_ok : CutTop4H0NegRestPart5Tree.geometryOK CutTop4H0NegPowerCache CutTop4H0NegRestPart5Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
