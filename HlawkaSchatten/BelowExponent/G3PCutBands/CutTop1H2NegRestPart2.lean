/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H2NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H2NegRestPart2`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H2NegRestPart2Box : Box := ((⟨![9/68, 4/25, 0, -8], ![27/136, 17/100, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutTop1H2NegRestPart2Tree : RatioRemainder :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.original (.cone))
          (.original (.row ⟨114055813619, 117423580140, .zero, (.variance 309245892799)⟩)))
        (.original (.row ⟨114055813619, 117423580140, .zero, (.variance 309245892799)⟩)))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (13/8)
            (.original (.row ⟨114055813619, 117423580140, (.direct 391506126583 389220204344), (.variance 250948778046)⟩))
            (.original (.row ⟨114055813619, 117423580140, (.direct 593382169971 586726221251), (.variance 225378196293)⟩)))
          (.original (.row ⟨114055813619, 117423580140, (.direct 391506126583 389220204344), (.variance 250948778046)⟩)))
        (.original (.row ⟨114055813619, 117423580140, (.direct 391506126583 389220204344), (.variance 250948778046)⟩))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.original (.row ⟨114055813619, 117423580140, (.direct 824633666698 812616568006), (.variance 206953306018)⟩))
            (.original (.row ⟨114055813619, 117423580140, (.direct 2002014560937 1960387412061), (.variance 164332716903)⟩)))
          (.original (.row ⟨114055813619, 117423580140, (.direct 3523554676644 3441540704828), (.chord .universal 0 10180665226)⟩)))
        (.cut 3 (5)
          (.original (.row ⟨114055813619, 117423580140, (.direct 824633666698 812616568006), (.variance 206953306018)⟩))
          (.original (.row ⟨114055813619, 117423580140, (.direct 3523554676644 3441540704828), (.variance 141815476288)⟩))))
      (.original (.row ⟨114055813619, 117423580140, (.direct 824633666698 812616568006), (.variance 206953306018)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop1H2NegRestPart2_ok : CutTop1H2NegRestPart2Tree.geometryOK CutTop1H2NegPowerCache CutTop1H2NegRestPart2Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
