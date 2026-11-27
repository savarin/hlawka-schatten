/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H3NegRestPart14`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H3NegRestPart14Box : Box := (((((((((((((⟨![27/68, 9/100, 0, -8], ![9/17, 11/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)).upperChild 3 (0)).lowerChild 3 (1/8)).lowerChild 3 (1/16)).lowerChild 1 (1/10)).lowerChild 3 (1/32)).upperChild 1 (19/200)).upperChild 0 (63/136)

set_option maxRecDepth 16000 in
def CutMid2H3NegRestPart14Tree : RatioRemainder :=
  .cut 1 (39/400)
    (.cut 0 (135/272)
      (.cut 1 (77/800)
        (.cut 3 (1/64)
          (.cut 2 (1/16)
            (.original (.row ⟨88806993132, 89365973271, (.direct 377054043 1694518789), (.variance 1313090902301)⟩))
            (.covered))
          (.cut 2 (1/16)
            (.original (.row ⟨88806993132, 89365973271, (.direct 1131165907 2815937393), (.variance 1063799710636)⟩))
            (.covered)))
        (.cut 3 (1/64)
          (.cut 2 (1/16)
            (.original (.row ⟨89365973270, 89921191063, (.direct 377054043 1717033675), (.variance 1305630409305)⟩))
            (.covered))
          (.cut 2 (1/16)
            (.original (.row ⟨89365973270, 89921191063, (.direct 1131165907 2842644503), (.variance 1060203038255)⟩))
            (.covered))))
      (.cut 3 (1/64)
        (.cut 2 (1/16)
          (.original (.row ⟨88806993132, 89921191063, (.direct 377054043 1830081789), (.variance 1276024250788)⟩))
          (.covered))
        (.cut 2 (1/16)
          (.original (.row ⟨88806993132, 89921191063, (.direct 1131165907 2976201998), (.variance 1045648415820)⟩))
          (.covered))))
    (.cut 3 (1/64)
      (.cut 2 (1/16)
        (.original (.row ⟨89921191062, 91020629598, (.direct 377054043 1879719697), (.variance 1298302959111)⟩))
        (.covered))
      (.cut 2 (1/16)
        (.original (.row ⟨89921191062, 91020629598, (.direct 1131165907 3034575728), (.variance 1056642844843)⟩))
        (.covered)))

set_option maxRecDepth 16000 in
theorem CutMid2H3NegRestPart14_ok : CutMid2H3NegRestPart14Tree.ok CutMid2H3NegRestPart14Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
