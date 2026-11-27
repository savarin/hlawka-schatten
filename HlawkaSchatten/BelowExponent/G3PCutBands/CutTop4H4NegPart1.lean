/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H4NegPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H4NegPart1Box : Box := ((((((⟨![9/34, 19/100, 0, -8], ![45/136, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutTop4H4NegPart1Tree : CertTree :=
  .cut 3 (0)
    (.row ⟨123862991199, 126950446638, (.direct 0 1463531430), (.chord .universal 0 10180665226)⟩)
    (.cut 3 (1/8)
      (.cut 3 (1/16)
        (.cut 3 (1/32)
          (.row ⟨123862991199, 126950446638, (.direct 1131165907 3776874053), (.chord .universal 0 10180665226)⟩)
          (.cut 2 (1/16)
            (.row ⟨123862991199, 126950446638, (.direct 3393509060 6807321803), (.variance 895036841024)⟩)
            (.row ⟨123862991199, 126950446638, (.direct 3393509060 6807321803), (.chord (.secant 1812179452256 409913155126 11429316345 81767026458) 3393555298 10180665226)⟩)))
        (.cut 3 (3/32)
          (.row ⟨123862991199, 126950446638, (.direct 6452795533 10448909455), (.variance 751788876005)⟩)
          (.row ⟨123862991199, 126950446638, (.direct 10180561190 14635652281), (.variance 665159722518)⟩)))
      (.cut 3 (3/16)
        (.row ⟨123862991199, 126950446638, (.direct 19358451269 24469794282), (.variance 605229129678)⟩)
        (.row ⟨123862991199, 126950446638, (.direct 30541785600 36050804961), (.variance 525264945945)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop4H4NegPart1_checked : CutTop4H4NegPart1Tree.commonOK CutTop4H4NegPart1Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
