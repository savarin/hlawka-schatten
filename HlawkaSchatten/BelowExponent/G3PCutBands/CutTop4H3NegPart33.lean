/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H3NegPart33`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H3NegPart33Box : Box := ((((((((((⟨![27/136, 19/100, 0, -8], ![9/34, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).upperChild 3 (0)).lowerChild 2 (5/16)).lowerChild 3 (1/8)).upperChild 3 (1/16)

set_option maxRecDepth 16000 in
def CutTop4H3NegPart33Tree : CertTree :=
  .cut 2 (7/32)
    (.cut 2 (11/64)
      (.cut 3 (3/32)
        (.row ⟨123862991199, 126950446638, (.direct 6452795533 9593842888), (.chord (.secant 1377650222555 179672791631 23624634987 85123345568) 10180665226 16864782083)⟩)
        (.row ⟨123862991199, 126950446638, (.direct 10180561190 13697503795), (.chord (.secant 1574151333884 278088253644 61959608719 140683829642) 10180665226 16864782083)⟩))
      (.cut 3 (3/32)
        (.cut 3 (5/64)
          (.row ⟨123862991199, 126950446638, (.direct 4833349683 7750442396), (.chord (.secant 1110964859721 67875878313 8352228671 58082670551) 16864782083 24716235638)⟩)
          (.row ⟨123862991199, 126950446638, (.direct 6452795533 9593842888), (.chord (.secant 1176017188871 92208793680 18187803238 76164747301) 16864782083 24716235638)⟩))
        (.row ⟨123862991199, 126950446638, (.direct 10180561190 13697503795), (.chord (.secant 1310170854231 148637174774 30581333461 95993554698) 16864782083 24716235638)⟩)))
    (.cut 3 (3/32)
      (.cut 2 (17/64)
        (.cut 3 (5/64)
          (.row ⟨123862991199, 126950446638, (.direct 4833349683 7750442396), (.chord (.secant 1016782879739 37083060804 1955573271 42697330986) 24716235638 33622326476)⟩)
          (.row ⟨123862991199, 126950446638, (.direct 6452795533 9593842888), (.chord (.secant 1066163652535 52506263591 7345917172 55989702163) 24716235638 33622326476)⟩))
        (.cut 3 (5/64)
          (.row ⟨123862991199, 126950446638, (.direct 4833349683 7750442396), (.chord (.secant 957497004145 21047926139 16689759 33001374757) 33622326476 43500686443)⟩)
          (.row ⟨123862991199, 126950446638, (.direct 6452795533 9593842888), (.chord (.secant 997221492186 31468154583 2143501535 43275237608) 33622326476 43500686443)⟩)))
      (.cut 2 (17/64)
        (.row ⟨123862991199, 126950446638, (.direct 10180561190 13697503795), (.chord (.secant 1167491787518 88895061808 14956877515 70566117890) 24716235638 33622326476)⟩)
        (.row ⟨123862991199, 126950446638, (.direct 10180561190 13697503795), (.chord (.secant 1078442834222 56596228467 6670253350 54541556765) 33622326476 43500686443)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop4H3NegPart33_checked : CutTop4H3NegPart33Tree.commonOK CutTop4H3NegPart33Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
