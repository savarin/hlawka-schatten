/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H4NegPart37`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H4NegPart37Box : Box := ((((((((((⟨![9/34, 19/100, 0, -8], ![45/136, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).upperChild 3 (0)).lowerChild 3 (1/8)).lowerChild 2 (5/16)).upperChild 3 (1/16)

set_option maxRecDepth 16000 in
def CutTop4H4NegPart37Tree : CertTree :=
  .cut 2 (7/32)
    (.cut 2 (11/64)
      (.cut 3 (3/32)
        (.row ⟨123862991199, 126950446638, (.direct 6452795533 10448909455), (.chord (.secant 1367501357085 174904535170 18840561190 96079777233) 10180665226 16864782083)⟩)
        (.row ⟨123862991199, 126950446638, (.direct 10180561190 14635652281), (.chord (.secant 1561968411682 271681329149 54697360714 153348731093) 10180665226 16864782083)⟩))
      (.cut 3 (3/32)
        (.cut 3 (5/64)
          (.row ⟨123862991199, 126950446638, (.direct 4833349683 8556446983), (.chord (.secant 1091522830020 61056549222 4427450251 65558631541) 16864782083 24716235638)⟩)
          (.row ⟨123862991199, 126950446638, (.direct 6452795533 10448909455), (.chord (.secant 1155665415371 84358397232 12650850275 84258538043) 16864782083 24716235638)⟩))
        (.row ⟨123862991199, 126950446638, (.direct 10180561190 14635652281), (.chord (.secant 1287956686089 138781126755 23660232885 104635265073) 16864782083 24716235638)⟩)))
    (.cut 3 (3/32)
      (.cut 2 (17/64)
        (.cut 3 (5/64)
          (.row ⟨123862991199, 126950446638, (.direct 4833349683 8556446983), (.chord (.secant 992050454316 30034865519 20428297 48193007713) 24716235638 33622326476)⟩)
          (.row ⟨123862991199, 126950446638, (.direct 6452795533 10448909455), (.chord (.secant 1040617134484 44314362881 3153410897 61939553624) 24716235638 33622326476)⟩))
        (.cut 0 (81/272)
          (.row ⟨123862991199, 126950446638, (.direct 6452795533 10018008898), (.chord (.secant 959887557477 21634896305 332523793 37249061511) 33622326476 43500686443)⟩)
          (.cut 3 (5/64)
            (.row ⟨123862991199, 126950446638, (.direct 4833349683 8556446983), (.chord (.secant 907073946726 10041331243 1484862492 39443327506) 33622326476 43500686443)⟩)
            (.row ⟨123862991199, 126950446638, (.direct 6452795533 10448909455), (.chord (.secant 945725933875 18238282461 226713618 50237033194) 33622326476 43500686443)⟩))))
      (.cut 2 (17/64)
        (.row ⟨123862991199, 126950446638, (.direct 10180561190 14635652281), (.chord (.secant 1140294373042 78569361693 9150196168 76918752241) 24716235638 33622326476)⟩)
        (.row ⟨123862991199, 126950446638, (.direct 10180561190 14635652281), (.chord (.secant 1048327661229 46740358148 2359962861 59451598261) 33622326476 43500686443)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop4H4NegPart37_checked : CutTop4H4NegPart37Tree.commonOK CutTop4H4NegPart37Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
