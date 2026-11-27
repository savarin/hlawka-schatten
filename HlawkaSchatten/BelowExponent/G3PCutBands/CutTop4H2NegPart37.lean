/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H2NegPart37`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H2NegPart37Box : Box := (((((⟨![9/68, 19/100, 0, -8], ![27/136, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).upperChild 3 (1/4)).upperChild 2 (1/2)

set_option maxRecDepth 16000 in
def CutTop4H2NegPart37Tree : CertTree :=
  .cut 3 (1/2)
    (.cut 3 (3/8)
      (.cut 2 (3/4)
        (.row ⟨123862991199, 126950446638, (.direct 58075547817 61496152177), (.chord (.secant 1284482322281 137256707697 13405142966 51407525916) 91625974997 174227471798)⟩)
        (.row ⟨123862991199, 126950446638, (.direct 58075547817 61496152177), (.chord (.secant 1090796220336 60806032949 3341264441 32583886820) 174227471798 274877906944)⟩))
      (.row ⟨123862991199, 126950446638, (.direct 91625662891 94850045034), (.chord (.secant 1477671160135 228400545082 18976110592 60221367022) 91625974997 274877906944)⟩))
    (.row ⟨123862991199, 126950446638, (.direct 174227225485 176262304627), (.variance 364411078691)⟩)

set_option maxRecDepth 16000 in
theorem CutTop4H2NegPart37_checked : CutTop4H2NegPart37Tree.commonOK CutTop4H2NegPart37Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
