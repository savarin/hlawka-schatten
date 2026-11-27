/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H4NegPart53`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H4NegPart53Box : Box := (((((⟨![9/34, 19/100, 0, -8], ![45/136, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).upperChild 3 (1/4)).upperChild 2 (1/2)

set_option maxRecDepth 16000 in
def CutTop4H4NegPart53Tree : CertTree :=
  .cut 3 (1/2)
    (.cut 2 (3/4)
      (.cut 3 (3/8)
        (.cut 2 (5/8)
          (.row ⟨123862991199, 126950446638, (.direct 58075547817 63816266796), (.chord (.secant 1197878289106 100866659274 7428786252 73035151820) 91625974997 130502050762)⟩)
          (.row ⟨123862991199, 126950446638, (.direct 58075547817 63816266796), (.chord (.secant 1080690719374 57355261866 1073664723 54705658368) 130502050762 174227471798)⟩))
        (.row ⟨123862991199, 126950446638, (.direct 91625662891 97022205632), (.chord (.secant 1383462000445 182418708244 20145516394 98441691225) 91625974997 174227471798)⟩))
      (.row ⟨123862991199, 126950446638, (.direct 91625662891 97022205632), (.chord (.secant 1120244136111 71207564248 3184490994 34674358451) 174227471798 274877906944)⟩))
    (.row ⟨123862991199, 126950446638, (.direct 174227225485 177623698670), (.variance 362358449034)⟩)

set_option maxRecDepth 16000 in
theorem CutTop4H4NegPart53_checked : CutTop4H4NegPart53Tree.commonOK CutTop4H4NegPart53Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
