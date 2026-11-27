/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H7NegPart26`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H7NegPart26Box : Box := ((((((⟨![63/136, 9/50, 0, -8], ![9/17, 19/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).upperChild 2 (1/2)).upperChild 2 (3/4)

set_option maxRecDepth 16000 in
def CutTop3H7NegPart26Tree : CertTree :=
  .cut 3 (0)
    (.cut 3 (-1/8)
      (.row ⟨120689819474, 123862991200, (.direct 10180561190 3391807444), (.chord (.midpoint ⟨508552656970, 99206076045, 134346731172, 456810433667, 188706959889, 307838880270⟩) 174227471798 274877906944)⟩)
      (.cut 3 (-1/16)
        (.row ⟨120689819474, 123862991200, (.direct 3393509060 34457334), (.chord (.midpoint ⟨541200285160, 82140691955, 117845928304, 501321242742, 176007596899, 330830783157⟩) 174227471798 274877906944)⟩)
        (.cut 3 (-1/32)
          (.row ⟨120689819474, 123862991200, (.direct 1131165907 848254909), (.chord (.secant 562725853934 71742257913 105905230309 489818315) 174227471798 274877906944)⟩)
          (.row ⟨120689819474, 123862991200, (.direct 0 2817109798), (.chord (.secant 585222340856 61583730646 95552962714 391349178) 174227471798 274877906944)⟩))))
    (.cut 3 (1/8)
      (.cut 3 (1/16)
        (.cut 3 (1/32)
          (.row ⟨120689819474, 123862991200, (.direct 1131165907 5533663332), (.chord (.secant 608042631703 52009380017 86907769815 2074306675) 174227471798 274877906944)⟩)
          (.row ⟨120689819474, 123862991200, (.direct 3393509060 8871241147), (.chord (.secant 631183498744 43045707334 78568973834 4591260176) 174227471798 274877906944)⟩))
        (.cut 0 (135/272)
          (.row ⟨120689819474, 123862991200, (.direct 10180561190 16665024121), (.chord (.secant 675952105873 27835462938 62019855820 7775129165) 174227471798 274877906944)⟩)
          (.row ⟨120689819474, 123862991200, (.direct 10180561190 17138050606), (.chord (.secant 658404375780 33460947770 69737394023 8136695715) 174227471798 274877906944)⟩)))
      (.cut 3 (3/16)
        (.row ⟨120689819474, 123862991200, (.direct 19358451269 27252008608), (.chord (.secant 726891802613 14029423444 55477212813 15821334044) 174227471798 274877906944)⟩)
        (.row ⟨120689819474, 123862991200, (.direct 30541785600 38997564469), (.chord (.secant 776592836709 4466389529 41789660163 25794447058) 174227471798 274877906944)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop3H7NegPart26_checked : CutTop3H7NegPart26Tree.commonOK CutTop3H7NegPart26Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
