/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H6NegPart32`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H6NegPart32Box : Box := ((((((⟨![27/68, 9/50, 0, -8], ![63/136, 19/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).upperChild 2 (1/2)).upperChild 2 (3/4)

set_option maxRecDepth 16000 in
def CutTop3H6NegPart32Tree : CertTree :=
  .cut 3 (0)
    (.cut 3 (-1/8)
      (.row ⟨120689819474, 123862991200, (.direct 10180561190 4088422227), (.chord (.midpoint ⟨540828187791, 82326342632, 127467720007, 474167686685, 176154310881, 315963631129⟩) 174227471798 274877906944)⟩)
      (.cut 3 (-1/16)
        (.row ⟨120689819474, 123862991200, (.direct 3393509060 211031955), (.chord (.midpoint ⟨574459438858, 66354124104, 110126595889, 526007113238, 162675426255, 338710205359⟩) 174227471798 274877906944)⟩)
        (.cut 3 (-1/32)
          (.row ⟨120689819474, 123862991200, (.direct 1131165907 509646583), (.chord (.secant 595199913451 57307542753 89007571113 934453247) 174227471798 274877906944)⟩)
          (.row ⟨120689819474, 123862991200, (.direct 0 2279757842), (.chord (.secant 618331394526 47931544908 78626495590 164171355) 174227471798 274877906944)⟩))))
    (.cut 3 (1/8)
      (.cut 3 (1/16)
        (.cut 3 (1/32)
          (.row ⟨120689819474, 123862991200, (.direct 1131165907 4856210701), (.chord (.secant 641786758842 39188683093 70546115572 1624667494) 174227471798 274877906944)⟩)
          (.row ⟨120689819474, 123862991200, (.direct 3393509060 8085590294), (.chord (.secant 665562863702 31113376806 62793806953 3996356367) 174227471798 274877906944)⟩))
        (.row ⟨120689819474, 123862991200, (.direct 10180561190 16196901941), (.chord (.secant 714065226811 17143199624 55379737529 7070377116) 174227471798 274877906944)⟩))
      (.cut 3 (3/16)
        (.row ⟨120689819474, 123862991200, (.direct 19358451269 26211593380), (.chord (.secant 763815278522 6521623142 41613048436 14960318468) 174227471798 274877906944)⟩)
        (.row ⟨120689819474, 123862991200, (.direct 30541785600 37899295126), (.chord (.secant 814791197767 357119127 29355707518 24833723624) 174227471798 274877906944)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop3H6NegPart32_checked : CutTop3H6NegPart32Tree.commonOK CutTop3H6NegPart32Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
