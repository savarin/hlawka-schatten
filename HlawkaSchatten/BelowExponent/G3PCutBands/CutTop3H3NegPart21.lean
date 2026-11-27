/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H3NegPart21`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H3NegPart21Box : Box := ((((((((((⟨![27/136, 9/50, 0, -8], ![9/34, 19/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).upperChild 3 (0)).upperChild 2 (5/16)).lowerChild 3 (1/8)).upperChild 3 (1/16)

set_option maxRecDepth 16000 in
def CutTop3H3NegPart21Tree : CertTree :=
  .cut 2 (13/32)
    (.cut 3 (3/32)
      (.cut 2 (23/64)
        (.cut 0 (63/272)
          (.row ⟨120689819474, 123862991200, (.direct 6452795533 9016923658), (.chord (.secant 939821075617 16880907412 93526455 25869065188) 43500686443 54287507865)⟩)
          (.row ⟨120689819474, 123862991200, (.direct 6452795533 9408532105), (.chord (.secant 924085580440 13443153825 1118864790 27440958824) 43500686443 54287507865)⟩))
        (.cut 0 (63/272)
          (.row ⟨120689819474, 123862991200, (.direct 6452795533 9016923658), (.chord (.secant 906893666426 10007145840 1201415279 21300428431) 54287507865 65931360876)⟩)
          (.row ⟨120689819474, 123862991200, (.direct 6452795533 9408532105), (.chord (.secant 890481580500 7071255632 3014272519 22594715938) 54287507865 65931360876)⟩)))
      (.row ⟨120689819474, 123862991200, (.direct 10180561190 13493285519), (.chord (.secant 1014461442487 36401175653 181881986 35434232840) 43500686443 65931360876)⟩))
    (.cut 3 (3/32)
      (.cut 0 (63/272)
        (.row ⟨120689819474, 123862991200, (.direct 6452795533 9016923658), (.chord (.secant 881860984640 5677618863 4043134679 15327147141) 65931360876 91625974997)⟩)
        (.row ⟨120689819474, 123862991200, (.direct 6452795533 9408532105), (.chord (.secant 864946251676 3277008350 6783736434 16258477472) 65931360876 91625974997)⟩))
      (.row ⟨120689819474, 123862991200, (.direct 10180561190 13493285519), (.chord (.secant 937786235539 16421465958 1781352866 25497407356) 65931360876 91625974997)⟩))

set_option maxRecDepth 16000 in
theorem CutTop3H3NegPart21_checked : CutTop3H3NegPart21Tree.commonOK CutTop3H3NegPart21Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
