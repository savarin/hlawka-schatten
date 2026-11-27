/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H4NegPart20`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H4NegPart20Box : Box := ((((((((((⟨![9/34, 9/50, 0, -8], ![45/136, 19/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).upperChild 3 (0)).lowerChild 2 (5/16)).lowerChild 3 (1/8)).upperChild 3 (1/16)

set_option maxRecDepth 16000 in
def CutTop3H4NegPart20Tree : CertTree :=
  .cut 2 (7/32)
    (.cut 2 (11/64)
      (.cut 3 (3/32)
        (.row ⟨120689819474, 123862991200, (.direct 6452795533 10210014778), (.chord (.secant 1355920654431 169505880973 17440258963 93501639142) 10180665226 16864782083)⟩)
        (.row ⟨120689819474, 123862991200, (.direct 10180561190 14374205462), (.chord (.secant 1550222592894 265539342203 52676881166 150382990260) 10180665226 16864782083)⟩))
      (.cut 3 (3/32)
        (.cut 3 (5/64)
          (.row ⟨120689819474, 123862991200, (.direct 4833349683 8330858079), (.chord (.secant 1083637384710 58355000236 3791642954 63799476700) 16864782083 24716235638)⟩)
          (.row ⟨120689819474, 123862991200, (.direct 6452795533 10210014778), (.chord (.secant 1147747971295 81361135587 11716759851 82359305463) 16864782083 24716235638)⟩))
        (.row ⟨120689819474, 123862991200, (.direct 10180561190 14374205462), (.chord (.secant 1279999287461 135296686058 22497746066 102611635168) 16864782083 24716235638)⟩)))
    (.cut 3 (3/32)
      (.cut 2 (17/64)
        (.cut 3 (5/64)
          (.row ⟨120689819474, 123862991200, (.direct 4833349683 8330858079), (.chord (.secant 986068117262 28404334299 30379986 46899829976) 24716235638 33622326476)⟩)
          (.row ⟨120689819474, 123862991200, (.direct 6452795533 10210014778), (.chord (.secant 1034631224996 42459630971 2699181665 60543402908) 24716235638 33622326476)⟩))
        (.cut 0 (81/272)
          (.row ⟨120689819474, 123862991200, (.direct 6452795533 9806251112), (.chord (.secant 955580209708 20581213696 525056642 36249546034) 33622326476 43500686443)⟩)
          (.cut 3 (5/64)
            (.row ⟨120689819474, 123862991200, (.direct 4833349683 8330858079), (.chord (.secant 902306797693 9151137612 1843344488 38295357023) 33622326476 43500686443)⟩)
            (.row ⟨120689819474, 123862991200, (.direct 6452795533 10210014778), (.chord (.secant 940966654394 17141454836 82750229 49001735172) 33622326476 43500686443)⟩))))
      (.cut 2 (17/64)
        (.row ⟨120689819474, 123862991200, (.direct 10180561190 14374205462), (.chord (.secant 1134315863519 76351404013 8479135247 75431155424) 24716235638 33622326476)⟩)
        (.row ⟨120689819474, 123862991200, (.direct 10180561190 14374205462), (.chord (.secant 1043554028582 45233558466 2018948841 58301813510) 33622326476 43500686443)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop3H4NegPart20_checked : CutTop3H4NegPart20Tree.commonOK CutTop3H4NegPart20Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
