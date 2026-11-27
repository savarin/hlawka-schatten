/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H5NegPart21`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H5NegPart21Box : Box := ((((((((((⟨![45/136, 9/50, 0, -8], ![27/68, 19/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).upperChild 3 (0)).lowerChild 2 (5/16)).lowerChild 3 (1/8)).upperChild 3 (1/16)

set_option maxRecDepth 16000 in
def CutTop3H5NegPart21Tree : CertTree :=
  .cut 2 (7/32)
    (.cut 2 (11/64)
      (.cut 3 (3/32)
        (.row ⟨120689819474, 123862991200, (.direct 6452795533 11035424146), (.chord (.secant 1343525895155 163778699454 12891338883 104161681881) 10180665226 16864782083)⟩)
        (.row ⟨120689819474, 123862991200, (.direct 10180561190 15275518371), (.chord (.secant 1535770068106 258030098435 45378303878 162593904411) 10180665226 16864782083)⟩))
      (.cut 3 (3/32)
        (.cut 3 (5/64)
          (.row ⟨120689819474, 123862991200, (.direct 4833349683 9111515937), (.chord (.secant 1062810078792 51406081573 999569345 71073201039) 16864782083 24716235638)⟩)
          (.row ⟨120689819474, 123862991200, (.direct 6452795533 11035424146), (.chord (.secant 1126008386653 73301495839 6922066042 90193211822) 16864782083 24716235638)⟩))
        (.row ⟨120689819474, 123862991200, (.direct 10180561190 15275518371), (.chord (.secant 1256397198956 125109702892 16126098762 110943573944) 16864782083 24716235638)⟩)))
    (.cut 3 (3/32)
      (.cut 2 (17/64)
        (.cut 3 (5/64)
          (.row ⟨120689819474, 123862991200, (.direct 4833349683 9111515937), (.chord (.secant 960432437675 21769441059 2106834752 52246839896) 24716235638 33622326476)⟩)
          (.row ⟨120689819474, 123862991200, (.direct 6452795533 11035424146), (.chord (.secant 1008183580679 34577844343 204848737 66302209959) 24716235638 33622326476)⟩))
        (.cut 0 (99/272)
          (.cut 3 (5/64)
            (.row ⟨120689819474, 123862991200, (.direct 4833349683 8717961705), (.chord (.secant 888138106035 6681791822 3681610299 40382326096) 33622326476 43500686443)⟩)
            (.row ⟨120689819474, 123862991200, (.direct 6452795533 10619759562), (.chord (.secant 926436385756 13939597657 448516266 51245921644) 33622326476 43500686443)⟩))
          (.cut 3 (5/64)
            (.row ⟨120689819474, 123862991200, (.direct 4833349683 9111515937), (.chord (.secant 874052351711 4511574544 5949558479 42509885169) 33622326476 43500686443)⟩)
            (.row ⟨120689819474, 123862991200, (.direct 6452795533 11035424146), (.chord (.secant 911989743892 10988933220 1730711487 53526982123) 33622326476 43500686443)⟩))))
      (.cut 2 (17/64)
        (.row ⟨120689819474, 123862991200, (.direct 10180561190 15275518371), (.chord (.secant 1106224664666 66192873657 3836606385 81556072621) 24716235638 33622326476)⟩)
        (.row ⟨120689819474, 123862991200, (.direct 10180561190 15275518371), (.chord (.secant 1012861795074 35933695671 16350109 63035849177) 33622326476 43500686443)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop3H5NegPart21_checked : CutTop3H5NegPart21Tree.commonOK CutTop3H5NegPart21Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
