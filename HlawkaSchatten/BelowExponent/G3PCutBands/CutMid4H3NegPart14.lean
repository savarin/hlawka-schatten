/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid4H3NegPart14`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid4H3NegPart14Box : Box := (((((((((((⟨![27/68, 13/100, 0, -8], ![9/17, 3/20, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 3 (0)).upperChild 2 (5/16)).upperChild 3 (-1/8)).upperChild 0 (63/136)).lowerChild 3 (-1/16)

set_option maxRecDepth 16000 in
def CutMid4H3NegPart14Tree : CertTree :=
  .cut 1 (7/50)
    (.cut 0 (135/272)
      (.row ⟨103236350715, 106974752992, (.direct 3393509060 686678537), (.chord (.midpoint ⟨517803973320, 94209459477, 129785048718, 468145032153, 185141829526, 308727765006⟩) 43500686443 91625974997)⟩)
      (.row ⟨103236350715, 106974752992, (.direct 3393509060 564761546), (.chord (.midpoint ⟨502589229412, 102495341372, 132840850746, 460478542030, 190992423967, 305038753425⟩) 43500686443 91625974997)⟩))
    (.cut 0 (135/272)
      (.cut 3 (-3/32)
        (.row ⟨106974752991, 110576703735, (.direct 6452795533 2362630658), (.chord (.midpoint ⟨488477980082, 110495081779, 143987320987, 434892322221, 196364158621, 310145372492⟩) 43500686443 91625974997)⟩)
        (.row ⟨106974752991, 110576703735, (.direct 3393509060 546276838), (.chord (.midpoint ⟨521181938187, 92416962414, 128098547257, 472509746496, 183833835154, 324166345548⟩) 43500686443 91625974997)⟩))
      (.cut 2 (13/32)
        (.row ⟨106974752991, 110576703735, (.direct 3393509060 426654725), (.chord (.midpoint ⟨501904893319, 102876256654, 133179257985, 459648055944, 191254087540, 306570395789⟩) 43500686443 65931360876)⟩)
        (.row ⟨106974752991, 110576703735, (.direct 3393509060 426654725), (.chord (.midpoint ⟨506153320852, 100523004145, 131071168849, 464881143012, 189627650181, 315594568889⟩) 65931360876 91625974997)⟩)))

set_option maxRecDepth 16000 in
theorem CutMid4H3NegPart14_checked : CutMid4H3NegPart14Tree.commonOK CutMid4H3NegPart14Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
