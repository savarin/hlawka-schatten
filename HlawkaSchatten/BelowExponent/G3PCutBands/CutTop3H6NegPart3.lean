/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H6NegPart3`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H6NegPart3Box : Box := (((((((((((⟨![27/68, 9/50, 0, -8], ![63/136, 19/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 3 (0)).upperChild 3 (-1/8)).lowerChild 2 (5/16)).lowerChild 1 (37/200)).lowerChild 3 (-1/16)

set_option maxRecDepth 16000 in
def CutTop3H6NegPart3Tree : CertTree :=
  .cut 2 (7/32)
    (.row ⟨120689819474, 122287555846, (.direct 3393509060 259123544), (.chord (.midpoint ⟨548633768097, 78474089275, 123564394144, 484747120192, 173066076194, 256796481901⟩) 10180665226 24716235638)⟩)
    (.cut 3 (-3/32)
      (.row ⟨120689819474, 122287555846, (.direct 6452795533 1814623866), (.chord (.midpoint ⟨505229825768, 101032207588, 144541972198, 433707618928, 189981603656, 300910763833⟩) 24716235638 43500686443)⟩)
      (.cut 0 (117/272)
        (.row ⟨120689819474, 122287555846, (.direct 3393509060 388234966), (.chord (.midpoint ⟨551698794749, 76985570061, 122013304650, 489111335002, 171847172574, 325867845869⟩) 24716235638 43500686443)⟩)
        (.row ⟨120689819474, 122287555846, (.direct 3393509060 259123544), (.chord (.midpoint ⟨539566793342, 82957192983, 123459867037, 485038275328, 176651298249, 323478077047⟩) 24716235638 43500686443)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop3H6NegPart3_checked : CutTop3H6NegPart3Tree.commonOK CutTop3H6NegPart3Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
