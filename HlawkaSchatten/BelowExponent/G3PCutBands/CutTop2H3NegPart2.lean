/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H3NegPart2`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H3NegPart2Box : Box := (((((((((⟨![27/136, 17/100, 0, -8], ![9/34, 9/50, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 3 (0)).lowerChild 2 (5/16)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutTop2H3NegPart2Tree : CertTree :=
  .cut 2 (7/32)
    (.cut 3 (-3/16)
      (.row ⟨117423580139, 120689819475, (.direct 19358451269 14524006646), (.variance 593674649434)⟩)
      (.row ⟨117423580139, 120689819475, (.direct 10180561190 6650100644), (.chord (.midpoint ⟨449945102362, 133933402127, 190869877204, 356064109259, 210812669073, 163282662991⟩) 10180665226 24716235638)⟩))
    (.cut 3 (-3/16)
      (.row ⟨117423580139, 120689819475, (.direct 19358451269 14524006646), (.chord (.midpoint ⟨417100769120, 155842918165, 203832892412, 339845057388, 222936398180, 222708130712⟩) 24716235638 43500686443)⟩)
      (.row ⟨117423580139, 120689819475, (.direct 10180561190 6650100644), (.chord (.midpoint ⟨520320222974, 92872610826, 162004445323, 399993419513, 184167830729, 271367654222⟩) 24716235638 43500686443)⟩))

set_option maxRecDepth 16000 in
theorem CutTop2H3NegPart2_checked : CutTop2H3NegPart2Tree.commonOK CutTop2H3NegPart2Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
