/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H1NegPart2`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H1NegPart2Box : Box := (((((((((⟨![9/136, 17/100, 0, -8], ![9/68, 9/50, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 2 (5/16)).lowerChild 3 (0)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutTop2H1NegPart2Tree : CertTree :=
  .cut 1 (7/40)
    (.cut 3 (-3/16)
      (.cut 2 (7/32)
        (.row ⟨117423580139, 119068833411, (.direct 19358451269 16951019741), (.variance 570131803012)⟩)
        (.row ⟨117423580139, 119068833411, (.direct 19358451269 16951019741), (.chord (.midpoint ⟨459056114402, 128176040783, 200851185688, 343416958841, 207421635353, 234095201182⟩) 24716235638 43500686443)⟩))
      (.cut 2 (7/32)
        (.row ⟨117423580139, 119068833411, (.direct 10180561190 8400164192), (.chord (.midpoint ⟨483300717879, 113507251368, 191533912624, 355187810481, 198323065773, 166872818518⟩) 10180665226 24716235638)⟩)
        (.cut 0 (27/272)
          (.row ⟨117423580139, 119068833411, (.direct 10180561190 8833406858), (.chord (.midpoint ⟨560785236718, 72652350335, 160550000835, 402561032526, 168211878295, 287062529818⟩) 24716235638 43500686443)⟩)
          (.row ⟨117423580139, 119068833411, (.direct 10180561190 8400164192), (.chord (.midpoint ⟨548554222687, 78512901110, 161752921222, 400434625877, 173097662103, 284496973850⟩) 24716235638 43500686443)⟩))))
    (.cut 3 (-3/16)
      (.cut 2 (7/32)
        (.row ⟨119068833410, 120689819475, (.direct 19358451269 16877350089), (.variance 570782426377)⟩)
        (.row ⟨119068833410, 120689819475, (.direct 19358451269 16877350089), (.chord (.midpoint ⟨459853528952, 127678594911, 200546840679, 343786647309, 207124169698, 234299174968⟩) 24716235638 43500686443)⟩))
      (.cut 2 (7/32)
        (.row ⟨119068833410, 120689819475, (.direct 10180561190 8346323699), (.chord (.midpoint ⟨484400730145, 112863760992, 191107791771, 355749545358, 197907364483, 167303715713⟩) 10180665226 24716235638)⟩)
        (.cut 0 (27/272)
          (.row ⟨119068833410, 120689819475, (.direct 10180561190 8792256668), (.chord (.midpoint ⟨561395189293, 72365719151, 160296507726, 403012611399, 167966642952, 287230212484⟩) 24716235638 43500686443)⟩)
          (.row ⟨119068833410, 120689819475, (.direct 10180561190 8346323699), (.chord (.midpoint ⟨549360957619, 78119703146, 161416656045, 401026314670, 172777212170, 284750077648⟩) 24716235638 43500686443)⟩))))

set_option maxRecDepth 16000 in
theorem CutTop2H1NegPart2_checked : CutTop2H1NegPart2Tree.commonOK CutTop2H1NegPart2Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
