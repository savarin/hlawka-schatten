/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H0NegPart2`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H0NegPart2Box : Box := (((((((((⟨![0, 17/100, 0, -8], ![9/136, 9/50, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 2 (5/16)).lowerChild 3 (0)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutTop2H0NegPart2Tree : CertTree :=
  .cut 1 (7/40)
    (.cut 3 (-3/16)
      (.cut 2 (7/32)
        (.row ⟨117423580139, 119068833411, (.direct 19358451269 18140070146), (.variance 560099649713)⟩)
        (.row ⟨117423580139, 119068833411, (.direct 19358451269 18140070146), (.chord (.midpoint ⟨481396657907, 114625570282, 199042527709, 345628120315, 199041987925, 239643475624⟩) 24716235638 43500686443)⟩))
      (.cut 2 (7/32)
        (.row ⟨117423580139, 119068833411, (.direct 10180561190 9274638103), (.chord (.midpoint ⟨501420729457, 103146182890, 191439720946, 355311794863, 191439139145, 168647478831⟩) 10180665226 24716235638)⟩)
        (.cut 0 (9/272)
          (.row ⟨117423580139, 119068833411, (.direct 10180561190 9723756587), (.chord (.midpoint ⟨585544476576, 61443477349, 158124754209, 406932075219, 158124019680, 292145484615⟩) 24716235638 43500686443)⟩)
          (.row ⟨117423580139, 119068833411, (.direct 10180561190 9274638103), (.chord (.midpoint ⟨573115509252, 66961321679, 159340651391, 404726436750, 163223256557, 289611919362⟩) 24716235638 43500686443)⟩))))
    (.cut 3 (-3/16)
      (.cut 2 (7/32)
        (.row ⟨119068833410, 120689819475, (.direct 19358451269 18102286227), (.variance 560405545200)⟩)
        (.row ⟨119068833410, 120689819475, (.direct 19358451269 18102286227), (.chord (.midpoint ⟨481802352485, 114386816150, 198889415963, 345816883301, 198888875309, 239643475624⟩) 24716235638 43500686443)⟩))
      (.cut 2 (7/32)
        (.row ⟨119068833410, 120689819475, (.direct 10180561190 9246698153), (.chord (.midpoint ⟨501978138348, 102835452914, 191226670279, 355592618262, 191226087336, 168647478831⟩) 10180665226 24716235638)⟩)
        (.cut 0 (9/272)
          (.row ⟨119068833410, 120689819475, (.direct 10180561190 9709536584), (.chord (.midpoint ⟨585751034074, 61353622246, 158039370516, 407088050930, 158038635667, 292145484615⟩) 24716235638 43500686443)⟩)
          (.row ⟨119068833410, 120689819475, (.direct 10180561190 9246698153), (.chord (.midpoint ⟨573525393360, 66775860933, 159170777875, 405032856036, 163056262438, 289695245137⟩) 24716235638 43500686443)⟩))))

set_option maxRecDepth 16000 in
theorem CutTop2H0NegPart2_checked : CutTop2H0NegPart2Tree.commonOK CutTop2H0NegPart2Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
