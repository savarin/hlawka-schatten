/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H5NegPart3`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H5NegPart3Box : Box := ((((((((((⟨![45/136, 17/100, 0, -8], ![27/68, 9/50, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 3 (0)).lowerChild 2 (5/16)).upperChild 3 (-1/8)).lowerChild 3 (-1/16)

set_option maxRecDepth 16000 in
def CutTop2H5NegPart3Tree : CertTree :=
  .cut 2 (7/32)
    (.cut 3 (-3/32)
      (.row ⟨117423580139, 120689819475, (.direct 6452795533 2443250010), (.chord (.midpoint ⟨488261953293, 110619934135, 160277458181, 403046596047, 196446018777, 255001587410⟩) 10180665226 24716235638)⟩)
      (.row ⟨117423580139, 120689819475, (.direct 3393509060 592300407), (.chord (.midpoint ⟨564218907618, 71045729195, 125120645054, 480461502283, 166829306689, 294008745820⟩) 10180665226 24716235638)⟩))
    (.cut 3 (-3/32)
      (.row ⟨117423580139, 120689819475, (.direct 6452795533 2443250010), (.chord (.midpoint ⟨526311682781, 89727340038, 143199823175, 436587838200, 181840826670, 304260027596⟩) 24716235638 43500686443)⟩)
      (.cut 0 (99/272)
        (.cut 1 (7/40)
          (.row ⟨117423580139, 119068833411, (.direct 3393509060 815327491), (.chord (.midpoint ⟨571987874536, 67472776286, 121244125584, 491310889304, 163682278063, 329207068928⟩) 24716235638 43500686443)⟩)
          (.row ⟨119068833410, 120689819475, (.direct 3393509060 756931182), (.chord (.midpoint ⟨574116626518, 66508765518, 120169978945, 494422759115, 162815247166, 329907385381⟩) 24716235638 43500686443)⟩))
        (.cut 1 (7/40)
          (.row ⟨117423580139, 119068833411, (.direct 3393509060 650709467), (.chord (.midpoint ⟨559307243644, 73349106615, 122890597553, 486631375267, 168805473117, 326693332596⟩) 24716235638 43500686443)⟩)
          (.row ⟨119068833410, 120689819475, (.direct 3393509060 592300407), (.chord (.midpoint ⟨561610550943, 72264642949, 121729719084, 489919514601, 167880018234, 327467814799⟩) 24716235638 43500686443)⟩))))

set_option maxRecDepth 16000 in
theorem CutTop2H5NegPart3_checked : CutTop2H5NegPart3Tree.commonOK CutTop2H5NegPart3Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
