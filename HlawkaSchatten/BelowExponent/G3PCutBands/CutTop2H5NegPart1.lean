/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H5NegPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H5NegPart1Box : Box := ((((((⟨![45/136, 17/100, 0, -8], ![27/68, 9/50, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutTop2H5NegPart1Tree : CertTree :=
  .cut 3 (0)
    (.row ⟨117423580139, 120689819475, (.direct 0 1624693341), (.chord .universal 0 10180665226)⟩)
    (.cut 3 (1/8)
      (.cut 3 (1/16)
        (.cut 3 (1/32)
          (.cut 1 (7/40)
            (.row ⟨117423580139, 119068833411, (.direct 1131165907 3891066533), (.chord .universal 0 10180665226)⟩)
            (.row ⟨119068833410, 120689819475, (.direct 1131165907 3996408794), (.chord .universal 0 10180665226)⟩))
          (.cut 3 (3/64)
            (.row ⟨117423580139, 120689819475, (.direct 2150924658 5453155715), (.variance 877391465451)⟩)
            (.row ⟨117423580139, 120689819475, (.direct 3393509060 7070457360), (.variance 800271028710)⟩)))
        (.cut 3 (3/32)
          (.row ⟨117423580139, 120689819475, (.direct 6452795533 10746309384), (.variance 742250974332)⟩)
          (.row ⟨117423580139, 120689819475, (.direct 10180561190 14960453493), (.variance 659049207574)⟩)))
      (.cut 3 (3/16)
        (.row ⟨117423580139, 120689819475, (.direct 19358451269 24833908738), (.variance 600937737014)⟩)
        (.row ⟨117423580139, 120689819475, (.direct 30541785600 36438291473), (.variance 522796766966)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop2H5NegPart1_checked : CutTop2H5NegPart1Tree.commonOK CutTop2H5NegPart1Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
