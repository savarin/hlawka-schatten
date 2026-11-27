/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H2NegPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H2NegPart1Box : Box := ((((((⟨![9/68, 19/100, 0, -8], ![27/136, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutTop4H2NegPart1Tree : CertTree :=
  .cut 3 (0)
    (.row ⟨123862991199, 126950446638, (.direct 0 651298572), (.chord .universal 0 10180665226)⟩)
    (.cut 3 (1/8)
      (.cut 3 (1/16)
        (.cut 1 (39/200)
          (.cut 0 (45/272)
            (.row ⟨123862991199, 125417011706, (.direct 3393509060 4944789777), (.chord .universal 0 10180665226)⟩)
            (.cut 3 (1/32)
              (.row ⟨123862991199, 125417011706, (.direct 1131165907 2537568469), (.chord .universal 0 10180665226)⟩)
              (.row ⟨123862991199, 125417011706, (.direct 3393509060 5280252266), (.chord .universal 0 10180665226)⟩)))
          (.cut 0 (45/272)
            (.row ⟨125417011705, 126950446638, (.direct 3393509060 4992079111), (.chord .universal 0 10180665226)⟩)
            (.row ⟨125417011705, 126950446638, (.direct 3393509060 5338406430), (.chord .universal 0 10180665226)⟩)))
        (.cut 3 (3/32)
          (.cut 3 (5/64)
            (.row ⟨123862991199, 126950446638, (.direct 4833349683 6974255551), (.variance 803108463218)⟩)
            (.row ⟨123862991199, 126950446638, (.direct 6452795533 8766024539), (.variance 743548991703)⟩))
          (.row ⟨123862991199, 126950446638, (.direct 10180561190 12782493823), (.variance 696780189186)⟩)))
      (.cut 3 (3/16)
        (.cut 3 (5/32)
          (.row ⟨123862991199, 126950446638, (.direct 14500097491 17331697519), (.variance 626941716170)⟩)
          (.row ⟨123862991199, 126950446638, (.direct 19358451269 22372460883), (.variance 576361617693)⟩))
        (.cut 3 (7/32)
          (.row ⟨123862991199, 126950446638, (.direct 24716051037 27872805152), (.variance 537444892522)⟩)
          (.row ⟨123862991199, 126950446638, (.direct 30541785600 33806907894), (.variance 506240881315)⟩))))

set_option maxRecDepth 16000 in
theorem CutTop4H2NegPart1_checked : CutTop4H2NegPart1Tree.commonOK CutTop4H2NegPart1Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
