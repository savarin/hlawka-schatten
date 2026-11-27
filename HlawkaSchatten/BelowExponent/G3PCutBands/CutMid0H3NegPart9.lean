/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid0H3NegPart9`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid0H3NegPart9Box : Box := (((((((⟨![27/68, 1/20, 0, -8], ![9/17, 7/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).upperChild 2 (5/16)

set_option maxRecDepth 16000 in
def CutMid0H3NegPart9Tree : CertTree :=
  .cut 3 (0)
    (.cut 1 (3/50)
      (.row ⟨65259754744, 71228276419, (.direct 0 406091407), (.chord .universal 43500686443 91625974997)⟩)
      (.cut 0 (63/136)
        (.row ⟨71228276418, 76698504229, (.direct 0 423032966), (.chord .universal 43500686443 91625974997)⟩)
        (.cut 3 (-1/8)
          (.row ⟨71228276418, 76698504229, (.direct 10180561190 7536695702), (.chord (.midpoint ⟨431940648158, 145715905402, 169689858074, 387053608058, 217476038267, 228273131071⟩) 43500686443 91625974997)⟩)
          (.cut 3 (-1/16)
            (.row ⟨71228276418, 76698504229, (.direct 3393509060 1814066740), (.chord (.midpoint ⟨496730420528, 105779608533, 140063973544, 443500715069, 193228698224, 294049958456⟩) 43500686443 91625974997)⟩)
            (.row ⟨71228276418, 76698504229, (.direct 0 522744254), (.chord (.secant 577953048697 64787681245 149410599753 13777161341) 43500686443 91625974997)⟩)))))
    (.cut 3 (1/8)
      (.cut 3 (1/16)
        (.cut 3 (1/32)
          (.row ⟨65259754744, 76698504229, (.direct 1131165907 2371415464), (.chord (.secant 674890110992 28163487755 94268338708 573687230) 43500686443 91625974997)⟩)
          (.row ⟨65259754744, 76698504229, (.direct 3393509060 5068496708), (.chord (.secant 735378478325 12108575021 76767412390 5241578903) 43500686443 91625974997)⟩))
        (.row ⟨65259754744, 76698504229, (.direct 10180561190 12433252883), (.chord (.secant 862000104112 2908531188 60629899633 12752606031) 43500686443 91625974997)⟩))
      (.row ⟨65259754744, 76698504229, (.direct 30541785600 33377116207), (.variance 633209548660)⟩))

set_option maxRecDepth 16000 in
theorem CutMid0H3NegPart9_checked : CutMid0H3NegPart9Tree.commonOK CutMid0H3NegPart9Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
