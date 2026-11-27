/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H3NegPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H3NegPart1Box : Box := ((((((⟨![27/136, 19/100, 0, -8], ![9/34, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutTop4H3NegPart1Tree : CertTree :=
  .cut 3 (0)
    (.row ⟨123862991199, 126950446638, (.direct 0 1027550858), (.chord .universal 0 10180665226)⟩)
    (.cut 3 (1/8)
      (.cut 3 (1/16)
        (.cut 1 (39/200)
          (.cut 0 (63/272)
            (.cut 1 (77/400)
              (.row ⟨123862991199, 124642625207, (.direct 3393509060 5589303785), (.chord .universal 0 10180665226)⟩)
              (.row ⟨124642625206, 125417011706, (.direct 3393509060 5623772331), (.chord .universal 0 10180665226)⟩))
            (.cut 3 (1/32)
              (.row ⟨123862991199, 125417011706, (.direct 1131165907 3093444491), (.chord .universal 0 10180665226)⟩)
              (.row ⟨123862991199, 125417011706, (.direct 3393509060 5975218027), (.variance 917447628162)⟩)))
          (.cut 0 (63/272)
            (.row ⟨125417011705, 126950446638, (.direct 3393509060 5693232604), (.chord .universal 0 10180665226)⟩)
            (.cut 3 (1/32)
              (.row ⟨125417011705, 126950446638, (.direct 1131165907 3159342508), (.chord .universal 0 10180665226)⟩)
              (.row ⟨125417011705, 126950446638, (.direct 3393509060 6056415565), (.variance 912717666271)⟩))))
        (.cut 3 (3/32)
          (.row ⟨123862991199, 126950446638, (.direct 6452795533 9593842888), (.variance 776006384629)⟩)
          (.row ⟨123862991199, 126950446638, (.direct 10180561190 13697503795), (.variance 680344517847)⟩)))
      (.cut 3 (3/16)
        (.row ⟨123862991199, 126950446638, (.direct 19358451269 23412458922), (.variance 615759399401)⟩)
        (.row ⟨123862991199, 126950446638, (.direct 30541785600 34922204517), (.variance 531235947379)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop4H3NegPart1_checked : CutTop4H3NegPart1Tree.commonOK CutTop4H3NegPart1Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
