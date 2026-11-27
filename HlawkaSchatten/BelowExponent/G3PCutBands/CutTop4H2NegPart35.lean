/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H2NegPart35`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H2NegPart35Box : Box := ((((((⟨![9/68, 19/100, 0, -8], ![27/136, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).upperChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutTop4H2NegPart35Tree : CertTree :=
  .cut 3 (1/2)
    (.cut 3 (3/8)
      (.cut 3 (5/16)
        (.cut 3 (9/32)
          (.row ⟨123862991199, 126950446638, (.direct 36810312175 40153316976), (.variance 480459646619)⟩)
          (.row ⟨123862991199, 126950446638, (.direct 43500437793 46893820279), (.variance 458667902995)⟩))
        (.cut 3 (11/32)
          (.row ⟨123862991199, 126950446638, (.direct 50594077426 54012689549), (.variance 439915438937)⟩)
          (.row ⟨123862991199, 126950446638, (.direct 58075547817 61496152177), (.variance 423543459819)⟩)))
      (.cut 3 (7/16)
        (.cut 3 (13/32)
          (.row ⟨123862991199, 126950446638, (.direct 65931069018 69332009174), (.variance 409078530490)⟩)
          (.row ⟨123862991199, 126950446638, (.direct 74148400816 77509350901), (.variance 396170265494)⟩))
        (.cut 3 (15/32)
          (.row ⟨123862991199, 126950446638, (.direct 82716570280 86018340422), (.variance 384552897431)⟩)
          (.row ⟨123862991199, 126950446638, (.direct 91625662891 94850045034), (.variance 374020597484)⟩))))
    (.cut 3 (5/8)
      (.cut 3 (9/16)
        (.cut 3 (17/32)
          (.row ⟨123862991199, 126950446638, (.direct 100866659274 103996302957), (.variance 364411078691)⟩)
          (.row ⟨123862991199, 126950446638, (.direct 110431305439 113449616231), (.variance 355594380508)⟩))
        (.cut 3 (19/32)
          (.row ⟨123862991199, 126950446638, (.direct 120312008131 123203063525), (.variance 347465001721)⟩)
          (.row ⟨123862991199, 126950446638, (.direct 130501749339 133250228310), (.variance 339936259189)⟩)))
      (.cut 3 (11/16)
        (.row ⟨123862991199, 126950446638, (.direct 151782739331 154202219096), (.variance 332936163328)⟩)
        (.row ⟨123862991199, 126950446638, (.direct 174227225485 176262304627), (.variance 320289762919)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop4H2NegPart35_checked : CutTop4H2NegPart35Tree.commonOK CutTop4H2NegPart35Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
