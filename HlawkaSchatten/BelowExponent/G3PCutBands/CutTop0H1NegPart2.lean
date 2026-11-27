/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H1NegPart2`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H1NegPart2Box : Box := (((((((((⟨![9/136, 3/20, 0, -8], ![9/68, 4/25, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 2 (5/16)).lowerChild 3 (0)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutTop0H1NegPart2Tree : CertTree :=
  .cut 1 (31/200)
    (.cut 2 (7/32)
      (.row ⟨110576703734, 112330851340, (.direct 10180561190 8613851627), (.chord .universal 10180665226 24716235638)⟩)
      (.cut 3 (-3/16)
        (.row ⟨110576703734, 112330851340, (.direct 19358451269 17242858988), (.chord (.midpoint ⟨455914663871, 130145817930, 202048892182, 341971353105, 208592434832, 233289097843⟩) 24716235638 43500686443)⟩)
        (.row ⟨110576703734, 112330851340, (.direct 10180561190 8613851627), (.chord (.midpoint ⟨564054752136, 71122153814, 159189057535, 404999856192, 166895517915, 281199022170⟩) 24716235638 43500686443)⟩)))
    (.cut 2 (7/32)
      (.row ⟨112330851339, 114055813620, (.direct 10180561190 8560680660), (.chord .universal 10180665226 24716235638)⟩)
      (.cut 3 (-3/16)
        (.row ⟨112330851339, 114055813620, (.direct 19358451269 17170322595), (.chord (.midpoint ⟨456692881660, 129656354732, 201752377040, 342327873816, 208302556550, 233489169331⟩) 24716235638 43500686443)⟩)
        (.row ⟨112330851339, 114055813620, (.direct 10180561190 8560680660), (.chord (.midpoint ⟨564852219237, 70751244158, 158856300714, 405601590591, 166573755628, 281365513625⟩) 24716235638 43500686443)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop0H1NegPart2_checked : CutTop0H1NegPart2Tree.commonOK CutTop0H1NegPart2Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
