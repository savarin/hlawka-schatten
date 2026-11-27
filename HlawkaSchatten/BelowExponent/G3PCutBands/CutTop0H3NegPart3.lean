/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H3NegPart3`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H3NegPart3Box : Box := ((((((((((⟨![27/136, 3/20, 0, -8], ![9/34, 4/25, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 2 (5/16)).lowerChild 3 (0)).upperChild 3 (-1/8)).lowerChild 3 (-1/16)

set_option maxRecDepth 16000 in
def CutTop0H3NegPart3Tree : CertTree :=
  .cut 2 (7/32)
    (.cut 3 (-3/32)
      (.row ⟨110576703734, 114055813620, (.direct 6452795533 3930954924), (.chord (.midpoint ⟨516065232019, 95138752276, 163805751258, 396867577266, 185813765037, 255101022771⟩) 10180665226 24716235638)⟩)
      (.row ⟨110576703734, 114055813620, (.direct 3393509060 1545031550), (.chord (.midpoint ⟨594864485097, 57449023984, 128671254518, 471016599334, 154249396585, 294659228105⟩) 10180665226 24716235638)⟩))
    (.cut 3 (-3/32)
      (.cut 0 (63/272)
        (.row ⟨110576703734, 114055813620, (.direct 6452795533 4220692539), (.chord (.midpoint ⟨562981929572, 71622568729, 143397559920, 436160606213, 167327952039, 317542369115⟩) 24716235638 43500686443)⟩)
        (.row ⟨110576703734, 114055813620, (.direct 6452795533 3930954924), (.chord (.midpoint ⟨549972134965, 77822445699, 145042578394, 432645005688, 172534276100, 314733539408⟩) 24716235638 43500686443)⟩))
      (.cut 0 (63/272)
        (.cut 1 (31/200)
          (.row ⟨110576703734, 112330851340, (.direct 3393509060 1795457657), (.chord (.midpoint ⟨618244468302, 47965376867, 117268822773, 503070438358, 144312815739, 337501502125⟩) 24716235638 43500686443)⟩)
          (.row ⟨112330851339, 114055813620, (.direct 3393509060 1746386383), (.chord (.midpoint ⟨619608090534, 47435867955, 116584764209, 505162962247, 143722776990, 337905581996⟩) 24716235638 43500686443)⟩))
        (.cut 1 (31/200)
          (.row ⟨110576703734, 112330851340, (.direct 3393509060 1598698094), (.chord (.midpoint ⟨604413073503, 53483275597, 119343107625, 496850836685, 150230590263, 334758827800⟩) 24716235638 43500686443)⟩)
          (.row ⟨112330851339, 114055813620, (.direct 3393509060 1545031550), (.chord (.midpoint ⟨605958639288, 52853393782, 118570816442, 499144759881, 149575152222, 335232954658⟩) 24716235638 43500686443)⟩))))

set_option maxRecDepth 16000 in
theorem CutTop0H3NegPart3_checked : CutTop0H3NegPart3Tree.commonOK CutTop0H3NegPart3Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
