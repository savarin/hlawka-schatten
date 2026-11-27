/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H3NegPart4`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H3NegPart4Box : Box := (((((((((((⟨![27/68, 11/100, 0, -8], ![9/17, 13/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)).upperChild 3 (0)).lowerChild 3 (1/8)).lowerChild 3 (1/16)).lowerChild 1 (3/25)).upperChild 3 (1/32)

set_option maxRecDepth 16000 in
def CutMid3H3NegPart4Tree : CertTree :=
  .cut 0 (63/136)
    (.cut 1 (23/200)
      (.cut 3 (3/64)
        (.cut 2 (1/16)
          (.row ⟨95281442640, 97336292160, (.direct 2150924658 4417302477), (.variance 925677212152)⟩)
          (.row ⟨95281442640, 97336292160, (.direct 2150924658 4417302477), (.chord (.secant 1392857717085 186881272523 1301339285 71903775789) 3393555298 10180665226)⟩))
        (.row ⟨95281442640, 97336292160, (.direct 3393509060 5941850047), (.variance 834295543089)⟩))
      (.cut 3 (3/64)
        (.cut 2 (1/16)
          (.row ⟨97336292159, 99345187400, (.direct 2150924658 4536062258), (.variance 918052110872)⟩)
          (.row ⟨97336292159, 99345187400, (.direct 2150924658 4536062258), (.chord (.secant 1408698622200 194469187799 819595603 74211280879) 3393555298 10180665226)⟩))
        (.row ⟨97336292159, 99345187400, (.direct 3393509060 6072053475), (.variance 829014633034)⟩)))
    (.cut 1 (23/200)
      (.cut 3 (3/64)
        (.cut 0 (135/272)
          (.row ⟨95281442640, 97336292160, (.direct 2150924658 4601189026), (.variance 900197403728)⟩)
          (.row ⟨95281442640, 97336292160, (.direct 2150924658 4787828875), (.variance 888320011952)⟩))
        (.row ⟨95281442640, 97336292160, (.direct 3393509060 6347335992), (.variance 816513738356)⟩))
      (.cut 3 (3/64)
        (.row ⟨97336292159, 99345187400, (.direct 2150924658 4927708675), (.variance 892119234276)⟩)
        (.row ⟨97336292159, 99345187400, (.direct 3393509060 6499868527), (.variance 810795622415)⟩)))

set_option maxRecDepth 16000 in
theorem CutMid3H3NegPart4_checked : CutMid3H3NegPart4Tree.commonOK CutMid3H3NegPart4Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
