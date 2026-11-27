/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid4H2NegPart7`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid4H2NegPart7Box : Box := (((((((((⟨![9/34, 13/100, 0, -8], ![27/68, 3/20, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 2 (5/16)).lowerChild 3 (0)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutMid4H2NegPart7Tree : CertTree :=
  .cut 2 (7/32)
    (.cut 3 (-3/16)
      (.row ⟨103236350715, 110576703735, (.direct 19358451269 13487015310), (.variance 605302797853)⟩)
      (.cut 2 (11/64)
        (.row ⟨103236350715, 110576703735, (.direct 10180561190 5919333362), (.chord (.midpoint ⟨376105048583, 185874372916, 213437886041, 328921818256, 237917821886, 129928692689⟩) 10180665226 16864782083)⟩)
        (.row ⟨103236350715, 110576703735, (.direct 10180561190 5919333362), (.chord (.midpoint ⟨431666046087, 145899848891, 191318932924, 355470940674, 217577319109, 211559762298⟩) 16864782083 24716235638)⟩)))
    (.cut 3 (-3/16)
      (.cut 1 (7/50)
        (.row ⟨103236350715, 106974752992, (.direct 19358451269 13881578910), (.chord (.midpoint ⟨390941522338, 174646606191, 207586295855, 335473713325, 232509186467, 196880838380⟩) 24716235638 43500686443)⟩)
        (.row ⟨106974752991, 110576703735, (.direct 19358451269 13487015310), (.chord (.midpoint ⟨395301575813, 171425862096, 205860242513, 337467012094, 230917372863, 198647386206⟩) 24716235638 43500686443)⟩))
      (.cut 0 (45/136)
        (.cut 1 (7/50)
          (.row ⟨103236350715, 106974752992, (.direct 10180561190 6808971372), (.chord (.midpoint ⟨481846216534, 114361017298, 170656978401, 385496046367, 198872318482, 260436773722⟩) 24716235638 43500686443)⟩)
          (.row ⟨106974752991, 110576703735, (.direct 10180561190 6569788516), (.chord (.midpoint ⟨485562134429, 112186406835, 169090635027, 388026302197, 197468168181, 261814652368⟩) 24716235638 43500686443)⟩))
        (.cut 1 (7/50)
          (.row ⟨103236350715, 106974752992, (.direct 10180561190 6196030444), (.chord (.midpoint ⟨456246449772, 129937018941, 174050891423, 380147416586, 208468860589, 253487115584⟩) 24716235638 43500686443)⟩)
          (.row ⟨106974752991, 110576703735, (.direct 10180561190 5919333362), (.chord (.midpoint ⟨460618105633, 127202603071, 172196381812, 383047696068, 206838847881, 255241822123⟩) 24716235638 43500686443)⟩))))

set_option maxRecDepth 16000 in
theorem CutMid4H2NegPart7_checked : CutMid4H2NegPart7Tree.commonOK CutMid4H2NegPart7Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
