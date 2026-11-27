/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H1NegPart9`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H1NegPart9Box : Box := ((((((((((⟨![9/68, 11/100, 0, -8], ![9/34, 13/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 2 (5/16)).lowerChild 3 (0)).lowerChild 1 (3/25)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutMid3H1NegPart9Tree : CertTree :=
  .cut 2 (7/32)
    (.cut 3 (-3/16)
      (.row ⟨95281442640, 99345187400, (.direct 19358451269 16179639437), (.variance 577127672606)⟩)
      (.cut 2 (11/64)
        (.row ⟨95281442640, 99345187400, (.direct 10180561190 7838508693), (.chord (.midpoint ⟨391986761321, 173871274110, 219901786402, 322032249713, 232127691969, 138149362466⟩) 10180665226 16864782083)⟩)
        (.row ⟨95281442640, 99345187400, (.direct 10180561190 7838508693), (.chord (.midpoint ⟨459615364821, 127827059142, 193905369550, 352100233560, 207213025660, 222667602000⟩) 16864782083 24716235638)⟩)))
    (.cut 3 (-3/16)
      (.row ⟨95281442640, 99345187400, (.direct 19358451269 16179639437), (.chord (.midpoint ⟨432911017914, 145066929800, 204267804186, 339331515245, 217118061086, 211032909798⟩) 24716235638 43500686443)⟩)
      (.cut 0 (27/136)
        (.row ⟨95281442640, 99345187400, (.direct 10180561190 8402773542), (.chord (.midpoint ⟨530029364603, 87802432758, 165611881537, 393791811169, 180391215669, 272643562698⟩) 24716235638 43500686443)⟩)
        (.row ⟨95281442640, 99345187400, (.direct 10180561190 7838508693), (.chord (.midpoint ⟨502013818761, 102815578834, 169695363885, 387044697931, 191212446875, 265251130386⟩) 24716235638 43500686443)⟩)))

set_option maxRecDepth 16000 in
theorem CutMid3H1NegPart9_checked : CutMid3H1NegPart9Tree.commonOK CutMid3H1NegPart9Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
