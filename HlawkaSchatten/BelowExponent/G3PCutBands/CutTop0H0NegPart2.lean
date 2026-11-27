/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H0NegPart2`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H0NegPart2Box : Box := (((((((((⟨![0, 3/20, 0, -8], ![9/136, 4/25, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 2 (5/16)).lowerChild 3 (0)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutTop0H0NegPart2Tree : CertTree :=
  .cut 1 (31/200)
    (.cut 3 (-3/16)
      (.cut 2 (7/32)
        (.row ⟨110576703734, 112330851340, (.direct 19358451269 18289441398), (.variance 558898177718)⟩)
        (.row ⟨110576703734, 112330851340, (.direct 19358451269 18289441398), (.chord (.midpoint ⟨479797099599, 115569437534, 199645862477, 344886712054, 199645326133, 239643475624⟩) 24716235638 43500686443)⟩))
      (.cut 2 (7/32)
        (.row ⟨110576703734, 112330851340, (.direct 10180561190 9385186757), (.chord (.midpoint ⟨499223536990, 104375633265, 192278740285, 354211052992, 192278162998, 168647478831⟩) 10180665226 24716235638)⟩)
        (.row ⟨110576703734, 112330851340, (.direct 10180561190 9385186757), (.chord (.midpoint ⟨590500653428, 59304080826, 156070005247, 410726047411, 156069263114, 287018225720⟩) 24716235638 43500686443)⟩)))
    (.cut 3 (-3/16)
      (.cut 2 (7/32)
        (.row ⟨112330851339, 114055813620, (.direct 19358451269 18252360866), (.variance 559195277756)⟩)
        (.row ⟨112330851339, 114055813620, (.direct 19358451269 18252360866), (.chord (.midpoint ⟨480193545993, 115335128055, 199496379133, 345070047516, 199495841935, 239643475624⟩) 24716235638 43500686443)⟩))
      (.cut 2 (7/32)
        (.row ⟨112330851339, 114055813620, (.direct 10180561190 9357729833), (.chord (.midpoint ⟨499768025059, 104070275175, 192070937918, 354482911046, 192070359511, 168647478831⟩) 10180665226 24716235638)⟩)
        (.cut 0 (9/272)
          (.row ⟨112330851339, 114055813620, (.direct 10180561190 9765998091), (.chord (.midpoint ⟨584931697942, 61710398158, 158377928718, 406470430775, 158377195142, 292145484615⟩) 24716235638 43500686443)⟩)
          (.row ⟨112330851339, 114055813620, (.direct 10180561190 9357729833), (.chord (.midpoint ⟨571899859478, 67512772836, 159843978060, 403821801373, 163718081582, 289364551619⟩) 24716235638 43500686443)⟩))))

set_option maxRecDepth 16000 in
theorem CutTop0H0NegPart2_checked : CutTop0H0NegPart2Tree.commonOK CutTop0H0NegPart2Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
