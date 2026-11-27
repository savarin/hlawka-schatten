/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H6NegPart40`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H6NegPart40Box : Box := ((((((((⟨![27/68, 19/100, 0, -8], ![63/136, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).upperChild 2 (1/2)).lowerChild 2 (3/4)).lowerChild 3 (0)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutTop4H6NegPart40Tree : CertTree :=
  .cut 0 (117/272)
    (.cut 3 (-3/16)
      (.row ⟨123862991199, 126950446638, (.direct 19358451269 10932112927), (.chord (.midpoint ⟨483810699142, 113208685095, 154350163267, 413967898852, 198130374343, 301928855811⟩) 91625974997 174227471798)⟩)
      (.cut 0 (225/544)
        (.row ⟨123862991199, 126950446638, (.direct 10180561190 4368867242), (.chord (.midpoint ⟨525562856839, 90117531769, 134924353742, 455422017178, 182132274733, 321969164638⟩) 91625974997 174227471798)⟩)
        (.row ⟨123862991199, 126950446638, (.direct 10180561190 4175123892), (.chord (.midpoint ⟨517953565338, 94129719178, 136387871881, 451949252607, 185083977951, 320180601655⟩) 91625974997 174227471798)⟩)))
    (.cut 3 (-3/16)
      (.row ⟨123862991199, 126950446638, (.direct 19358451269 10359208742), (.chord (.midpoint ⟨469256689352, 121890134383, 156931517532, 409124978612, 203607675858, 298241552261⟩) 91625974997 174227471798)⟩)
      (.cut 0 (243/544)
        (.row ⟨123862991199, 126950446638, (.direct 10180561190 3984643383), (.chord (.midpoint ⟨510385310161, 98206042777, 137840331297, 448565145914, 188002653153, 318384921574⟩) 91625974997 174227471798)⟩)
        (.row ⟨123862991199, 126950446638, (.direct 10180561190 3797465865), (.chord (.midpoint ⟨502858249787, 102345794402, 139282011807, 445265902581, 190889527388, 316582026903⟩) 91625974997 174227471798)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop4H6NegPart40_checked : CutTop4H6NegPart40Tree.commonOK CutTop4H6NegPart40Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
