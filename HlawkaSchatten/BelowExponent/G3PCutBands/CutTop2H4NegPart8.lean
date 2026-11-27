/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H4NegPart8`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H4NegPart8Box : Box := (((((((((⟨![9/34, 17/100, 0, -8], ![45/136, 9/50, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 3 (0)).upperChild 2 (5/16)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutTop2H4NegPart8Tree : CertTree :=
  .cut 2 (13/32)
    (.cut 3 (-3/16)
      (.row ⟨117423580139, 120689819475, (.direct 19358451269 13396882232), (.chord (.midpoint ⟨452420317112, 132355816370, 182873228604, 367042265515, 209892784751, 269612750154⟩) 43500686443 65931360876)⟩)
      (.cut 0 (81/272)
        (.row ⟨117423580139, 120689819475, (.direct 10180561190 6248582883), (.chord (.midpoint ⟨527752350272, 88978982268, 150842041081, 420775960631, 181279606169, 305165181340⟩) 43500686443 65931360876)⟩)
        (.row ⟨117423580139, 120689819475, (.direct 10180561190 5856369868), (.chord (.midpoint ⟨514497791023, 95980369249, 152675726492, 417184045173, 186418741333, 301957006520⟩) 43500686443 65931360876)⟩)))
    (.cut 3 (-3/16)
      (.row ⟨117423580139, 120689819475, (.direct 19358451269 13396882232), (.chord (.midpoint ⟨488865902266, 110271064483, 167693072409, 390317975247, 196217133990, 295156732461⟩) 65931360876 91625974997)⟩)
      (.cut 0 (81/272)
        (.row ⟨117423580139, 120689819475, (.direct 10180561190 6248582883), (.chord (.midpoint ⟨551445317009, 77108155663, 140134274830, 443342843342, 171948113155, 322279340686⟩) 65931360876 91625974997)⟩)
        (.row ⟨117423580139, 120689819475, (.direct 10180561190 5856369868), (.chord (.midpoint ⟨537024285004, 84235816918, 142501126424, 438105562195, 177651339016, 318804060551⟩) 65931360876 91625974997)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop2H4NegPart8_checked : CutTop2H4NegPart8Tree.commonOK CutTop2H4NegPart8Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
