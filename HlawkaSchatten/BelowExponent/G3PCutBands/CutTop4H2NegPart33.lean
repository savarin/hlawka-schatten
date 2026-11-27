/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H2NegPart33`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H2NegPart33Box : Box := (((((((((⟨![9/68, 19/100, 0, -8], ![27/136, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).upperChild 3 (0)).upperChild 2 (5/16)).upperChild 3 (1/8)

set_option maxRecDepth 16000 in
def CutTop4H2NegPart33Tree : CertTree :=
  .cut 3 (3/16)
    (.cut 2 (13/32)
      (.cut 3 (5/32)
        (.row ⟨123862991199, 126950446638, (.direct 14500097491 17331697519), (.chord (.secant 1120782229356 71402251425 12058184919 49170754692) 43500686443 65931360876)⟩)
        (.row ⟨123862991199, 126950446638, (.direct 19358451269 22372460883), (.chord (.secant 1193193779624 98992314001 24037681534 67798117692) 43500686443 65931360876)⟩))
      (.row ⟨123862991199, 126950446638, (.direct 19358451269 22372460883), (.chord (.secant 1081589395748 57659593303 4605881095 35381795001) 65931360876 91625974997)⟩))
    (.cut 2 (13/32)
      (.cut 3 (7/32)
        (.row ⟨123862991199, 126950446638, (.direct 24716051037 27872805152), (.chord (.secant 1267264907216 129772476224 38810328350 88544632768) 43500686443 65931360876)⟩)
        (.row ⟨123862991199, 126950446638, (.direct 30541785600 33806907894), (.chord (.secant 1342969635649 163522924721 56039665746 111266269109) 43500686443 65931360876)⟩))
      (.row ⟨123862991199, 126950446638, (.direct 30541785600 33806907894), (.chord (.secant 1192261925948 98620691816 21281985602 63714052483) 65931360876 91625974997)⟩))

set_option maxRecDepth 16000 in
theorem CutTop4H2NegPart33_checked : CutTop4H2NegPart33Tree.commonOK CutTop4H2NegPart33Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
