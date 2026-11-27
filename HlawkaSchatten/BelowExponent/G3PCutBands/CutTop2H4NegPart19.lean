/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H4NegPart19`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H4NegPart19Box : Box := (((((((((⟨![9/34, 17/100, 0, -8], ![45/136, 9/50, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).upperChild 3 (0)).upperChild 2 (5/16)).upperChild 3 (1/8)

set_option maxRecDepth 16000 in
def CutTop2H4NegPart19Tree : CertTree :=
  .cut 3 (3/16)
    (.cut 2 (13/32)
      (.cut 3 (5/32)
        (.row ⟨117423580139, 120689819475, (.direct 14500097491 18766576223), (.chord (.secant 1045944476670 45986144101 1047646878 54594195414) 43500686443 65931360876)⟩)
        (.row ⟨117423580139, 120689819475, (.direct 19358451269 23886706938), (.chord (.secant 1115789319379 69602004942 7699837320 73662047616) 43500686443 65931360876)⟩))
      (.row ⟨117423580139, 120689819475, (.direct 19358451269 23886706938), (.chord (.secant 1002500924333 32953871978 1532568256 39284339695) 65931360876 91625974997)⟩))
    (.cut 2 (13/32)
      (.row ⟨117423580139, 120689819475, (.direct 30541785600 35429054793), (.chord (.secant 1260409387890 126825514669 18119615732 94758370029) 43500686443 65931360876)⟩)
      (.row ⟨117423580139, 120689819475, (.direct 30541785600 35429054793), (.chord (.secant 1109012899850 67181269086 5429888088 68185270778) 65931360876 91625974997)⟩))

set_option maxRecDepth 16000 in
theorem CutTop2H4NegPart19_checked : CutTop2H4NegPart19Tree.commonOK CutTop2H4NegPart19Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
