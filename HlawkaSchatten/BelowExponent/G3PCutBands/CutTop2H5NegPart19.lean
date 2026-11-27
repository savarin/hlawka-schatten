/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H5NegPart19`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H5NegPart19Box : Box := (((((((((⟨![45/136, 17/100, 0, -8], ![27/68, 9/50, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).upperChild 3 (0)).upperChild 2 (5/16)).upperChild 3 (1/8)

set_option maxRecDepth 16000 in
def CutTop2H5NegPart19Tree : CertTree :=
  .cut 2 (13/32)
    (.cut 3 (3/16)
      (.cut 2 (23/64)
        (.cut 3 (5/32)
          (.row ⟨117423580139, 120689819475, (.direct 14500097491 19667763121), (.chord (.secant 1011550792569 35552032459 824983631 70203269408) 43500686443 54287507865)⟩)
          (.row ⟨117423580139, 120689819475, (.direct 19358451269 24833908738), (.chord (.secant 1080083977018 57150075770 8300383695 93652285667) 43500686443 54287507865)⟩))
        (.row ⟨117423580139, 120689819475, (.direct 19358451269 24833908738), (.chord (.secant 1014719979479 36476913905 703684761 57804938245) 54287507865 65931360876)⟩))
      (.cut 2 (23/64)
        (.row ⟨117423580139, 120689819475, (.direct 30541785600 36438291473), (.chord (.secant 1222055486813 110700451868 20462106142 119504666498) 43500686443 54287507865)⟩)
        (.row ⟨117423580139, 120689819475, (.direct 30541785600 36438291473), (.chord (.secant 1135100306092 76641330380 10304225436 98399403977) 54287507865 65931360876)⟩)))
    (.cut 3 (3/16)
      (.cut 2 (29/64)
        (.row ⟨117423580139, 120689819475, (.direct 19358451269 24833908738), (.chord (.secant 965471870811 23026957678 3337033832 48618149108) 65931360876 78389578142)⟩)
        (.row ⟨117423580139, 120689819475, (.direct 19358451269 24833908738), (.chord (.secant 927059645911 14072250741 6400349033 41594693591) 78389578142 91625974997)⟩))
      (.row ⟨117423580139, 120689819475, (.direct 30541785600 36438291473), (.chord (.secant 1069836906660 53719676008 944567206 70805249209) 65931360876 91625974997)⟩))

set_option maxRecDepth 16000 in
theorem CutTop2H5NegPart19_checked : CutTop2H5NegPart19Tree.commonOK CutTop2H5NegPart19Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
