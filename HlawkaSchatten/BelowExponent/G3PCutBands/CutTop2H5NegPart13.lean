/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H5NegPart13`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H5NegPart13Box : Box := ((((((((((⟨![45/136, 17/100, 0, -8], ![27/68, 9/50, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).upperChild 3 (0)).lowerChild 2 (5/16)).lowerChild 3 (1/8)).upperChild 3 (1/16)

set_option maxRecDepth 16000 in
def CutTop2H5NegPart13Tree : CertTree :=
  .cut 2 (7/32)
    (.cut 2 (11/64)
      (.cut 3 (3/32)
        (.row ⟨117423580139, 120689819475, (.direct 6452795533 10746309384), (.chord (.secant 1329875486134 157533649202 11398664162 100880674743) 10180665226 16864782083)⟩)
        (.row ⟨117423580139, 120689819475, (.direct 10180561190 14960453493), (.chord (.secant 1521920582254 250884923280 43053055861 158849749388) 10180665226 16864782083)⟩))
      (.cut 3 (3/32)
        (.cut 3 (5/64)
          (.row ⟨117423580139, 120689819475, (.direct 4833349683 8837691056), (.chord (.secant 1053545717997 48405243913 574881707 68834453779) 16864782083 24716235638)⟩)
          (.row ⟨117423580139, 120689819475, (.direct 6452795533 10746309384), (.chord (.secant 1116704025475 69930763017 6008313734 87787254372) 16864782083 24716235638)⟩))
        (.row ⟨117423580139, 120689819475, (.direct 10180561190 14960453493), (.chord (.secant 1247041529988 121134611347 14885184611 108388804495) 16864782083 24716235638)⟩)))
    (.cut 3 (3/32)
      (.cut 2 (17/64)
        (.cut 3 (5/64)
          (.row ⟨117423580139, 120689819475, (.direct 4833349683 8837691056), (.chord (.secant 953418546238 20059118871 2634966195 50601107496) 24716235638 33622326476)⟩)
          (.row ⟨117423580139, 120689819475, (.direct 6452795533 10746309384), (.chord (.secant 1001163537565 32575394683 39051024 64533559162) 24716235638 33622326476)⟩))
        (.cut 3 (5/64)
          (.cut 0 (99/272)
            (.row ⟨117423580139, 120689819475, (.direct 4833349683 8470932800), (.chord (.secant 882992604327 5854361481 4224081251 39110316103) 33622326476 43500686443)⟩)
            (.row ⟨117423580139, 120689819475, (.direct 4833349683 8837691056), (.chord (.secant 868472710186 3738374114 6658548486 41084454356) 33622326476 43500686443)⟩))
          (.row ⟨117423580139, 120689819475, (.direct 6452795533 10746309384), (.chord (.secant 928911030343 14468825031 2882383038 49878906272) 33622326476 43500686443)⟩)))
      (.cut 2 (17/64)
        (.row ⟨117423580139, 120689819475, (.direct 10180561190 14960453493), (.chord (.secant 1099209710115 63726157315 3244374715 79678028176) 24716235638 33622326476)⟩)
        (.row ⟨117423580139, 120689819475, (.direct 10180561190 14960453493), (.chord (.secant 1007268895762 34314734352 128426009 61584281899) 33622326476 43500686443)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop2H5NegPart13_checked : CutTop2H5NegPart13Tree.commonOK CutTop2H5NegPart13Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
