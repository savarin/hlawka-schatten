/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H7NegPart42`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H7NegPart42Box : Box := ((((((((⟨![63/136, 19/100, 0, -8], ![9/17, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).upperChild 2 (1/2)).lowerChild 2 (3/4)).upperChild 3 (0)).upperChild 3 (1/8)

set_option maxRecDepth 16000 in
def CutTop4H7NegPart42Tree : CertTree :=
  .cut 3 (3/16)
    (.cut 2 (5/8)
      (.cut 3 (5/32)
        (.cut 2 (9/16)
          (.cut 0 (135/272)
            (.row ⟨123862991199, 126950446638, (.direct 14500097491 21918045456), (.chord (.secant 787264656910 2987729595 21182441184 40315845223) 91625974997 110431617683)⟩)
            (.row ⟨123862991199, 126950446638, (.direct 14500097491 22451840534), (.chord (.secant 770063766690 5479258658 26053528725 41481055755) 91625974997 110431617683)⟩))
          (.cut 0 (135/272)
            (.row ⟨123862991199, 126950446638, (.direct 14500097491 21918045456), (.chord (.secant 758512808412 7460342301 26438240874 34115492248) 110431617683 130502050762)⟩)
            (.row ⟨123862991199, 126950446638, (.direct 14500097491 22451840534), (.chord (.secant 741115010818 10874540117 31804515026 35101499874) 110431617683 130502050762)⟩)))
        (.cut 2 (9/16)
          (.row ⟨123862991199, 126950446638, (.direct 19358451269 27743867696), (.chord (.secant 829446867568 114169576 17937454074 52229215505) 91625974997 110431617683)⟩)
          (.row ⟨123862991199, 126950446638, (.direct 19358451269 27743867696), (.chord (.secant 795464770194 2011523840 23829555575 44196652378) 110431617683 130502050762)⟩)))
      (.cut 3 (5/32)
        (.cut 0 (135/272)
          (.row ⟨123862991199, 126950446638, (.direct 14500097491 21918045456), (.chord (.secant 735796788382 12016819155 35098687690 25553591900) 130502050762 174227471798)⟩)
          (.row ⟨123862991199, 126950446638, (.direct 14500097491 22451840534), (.chord (.secant 718252053178 16099302401 41198608025 26292143063) 130502050762 174227471798)⟩))
        (.row ⟨123862991199, 126950446638, (.direct 19358451269 27743867696), (.chord (.secant 768658644166 5707531824 33772546840 33104702403) 130502050762 174227471798)⟩)))
    (.cut 2 (5/8)
      (.cut 2 (9/16)
        (.row ⟨123862991199, 126950446638, (.direct 30541785600 39515340825), (.chord (.secant 907805998772 10180561190 10289255163 65243595528) 91625974997 110431617683)⟩)
        (.row ⟨123862991199, 126950446638, (.direct 30541785600 39515340825), (.chord (.secant 863950765509 3150743407 15990276559 55209493069) 110431617683 130502050762)⟩))
      (.row ⟨123862991199, 126950446638, (.direct 30541785600 39515340825), (.chord (.secant 829446867568 114169576 26160963985 41353671366) 130502050762 174227471798)⟩))

set_option maxRecDepth 16000 in
theorem CutTop4H7NegPart42_checked : CutTop4H7NegPart42Tree.commonOK CutTop4H7NegPart42Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
