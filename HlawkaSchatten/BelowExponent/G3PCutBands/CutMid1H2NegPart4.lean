/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid1H2NegPart4`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid1H2NegPart4Box : Box := (((((((((⟨![9/34, 7/100, 0, -8], ![27/68, 9/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)).upperChild 3 (0)).lowerChild 3 (1/8)).upperChild 3 (1/16)

set_option maxRecDepth 16000 in
def CutMid1H2NegPart4Tree : CertTree :=
  .cut 1 (2/25)
    (.cut 0 (45/136)
      (.cut 1 (3/40)
        (.cut 3 (3/32)
          (.cut 0 (81/272)
            (.cut 1 (29/400)
              (.row ⟨76698504228, 78001342659, (.direct 6452795533 7594844848), (.variance 821569239306)⟩)
              (.row ⟨78001342658, 79281022314, (.direct 6452795533 7637021434), (.variance 819983819816)⟩))
            (.row ⟨76698504228, 79281022314, (.direct 6452795533 7773095963), (.variance 816262765879)⟩))
          (.row ⟨76698504228, 79281022314, (.direct 10180561190 11674752931), (.variance 707641677252)⟩))
        (.cut 3 (3/32)
          (.cut 0 (81/272)
            (.cut 1 (31/400)
              (.row ⟨79281022313, 80538706897, (.direct 6452795533 7679394191), (.variance 818404705446)⟩)
              (.cut 3 (5/64)
                (.row ⟨80538706896, 81775466253, (.direct 4833349683 6002173425), (.variance 816831844645)⟩)
                (.row ⟨80538706896, 81775466253, (.direct 6452795533 7721964097), (.variance 753870367841)⟩)))
            (.cut 1 (31/400)
              (.row ⟨79281022313, 80538706897, (.direct 6452795533 7820489463), (.variance 812782908334)⟩)
              (.row ⟨80538706896, 81775466253, (.direct 6452795533 7868113039), (.variance 811055141222)⟩)))
          (.row ⟨79281022313, 81775466253, (.direct 10180561190 11781292986), (.variance 705798875733)⟩)))
      (.cut 1 (3/40)
        (.cut 3 (3/32)
          (.cut 0 (99/272)
            (.row ⟨76698504228, 79281022314, (.direct 6452795533 7910055395), (.variance 811071358381)⟩)
            (.row ⟨76698504228, 79281022314, (.direct 6452795533 8047895690), (.variance 805990822666)⟩))
          (.row ⟨76698504228, 79281022314, (.direct 10180561190 11982553487), (.variance 701498170943)⟩))
        (.cut 3 (3/32)
          (.cut 0 (99/272)
            (.row ⟨79281022313, 81775466253, (.direct 6452795533 8015270839), (.variance 807290631950)⟩)
            (.row ⟨79281022313, 81775466253, (.direct 6452795533 8163432615), (.variance 801922864989)⟩))
          (.row ⟨79281022313, 81775466253, (.direct 10180561190 12111674393), (.variance 699264359619)⟩))))
    (.cut 0 (45/136)
      (.cut 3 (3/32)
        (.cut 1 (17/200)
          (.cut 3 (5/64)
            (.cut 2 (1/16)
              (.row ⟨81775466252, 84190079492, (.direct 4833349683 6226817115), (.variance 815265186436)⟩)
              (.row ⟨81775466252, 84190079492, (.direct 4833349683 6226817115), (.chord (.secant 1738599324231 367909624189 30898698907 116789063112) 3393555298 10180665226)⟩))
            (.row ⟨81775466252, 84190079492, (.direct 6452795533 7964055012), (.variance 752697704339)⟩))
          (.cut 3 (5/64)
            (.cut 2 (1/16)
              (.row ⟨84190079491, 86531900009, (.direct 4833349683 6316845835), (.variance 812150276714)⟩)
              (.row ⟨84190079491, 86531900009, (.direct 4833349683 6316845835), (.chord (.secant 1750096764781 374404229779 31955271383 118508914383) 3393555298 10180665226)⟩))
            (.row ⟨84190079491, 86531900009, (.direct 6452795533 8060931150), (.variance 750361844819)⟩)))
        (.row ⟨81775466252, 86531900009, (.direct 10180561190 11997130018), (.variance 703962862664)⟩))
      (.cut 1 (17/200)
        (.cut 3 (3/32)
          (.cut 3 (5/64)
            (.row ⟨81775466252, 84190079492, (.direct 4833349683 6520874385), (.variance 803550095298)⟩)
            (.row ⟨81775466252, 84190079492, (.direct 6452795533 8280184302), (.variance 743882872785)⟩))
          (.row ⟨81775466252, 84190079492, (.direct 10180561190 12241983611), (.variance 697043168820)⟩))
        (.cut 3 (3/32)
          (.cut 3 (5/64)
            (.cut 2 (1/16)
              (.row ⟨84190079491, 86531900009, (.direct 4833349683 6630812594), (.variance 799848920185)⟩)
              (.row ⟨84190079491, 86531900009, (.direct 4833349683 6630812594), (.chord (.secant 1732717440975 364597256419 23710557429 125621515988) 3393555298 10180665226)⟩))
            (.row ⟨84190079491, 86531900009, (.direct 6452795533 8398162813), (.variance 741081176248)⟩))
          (.row ⟨84190079491, 86531900009, (.direct 10180561190 12373493068), (.variance 694834438329)⟩))))

set_option maxRecDepth 16000 in
theorem CutMid1H2NegPart4_checked : CutMid1H2NegPart4Tree.commonOK CutMid1H2NegPart4Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
