/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H3NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid1H3NegRestPart6`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid1H3NegRestPart6Box : Box := ((((((((((⟨![27/68, 7/100, 0, -8], ![9/17, 9/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)).upperChild 3 (0)).lowerChild 3 (1/8)).lowerChild 3 (1/16)).lowerChild 1 (2/25)

set_option maxRecDepth 16000 in
def CutMid1H3NegRestPart6Tree : RatioRemainder :=
  .cut 3 (1/32)
    (.cut 1 (3/40)
      (.cut 1 (29/400)
        (.cut 0 (63/136)
          (.cut 2 (1/16)
            (.original (.row ⟨76698504228, 78001342659, (.direct 1131165907 2242900007), (.chord .universal 0 3393555298)⟩))
            (.covered))
          (.cut 2 (1/16)
            (.original (.row ⟨76698504228, 78001342659, (.direct 1131165907 2423597649), (.chord .universal 0 3393555298)⟩))
            (.covered)))
        (.cut 0 (63/136)
          (.cut 2 (1/16)
            (.original (.row ⟨78001342658, 79281022314, (.direct 1131165907 2287729827), (.chord .universal 0 3393555298)⟩))
            (.covered))
          (.cut 2 (1/16)
            (.original (.row ⟨78001342658, 79281022314, (.direct 1131165907 2476335000), (.chord .universal 0 3393555298)⟩))
            (.covered))))
      (.cut 1 (31/400)
        (.cut 0 (63/136)
          (.cut 2 (1/16)
            (.original (.row ⟨79281022313, 80538706897, (.direct 1131165907 2333004105), (.chord .universal 0 3393555298)⟩))
            (.covered))
          (.cut 1 (61/800)
            (.cut 2 (1/16)
              (.original (.row ⟨79281022313, 79912545052, (.direct 1131165907 2502912309), (.chord .universal 0 3393555298)⟩))
              (.covered))
            (.cut 0 (135/272)
              (.cut 2 (1/16)
                (.original (.row ⟨79912545051, 80538706897, (.direct 1131165907 2430582652), (.chord .universal 0 3393555298)⟩))
                (.covered))
              (.cut 2 (1/16)
                (.original (.row ⟨79912545051, 80538706897, (.direct 1131165907 2529628949), (.variance 1403633429276)⟩))
                (.covered)))))
        (.cut 0 (63/136)
          (.cut 2 (1/16)
            (.original (.row ⟨80538706896, 81775466253, (.direct 1131165907 2378724172), (.chord .universal 0 3393555298)⟩))
            (.covered))
          (.cut 1 (63/800)
            (.cut 0 (135/272)
              (.cut 2 (1/16)
                (.original (.row ⟨80538706896, 81159638739, (.direct 1131165907 2455390007), (.chord .universal 0 3393555298)⟩))
                (.covered))
              (.cut 2 (1/16)
                (.original (.row ⟨80538706896, 81159638739, (.direct 1131165907 2556485107), (.variance 1393816525089)⟩))
                (.covered)))
            (.cut 0 (135/272)
              (.cut 2 (1/16)
                (.original (.row ⟨81159638738, 81775466253, (.direct 1131165907 2480322694), (.variance 1424427010755)⟩))
                (.covered))
              (.cut 0 (279/544)
                (.cut 2 (1/16)
                  (.original (.row ⟨81159638738, 81775466253, (.direct 1131165907 2531707911), (.variance 1384217502395)⟩))
                  (.covered))
                (.original (.empty))))))))
    (.cut 1 (3/40)
      (.cut 0 (63/136)
        (.cut 2 (1/16)
          (.original (.row ⟨76698504228, 79281022314, (.direct 3393509060 4961021375), (.variance 993810783364)⟩))
          (.cut 2 (3/32)
            (.original (.row ⟨76698504228, 79281022314, (.direct 3393509060 4961021375), (.chord (.secant 1464689871710 221907501001 510197146 86494067810) 3393555298 6452870597)⟩))
            (.covered)))
        (.cut 1 (29/400)
          (.cut 3 (3/64)
            (.cut 2 (1/16)
              (.original (.row ⟨76698504228, 78001342659, (.direct 2150924658 3686746272), (.variance 973334662170)⟩))
              (.cut 2 (3/32)
                (.original (.row ⟨76698504228, 78001342659, (.direct 2150924658 3686746272), (.chord (.secant 1242575927391 119250153612 670418100 93651456117) 3393555298 6452870597)⟩))
                (.covered)))
            (.original (.row ⟨76698504228, 78001342659, (.direct 3393509060 5135227788), (.variance 866517439819)⟩)))
          (.cut 3 (3/64)
            (.cut 2 (1/16)
              (.original (.row ⟨78001342658, 79281022314, (.direct 2150924658 3747262540), (.variance 968253414246)⟩))
              (.cut 2 (3/32)
                (.original (.row ⟨78001342658, 79281022314, (.direct 2150924658 3747262540), (.chord (.secant 1250857468369 122751551144 392727927 95542228860) 3393555298 6452870597)⟩))
                (.covered)))
            (.original (.row ⟨78001342658, 79281022314, (.direct 3393509060 5202455036), (.variance 863146316826)⟩)))))
      (.cut 0 (63/136)
        (.cut 1 (31/400)
          (.cut 2 (1/16)
            (.original (.row ⟨79281022313, 80538706897, (.direct 3393509060 5019237302), (.variance 984513529664)⟩))
            (.cut 2 (3/32)
              (.original (.row ⟨79281022313, 80538706897, (.direct 3393509060 5019237302), (.chord (.secant 1472281073658 225698685231 1057675653 89655087539) 3393555298 6452870597)⟩))
              (.covered)))
          (.cut 3 (3/64)
            (.cut 2 (1/16)
              (.original (.row ⟨80538706896, 81775466253, (.direct 2150924658 3635160146), (.variance 979957060640)⟩))
              (.original (.row ⟨80538706896, 81775466253, (.direct 2150924658 3635160146), (.chord (.secant 1286074309060 137954628355 5962176285 57842192504) 3393555298 10180665226)⟩)))
            (.cut 2 (1/16)
              (.original (.row ⟨80538706896, 81775466253, (.direct 3393509060 5077856089), (.variance 870887986079)⟩))
              (.original (.row ⟨80538706896, 81775466253, (.direct 3393509060 5077856089), (.chord (.secant 1479906574307 229523485383 1281690919 90769694163) 3393555298 10180665226)⟩)))))
        (.cut 1 (31/400)
          (.cut 3 (3/64)
            (.cut 2 (1/16)
              (.original (.row ⟨79281022313, 80538706897, (.direct 2150924658 3808300478), (.variance 963248631171)⟩))
              (.cut 2 (3/32)
                (.original (.row ⟨79281022313, 80538706897, (.direct 2150924658 3808300478), (.chord (.secant 1259180912688 126299456108 173683859 97451879000) 3393555298 6452870597)⟩))
                (.covered)))
            (.original (.row ⟨79281022313, 80538706897, (.direct 3393509060 5270180546), (.variance 859810909406)⟩)))
          (.cut 3 (3/64)
            (.cut 2 (1/16)
              (.original (.row ⟨80538706896, 81775466253, (.direct 2150924658 3869862004), (.variance 958318284045)⟩))
              (.cut 2 (3/32)
                (.original (.row ⟨80538706896, 81775466253, (.direct 2150924658 3869862004), (.chord (.secant 1267546468165 129893916982 29250100 99380462172) 3393555298 6452870597)⟩))
                (.covered)))
            (.original (.row ⟨80538706896, 81775466253, (.direct 3393509060 5338406430), (.variance 856510534719)⟩))))))

set_option maxRecDepth 16000 in
theorem CutMid1H3NegRestPart6_ok : CutMid1H3NegRestPart6Tree.geometryOK CutMid1H3NegPowerCache CutMid1H3NegRestPart6Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
