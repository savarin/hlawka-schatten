/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid1H3NegRestPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid1H3NegRestPart1Box : Box := ((((((((⟨![27/68, 7/100, 0, -8], ![9/17, 9/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)).lowerChild 3 (0)).lowerChild 1 (2/25)

set_option maxRecDepth 16000 in
def CutMid1H3NegRestPart1Tree : RatioRemainder :=
  .cut 1 (3/40)
    (.cut 3 (-1/8)
      (.original (.row ⟨76698504228, 79281022314, (.direct 10180561190 7352335882), (.variance 709529075087)⟩))
      (.cut 1 (29/400)
        (.cut 0 (63/136)
          (.cut 2 (1/16)
            (.original (.row ⟨76698504228, 78001342659, (.direct 0 448147726), (.chord .universal 0 3393555298)⟩))
            (.cut 3 (-1/16)
              (.original (.row ⟨76698504228, 78001342659, (.direct 3393509060 1944740495), (.variance 1005103490519)⟩))
              (.covered)))
          (.cut 2 (1/16)
            (.original (.row ⟨76698504228, 78001342659, (.direct 0 553778706), (.chord .universal 0 3393555298)⟩))
            (.cut 3 (-1/16)
              (.original (.row ⟨76698504228, 78001342659, (.direct 3393509060 1762703302), (.variance 1031306101197)⟩))
              (.covered))))
        (.cut 0 (63/136)
          (.cut 2 (1/16)
            (.original (.row ⟨78001342658, 79281022314, (.direct 0 473860353), (.chord .universal 0 3393555298)⟩))
            (.cut 3 (-1/16)
              (.original (.row ⟨78001342658, 79281022314, (.direct 3393509060 1898469686), (.variance 1011461382974)⟩))
              (.covered)))
          (.cut 1 (59/800)
            (.cut 2 (1/16)
              (.original (.row ⟨78001342658, 78644002272, (.direct 0 569573246), (.chord .universal 0 3393555298)⟩))
              (.cut 3 (-1/16)
                (.original (.row ⟨78001342658, 78644002272, (.direct 3393509060 1737176811), (.variance 1035253049461)⟩))
                (.covered)))
            (.cut 3 (-1/16)
              (.original (.row ⟨78644002271, 79281022314, (.direct 3393509060 1711755128), (.variance 1039257206003)⟩))
              (.cut 2 (1/16)
                (.original (.row ⟨78644002271, 79281022314, (.direct 0 585551947), (.chord .universal 0 3393555298)⟩))
                (.covered)))))))
    (.cut 3 (-1/8)
      (.original (.row ⟨79281022313, 81775466253, (.direct 10180561190 7168719696), (.variance 714243660188)⟩))
      (.cut 1 (31/400)
        (.cut 0 (63/136)
          (.cut 3 (-1/16)
            (.original (.row ⟨79281022313, 80538706897, (.direct 3393509060 1852492676), (.variance 1017975601448)⟩))
            (.cut 2 (1/16)
              (.original (.row ⟨79281022313, 80538706897, (.direct 0 500167495), (.chord .universal 0 3393555298)⟩))
              (.covered)))
          (.cut 1 (61/800)
            (.cut 3 (-1/16)
              (.original (.row ⟨79281022313, 79912545052, (.direct 3393509060 1686439263), (.variance 1043319970231)⟩))
              (.cut 0 (135/272)
                (.cut 2 (1/16)
                  (.original (.row ⟨79281022313, 79912545052, (.direct 0 543207631), (.chord .universal 0 3393555298)⟩))
                  (.covered))
                (.cut 2 (1/16)
                  (.original (.row ⟨79281022313, 79912545052, (.direct 0 601714304), (.chord .universal 0 3393555298)⟩))
                  (.covered))))
            (.cut 3 (-1/16)
              (.original (.row ⟨79912545051, 80538706897, (.direct 3393509060 1661230236), (.variance 1047442790283)⟩))
              (.cut 0 (135/272)
                (.cut 2 (1/16)
                  (.original (.row ⟨79912545051, 80538706897, (.direct 0 557963830), (.chord .universal 0 3393555298)⟩))
                  (.covered))
                (.cut 2 (1/16)
                  (.original (.row ⟨79912545051, 80538706897, (.direct 0 618059832), (.chord .universal 0 3393555298)⟩))
                  (.covered))))))
        (.cut 0 (63/136)
          (.cut 3 (-1/16)
            (.original (.row ⟨80538706896, 81775466253, (.direct 3393509060 1806814914), (.variance 1024652652764)⟩))
            (.cut 1 (63/800)
              (.cut 2 (1/16)
                (.original (.row ⟨80538706896, 81159638739, (.direct 0 513543039), (.chord .universal 0 3393555298)⟩))
                (.covered))
              (.cut 0 (117/272)
                (.cut 2 (1/16)
                  (.original (.row ⟨81159638738, 81775466253, (.direct 0 468655326), (.chord .universal 0 3393555298)⟩))
                  (.covered))
                (.cut 2 (1/16)
                  (.original (.row ⟨81159638738, 81775466253, (.direct 0 527066083), (.chord .universal 0 3393555298)⟩))
                  (.covered)))))
          (.cut 3 (-1/16)
            (.original (.row ⟨80538706896, 81775466253, (.direct 3393509060 1611136853), (.variance 1055874647463)⟩))
            (.cut 1 (63/800)
              (.cut 0 (135/272)
                (.cut 2 (1/16)
                  (.original (.row ⟨80538706896, 81159638739, (.direct 0 572884971), (.chord .universal 0 3393555298)⟩))
                  (.covered))
                (.cut 0 (279/544)
                  (.cut 2 (1/16)
                    (.original (.row ⟨80538706896, 81159638739, (.direct 0 603445413), (.chord .universal 0 3393555298)⟩))
                    (.covered))
                  (.original (.empty))))
              (.cut 0 (135/272)
                (.cut 2 (1/16)
                  (.original (.row ⟨81159638738, 81775466253, (.direct 0 587970657), (.chord .universal 0 3393555298)⟩))
                  (.covered))
                (.cut 0 (279/544)
                  (.cut 2 (1/16)
                    (.original (.row ⟨81159638738, 81775466253, (.direct 0 619335841), (.chord .universal 0 3393555298)⟩))
                    (.covered))
                  (.original (.empty)))))))))

set_option maxRecDepth 16000 in
theorem CutMid1H3NegRestPart1_ok : CutMid1H3NegRestPart1Tree.ok CutMid1H3NegRestPart1Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
