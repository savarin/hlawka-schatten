/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid1H1NegPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid1H1NegPart1Box : Box := (((((((⟨![9/68, 7/100, 0, -8], ![9/34, 9/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)).lowerChild 3 (0)

set_option maxRecDepth 16000 in
def CutMid1H1NegPart1Tree : CertTree :=
  .cut 1 (2/25)
    (.cut 1 (3/40)
      (.cut 3 (-1/8)
        (.row ⟨76698504228, 79281022314, (.direct 10180561190 8724141326), (.variance 678445119678)⟩)
        (.cut 2 (1/16)
          (.row ⟨76698504228, 79281022314, (.direct 0 195183996), (.chord .universal 0 3393555298)⟩)
          (.cut 1 (29/400)
            (.cut 0 (27/136)
              (.row ⟨76698504228, 78001342659, (.direct 0 117001607), (.chord .universal 3393555298 10180665226)⟩)
              (.cut 3 (-1/16)
                (.row ⟨76698504228, 78001342659, (.direct 3393509060 2529353886), (.chord .universal 3393555298 10180665226)⟩)
                (.row ⟨76698504228, 78001342659, (.direct 0 184592915), (.chord .universal 3393555298 10180665226)⟩)))
            (.cut 0 (27/136)
              (.row ⟨78001342658, 79281022314, (.direct 0 123714614), (.chord .universal 3393555298 10180665226)⟩)
              (.cut 3 (-1/16)
                (.row ⟨78001342658, 79281022314, (.direct 3393509060 2500153266), (.chord .universal 3393555298 10180665226)⟩)
                (.row ⟨78001342658, 79281022314, (.direct 0 195183996), (.chord .universal 3393555298 10180665226)⟩))))))
      (.cut 3 (-1/8)
        (.row ⟨79281022313, 81775466253, (.direct 10180561190 8626098130), (.variance 680455936934)⟩)
        (.cut 1 (31/400)
          (.cut 2 (1/16)
            (.row ⟨79281022313, 80538706897, (.direct 0 206019958), (.chord .universal 0 3393555298)⟩)
            (.cut 0 (27/136)
              (.row ⟨79281022313, 80538706897, (.direct 0 130582835), (.chord .universal 3393555298 10180665226)⟩)
              (.cut 3 (-1/16)
                (.row ⟨79281022313, 80538706897, (.direct 3393509060 2471002524), (.chord .universal 3393555298 10180665226)⟩)
                (.row ⟨79281022313, 80538706897, (.direct 0 206019958), (.chord .universal 3393555298 10180665226)⟩))))
          (.cut 2 (1/16)
            (.row ⟨80538706896, 81775466253, (.direct 0 217099539), (.chord .universal 0 3393555298)⟩)
            (.cut 0 (27/136)
              (.row ⟨80538706896, 81775466253, (.direct 0 137605471), (.chord .universal 3393555298 10180665226)⟩)
              (.cut 3 (-1/16)
                (.row ⟨80538706896, 81775466253, (.direct 3393509060 2441902736), (.chord .universal 3393555298 10180665226)⟩)
                (.cut 1 (63/800)
                  (.row ⟨80538706896, 81159638739, (.direct 0 211529371), (.chord .universal 3393555298 10180665226)⟩)
                  (.row ⟨81159638738, 81775466253, (.direct 0 217099539), (.chord .universal 3393555298 10180665226)⟩))))))))
    (.cut 1 (17/200)
      (.cut 3 (-1/8)
        (.row ⟨81775466252, 84190079492, (.direct 10180561190 8527955732), (.variance 682497881357)⟩)
        (.cut 1 (33/400)
          (.cut 0 (27/136)
            (.cut 2 (1/16)
              (.row ⟨81775466252, 82992286623, (.direct 0 144781789), (.chord .universal 0 3393555298)⟩)
              (.cut 3 (-1/16)
                (.row ⟨81775466252, 82992286623, (.direct 3393509060 2646402003), (.chord .universal 3393555298 10180665226)⟩)
                (.row ⟨81775466252, 82992286623, (.direct 0 144781789), (.chord .universal 3393555298 10180665226)⟩)))
            (.cut 2 (1/16)
              (.row ⟨81775466252, 82992286623, (.direct 0 228421583), (.chord .universal 0 3393555298)⟩)
              (.cut 3 (-1/16)
                (.row ⟨81775466252, 82992286623, (.direct 3393509060 2412854994), (.chord .universal 3393555298 10180665226)⟩)
                (.cut 1 (13/160)
                  (.row ⟨81775466252, 82386310187, (.direct 0 222730321), (.chord .universal 3393555298 10180665226)⟩)
                  (.row ⟨82386310186, 82992286623, (.direct 0 228421583), (.chord .universal 3393555298 10180665226)⟩)))))
          (.cut 0 (27/136)
            (.cut 2 (1/16)
              (.row ⟨82992286622, 84190079492, (.direct 0 152111122), (.chord .universal 0 3393555298)⟩)
              (.cut 3 (-1/16)
                (.row ⟨82992286622, 84190079492, (.direct 3393509060 2623887088), (.chord .universal 3393555298 10180665226)⟩)
                (.row ⟨82992286622, 84190079492, (.direct 0 152111122), (.chord .universal 3393555298 10180665226)⟩)))
            (.cut 2 (1/16)
              (.row ⟨82992286622, 84190079492, (.direct 0 239985040), (.chord .universal 0 3393555298)⟩)
              (.cut 3 (-1/16)
                (.row ⟨82992286622, 84190079492, (.direct 3393509060 2383860407), (.chord .universal 3393555298 10180665226)⟩)
                (.cut 1 (67/800)
                  (.row ⟨82992286622, 83593507230, (.direct 0 234173197), (.chord .universal 3393555298 10180665226)⟩)
                  (.row ⟨83593507229, 84190079492, (.direct 0 239985040), (.chord .universal 3393555298 10180665226)⟩)))))))
      (.cut 3 (-1/8)
        (.row ⟨84190079491, 86531900009, (.direct 10180561190 8429717858), (.variance 684571726439)⟩)
        (.cut 1 (7/80)
          (.cut 0 (27/136)
            (.cut 2 (1/16)
              (.row ⟨84190079491, 85369689272, (.direct 0 159592863), (.chord .universal 0 3393555298)⟩)
              (.cut 3 (-1/16)
                (.row ⟨84190079491, 85369689272, (.direct 3393509060 2601384667), (.chord .universal 3393555298 10180665226)⟩)
                (.row ⟨84190079491, 85369689272, (.direct 0 159592863), (.chord .universal 3393555298 10180665226)⟩)))
            (.cut 3 (-1/16)
              (.row ⟨84190079491, 85369689272, (.direct 3393509060 2354920102), (.chord .universal 0 10180665226)⟩)
              (.cut 2 (1/16)
                (.row ⟨84190079491, 85369689272, (.direct 0 251788950), (.chord .universal 0 3393555298)⟩)
                (.cut 1 (69/800)
                  (.row ⟨84190079491, 84782106923, (.direct 0 245856995), (.chord .universal 3393555298 10180665226)⟩)
                  (.row ⟨84782106922, 85369689272, (.direct 0 251788950), (.chord .universal 3393555298 10180665226)⟩)))))
          (.cut 0 (27/136)
            (.cut 3 (-1/16)
              (.row ⟨85369689271, 86531900009, (.direct 3393509060 2578895232), (.chord .universal 0 10180665226)⟩)
              (.cut 2 (1/16)
                (.row ⟨85369689271, 86531900009, (.direct 0 167226462), (.chord .universal 0 3393555298)⟩)
                (.row ⟨85369689271, 86531900009, (.direct 0 167226462), (.chord .universal 3393555298 10180665226)⟩)))
            (.cut 3 (-1/16)
              (.row ⟨85369689271, 86531900009, (.direct 3393509060 2326035221), (.chord .universal 0 10180665226)⟩)
              (.cut 1 (71/800)
                (.cut 2 (1/16)
                  (.row ⟨85369689271, 85952922711, (.direct 0 257780800), (.chord .universal 0 3393555298)⟩)
                  (.row ⟨85369689271, 85952922711, (.direct 0 257780800), (.chord .universal 3393555298 10180665226)⟩))
                (.cut 0 (63/272)
                  (.row ⟨85952922710, 86531900009, (.direct 0 213507505), (.chord .universal 0 10180665226)⟩)
                  (.row ⟨85952922710, 86531900009, (.direct 0 263832444), (.chord .universal 0 10180665226)⟩))))))))

set_option maxRecDepth 16000 in
theorem CutMid1H1NegPart1_checked : CutMid1H1NegPart1Tree.commonOK CutMid1H1NegPart1Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
