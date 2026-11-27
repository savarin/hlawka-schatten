/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid1H3NegRestPart7`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid1H3NegRestPart7Box : Box := ((((((((((((⟨![27/68, 7/100, 0, -8], ![9/17, 9/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)).upperChild 3 (0)).lowerChild 3 (1/8)).lowerChild 3 (1/16)).upperChild 1 (2/25)).lowerChild 3 (1/32)).lowerChild 1 (17/200)

set_option maxRecDepth 16000 in
def CutMid1H3NegRestPart7Tree : RatioRemainder :=
  .cut 0 (63/136)
    (.cut 1 (33/400)
      (.cut 1 (13/160)
        (.cut 0 (117/272)
          (.cut 2 (1/16)
            (.original (.row ⟨81775466252, 82386310187, (.direct 1131165907 2299747321), (.chord .universal 0 3393555298)⟩))
            (.covered))
          (.cut 2 (1/16)
            (.original (.row ⟨81775466252, 82386310187, (.direct 1131165907 2401751800), (.chord .universal 0 3393555298)⟩))
            (.covered)))
        (.cut 0 (117/272)
          (.cut 2 (1/16)
            (.original (.row ⟨82386310186, 82992286623, (.direct 1131165907 2320890953), (.chord .universal 0 3393555298)⟩))
            (.covered))
          (.cut 2 (1/16)
            (.original (.row ⟨82386310186, 82992286623, (.direct 1131165907 2424891386), (.chord .universal 0 3393555298)⟩))
            (.covered))))
      (.cut 1 (67/800)
        (.cut 0 (117/272)
          (.cut 2 (1/16)
            (.original (.row ⟨82992286622, 83593507230, (.direct 1131165907 2342133641), (.chord .universal 0 3393555298)⟩))
            (.covered))
          (.cut 2 (1/16)
            (.original (.row ⟨82992286622, 83593507230, (.direct 1131165907 2448143103), (.chord .universal 0 3393555298)⟩))
            (.covered)))
        (.cut 0 (117/272)
          (.cut 2 (1/16)
            (.original (.row ⟨83593507229, 84190079492, (.direct 1131165907 2363475547), (.chord .universal 0 3393555298)⟩))
            (.covered))
          (.cut 2 (1/16)
            (.original (.row ⟨83593507229, 84190079492, (.direct 1131165907 2471507128), (.chord .universal 0 3393555298)⟩))
            (.covered)))))
    (.cut 1 (33/400)
      (.cut 1 (13/160)
        (.cut 0 (135/272)
          (.cut 2 (1/16)
            (.original (.row ⟨81775466252, 82386310187, (.direct 1131165907 2505380892), (.variance 1414764881931)⟩))
            (.covered))
          (.cut 3 (1/64)
            (.cut 2 (1/16)
              (.original (.row ⟨81775466252, 82386310187, (.direct 377054043 1522520039), (.variance 1374828121453)⟩))
              (.covered))
            (.cut 2 (1/16)
              (.original (.row ⟨81775466252, 82386310187, (.direct 1131165907 2610616723), (.variance 1092492890831)⟩))
              (.covered))))
        (.cut 0 (135/272)
          (.cut 2 (1/16)
            (.original (.row ⟨82386310186, 82992286623, (.direct 1131165907 2530564785), (.variance 1405310452583)⟩))
            (.covered))
          (.cut 3 (1/64)
            (.cut 2 (1/16)
              (.original (.row ⟨82386310186, 82992286623, (.direct 377054043 1545252900), (.variance 1365640576932)⟩))
              (.covered))
            (.cut 2 (1/16)
              (.original (.row ⟨82386310186, 82992286623, (.direct 1131165907 2637892563), (.variance 1088341947813)⟩))
              (.covered)))))
      (.cut 1 (67/800)
        (.cut 0 (135/272)
          (.cut 2 (1/16)
            (.original (.row ⟨82992286622, 83593507230, (.direct 1131165907 2555874555), (.variance 1396056107654)⟩))
            (.covered))
          (.cut 3 (1/64)
            (.cut 2 (1/16)
              (.original (.row ⟨82992286622, 83593507230, (.direct 377054043 1568139767), (.variance 1356647468737)⟩))
              (.covered))
            (.cut 2 (1/16)
              (.original (.row ⟨82992286622, 83593507230, (.direct 1131165907 2665308682), (.variance 1084238980947)⟩))
              (.covered))))
        (.cut 0 (135/272)
          (.cut 1 (27/320)
            (.cut 2 (1/16)
              (.original (.row ⟨83593507229, 83892367844, (.direct 1131165907 2568576703), (.variance 1386994621510)⟩))
              (.covered))
            (.cut 0 (261/544)
              (.cut 2 (1/16)
                (.original (.row ⟨83892367843, 84190079492, (.direct 1131165907 2526188570), (.variance 1382534042667)⟩))
                (.covered))
              (.cut 2 (1/16)
                (.original (.row ⟨83892367843, 84190079492, (.direct 1131165907 2581310390), (.variance 1362544436758)⟩))
                (.covered))))
          (.cut 3 (1/64)
            (.cut 2 (1/16)
              (.original (.row ⟨83593507229, 84190079492, (.direct 377054043 1591180706), (.variance 1347841775203)⟩))
              (.covered))
            (.cut 2 (1/16)
              (.original (.row ⟨83593507229, 84190079492, (.direct 1131165907 2692865276), (.variance 1080183025027)⟩))
              (.covered))))))

set_option maxRecDepth 16000 in
theorem CutMid1H3NegRestPart7_ok : CutMid1H3NegRestPart7Tree.ok CutMid1H3NegRestPart7Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
