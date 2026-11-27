/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H3NegPart14`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H3NegPart14Box : Box := (((((((((((((⟨![27/68, 9/100, 0, -8], ![9/17, 11/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)).upperChild 3 (0)).lowerChild 3 (1/8)).lowerChild 3 (1/16)).lowerChild 1 (1/10)).lowerChild 3 (1/32)).upperChild 1 (19/200)).upperChild 0 (63/136)

set_option maxRecDepth 16000 in
def CutMid2H3NegPart14Tree : CertTree :=
  .cut 1 (39/400)
    (.cut 0 (135/272)
      (.cut 1 (77/800)
        (.cut 3 (1/64)
          (.cut 2 (1/16)
            (.row ⟨88806993132, 89365973271, (.direct 377054043 1694518789), (.variance 1313090902301)⟩)
            (.cut 2 (3/32)
              (.row ⟨88806993132, 89365973271, (.direct 377054043 1694518789), (.chord (.secant 946690334868 18463334212 30525179292 29849648043) 3393555298 6452870597)⟩)
              (.row ⟨88806993132, 89365973271, (.direct 377054043 1694518789), (.chord (.secant 803116524908 1238547661 43283730818 18919750292) 6452870597 10180665226)⟩)))
          (.cut 2 (1/16)
            (.row ⟨88806993132, 89365973271, (.direct 1131165907 2815937393), (.variance 1063799710636)⟩)
            (.row ⟨88806993132, 89365973271, (.direct 1131165907 2815937393), (.chord (.secant 1119686887951 71006117178 19671003126 42275804696) 3393555298 10180665226)⟩)))
        (.cut 3 (1/64)
          (.cut 2 (1/16)
            (.row ⟨89365973270, 89921191063, (.direct 377054043 1717033675), (.variance 1305630409305)⟩)
            (.cut 2 (3/32)
              (.row ⟨89365973270, 89921191063, (.direct 377054043 1717033675), (.chord (.secant 950403478749 19338493370 29868405897 30506269418) 3393555298 6452870597)⟩)
              (.row ⟨89365973270, 89921191063, (.direct 377054043 1717033675), (.chord (.secant 805445721877 1032039791 42722493836 19335939871) 6452870597 10180665226)⟩)))
          (.cut 2 (1/16)
            (.row ⟨89365973270, 89921191063, (.direct 1131165907 2842644503), (.variance 1060203038255)⟩)
            (.row ⟨89365973270, 89921191063, (.direct 1131165907 2842644503), (.chord (.secant 1123574277758 72415029914 19258666230 42826121063) 3393555298 10180665226)⟩))))
      (.cut 3 (1/64)
        (.cut 2 (1/16)
          (.row ⟨88806993132, 89921191063, (.direct 377054043 1830081789), (.variance 1276024250788)⟩)
          (.cut 2 (3/32)
            (.row ⟨88806993132, 89921191063, (.direct 377054043 1830081789), (.chord (.secant 946013112992 18305200640 33577327820 33298904401) 3393555298 6452870597)⟩)
            (.row ⟨88806993132, 89921191063, (.direct 377054043 1830081789), (.chord (.secant 795566891466 2000299984 47744539095 21106009537) 6452870597 10180665226)⟩)))
        (.cut 2 (1/16)
          (.row ⟨88806993132, 89921191063, (.direct 1131165907 2976201998), (.variance 1045648415820)⟩)
          (.cut 2 (3/32)
            (.row ⟨88806993132, 89921191063, (.direct 1131165907 2976201998), (.chord (.secant 1118593683186 70611425052 7474498368 71229271599) 3393555298 6452870597)⟩)
            (.row ⟨88806993132, 89921191063, (.direct 1131165907 2976201998), (.chord (.secant 902644097790 9213173525 23079861175 45147602082) 6452870597 10180665226)⟩)))))
    (.cut 3 (1/64)
      (.cut 2 (1/16)
        (.row ⟨89921191062, 91020629598, (.direct 377054043 1879719697), (.variance 1298302959111)⟩)
        (.cut 2 (3/32)
          (.row ⟨89921191062, 91020629598, (.direct 377054043 1879719697), (.chord (.secant 976872965769 25957448363 35765306574 31169022146) 3393555298 6452870597)⟩)
          (.row ⟨89921191062, 91020629598, (.direct 377054043 1879719697), (.chord (.secant 822024635103 43481615 49604496665 19756015716) 6452870597 10180665226)⟩)))
      (.cut 2 (1/16)
        (.row ⟨89921191062, 91020629598, (.direct 1131165907 3034575728), (.variance 1056642844843)⟩)
        (.cut 2 (3/32)
          (.row ⟨89921191062, 91020629598, (.direct 1131165907 3034575728), (.chord (.secant 1151267531974 82689512459 8733527879 68440195471) 3393555298 6452870597)⟩)
          (.row ⟨89921191062, 91020629598, (.direct 1131165907 3034575728), (.chord (.secant 930267872427 14761853988 24485419376 43379788143) 6452870597 10180665226)⟩))))

set_option maxRecDepth 16000 in
theorem CutMid2H3NegPart14_checked : CutMid2H3NegPart14Tree.commonOK CutMid2H3NegPart14Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
