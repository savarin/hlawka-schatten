/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H3NegRestPart15`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H3NegRestPart15Box : Box := (((((((((((⟨![27/68, 9/100, 0, -8], ![9/17, 11/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)).upperChild 3 (0)).lowerChild 3 (1/8)).lowerChild 3 (1/16)).lowerChild 1 (1/10)).upperChild 3 (1/32)

set_option maxRecDepth 16000 in
def CutMid2H3NegRestPart15Tree : RatioRemainder :=
  .cut 1 (19/200)
    (.cut 0 (63/136)
      (.cut 3 (3/64)
        (.cut 2 (1/16)
          (.original (.row ⟨86531900008, 88806993133, (.direct 2150924658 3959972648), (.variance 958040464765)⟩))
          (.cut 2 (3/32)
            (.original (.row ⟨86531900008, 88806993133, (.direct 2150924658 3959972648), (.chord (.secant 1330974137972 158033828503 3473967360 99490562829) 3393555298 6452870597)⟩))
            (.covered)))
        (.cut 2 (1/16)
          (.original (.row ⟨86531900008, 88806993133, (.direct 3393509060 5438130292), (.variance 856324131875)⟩))
          (.original (.row ⟨86531900008, 88806993133, (.direct 3393509060 5438130292), (.chord (.secant 1526389520411 253185032958 2725404095 96807853860) 3393555298 10180665226)⟩))))
      (.cut 3 (3/64)
        (.cut 2 (1/16)
          (.original (.row ⟨86531900008, 88806993133, (.direct 2150924658 4250336757), (.variance 934717160854)⟩))
          (.cut 2 (3/32)
            (.original (.row ⟨86531900008, 88806993133, (.direct 2150924658 4250336757), (.chord (.secant 1318635943229 152441697910 1031105981 109309396439) 3393555298 6452870597)⟩))
            (.covered)))
        (.original (.row ⟨86531900008, 88806993133, (.direct 3393509060 5758390242), (.variance 840511500935)⟩))))
    (.cut 0 (63/136)
      (.cut 3 (3/64)
        (.cut 2 (1/16)
          (.original (.row ⟨88806993132, 91020629598, (.direct 2150924658 4071678547), (.variance 949653843121)⟩))
          (.original (.row ⟨88806993132, 91020629598, (.direct 2150924658 4071678547), (.chord (.secant 1346226006064 165021780682 3162376018 65213941213) 3393555298 10180665226)⟩)))
        (.cut 2 (1/16)
          (.original (.row ⟨88806993132, 91020629598, (.direct 3393509060 5561527551), (.variance 850675499239)⟩))
          (.original (.row ⟨88806993132, 91020629598, (.direct 3393509060 5561527551), (.chord (.secant 1542166118763 261346751707 3414755486 99285759108) 3393555298 10180665226)⟩))))
      (.cut 3 (3/64)
        (.cut 1 (39/400)
          (.cut 2 (1/16)
            (.original (.row ⟨88806993132, 89921191063, (.direct 2150924658 4315619020), (.variance 925734610426)⟩))
            (.cut 2 (3/32)
              (.original (.row ⟨88806993132, 89921191063, (.direct 2150924658 4315619020), (.chord (.secant 1327302209512 156363819724 1850615957 113415568906) 3393555298 6452870597)⟩))
              (.covered)))
          (.cut 2 (1/16)
            (.original (.row ⟨89921191062, 91020629598, (.direct 2150924658 4381441044), (.variance 921335057425)⟩))
            (.cut 2 (3/32)
              (.original (.row ⟨89921191062, 91020629598, (.direct 2150924658 4381441044), (.chord (.secant 1336012298565 160333058032 2325138082 115497747870) 3393555298 6452870597)⟩))
              (.covered))))
        (.original (.row ⟨88806993132, 91020629598, (.direct 3393509060 5902486651), (.variance 834335164159)⟩))))

set_option maxRecDepth 16000 in
theorem CutMid2H3NegRestPart15_ok : CutMid2H3NegRestPart15Tree.ok CutMid2H3NegRestPart15Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
