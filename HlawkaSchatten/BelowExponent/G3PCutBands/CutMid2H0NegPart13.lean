/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H0NegPart13`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H0NegPart13Box : Box := (((((((⟨![0, 9/100, 0, -8], ![9/68, 11/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).upperChild 2 (5/16)

set_option maxRecDepth 16000 in
def CutMid2H0NegPart13Tree : CertTree :=
  .cut 3 (0)
    (.cut 3 (-1/8)
      (.cut 1 (1/10)
        (.row ⟨86531900008, 91020629598, (.direct 10180561190 9187759033), (.chord .universal 43500686443 91625974997)⟩)
        (.cut 1 (21/200)
          (.row ⟨91020629597, 93177423805, (.direct 10180561190 9136412464), (.chord .universal 43500686443 91625974997)⟩)
          (.row ⟨93177423804, 95281442641, (.direct 10180561190 9084901347), (.chord .universal 43500686443 91625974997)⟩)))
      (.cut 1 (1/10)
        (.cut 0 (9/136)
          (.row ⟨86531900008, 91020629598, (.direct 0 34931964), (.chord .universal 43500686443 91625974997)⟩)
          (.row ⟨86531900008, 91020629598, (.direct 0 104795883), (.chord .universal 43500686443 91625974997)⟩))
        (.cut 0 (9/136)
          (.cut 1 (21/200)
            (.row ⟨91020629597, 93177423805, (.direct 0 37898415), (.chord .universal 43500686443 91625974997)⟩)
            (.cut 3 (-1/16)
              (.row ⟨93177423804, 95281442641, (.direct 3393509060 3048188173), (.chord .universal 43500686443 91625974997)⟩)
              (.row ⟨93177423804, 95281442641, (.direct 0 40969556), (.chord .universal 43500686443 91625974997)⟩)))
          (.cut 1 (21/200)
            (.cut 3 (-1/16)
              (.row ⟨91020629597, 93177423805, (.direct 3393509060 2747889617), (.chord (.midpoint ⟨712868390338, 17446457177, 87934904719, 617067727964, 99357532665, 345754962309⟩) 43500686443 91625974997)⟩)
              (.row ⟨91020629597, 93177423805, (.direct 0 113695238), (.chord .universal 43500686443 91625974997)⟩))
            (.cut 3 (-1/16)
              (.row ⟨93177423804, 95281442641, (.direct 3393509060 2716697524), (.chord (.midpoint ⟨713354779678, 17322955223, 87651125921, 618484535220, 99097366286, 345845365376⟩) 43500686443 91625974997)⟩)
              (.cut 3 (-1/32)
                (.row ⟨93177423804, 95281442641, (.direct 1131165907 710629795), (.chord (.midpoint ⟨752153184289, 8649933706, 62594512406, 785370356645, 76691379637, 372352732030⟩) 43500686443 91625974997)⟩)
                (.cut 3 (-1/64)
                  (.row ⟨93177423804, 95281442641, (.direct 377054043 125408368), (.chord (.midpoint ⟨771835457566, 5196579256, 46918973225, 963599730542, 63543721085, 385114675113⟩) 43500686443 91625974997)⟩)
                  (.row ⟨93177423804, 95281442641, (.direct 0 122908660), (.chord (.secant 797663666203 1775139419 16641527515 1547551249) 43500686443 91625974997)⟩))))))))
    (.cut 3 (1/8)
      (.cut 3 (1/16)
        (.cut 3 (1/32)
          (.cut 0 (9/136)
            (.row ⟨86531900008, 95281442641, (.direct 1131165907 1352608740), (.chord (.secant 898978798144 8546951523 3715346965 0) 43500686443 91625974997)⟩)
            (.row ⟨86531900008, 95281442641, (.direct 1131165907 1588307602), (.chord (.secant 862663029060 2990065766 10325156773 87941959) 43500686443 91625974997)⟩))
          (.row ⟨86531900008, 95281442641, (.direct 3393509060 4035719201), (.chord (.secant 975127426794 25501249743 4047771904 3393509060) 43500686443 91625974997)⟩))
        (.row ⟨86531900008, 95281442641, (.direct 10180561190 11064363690), (.chord (.secant 1116659285762 69914671961 114172333 10180561190) 43500686443 91625974997)⟩))
      (.row ⟨86531900008, 95281442641, (.direct 30541785600 31668201037), (.chord (.secant 1420367224941 200109031857 9247956506 30541785600) 43500686443 91625974997)⟩))

set_option maxRecDepth 16000 in
theorem CutMid2H0NegPart13_checked : CutMid2H0NegPart13Tree.commonOK CutMid2H0NegPart13Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
