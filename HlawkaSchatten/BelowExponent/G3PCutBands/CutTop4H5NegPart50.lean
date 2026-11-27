/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H5NegPart50`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H5NegPart50Box : Box := ((((((⟨![45/136, 19/100, 0, -8], ![27/68, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).upperChild 2 (1/2)).upperChild 2 (3/4)

set_option maxRecDepth 16000 in
def CutTop4H5NegPart50Tree : CertTree :=
  .cut 3 (0)
    (.cut 3 (-1/8)
      (.row ⟨123862991199, 126950446638, (.direct 10180561190 4565834898), (.chord (.midpoint ⟨575399173413, 65931069018, 119520233318, 496328297135, 162291862199, 324421658134⟩) 174227471798 274877906944)⟩)
      (.cut 3 (-1/16)
        (.row ⟨123862991199, 126950446638, (.direct 3393509060 377061750), (.chord (.midpoint ⟨609958506902, 51238819834, 101158545117, 558682726327, 147872243977, 346872633438⟩) 174227471798 274877906944)⟩)
        (.cut 3 (-1/32)
          (.row ⟨123862991199, 126950446638, (.direct 1131165907 325707822), (.chord (.secant 630323791908 43365325595 72459879950 1300645720) 174227471798 274877906944)⟩)
          (.row ⟨123862991199, 126950446638, (.direct 0 1953895586), (.chord (.secant 654056799327 34921981117 62427112153 53705914) 174227471798 274877906944)⟩))))
    (.cut 3 (1/8)
      (.cut 3 (1/16)
        (.cut 3 (1/32)
          (.row ⟨123862991199, 126950446638, (.direct 1131165907 4434166730), (.chord (.secant 678111993121 27173292263 54995584147 1337439372) 174227471798 274877906944)⟩)
          (.row ⟨123862991199, 126950446638, (.direct 3393509060 7590132277), (.chord (.secant 702486340121 20166720280 47917580595 3602186377) 174227471798 274877906944)⟩))
        (.row ⟨123862991199, 126950446638, (.direct 10180561190 15596541189), (.chord (.secant 752180832108 8644614224 41206111971 6596583163) 174227471798 274877906944)⟩))
      (.cut 3 (3/16)
        (.row ⟨123862991199, 126950446638, (.direct 19358451269 25544267546), (.chord (.secant 803117826769 1238428324 28944265852 14374073947) 174227471798 274877906944)⟩)
        (.row ⟨123862991199, 126950446638, (.direct 30541785600 37192598870), (.chord (.secant 855276178630 2128685297 18359968085 24175808916) 174227471798 274877906944)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop4H5NegPart50_checked : CutTop4H5NegPart50Tree.commonOK CutTop4H5NegPart50Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
