/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H6NegChartPart23`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H6NegChartPart23Box : Box := (((((⟨![27/68, 19/100, 0, -1], ![63/136, 1/5, 1, 1]⟩ : Box)).lowerChild 3 (1/4)).upperChild 3 (-1/4)).upperChild 2 (1/2)).upperChild 2 (3/4)

set_option maxRecDepth 16000 in
def CutTop4H6NegChartPart23Tree : RatioChart :=
  .cut 3 (0)
    (.cut 3 (-1/8)
      (.cut 3 (-3/16)
        (.row ⟨123862991199, 126950446638, (.direct 24471202710 32038871125), 174227471798, 274877906944, 393943346781/274877906944, .leaf (.secant 730620357551 13171657058 35673133487 19358451269)⟩)
        (.row ⟨123862991199, 126950446638, (.direct 13903418449 20734419376), 174227471798, 274877906944, 104726747587/68719476736, .leaf (.secant 691947682635 23090426145 49313920105 10180561190)⟩))
      (.cut 3 (-1/16)
        (.row ⟨123862991199, 126950446638, (.direct 5726197012 11358505827), 174227471798, 274877906944, 441519703115/274877906944, .leaf (.secant 654056799327 34921981117 64518468785 3393509060)⟩)
        (.cut 3 (-1/32)
          (.row ⟨123862991199, 126950446638, (.direct 635748259 4253995770), 174227471798, 274877906944, 438685332681/274877906944, .leaf (.secant 616959325387 48466791375 72672791918 1131165907)⟩)
          (.row ⟨123862991199, 126950446638, (.direct 212571126 1749511849), 174227471798, 274877906944, 111670849385/68719476736, .leaf (.secant 598711912953 55835701657 81179804332 0)⟩))))
    (.cut 3 (1/8)
      (.row ⟨123862991199, 126950446638, (.direct 1910201192 192281677), 174227471798, 274877906944, 220445049489/137438953472, .leaf (.midpoint ⟨580667489242, 63582541603, 106756363911, 537735758958, 160133808481, 336314167318⟩)⟩)
      (.row ⟨123862991199, 126950446638, (.direct 12366382360 5277086533), 174227471798, 274877906944, 216042674917/137438953472, .leaf (.midpoint ⟨510553046651, 98114766141, 142055421758, 439080394524, 187938143594, 318561080555⟩)⟩))

set_option maxRecDepth 16000 in
theorem CutTop4H6NegChartPart23_ok : CutTop4H6NegChartPart23Tree.ok CutTop4H6NegChartPart23Box false = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
