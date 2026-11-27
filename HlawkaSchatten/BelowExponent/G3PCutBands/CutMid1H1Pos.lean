/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H1PosPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid1H1Pos`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid1H1PosBox : Box := ⟨![9/68, 7/100, 0, -8], ![9/34, 9/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutMid1H1PosTree : CertTree :=
  .cut 3 (3/4)
    (.cut 3 (-1/4)
      (.cut 3 (-2)
        (.row ⟨76698504228, 86531900009, (.direct 824633666698 800316814064), (.variance 207781477512)⟩)
        (.row ⟨76698504228, 86531900009, (.direct 30541785600 27578575652), (.variance 501908366984)⟩))
      (.cut 3 (1/4)
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 2 (1/16)
              (.row ⟨76698504228, 86531900009, (.direct 30541785600 32373100089), (.chord .universal 0 3393555298)⟩)
              (.cut 1 (2/25)
                (.row ⟨76698504228, 81775466253, (.direct 30541785600 32159156970), (.chord .universal 3393555298 10180665226)⟩)
                (.row ⟨81775466252, 86531900009, (.direct 30541785600 32373100089), (.chord .universal 3393555298 10180665226)⟩)))
            (.cut 2 (5/16)
              (.cut 2 (7/32)
                (.cut 1 (2/25)
                  (.row ⟨76698504228, 81775466253, (.direct 30541785600 32159156970), (.chord .universal 10180665226 24716235638)⟩)
                  (.cut 1 (17/200)
                    (.row ⟨81775466252, 84190079492, (.direct 30541785600 32265783787), (.chord .universal 10180665226 24716235638)⟩)
                    (.row ⟨84190079491, 86531900009, (.direct 30541785600 32373100089), (.chord .universal 10180665226 24716235638)⟩)))
                (.row ⟨76698504228, 86531900009, (.direct 30541785600 32373100089), (.chord .universal 24716235638 43500686443)⟩))
              (.row ⟨76698504228, 86531900009, (.direct 30541785600 32373100089), (.chord .universal 43500686443 91625974997)⟩)))
          (.row ⟨76698504228, 86531900009, (.direct 30541785600 32373100089), (.chord .universal 91625974997 274877906944)⟩))
        (.row ⟨76698504228, 86531900009, (.direct 174227225485 175376986626), (.variance 485780527627)⟩)))
    (.cut 3 (2)
      (.cut 3 (5/4)
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cone)
            (.row ⟨76698504228, 86531900009, .zero, (.variance 309532260063)⟩))
          (.row ⟨76698504228, 86531900009, .zero, (.variance 309532260063)⟩))
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 3 (13/8)
              (.cut 3 (23/16)
                (.cut 3 (43/32)
                  (.row ⟨76698504228, 86531900009, (.direct 391506126583 389959717376), (.variance 250824074919)⟩)
                  (.row ⟨76698504228, 86531900009, (.direct 439055879922 436838157402), (.variance 243477884703)⟩))
                (.row ⟨76698504228, 86531900009, (.direct 488587506629 485651920888), (.variance 236817051303)⟩))
              (.row ⟨76698504228, 86531900009, (.direct 593382169971 588878064732), (.variance 225162250008)⟩))
            (.row ⟨76698504228, 86531900009, (.direct 391506126583 389959717376), (.variance 250824074919)⟩))
          (.row ⟨76698504228, 86531900009, (.direct 391506126583 389959717376), (.variance 250824074919)⟩)))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (5)
            (.cut 3 (7/2)
              (.cut 3 (11/4)
                (.cut 3 (19/8)
                  (.row ⟨76698504228, 86531900009, (.direct 824633666698 816500081227), (.variance 206695099793)⟩)
                  (.row ⟨76698504228, 86531900009, (.direct 1082810704946 1070448222493), (.variance 192545549081)⟩))
                (.row ⟨76698504228, 86531900009, (.direct 1366046989981 1348908063065), (.variance 181233636771)⟩))
              (.cut 3 (17/4)
                (.row ⟨76698504228, 86531900009, (.direct 2002014560937 1973830052749), (.variance 164038914451)⟩)
                (.row ⟨76698504228, 86531900009, (.direct 2723407729414 2682369987099), (.variance 151378910266)⟩)))
            (.cut 3 (13/2)
              (.row ⟨76698504228, 86531900009, (.direct 3523554676644 3468018178648), (.variance 141531155744)⟩)
              (.row ⟨76698504228, 86531900009, (.direct 5340438828596 5251428781911), (.variance 126959931299)⟩)))
          (.cut 3 (5)
            (.cut 3 (7/2)
              (.cut 3 (11/4)
                (.row ⟨76698504228, 86531900009, (.direct 824633666698 816500081227), (.variance 206695099793)⟩)
                (.row ⟨76698504228, 86531900009, (.direct 1366046989981 1348908063065), (.variance 181233636771)⟩))
              (.cut 3 (17/4)
                (.row ⟨76698504228, 86531900009, (.direct 2002014560937 1973830052749), (.variance 164038914451)⟩)
                (.row ⟨76698504228, 86531900009, (.direct 2723407729414 2682369987099), (.variance 151378910266)⟩)))
            (.cut 3 (13/2)
              (.row ⟨76698504228, 86531900009, (.direct 3523554676644 3468018178648), (.variance 141531155744)⟩)
              (.row ⟨76698504228, 86531900009, (.direct 5340438828596 5251428781911), (.variance 126959931299)⟩))))
        (.cut 3 (5)
          (.row ⟨76698504228, 86531900009, (.direct 824633666698 816500081227), (.variance 206695099793)⟩)
          (.row ⟨76698504228, 86531900009, (.direct 3523554676644 3468018178648), (.variance 141531155744)⟩))))

set_option maxRecDepth 16000 in
theorem CutMid1H1Pos_checked : CutMid1H1PosTree.geometryOK CutMid1H1PosPowerCache CutMid1H1PosBox true = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
