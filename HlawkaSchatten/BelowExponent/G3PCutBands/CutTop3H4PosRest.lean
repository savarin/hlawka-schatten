/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H4PosRest`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H4PosRestBox : Box := ⟨![9/34, 9/50, 0, -8], ![45/136, 19/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop3H4PosRestTree : RatioRemainder :=
  .cut 3 (3/4)
    (.cut 3 (-1/4)
      (.cut 3 (-2)
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 3 (-5)
              (.original (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3293662760743), (.chord .universal 0 10180665226)⟩))
              (.original (.row ⟨120689819474, 123862991200, (.direct 824633666698 757585599369), (.variance 210788498917)⟩)))
            (.cut 3 (-5)
              (.original (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3293662760743), (.variance 143455831009)⟩))
              (.original (.row ⟨120689819474, 123862991200, (.direct 824633666698 757585599369), (.variance 210788498917)⟩))))
          (.original (.row ⟨120689819474, 123862991200, (.direct 824633666698 757585599369), (.variance 210788498917)⟩)))
        (.cut 2 (1/2)
          (.original (.row ⟨120689819474, 123862991200, (.direct 30541785600 22573083161), (.variance 528933691388)⟩))
          (.original (.row ⟨120689819474, 123862991200, (.direct 30541785600 22573083161), (.chord .universal 91625974997 274877906944)⟩))))
      (.cut 3 (1/4)
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.original (.row ⟨120689819474, 123862991200, (.direct 30541785600 35737713343), (.chord .universal 0 10180665226)⟩))
            (.cut 2 (5/16)
              (.cut 2 (7/32)
                (.cut 3 (0)
                  (.original (.row ⟨120689819474, 123862991200, (.direct 0 1337461457), (.chord .universal 10180665226 24716235638)⟩))
                  (.cut 3 (1/8)
                    (.cut 3 (1/16)
                      (.covered)
                      (.original (.row ⟨120689819474, 123862991200, (.direct 10180561190 14374205462), (.chord (.midpoint ⟨435762822261, 143168944493, 189661434974, 357672285137, 216065291606, 166857788457⟩) 10180665226 24716235638)⟩)))
                    (.original (.row ⟨120689819474, 123862991200, (.direct 30541785600 35737713343), (.variance 607610715350)⟩))))
                (.cut 1 (37/200)
                  (.cut 3 (0)
                    (.covered)
                    (.cut 3 (1/8)
                      (.covered)
                      (.original (.row ⟨120689819474, 122287555846, (.direct 30541785600 35582835401), (.chord (.midpoint ⟨397475783471, 169832937497, 204998315210, 338473124104, 230123109669, 163312546143⟩) 24716235638 43500686443)⟩))))
                  (.cut 3 (0)
                    (.covered)
                    (.cut 3 (1/8)
                      (.covered)
                      (.original (.row ⟨122287555845, 123862991200, (.direct 30541785600 35737713343), (.chord (.midpoint ⟨396356287857, 170652043307, 205442222551, 337954057968, 230532116032, 162507733067⟩) 24716235638 43500686443)⟩))))))
              (.covered)))
          (.covered))
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.original (.row ⟨120689819474, 123862991200, (.direct 174227225485 177435430772), (.variance 473575507846)⟩))
            (.cut 3 (1/2)
              (.cut 3 (3/8)
                (.original (.row ⟨120689819474, 123862991200, (.direct 58075547817 63493923723), (.variance 473575507846)⟩))
                (.original (.row ⟨120689819474, 123862991200, (.direct 91625662891 96721103779), (.variance 405727892794)⟩)))
              (.original (.row ⟨120689819474, 123862991200, (.direct 174227225485 177435430772), (.variance 362593871130)⟩))))
          (.cut 3 (1/2)
            (.cut 3 (3/8)
              (.covered)
              (.original (.row ⟨120689819474, 123862991200, (.direct 91625662891 96721103779), (.variance 405727892794)⟩)))
            (.original (.row ⟨120689819474, 123862991200, (.direct 174227225485 177435430772), (.variance 362593871130)⟩))))))
    (.cut 3 (2)
      (.cut 3 (5/4)
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.original (.cone))
            (.original (.row ⟨120689819474, 123862991200, .zero, (.variance 308622781021)⟩)))
          (.original (.row ⟨120689819474, 123862991200, .zero, (.variance 308622781021)⟩)))
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 3 (13/8)
              (.cut 3 (23/16)
                (.cut 3 (43/32)
                  (.original (.row ⟨120689819474, 123862991200, (.direct 391506126583 387204720092), (.variance 251290169952)⟩))
                  (.original (.row ⟨120689819474, 123862991200, (.direct 439055879922 432889401838), (.variance 244057510802)⟩)))
                (.original (.row ⟨120689819474, 123862991200, (.direct 488587506629 480427527091), (.variance 237488708056)⟩)))
              (.original (.row ⟨120689819474, 123862991200, (.direct 593382169971 580868676106), (.variance 225971123836)⟩)))
            (.cut 3 (13/8)
              (.cut 3 (23/16)
                (.original (.row ⟨120689819474, 123862991200, (.direct 391506126583 387204720092), (.variance 251290169952)⟩))
                (.original (.row ⟨120689819474, 123862991200, (.direct 488587506629 480427527091), (.variance 237488708056)⟩)))
              (.cut 3 (29/16)
                (.original (.row ⟨120689819474, 123862991200, (.direct 593382169971 580868676106), (.variance 225971123836)⟩))
                (.original (.row ⟨120689819474, 123862991200, (.direct 705506110649 688176928483), (.variance 216159619789)⟩)))))
          (.original (.row ⟨120689819474, 123862991200, (.direct 391506126583 387204720092), (.variance 251290169952)⟩))))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (5)
            (.cut 3 (7/2)
              (.cut 3 (11/4)
                (.cut 3 (19/8)
                  (.original (.row ⟨120689819474, 123862991200, (.direct 824633666698 802053326042), (.variance 207663583789)⟩))
                  (.original (.row ⟨120689819474, 123862991200, (.direct 1082810704946 1048507468744), (.variance 193592554107)⟩)))
                (.original (.row ⟨120689819474, 123862991200, (.direct 1366046989981 1318507490228), (.variance 182318656097)⟩)))
              (.original (.row ⟨120689819474, 123862991200, (.direct 2002014560937 1923875459647), (.variance 165143724096)⟩)))
            (.cut 3 (13/2)
              (.original (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3369665913257), (.variance 142601408188)⟩))
              (.original (.row ⟨120689819474, 123862991200, (.direct 5340438828596 5093864494658), (.variance 127976743063)⟩))))
          (.cut 3 (5)
            (.cut 3 (7/2)
              (.cut 3 (11/4)
                (.cut 3 (19/8)
                  (.original (.row ⟨120689819474, 123862991200, (.direct 824633666698 802053326042), (.variance 207663583789)⟩))
                  (.original (.row ⟨120689819474, 123862991200, (.direct 1082810704946 1048507468744), (.variance 193592554107)⟩)))
                (.original (.row ⟨120689819474, 123862991200, (.direct 1366046989981 1318507490228), (.variance 182318656097)⟩)))
              (.cut 3 (17/4)
                (.original (.row ⟨120689819474, 123862991200, (.direct 2002014560937 1923875459647), (.variance 165143724096)⟩))
                (.original (.row ⟨120689819474, 123862991200, (.direct 2723407729414 2609669744395), (.variance 152472012434)⟩))))
            (.cut 3 (13/2)
              (.original (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3369665913257), (.variance 142601408188)⟩))
              (.original (.row ⟨120689819474, 123862991200, (.direct 5340438828596 5093864494658), (.variance 127976743063)⟩)))))
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.original (.row ⟨120689819474, 123862991200, (.direct 824633666698 802053326042), (.variance 207663583789)⟩))
            (.original (.row ⟨120689819474, 123862991200, (.direct 2002014560937 1923875459647), (.variance 165143724096)⟩)))
          (.cut 3 (13/2)
            (.original (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3369665913257), (.variance 142601408188)⟩))
            (.original (.row ⟨120689819474, 123862991200, (.direct 5340438828596 5093864494658), (.variance 127976743063)⟩))))))

set_option maxRecDepth 16000 in
theorem CutTop3H4PosRest_ok : CutTop3H4PosRestTree.ok CutTop3H4PosRestBox true (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
