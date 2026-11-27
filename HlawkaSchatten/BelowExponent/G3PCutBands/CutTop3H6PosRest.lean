/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H6PosRest`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H6PosRestBox : Box := ⟨![27/68, 9/50, 0, -8], ![63/136, 19/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop3H6PosRestTree : RatioRemainder :=
  .cut 3 (3/4)
    (.cut 3 (-1/4)
      (.cut 3 (-2)
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 3 (-5)
              (.original (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3203306558382), (.chord .universal 0 10180665226)⟩))
              (.original (.row ⟨120689819474, 123862991200, (.direct 824633666698 731356754041), (.variance 212742344158)⟩)))
            (.cut 3 (-5)
              (.original (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3203306558382), (.variance 144504571388)⟩))
              (.original (.row ⟨120689819474, 123862991200, (.direct 824633666698 731356754041), (.variance 212742344158)⟩))))
          (.original (.row ⟨120689819474, 123862991200, (.direct 824633666698 731356754041), (.variance 212742344158)⟩)))
        (.cut 2 (1/2)
          (.original (.row ⟨120689819474, 123862991200, (.direct 30541785600 19640228804), (.variance 548566345757)⟩))
          (.cut 3 (-9/8)
            (.original (.row ⟨120689819474, 123862991200, (.direct 331294831298 284377627551), (.variance 272443217095)⟩))
            (.original (.row ⟨120689819474, 123862991200, (.direct 30541785600 19640228804), (.chord .universal 91625974997 274877906944)⟩)))))
      (.cut 3 (1/4)
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 3 (0)
              (.original (.row ⟨120689819474, 123862991200, (.direct 0 2279757842), (.chord .universal 0 10180665226)⟩))
              (.cut 3 (1/8)
                (.original (.row ⟨120689819474, 123862991200, (.direct 10180561190 16196901941), (.chord .universal 0 10180665226)⟩))
                (.original (.row ⟨120689819474, 123862991200, (.direct 30541785600 37899295126), (.variance 589089701317)⟩))))
            (.cut 2 (5/16)
              (.cut 3 (0)
                (.cut 1 (37/200)
                  (.cut 1 (73/400)
                    (.cut 3 (-1/8)
                      (.original (.row ⟨120689819474, 121491533044, (.direct 10180561190 4309628555), (.chord .universal 10180665226 43500686443)⟩))
                      (.covered))
                    (.cut 3 (-1/8)
                      (.original (.row ⟨121491533043, 122287555846, (.direct 10180561190 4235619316), (.chord .universal 10180665226 43500686443)⟩))
                      (.covered)))
                  (.cut 1 (3/16)
                    (.cut 3 (-1/8)
                      (.original (.row ⟨122287555845, 123078004368, (.direct 10180561190 4161882103), (.chord .universal 10180665226 43500686443)⟩))
                      (.covered))
                    (.cut 3 (-1/8)
                      (.original (.row ⟨123078004367, 123862991200, (.direct 10180561190 4088422227), (.chord .universal 10180665226 43500686443)⟩))
                      (.covered))))
                (.cut 3 (1/8)
                  (.cut 3 (1/16)
                    (.covered)
                    (.cut 2 (7/32)
                      (.original (.row ⟨120689819474, 123862991200, (.direct 10180561190 16196901941), (.chord (.midpoint ⟨342533029018, 212881570084, 214137474451, 328159022247, 250133679364, 106076723592⟩) 10180665226 24716235638)⟩))
                      (.covered)))
                  (.cut 2 (7/32)
                    (.original (.row ⟨120689819474, 123862991200, (.direct 30541785600 37899295126), (.variance 589089701317)⟩))
                    (.original (.row ⟨120689819474, 123862991200, (.direct 30541785600 37899295126), (.chord (.midpoint ⟨316477603163, 235482735750, 224692511053, 317145425149, 259624268400, 115516733993⟩) 24716235638 43500686443)⟩)))))
              (.covered)))
          (.covered))
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 3 (1/2)
              (.original (.row ⟨120689819474, 123862991200, (.direct 91625662891 98787527510), (.variance 466598186830)⟩))
              (.original (.row ⟨120689819474, 123862991200, (.direct 174227225485 178724654070), (.variance 360691382611)⟩)))
            (.cut 3 (1/2)
              (.cut 3 (3/8)
                (.original (.row ⟨120689819474, 123862991200, (.direct 58075547817 65710749260), (.variance 466598186830)⟩))
                (.original (.row ⟨120689819474, 123862991200, (.direct 91625662891 98787527510), (.variance 402258970771)⟩)))
              (.original (.row ⟨120689819474, 123862991200, (.direct 174227225485 178724654070), (.variance 360691382611)⟩))))
          (.cut 3 (1/2)
            (.cut 3 (3/8)
              (.covered)
              (.original (.row ⟨120689819474, 123862991200, (.direct 91625662891 98787527510), (.variance 402258970771)⟩)))
            (.original (.row ⟨120689819474, 123862991200, (.direct 174227225485 178724654070), (.variance 360691382611)⟩))))))
    (.cut 3 (2)
      (.cut 3 (5/4)
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.original (.cone))
            (.original (.row ⟨120689819474, 123862991200, .zero, (.variance 308070412538)⟩)))
          (.original (.row ⟨120689819474, 123862991200, .zero, (.variance 308070412538)⟩)))
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 3 (13/8)
              (.cut 3 (23/16)
                (.cut 3 (43/32)
                  (.original (.row ⟨120689819474, 123862991200, (.direct 391506126583 385488901761), (.variance 251582574902)⟩))
                  (.original (.row ⟨120689819474, 123862991200, (.direct 439055879922 430431580927), (.variance 244421666466)⟩)))
                (.original (.row ⟨120689819474, 123862991200, (.direct 488587506629 477177410769), (.variance 237911216285)⟩)))
              (.original (.row ⟨120689819474, 123862991200, (.direct 593382169971 575890326604), (.variance 226481017508)⟩)))
            (.cut 3 (13/8)
              (.cut 3 (23/16)
                (.original (.row ⟨120689819474, 123862991200, (.direct 391506126583 385488901761), (.variance 251582574902)⟩))
                (.original (.row ⟨120689819474, 123862991200, (.direct 488587506629 477177410769), (.variance 237911216285)⟩)))
              (.original (.row ⟨120689819474, 123862991200, (.direct 593382169971 575890326604), (.variance 226481017508)⟩))))
          (.original (.row ⟨120689819474, 123862991200, (.direct 391506126583 385488901761), (.variance 251582574902)⟩))))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (5)
            (.cut 3 (7/2)
              (.cut 3 (11/4)
                (.cut 3 (19/8)
                  (.original (.row ⟨120689819474, 123862991200, (.direct 824633666698 793085009592), (.variance 208275946890)⟩))
                  (.original (.row ⟨120689819474, 123862991200, (.direct 1082810704946 1034898770427), (.variance 194255949547)⟩)))
                (.original (.row ⟨120689819474, 123862991200, (.direct 1366046989981 1299663518777), (.variance 183007187562)⟩)))
              (.original (.row ⟨120689819474, 123862991200, (.direct 2002014560937 1892937472114), (.variance 165846273544)⟩)))
            (.cut 3 (13/2)
              (.original (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3308812166908), (.variance 143283549414)⟩))
              (.original (.row ⟨120689819474, 123862991200, (.direct 5340438828596 4996424554251), (.variance 128625629396)⟩))))
          (.cut 3 (5)
            (.cut 3 (7/2)
              (.cut 3 (11/4)
                (.cut 3 (19/8)
                  (.original (.row ⟨120689819474, 123862991200, (.direct 824633666698 793085009592), (.variance 208275946890)⟩))
                  (.original (.row ⟨120689819474, 123862991200, (.direct 1082810704946 1034898770427), (.variance 194255949547)⟩)))
                (.original (.row ⟨120689819474, 123862991200, (.direct 1366046989981 1299663518777), (.variance 183007187562)⟩)))
              (.cut 3 (17/4)
                (.original (.row ⟨120689819474, 123862991200, (.direct 2002014560937 1892937472114), (.variance 165846273544)⟩))
                (.original (.row ⟨120689819474, 123862991200, (.direct 2723407729414 2564670063056), (.variance 153168056864)⟩))))
            (.cut 3 (13/2)
              (.original (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3308812166908), (.variance 143283549414)⟩))
              (.original (.row ⟨120689819474, 123862991200, (.direct 5340438828596 4996424554251), (.variance 128625629396)⟩)))))
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.original (.row ⟨120689819474, 123862991200, (.direct 824633666698 793085009592), (.variance 208275946890)⟩))
            (.original (.row ⟨120689819474, 123862991200, (.direct 2002014560937 1892937472114), (.variance 165846273544)⟩)))
          (.cut 3 (13/2)
            (.original (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3308812166908), (.variance 143283549414)⟩))
            (.original (.row ⟨120689819474, 123862991200, (.direct 5340438828596 4996424554251), (.variance 128625629396)⟩))))))

set_option maxRecDepth 16000 in
theorem CutTop3H6PosRest_ok : CutTop3H6PosRestTree.ok CutTop3H6PosRestBox true (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
