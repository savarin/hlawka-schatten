/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H5PosRest`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H5PosRestBox : Box := ⟨![45/136, 19/100, 0, -8], ![27/68, 1/5, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop4H5PosRestTree : RatioRemainder :=
  .cut 3 (3/4)
    (.cut 3 (-1/4)
      (.cut 3 (-2)
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 3 (-5)
              (.original (.row ⟨123862991199, 126950446638, (.direct 3523554676644 3232530974750), (.chord .universal 0 10180665226)⟩))
              (.original (.row ⟨123862991199, 126950446638, (.direct 824633666698 739832218923), (.variance 212101443382)⟩)))
            (.cut 3 (-5)
              (.original (.row ⟨123862991199, 126950446638, (.direct 3523554676644 3232530974750), (.variance 144161328916)⟩))
              (.original (.row ⟨123862991199, 126950446638, (.direct 824633666698 739832218923), (.variance 212101443382)⟩))))
          (.original (.row ⟨123862991199, 126950446638, (.direct 824633666698 739832218923), (.variance 212101443382)⟩)))
        (.cut 2 (1/2)
          (.original (.row ⟨123862991199, 126950446638, (.direct 30541785600 20575579627), (.variance 541923703492)⟩))
          (.original (.row ⟨123862991199, 126950446638, (.direct 30541785600 20575579627), (.chord .universal 91625974997 274877906944)⟩))))
      (.cut 3 (1/4)
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 3 (0)
              (.original (.row ⟨123862991199, 126950446638, (.direct 0 1953895586), (.chord .universal 0 10180665226)⟩))
              (.cut 3 (1/8)
                (.original (.row ⟨123862991199, 126950446638, (.direct 10180561190 15596541189), (.chord .universal 0 10180665226)⟩))
                (.original (.row ⟨123862991199, 126950446638, (.direct 30541785600 37192598870), (.variance 595288579784)⟩))))
            (.cut 2 (5/16)
              (.cut 3 (0)
                (.cut 1 (39/200)
                  (.original (.row ⟨123862991199, 125417011706, (.direct 0 1868807959), (.chord .universal 10180665226 43500686443)⟩))
                  (.original (.row ⟨125417011705, 126950446638, (.direct 0 1953895586), (.chord .universal 10180665226 43500686443)⟩)))
                (.cut 3 (1/8)
                  (.cut 2 (7/32)
                    (.cut 3 (1/16)
                      (.covered)
                      (.original (.row ⟨123862991199, 126950446638, (.direct 10180561190 15596541189), (.chord (.midpoint ⟨383862410313, 179951664783, 203878912534, 339790628415, 235091255011, 134351350819⟩) 10180665226 24716235638)⟩)))
                    (.covered))
                  (.cut 2 (7/32)
                    (.original (.row ⟨123862991199, 126950446638, (.direct 30541785600 37192598870), (.variance 595288579784)⟩))
                    (.original (.row ⟨123862991199, 126950446638, (.direct 30541785600 37192598870), (.chord (.midpoint ⟨353433625627, 203860831951, 216080244110, 326062888205, 246168249791, 138241069432⟩) 24716235638 43500686443)⟩)))))
              (.covered)))
          (.covered))
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 3 (1/2)
              (.original (.row ⟨123862991199, 126950446638, (.direct 91625662891 98115079534), (.variance 468976249299)⟩))
              (.original (.row ⟨123862991199, 126950446638, (.direct 174227225485 178305844413), (.variance 361346797580)⟩)))
            (.cut 3 (1/2)
              (.cut 3 (3/8)
                (.cut 0 (99/272)
                  (.original (.row ⟨123862991199, 126950446638, (.direct 58075547817 64401238232), (.variance 468976249299)⟩))
                  (.original (.row ⟨123862991199, 126950446638, (.direct 58075547817 64988177306), (.variance 467151627504)⟩)))
                (.original (.row ⟨123862991199, 126950446638, (.direct 91625662891 98115079534), (.variance 403449593146)⟩)))
              (.original (.row ⟨123862991199, 126950446638, (.direct 174227225485 178305844413), (.variance 361346797580)⟩))))
          (.cut 3 (1/2)
            (.cut 3 (3/8)
              (.covered)
              (.original (.row ⟨123862991199, 126950446638, (.direct 91625662891 98115079534), (.variance 403449593146)⟩)))
            (.original (.row ⟨123862991199, 126950446638, (.direct 174227225485 178305844413), (.variance 361346797580)⟩))))))
    (.cut 3 (2)
      (.cut 3 (5/4)
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.original (.cone))
            (.original (.row ⟨123862991199, 126950446638, .zero, (.variance 308261443908)⟩)))
          (.original (.row ⟨123862991199, 126950446638, .zero, (.variance 308261443908)⟩)))
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 3 (13/8)
              (.cut 3 (23/16)
                (.cut 3 (43/32)
                  (.original (.row ⟨123862991199, 126950446638, (.direct 391506126583 386045481877), (.variance 251487544411)⟩))
                  (.original (.row ⟨123862991199, 126950446638, (.direct 439055879922 431228728543), (.variance 244303272583)⟩)))
                (.original (.row ⟨123862991199, 126950446638, (.direct 488587506629 478231380494), (.variance 237773805593)⟩)))
              (.original (.row ⟨123862991199, 126950446638, (.direct 593382169971 577504372977), (.variance 226315095882)⟩)))
            (.cut 3 (13/8)
              (.cut 3 (23/16)
                (.original (.row ⟨123862991199, 126950446638, (.direct 391506126583 386045481877), (.variance 251487544411)⟩))
                (.original (.row ⟨123862991199, 126950446638, (.direct 488587506629 478231380494), (.variance 237773805593)⟩)))
              (.cut 3 (29/16)
                (.original (.row ⟨123862991199, 126950446638, (.direct 593382169971 577504372977), (.variance 226315095882)⟩))
                (.original (.row ⟨123862991199, 126950446638, (.direct 705506110649 683521795909), (.variance 216544147401)⟩)))))
          (.original (.row ⟨123862991199, 126950446638, (.direct 391506126583 386045481877), (.variance 251487544411)⟩))))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (5)
            (.cut 3 (7/2)
              (.cut 3 (11/4)
                (.cut 3 (19/8)
                  (.original (.row ⟨123862991199, 126950446638, (.direct 824633666698 795991698633), (.variance 208076522951)⟩))
                  (.original (.row ⟨123862991199, 126950446638, (.direct 1082810704946 1039308435082), (.variance 194039787900)⟩)))
                (.original (.row ⟨123862991199, 126950446638, (.direct 1366046989981 1305768568652), (.variance 182782745665)⟩)))
              (.original (.row ⟨123862991199, 126950446638, (.direct 2002014560937 1902958453637), (.variance 165617136935)⟩)))
            (.cut 3 (13/2)
              (.original (.row ⟨123862991199, 126950446638, (.direct 3523554676644 3328518067527), (.variance 143060934194)⟩))
              (.original (.row ⟨123862991199, 126950446638, (.direct 5340438828596 5027973642345), (.variance 128413797398)⟩))))
          (.cut 3 (5)
            (.cut 3 (7/2)
              (.cut 3 (11/4)
                (.cut 3 (19/8)
                  (.original (.row ⟨123862991199, 126950446638, (.direct 824633666698 795991698633), (.variance 208076522951)⟩))
                  (.original (.row ⟨123862991199, 126950446638, (.direct 1082810704946 1039308435082), (.variance 194039787900)⟩)))
                (.original (.row ⟨123862991199, 126950446638, (.direct 1366046989981 1305768568652), (.variance 182782745665)⟩)))
              (.cut 3 (17/4)
                (.original (.row ⟨123862991199, 126950446638, (.direct 2002014560937 1902958453637), (.variance 165617136935)⟩))
                (.original (.row ⟨123862991199, 126950446638, (.direct 2723407729414 2579243550353), (.variance 152940961113)⟩))))
            (.cut 3 (13/2)
              (.original (.row ⟨123862991199, 126950446638, (.direct 3523554676644 3328518067527), (.variance 143060934194)⟩))
              (.original (.row ⟨123862991199, 126950446638, (.direct 5340438828596 5027973642345), (.variance 128413797398)⟩)))))
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.original (.row ⟨123862991199, 126950446638, (.direct 824633666698 795991698633), (.variance 208076522951)⟩))
            (.original (.row ⟨123862991199, 126950446638, (.direct 2002014560937 1902958453637), (.variance 165617136935)⟩)))
          (.cut 3 (13/2)
            (.original (.row ⟨123862991199, 126950446638, (.direct 3523554676644 3328518067527), (.variance 143060934194)⟩))
            (.original (.row ⟨123862991199, 126950446638, (.direct 5340438828596 5027973642345), (.variance 128413797398)⟩))))))

set_option maxRecDepth 16000 in
theorem CutTop4H5PosRest_ok : CutTop4H5PosRestTree.ok CutTop4H5PosRestBox true (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
