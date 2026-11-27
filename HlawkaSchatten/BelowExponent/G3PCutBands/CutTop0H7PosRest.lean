/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H7PosPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H7PosRest`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H7PosRestBox : Box := ⟨![63/136, 3/20, 0, -8], ![9/17, 4/25, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop0H7PosRestTree : RatioRemainder :=
  .cut 3 (3/4)
    (.cut 3 (-1/4)
      (.cut 3 (-2)
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 3 (-5)
              (.original (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3220087465821), (.chord .universal 0 10180665226)⟩))
              (.original (.row ⟨110576703734, 114055813620, (.direct 824633666698 736222505013), (.variance 212373265587)⟩)))
            (.cut 3 (-5)
              (.original (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3220087465821), (.variance 144306998036)⟩))
              (.original (.row ⟨110576703734, 114055813620, (.direct 824633666698 736222505013), (.variance 212373265587)⟩))))
          (.original (.row ⟨110576703734, 114055813620, (.direct 824633666698 736222505013), (.variance 212373265587)⟩)))
        (.cut 2 (1/2)
          (.original (.row ⟨110576703734, 114055813620, (.direct 30541785600 20175736112), (.variance 544715702917)⟩))
          (.cut 3 (-9/8)
            (.original (.row ⟨110576703734, 114055813620, (.direct 331294831298 286810578091), (.variance 271836144897)⟩))
            (.original (.row ⟨110576703734, 114055813620, (.direct 30541785600 20175736112), (.chord .universal 91625974997 274877906944)⟩)))))
      (.cut 3 (1/4)
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 3 (0)
              (.original (.row ⟨110576703734, 114055813620, (.direct 0 2090243372), (.chord .universal 0 10180665226)⟩))
              (.cut 3 (1/8)
                (.original (.row ⟨110576703734, 114055813620, (.direct 10180561190 15850900736), (.chord .universal 0 10180665226)⟩))
                (.original (.row ⟨110576703734, 114055813620, (.direct 30541785600 37492614599), (.variance 591400553537)⟩))))
            (.cut 2 (5/16)
              (.cut 3 (0)
                (.cut 1 (31/200)
                  (.cut 1 (61/400)
                    (.cut 2 (7/32)
                      (.original (.row ⟨110576703734, 111457516073, (.direct 0 1924642785), (.chord .universal 10180665226 24716235638)⟩))
                      (.covered))
                    (.cut 2 (7/32)
                      (.original (.row ⟨111457516072, 112330851340, (.direct 0 1979133040), (.chord .universal 10180665226 24716235638)⟩))
                      (.covered)))
                  (.cut 1 (63/400)
                    (.cut 2 (7/32)
                      (.original (.row ⟨112330851339, 113196892094, (.direct 0 2034332859), (.chord .universal 10180665226 24716235638)⟩))
                      (.covered))
                    (.cut 3 (-1/8)
                      (.original (.row ⟨113196892093, 114055813620, (.direct 10180561190 4360376299), (.chord .universal 10180665226 43500686443)⟩))
                      (.covered))))
                (.cut 3 (1/8)
                  (.cut 3 (1/16)
                    (.covered)
                    (.cut 2 (7/32)
                      (.original (.row ⟨110576703734, 114055813620, (.direct 10180561190 15850900736), (.chord (.midpoint ⟨315145076036, 236679580085, 219042598182, 322927968122, 260110496674, 90022048575⟩) 10180665226 24716235638)⟩))
                      (.covered)))
                  (.cut 2 (7/32)
                    (.original (.row ⟨110576703734, 114055813620, (.direct 30541785600 37492614599), (.variance 591400553537)⟩))
                    (.original (.row ⟨110576703734, 114055813620, (.direct 30541785600 37492614599), (.chord (.midpoint ⟨288770863872, 261239413789, 229900031555, 312031546537, 269763334740, 97458385769⟩) 24716235638 43500686443)⟩)))))
              (.covered)))
          (.covered))
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 3 (1/2)
              (.original (.row ⟨110576703734, 114055813620, (.direct 91625662891 98400919551), (.variance 467489801186)⟩))
              (.original (.row ⟨110576703734, 114055813620, (.direct 174227225485 178483954142), (.variance 360937975571)⟩)))
            (.original (.row ⟨110576703734, 114055813620, (.direct 174227225485 178483954142), (.variance 467489801186)⟩)))
          (.original (.row ⟨110576703734, 114055813620, (.direct 174227225485 178483954142), (.variance 467489801186)⟩)))))
    (.cut 3 (2)
      (.cut 3 (5/4)
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.original (.cone))
            (.original (.row ⟨110576703734, 114055813620, .zero, (.variance 308142377461)⟩)))
          (.original (.row ⟨110576703734, 114055813620, .zero, (.variance 308142377461)⟩)))
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 3 (13/8)
              (.cut 3 (23/16)
                (.original (.row ⟨110576703734, 114055813620, (.direct 391506126583 385808686546), (.variance 251527953703)⟩))
                (.original (.row ⟨110576703734, 114055813620, (.direct 488587506629 477782935957), (.variance 237832224538)⟩)))
              (.original (.row ⟨110576703734, 114055813620, (.direct 593382169971 576817583100), (.variance 226385625275)⟩)))
            (.cut 3 (13/8)
              (.original (.row ⟨110576703734, 114055813620, (.direct 391506126583 385808686546), (.variance 251527953703)⟩))
              (.original (.row ⟨110576703734, 114055813620, (.direct 593382169971 576817583100), (.variance 226385625275)⟩))))
          (.original (.row ⟨110576703734, 114055813620, (.direct 391506126583 385808686546), (.variance 251527953703)⟩))))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (5)
            (.cut 3 (7/2)
              (.cut 3 (11/4)
                (.cut 3 (19/8)
                  (.original (.row ⟨110576703734, 114055813620, (.direct 824633666698 794754766079), (.variance 208161274693)⟩))
                  (.original (.row ⟨110576703734, 114055813620, (.direct 1082810704946 1037431797835), (.variance 194131638884)⟩)))
                (.original (.row ⟨110576703734, 114055813620, (.direct 1366046989981 1303170300422), (.variance 182878104439)⟩)))
              (.original (.row ⟨110576703734, 114055813620, (.direct 2002014560937 1898693322940), (.variance 165714475522)⟩)))
            (.cut 3 (13/2)
              (.original (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3320130256209), (.variance 143155486480)⟩))
              (.original (.row ⟨110576703734, 114055813620, (.direct 5340438828596 5014544274079), (.variance 128503761444)⟩))))
          (.cut 3 (5)
            (.cut 3 (7/2)
              (.cut 3 (11/4)
                (.cut 3 (19/8)
                  (.original (.row ⟨110576703734, 114055813620, (.direct 824633666698 794754766079), (.variance 208161274693)⟩))
                  (.original (.row ⟨110576703734, 114055813620, (.direct 1082810704946 1037431797835), (.variance 194131638884)⟩)))
                (.original (.row ⟨110576703734, 114055813620, (.direct 1366046989981 1303170300422), (.variance 182878104439)⟩)))
              (.cut 3 (17/4)
                (.original (.row ⟨110576703734, 114055813620, (.direct 2002014560937 1898693322940), (.variance 165714475522)⟩))
                (.original (.row ⟨110576703734, 114055813620, (.direct 2723407729414 2573040527915), (.variance 153037423160)⟩))))
            (.cut 3 (13/2)
              (.original (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3320130256209), (.variance 143155486480)⟩))
              (.original (.row ⟨110576703734, 114055813620, (.direct 5340438828596 5014544274079), (.variance 128503761444)⟩)))))
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.original (.row ⟨110576703734, 114055813620, (.direct 824633666698 794754766079), (.variance 208161274693)⟩))
            (.original (.row ⟨110576703734, 114055813620, (.direct 2002014560937 1898693322940), (.variance 165714475522)⟩)))
          (.cut 3 (13/2)
            (.original (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3320130256209), (.variance 143155486480)⟩))
            (.original (.row ⟨110576703734, 114055813620, (.direct 5340438828596 5014544274079), (.variance 128503761444)⟩))))))

set_option maxRecDepth 16000 in
theorem CutTop0H7PosRest_ok : CutTop0H7PosRestTree.geometryOK CutTop0H7PosPowerCache CutTop0H7PosRestBox true (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
