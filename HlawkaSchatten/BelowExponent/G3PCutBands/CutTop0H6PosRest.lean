/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H6PosPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H6PosRest`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H6PosRestBox : Box := ⟨![27/68, 3/20, 0, -8], ![63/136, 4/25, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop0H6PosRestTree : RatioRemainder :=
  .cut 3 (3/4)
    (.cut 3 (-1/4)
      (.cut 3 (-2)
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 3 (-5)
              (.original (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3257471086893), (.chord .universal 0 10180665226)⟩))
              (.original (.row ⟨110576703734, 114055813620, (.direct 824633666698 747071174114), (.variance 211561337848)⟩)))
            (.cut 3 (-5)
              (.original (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3257471086893), (.variance 143871488120)⟩))
              (.original (.row ⟨110576703734, 114055813620, (.direct 824633666698 747071174114), (.variance 211561337848)⟩))))
          (.original (.row ⟨110576703734, 114055813620, (.direct 824633666698 747071174114), (.variance 211561337848)⟩)))
        (.cut 2 (1/2)
          (.original (.row ⟨110576703734, 114055813620, (.direct 30541785600 21383917631), (.variance 536482890766)⟩))
          (.original (.row ⟨110576703734, 114055813620, (.direct 30541785600 21383917631), (.chord .universal 91625974997 274877906944)⟩))))
      (.cut 3 (1/4)
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 3 (0)
              (.original (.row ⟨110576703734, 114055813620, (.direct 0 1691538158), (.chord .universal 0 10180665226)⟩))
              (.cut 3 (1/8)
                (.original (.row ⟨110576703734, 114055813620, (.direct 10180561190 15092394261), (.chord .universal 0 10180665226)⟩))
                (.original (.row ⟨110576703734, 114055813620, (.direct 30541785600 36595240909), (.variance 598857804696)⟩))))
            (.cut 2 (5/16)
              (.cut 2 (7/32)
                (.cut 3 (0)
                  (.original (.row ⟨110576703734, 114055813620, (.direct 0 1691538158), (.chord .universal 10180665226 24716235638)⟩))
                  (.cut 3 (1/8)
                    (.cut 3 (1/16)
                      (.covered)
                      (.original (.row ⟨110576703734, 114055813620, (.direct 10180561190 15092394261), (.chord (.midpoint ⟨356972241902, 200985426749, 208259061205, 334704438194, 244881033269, 123532523524⟩) 10180665226 24716235638)⟩)))
                    (.original (.row ⟨110576703734, 114055813620, (.direct 30541785600 36595240909), (.variance 598857804696)⟩))))
                (.cut 3 (0)
                  (.covered)
                  (.cut 3 (1/8)
                    (.covered)
                    (.original (.row ⟨110576703734, 114055813620, (.direct 30541785600 36595240909), (.chord (.midpoint ⟨325617898175, 227382556006, 220995472816, 320900680789, 256291779819, 123817247712⟩) 24716235638 43500686443)⟩)))))
              (.covered)))
          (.covered))
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 3 (1/2)
              (.original (.row ⟨110576703734, 114055813620, (.direct 91625662891 97544320766), (.variance 470325817160)⟩))
              (.original (.row ⟨110576703734, 114055813620, (.direct 174227225485 177949821888), (.variance 361715515744)⟩)))
            (.original (.row ⟨110576703734, 114055813620, (.direct 174227225485 177949821888), (.variance 470325817160)⟩)))
          (.original (.row ⟨110576703734, 114055813620, (.direct 174227225485 177949821888), (.variance 470325817160)⟩)))))
    (.cut 3 (2)
      (.cut 3 (5/4)
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.original (.cone))
            (.original (.row ⟨110576703734, 114055813620, .zero, (.variance 308368571105)⟩)))
          (.original (.row ⟨110576703734, 114055813620, .zero, (.variance 308368571105)⟩)))
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 3 (13/8)
              (.cut 3 (23/16)
                (.original (.row ⟨110576703734, 114055813620, (.direct 391506126583 386519233386), (.variance 251406792182)⟩))
                (.original (.row ⟨110576703734, 114055813620, (.direct 488587506629 479128735291), (.variance 237657114319)⟩)))
              (.original (.row ⟨110576703734, 114055813620, (.direct 593382169971 578878857361), (.variance 226174261541)⟩)))
            (.cut 3 (13/8)
              (.original (.row ⟨110576703734, 114055813620, (.direct 391506126583 386519233386), (.variance 251406792182)⟩))
              (.original (.row ⟨110576703734, 114055813620, (.direct 593382169971 578878857361), (.variance 226174261541)⟩))))
          (.original (.row ⟨110576703734, 114055813620, (.direct 391506126583 386519233386), (.variance 251406792182)⟩))))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (5)
            (.cut 3 (7/2)
              (.cut 3 (11/4)
                (.cut 3 (19/8)
                  (.original (.row ⟨110576703734, 114055813620, (.direct 824633666698 798467692891), (.variance 207907371786)⟩))
                  (.original (.row ⟨110576703734, 114055813620, (.direct 1082810704946 1043065463365), (.variance 193856529526)⟩)))
                (.original (.row ⟨110576703734, 114055813620, (.direct 1366046989981 1310970832784), (.variance 182592535552)⟩)))
              (.original (.row ⟨110576703734, 114055813620, (.direct 2002014560937 1911499306169), (.variance 165423043082)⟩)))
            (.cut 3 (13/2)
              (.original (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3345317110211), (.variance 142872466558)⟩))
              (.original (.row ⟨110576703734, 114055813620, (.direct 5340438828596 5054872123476), (.variance 128234511561)⟩))))
          (.cut 3 (5)
            (.cut 3 (7/2)
              (.cut 3 (11/4)
                (.cut 3 (19/8)
                  (.original (.row ⟨110576703734, 114055813620, (.direct 824633666698 798467692891), (.variance 207907371786)⟩))
                  (.original (.row ⟨110576703734, 114055813620, (.direct 1082810704946 1043065463365), (.variance 193856529526)⟩)))
                (.original (.row ⟨110576703734, 114055813620, (.direct 1366046989981 1310970832784), (.variance 182592535552)⟩)))
              (.cut 3 (17/4)
                (.original (.row ⟨110576703734, 114055813620, (.direct 2002014560937 1911499306169), (.variance 165423043082)⟩))
                (.original (.row ⟨110576703734, 114055813620, (.direct 2723407729414 2591666124042), (.variance 152748657218)⟩))))
            (.cut 3 (13/2)
              (.original (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3345317110211), (.variance 142872466558)⟩))
              (.original (.row ⟨110576703734, 114055813620, (.direct 5340438828596 5054872123476), (.variance 128234511561)⟩)))))
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.original (.row ⟨110576703734, 114055813620, (.direct 824633666698 798467692891), (.variance 207907371786)⟩))
            (.original (.row ⟨110576703734, 114055813620, (.direct 2002014560937 1911499306169), (.variance 165423043082)⟩)))
          (.cut 3 (13/2)
            (.original (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3345317110211), (.variance 142872466558)⟩))
            (.original (.row ⟨110576703734, 114055813620, (.direct 5340438828596 5054872123476), (.variance 128234511561)⟩))))))

set_option maxRecDepth 16000 in
theorem CutTop0H6PosRest_ok : CutTop0H6PosRestTree.geometryOK CutTop0H6PosPowerCache CutTop0H6PosRestBox true (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
