/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H1PosPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H1Pos`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H1PosBox : Box := ⟨![9/136, 4/25, 0, -8], ![9/68, 17/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop1H1PosTree : CertTree :=
  .cut 3 (3/4)
    (.cut 3 (-1/4)
      (.cut 3 (-2)
        (.row ⟨114055813619, 117423580140, (.direct 824633666698 800661924032), (.variance 207758021928)⟩)
        (.row ⟨114055813619, 117423580140, (.direct 30541785600 27620070543), (.variance 501710804855)⟩))
      (.cut 3 (1/4)
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.row ⟨114055813619, 117423580140, (.direct 30541785600 32346697175), (.chord .universal 0 10180665226)⟩)
            (.cut 2 (5/16)
              (.cut 2 (7/32)
                (.row ⟨114055813619, 117423580140, (.direct 30541785600 32346697175), (.chord .universal 10180665226 24716235638)⟩)
                (.row ⟨114055813619, 117423580140, (.direct 30541785600 32346697175), (.chord .universal 24716235638 43500686443)⟩))
              (.row ⟨114055813619, 117423580140, (.direct 30541785600 32346697175), (.chord .universal 43500686443 91625974997)⟩)))
          (.row ⟨114055813619, 117423580140, (.direct 30541785600 32346697175), (.chord .universal 91625974997 274877906944)⟩))
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.row ⟨114055813619, 117423580140, (.direct 174227225485 175360565312), (.variance 485212758741)⟩)
            (.cut 3 (1/2)
              (.row ⟨114055813619, 117423580140, (.direct 91625662891 93417922671), (.variance 485212758741)⟩)
              (.row ⟨114055813619, 117423580140, (.direct 174227225485 175360565312), (.variance 365632117406)⟩)))
          (.row ⟨114055813619, 117423580140, (.direct 174227225485 175360565312), (.chord .universal 91625974997 274877906944)⟩))))
    (.cut 3 (2)
      (.cut 3 (5/4)
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cone)
            (.row ⟨114055813619, 117423580140, .zero, (.variance 309491477116)⟩))
          (.row ⟨114055813619, 117423580140, .zero, (.variance 309491477116)⟩))
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 3 (13/8)
              (.cut 3 (23/16)
                (.cut 3 (43/32)
                  (.row ⟨114055813619, 117423580140, (.direct 391506126583 389981772339), (.variance 250820360402)⟩)
                  (.row ⟨114055813619, 117423580140, (.direct 439055879922 436869780606), (.variance 243473269541)⟩))
                (.row ⟨114055813619, 117423580140, (.direct 488587506629 485693773380), (.variance 236811707535)⟩))
              (.row ⟨114055813619, 117423580140, (.direct 593382169971 588942261999), (.variance 225155822852)⟩))
            (.cut 3 (13/8)
              (.row ⟨114055813619, 117423580140, (.direct 391506126583 389981772339), (.variance 250820360402)⟩)
              (.row ⟨114055813619, 117423580140, (.direct 593382169971 588942261999), (.variance 225155822852)⟩)))
          (.row ⟨114055813619, 117423580140, (.direct 391506126583 389981772339), (.variance 250820360402)⟩)))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (5)
            (.cut 3 (7/2)
              (.cut 3 (11/4)
                (.cut 3 (19/8)
                  (.row ⟨114055813619, 117423580140, (.direct 824633666698 816615964804), (.variance 206687418772)⟩)
                  (.row ⟨114055813619, 117423580140, (.direct 1082810704946 1070624311711), (.variance 192537255970)⟩))
                (.row ⟨114055813619, 117423580140, (.direct 1366046989981 1349152142078), (.variance 181225050605)⟩))
              (.row ⟨114055813619, 117423580140, (.direct 2002014560937 1974231336830), (.variance 164030182821)⟩))
            (.row ⟨114055813619, 117423580140, (.direct 3523554676644 3468808697583), (.variance 141522709133)⟩))
          (.cut 3 (5)
            (.cut 3 (7/2)
              (.cut 3 (11/4)
                (.cut 3 (19/8)
                  (.row ⟨114055813619, 117423580140, (.direct 824633666698 816615964804), (.variance 206687418772)⟩)
                  (.row ⟨114055813619, 117423580140, (.direct 1082810704946 1070624311711), (.variance 192537255970)⟩))
                (.row ⟨114055813619, 117423580140, (.direct 1366046989981 1349152142078), (.variance 181225050605)⟩))
              (.cut 3 (17/4)
                (.row ⟨114055813619, 117423580140, (.direct 2002014560937 1974231336830), (.variance 164030182821)⟩)
                (.row ⟨114055813619, 117423580140, (.direct 2723407729414 2682954185215), (.variance 151370278311)⟩)))
            (.cut 3 (13/2)
              (.row ⟨114055813619, 117423580140, (.direct 3523554676644 3468808697583), (.variance 141522709133)⟩)
              (.row ⟨114055813619, 117423580140, (.direct 5340438828596 5252695620869), (.variance 126951912552)⟩))))
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.row ⟨114055813619, 117423580140, (.direct 824633666698 816615964804), (.variance 206687418772)⟩)
            (.row ⟨114055813619, 117423580140, (.direct 2002014560937 1974231336830), (.variance 164030182821)⟩))
          (.cut 3 (13/2)
            (.row ⟨114055813619, 117423580140, (.direct 3523554676644 3468808697583), (.variance 141522709133)⟩)
            (.row ⟨114055813619, 117423580140, (.direct 5340438828596 5252695620869), (.variance 126951912552)⟩)))))

set_option maxRecDepth 16000 in
theorem CutTop1H1Pos_checked : CutTop1H1PosTree.geometryOK CutTop1H1PosPowerCache CutTop1H1PosBox true = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
