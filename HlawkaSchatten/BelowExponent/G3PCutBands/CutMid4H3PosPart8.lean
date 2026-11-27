/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid4H3PosPart8`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid4H3PosPart8Box : Box := ((⟨![27/68, 13/100, 0, -8], ![9/17, 3/20, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutMid4H3PosPart8Tree : CertTree :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cone)
          (.row ⟨103236350715, 110576703735, .zero, (.variance 308562555869)⟩))
        (.row ⟨103236350715, 110576703735, .zero, (.variance 308562555869)⟩))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (13/8)
            (.cut 3 (23/16)
              (.cut 3 (43/32)
                (.row ⟨103236350715, 110576703735, (.direct 391506126583 386192705999), (.variance 251462436274)⟩)
                (.row ⟨103236350715, 110576703735, (.direct 439055879922 431439606559), (.variance 244271998764)⟩))
              (.row ⟨103236350715, 110576703735, (.direct 488587506629 478510221568), (.variance 237737515762)⟩))
            (.cut 3 (29/16)
              (.row ⟨103236350715, 110576703735, (.direct 593382169971 577931448419), (.variance 226271291026)⟩)
              (.row ⟨103236350715, 110576703735, (.direct 705506110649 684112640091), (.variance 216495159113)⟩)))
          (.cut 3 (13/8)
            (.row ⟨103236350715, 110576703735, (.direct 391506126583 386192705999), (.variance 251462436274)⟩)
            (.row ⟨103236350715, 110576703735, (.direct 593382169971 577931448419), (.variance 226271291026)⟩)))
        (.row ⟨103236350715, 110576703735, (.direct 391506126583 386192705999), (.variance 251462436274)⟩)))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.cut 3 (11/4)
              (.cut 3 (19/8)
                (.row ⟨103236350715, 110576703735, (.direct 824633666698 796760960430), (.variance 208023898692)⟩)
                (.row ⟨103236350715, 110576703735, (.direct 1082810704946 1040475624166), (.variance 193982765963)⟩))
              (.row ⟨103236350715, 110576703735, (.direct 1366046989981 1307384670875), (.variance 182723553960)⟩))
            (.cut 3 (17/4)
              (.row ⟨103236350715, 110576703735, (.direct 2002014560937 1905611530950), (.variance 165556727320)⟩)
              (.row ⟨103236350715, 110576703735, (.direct 2723407729414 2583102260960), (.variance 152881102591)⟩)))
          (.cut 3 (13/2)
            (.row ⟨103236350715, 110576703735, (.direct 3523554676644 3333736048298), (.variance 143002265646)⟩)
            (.row ⟨103236350715, 110576703735, (.direct 5340438828596 5036328307494), (.variance 128357981906)⟩)))
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.cut 3 (11/4)
              (.cut 3 (19/8)
                (.row ⟨103236350715, 110576703735, (.direct 824633666698 796760960430), (.variance 208023898692)⟩)
                (.row ⟨103236350715, 110576703735, (.direct 1082810704946 1040475624166), (.variance 193982765963)⟩))
              (.row ⟨103236350715, 110576703735, (.direct 1366046989981 1307384670875), (.variance 182723553960)⟩))
            (.cut 3 (17/4)
              (.row ⟨103236350715, 110576703735, (.direct 2002014560937 1905611530950), (.variance 165556727320)⟩)
              (.row ⟨103236350715, 110576703735, (.direct 2723407729414 2583102260960), (.variance 152881102591)⟩)))
          (.cut 3 (13/2)
            (.cut 3 (23/4)
              (.row ⟨103236350715, 110576703735, (.direct 3523554676644 3333736048298), (.variance 143002265646)⟩)
              (.row ⟨103236350715, 110576703735, (.direct 4397286982341 4152758077611), (.variance 135008299745)⟩))
            (.row ⟨103236350715, 110576703735, (.direct 5340438828596 5036328307494), (.variance 128357981906)⟩))))
      (.cut 3 (5)
        (.cut 3 (7/2)
          (.row ⟨103236350715, 110576703735, (.direct 824633666698 796760960430), (.variance 208023898692)⟩)
          (.row ⟨103236350715, 110576703735, (.direct 2002014560937 1905611530950), (.variance 165556727320)⟩))
        (.cut 3 (13/2)
          (.row ⟨103236350715, 110576703735, (.direct 3523554676644 3333736048298), (.variance 143002265646)⟩)
          (.row ⟨103236350715, 110576703735, (.direct 5340438828596 5036328307494), (.variance 128357981906)⟩))))

set_option maxRecDepth 16000 in
theorem CutMid4H3PosPart8_checked : CutMid4H3PosPart8Tree.commonOK CutMid4H3PosPart8Box true = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
