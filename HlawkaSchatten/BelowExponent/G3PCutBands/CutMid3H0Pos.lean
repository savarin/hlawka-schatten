/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H0Pos`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H0PosBox : Box := ⟨![0, 11/100, 0, -8], ![9/68, 13/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutMid3H0PosTree : CertTree :=
  .cut 3 (3/4)
    (.cut 3 (-1/4)
      (.cut 3 (-2)
        (.row ⟨95281442640, 103236350716, (.direct 824633666698 806670557967), (.variance 207351675197)⟩)
        (.row ⟨95281442640, 103236350716, (.direct 30541785600 28345145725), (.variance 498317925345)⟩))
      (.cut 3 (1/4)
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 2 (1/16)
              (.row ⟨95281442640, 103236350716, (.direct 30541785600 31888945087), (.chord .universal 0 3393555298)⟩)
              (.row ⟨95281442640, 103236350716, (.direct 30541785600 31888945087), (.chord .universal 3393555298 10180665226)⟩))
            (.cut 2 (5/16)
              (.cut 2 (7/32)
                (.cut 1 (3/25)
                  (.row ⟨95281442640, 99345187400, (.direct 30541785600 31777915238), (.chord .universal 10180665226 24716235638)⟩)
                  (.row ⟨99345187399, 103236350716, (.direct 30541785600 31888945087), (.chord .universal 10180665226 24716235638)⟩))
                (.row ⟨95281442640, 103236350716, (.direct 30541785600 31888945087), (.chord .universal 24716235638 43500686443)⟩))
              (.row ⟨95281442640, 103236350716, (.direct 30541785600 31888945087), (.chord .universal 43500686443 91625974997)⟩)))
          (.row ⟨95281442640, 103236350716, (.direct 30541785600 31888945087), (.chord .universal 91625974997 274877906944)⟩))
        (.row ⟨95281442640, 103236350716, (.direct 174227225485 175075165445), (.variance 488671898726)⟩)))
    (.cut 3 (2)
      (.cut 3 (5/4)
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cone)
            (.row ⟨95281442640, 103236350716, .zero, (.variance 309737727641)⟩))
          (.row ⟨95281442640, 103236350716, .zero, (.variance 309737727641)⟩))
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 3 (13/8)
              (.cut 3 (23/16)
                (.cut 3 (43/32)
                  (.row ⟨95281442640, 103236350716, (.direct 391506126583 390365279556), (.variance 250755812125)⟩)
                  (.row ⟨95281442640, 103236350716, (.direct 439055879922 437419696646), (.variance 243393080885)⟩))
                (.row ⟨95281442640, 103236350716, (.direct 488587506629 486421607049), (.variance 236718869827)⟩))
              (.cut 3 (29/16)
                (.row ⟨95281442640, 103236350716, (.direct 593382169971 590058767835), (.variance 225044184243)⟩)
                (.row ⟨95281442640, 103236350716, (.direct 705506110649 700901593558), (.variance 215125056914)⟩)))
            (.cut 3 (13/8)
              (.row ⟨95281442640, 103236350716, (.direct 391506126583 390365279556), (.variance 250755812125)⟩)
              (.row ⟨95281442640, 103236350716, (.direct 593382169971 590058767835), (.variance 225044184243)⟩)))
          (.row ⟨95281442640, 103236350716, (.direct 391506126583 390365279556), (.variance 250755812125)⟩)))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (5)
            (.cut 3 (7/2)
              (.cut 3 (11/4)
                (.cut 3 (19/8)
                  (.row ⟨95281442640, 103236350716, (.direct 824633666698 818631613270), (.variance 206554036734)⟩)
                  (.row ⟨95281442640, 103236350716, (.direct 1082810704946 1073687395593), (.variance 192393271522)⟩))
                (.row ⟨95281442640, 103236350716, (.direct 1366046989981 1353398149623), (.variance 181075998236)⟩))
              (.row ⟨95281442640, 103236350716, (.direct 2002014560937 1981212618346), (.variance 163878633006)⟩))
            (.row ⟨95281442640, 103236350716, (.direct 3523554676644 3482562783967), (.variance 141376135810)⟩))
          (.cut 3 (5)
            (.cut 3 (7/2)
              (.cut 3 (11/4)
                (.cut 3 (19/8)
                  (.row ⟨95281442640, 103236350716, (.direct 824633666698 818631613270), (.variance 206554036734)⟩)
                  (.row ⟨95281442640, 103236350716, (.direct 1082810704946 1073687395593), (.variance 192393271522)⟩))
                (.row ⟨95281442640, 103236350716, (.direct 1366046989981 1353398149623), (.variance 181075998236)⟩))
              (.cut 3 (17/4)
                (.row ⟨95281442640, 103236350716, (.direct 2002014560937 1981212618346), (.variance 163878633006)⟩)
                (.row ⟨95281442640, 103236350716, (.direct 2723407729414 2693118185916), (.variance 151220476281)⟩)))
            (.cut 3 (13/2)
              (.row ⟨95281442640, 103236350716, (.direct 3523554676644 3482562783967), (.variance 141376135810)⟩)
              (.row ⟨95281442640, 103236350716, (.direct 5340438828596 5274738099640), (.variance 126812779061)⟩))))
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.row ⟨95281442640, 103236350716, (.direct 824633666698 818631613270), (.variance 206554036734)⟩)
            (.row ⟨95281442640, 103236350716, (.direct 2002014560937 1981212618346), (.variance 163878633006)⟩))
          (.cut 3 (13/2)
            (.row ⟨95281442640, 103236350716, (.direct 3523554676644 3482562783967), (.variance 141376135810)⟩)
            (.row ⟨95281442640, 103236350716, (.direct 5340438828596 5274738099640), (.variance 126812779061)⟩)))))

set_option maxRecDepth 16000 in
theorem CutMid3H0Pos_checked : CutMid3H0PosTree.commonOK CutMid3H0PosBox true = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
