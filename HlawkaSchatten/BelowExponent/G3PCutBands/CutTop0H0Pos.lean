/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H0Pos`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H0PosBox : Box := ⟨![0, 3/20, 0, -8], ![9/136, 4/25, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop0H0PosTree : CertTree :=
  .cut 3 (3/4)
    (.cut 3 (-1/4)
      (.cut 3 (-2)
        (.row ⟨110576703734, 114055813620, (.direct 824633666698 813383153944), (.variance 206902214225)⟩)
        (.row ⟨110576703734, 114055813620, (.direct 30541785600 29160951079), (.variance 494629047057)⟩))
      (.cut 3 (1/4)
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.row ⟨110576703734, 114055813620, (.direct 30541785600 31381889682), (.chord .universal 0 10180665226)⟩)
            (.cut 2 (5/16)
              (.row ⟨110576703734, 114055813620, (.direct 30541785600 31381889682), (.chord .universal 10180665226 43500686443)⟩)
              (.row ⟨110576703734, 114055813620, (.direct 30541785600 31381889682), (.chord .universal 43500686443 91625974997)⟩)))
          (.row ⟨110576703734, 114055813620, (.direct 30541785600 31381889682), (.chord .universal 91625974997 274877906944)⟩))
        (.row ⟨110576703734, 114055813620, (.direct 174227225485 174757456853), (.variance 488671898726)⟩)))
    (.cut 3 (2)
      (.cut 3 (5/4)
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cone)
            (.row ⟨110576703734, 114055813620, .zero, (.variance 309737727641)⟩))
          (.row ⟨110576703734, 114055813620, .zero, (.variance 309737727641)⟩))
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 3 (13/8)
              (.cut 3 (23/16)
                (.cut 3 (43/32)
                  (.row ⟨110576703734, 114055813620, (.direct 391506126583 390792637022), (.variance 250683977592)⟩)
                  (.row ⟨110576703734, 114055813620, (.direct 439055879922 438032555842), (.variance 243303863619)⟩))
                (.row ⟨110576703734, 114055813620, (.direct 488587506629 487232823949), (.variance 236615602637)⟩))
              (.row ⟨110576703734, 114055813620, (.direct 593382169971 591303376881), (.variance 224920050449)⟩))
            (.cut 3 (13/8)
              (.row ⟨110576703734, 114055813620, (.direct 391506126583 390792637022), (.variance 250683977592)⟩)
              (.row ⟨110576703734, 114055813620, (.direct 593382169971 591303376881), (.variance 224920050449)⟩)))
          (.row ⟨110576703734, 114055813620, (.direct 391506126583 390792637022), (.variance 250683977592)⟩)))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (5)
            (.cut 3 (7/2)
              (.cut 3 (11/4)
                (.cut 3 (19/8)
                  (.row ⟨110576703734, 114055813620, (.direct 824633666698 820879028854), (.variance 206405805678)⟩)
                  (.row ⟨110576703734, 114055813620, (.direct 1082810704946 1077103205746), (.variance 192233316743)⟩))
                (.row ⟨110576703734, 114055813620, (.direct 1366046989981 1358133627707), (.variance 180910457894)⟩))
              (.row ⟨110576703734, 114055813620, (.direct 2002014560937 1988999861980), (.variance 163710380383)⟩))
            (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3497907277678), (.variance 141213473581)⟩))
          (.cut 3 (5)
            (.cut 3 (7/2)
              (.cut 3 (11/4)
                (.cut 3 (19/8)
                  (.row ⟨110576703734, 114055813620, (.direct 824633666698 820879028854), (.variance 206405805678)⟩)
                  (.row ⟨110576703734, 114055813620, (.direct 1082810704946 1077103205746), (.variance 192233316743)⟩))
                (.row ⟨110576703734, 114055813620, (.direct 1366046989981 1358133627707), (.variance 180910457894)⟩))
              (.cut 3 (17/4)
                (.row ⟨110576703734, 114055813620, (.direct 2002014560937 1988999861980), (.variance 163710380383)⟩)
                (.row ⟨110576703734, 114055813620, (.direct 2723407729414 2704456689905), (.variance 151054203398)⟩)))
            (.cut 3 (13/2)
              (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3497907277678), (.variance 141213473581)⟩)
              (.row ⟨110576703734, 114055813620, (.direct 5340438828596 5299331590242), (.variance 126658406783)⟩))))
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.row ⟨110576703734, 114055813620, (.direct 824633666698 820879028854), (.variance 206405805678)⟩)
            (.row ⟨110576703734, 114055813620, (.direct 2002014560937 1988999861980), (.variance 163710380383)⟩))
          (.cut 3 (13/2)
            (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3497907277678), (.variance 141213473581)⟩)
            (.row ⟨110576703734, 114055813620, (.direct 5340438828596 5299331590242), (.variance 126658406783)⟩)))))

set_option maxRecDepth 16000 in
theorem CutTop0H0Pos_checked : CutTop0H0PosTree.commonOK CutTop0H0PosBox true = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
