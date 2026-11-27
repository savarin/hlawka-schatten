/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H7PosPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H7PosPart1Box : Box := ((⟨![63/136, 19/100, 0, -8], ![9/17, 1/5, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutTop4H7PosPart1Tree : CertTree :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cone)
          (.row ⟨123862991199, 126950446638, .zero, (.variance 307677607899)⟩))
        (.row ⟨123862991199, 126950446638, .zero, (.variance 307677607899)⟩))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (13/8)
            (.cut 3 (23/16)
              (.cut 3 (43/32)
                (.row ⟨123862991199, 126950446638, (.direct 391506126583 384231421904), (.variance 251797915942)⟩)
                (.row ⟨123862991199, 126950446638, (.direct 439055879922 428631029992), (.variance 244690108973)⟩))
              (.row ⟨123862991199, 126950446638, (.direct 488587506629 474797276115), (.variance 238222938884)⟩))
            (.row ⟨123862991199, 126950446638, (.direct 593382169971 572246697767), (.variance 226857744383)⟩))
          (.cut 3 (13/8)
            (.cut 3 (23/16)
              (.row ⟨123862991199, 126950446638, (.direct 391506126583 384231421904), (.variance 251797915942)⟩)
              (.row ⟨123862991199, 126950446638, (.direct 488587506629 474797276115), (.variance 238222938884)⟩))
            (.row ⟨123862991199, 126950446638, (.direct 593382169971 572246697767), (.variance 226857744383)⟩)))
        (.row ⟨123862991199, 126950446638, (.direct 391506126583 384231421904), (.variance 251797915942)⟩)))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.cut 3 (11/4)
              (.cut 3 (19/8)
                (.row ⟨123862991199, 126950446638, (.direct 824633666698 786526710110), (.variance 208729310580)⟩)
                (.row ⟨123862991199, 126950446638, (.direct 1082810704946 1024952908462), (.variance 194747791286)⟩))
              (.row ⟨123862991199, 126950446638, (.direct 1366046989981 1285897385702), (.variance 183518194799)⟩))
            (.row ⟨123862991199, 126950446638, (.direct 2002014560937 1870349510385), (.variance 166368423670)⟩))
          (.cut 3 (13/2)
            (.row ⟨123862991199, 126950446638, (.direct 3523554676644 3264411444305), (.variance 143791328671)⟩)
            (.row ⟨123862991199, 126950446638, (.direct 5340438828596 4925354484016), (.variance 129109065386)⟩)))
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.cut 3 (11/4)
              (.cut 3 (19/8)
                (.row ⟨123862991199, 126950446638, (.direct 824633666698 786526710110), (.variance 208729310580)⟩)
                (.row ⟨123862991199, 126950446638, (.direct 1082810704946 1024952908462), (.variance 194747791286)⟩))
              (.row ⟨123862991199, 126950446638, (.direct 1366046989981 1285897385702), (.variance 183518194799)⟩))
            (.cut 3 (17/4)
              (.row ⟨123862991199, 126950446638, (.direct 2002014560937 1870349510385), (.variance 166368423670)⟩)
              (.row ⟨123862991199, 126950446638, (.direct 2723407729414 2531828132921), (.variance 153685849699)⟩)))
          (.cut 3 (13/2)
            (.row ⟨123862991199, 126950446638, (.direct 3523554676644 3264411444305), (.variance 143791328671)⟩)
            (.cut 3 (29/4)
              (.row ⟨123862991199, 126950446638, (.direct 5340438828596 4925354484016), (.variance 129109065386)⟩)
              (.row ⟨123862991199, 126950446638, (.direct 6349554162205 5846897880426), (.variance 123438782048)⟩)))))
      (.cut 3 (5)
        (.cut 3 (7/2)
          (.row ⟨123862991199, 126950446638, (.direct 824633666698 786526710110), (.variance 208729310580)⟩)
          (.row ⟨123862991199, 126950446638, (.direct 2002014560937 1870349510385), (.variance 166368423670)⟩))
        (.cut 3 (13/2)
          (.row ⟨123862991199, 126950446638, (.direct 3523554676644 3264411444305), (.variance 143791328671)⟩)
          (.row ⟨123862991199, 126950446638, (.direct 5340438828596 4925354484016), (.variance 129109065386)⟩))))

set_option maxRecDepth 16000 in
theorem CutTop4H7PosPart1_checked : CutTop4H7PosPart1Tree.commonOK CutTop4H7PosPart1Box true = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
