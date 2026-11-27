/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H5NegPart55`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H5NegPart55Box : Box := ((⟨![45/136, 19/100, 0, -8], ![27/68, 1/5, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutTop4H5NegPart55Tree : CertTree :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cone)
          (.row ⟨123862991199, 126950446638, .zero, (.variance 308261443908)⟩))
        (.row ⟨123862991199, 126950446638, .zero, (.variance 308261443908)⟩))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (13/8)
            (.row ⟨123862991199, 126950446638, (.direct 391506126583 386045481877), (.variance 251487544411)⟩)
            (.row ⟨123862991199, 126950446638, (.direct 593382169971 577504372977), (.variance 226315095882)⟩))
          (.row ⟨123862991199, 126950446638, (.direct 391506126583 386045481877), (.variance 251487544411)⟩))
        (.row ⟨123862991199, 126950446638, (.direct 391506126583 386045481877), (.variance 251487544411)⟩)))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.cut 3 (11/4)
              (.row ⟨123862991199, 126950446638, (.direct 824633666698 795991698633), (.variance 208076522951)⟩)
              (.row ⟨123862991199, 126950446638, (.direct 1366046989981 1305768568652), (.variance 182782745665)⟩))
            (.row ⟨123862991199, 126950446638, (.direct 2002014560937 1902958453637), (.variance 165617136935)⟩))
          (.cut 3 (13/2)
            (.row ⟨123862991199, 126950446638, (.direct 3523554676644 3328518067527), (.chord .universal 0 10180665226)⟩)
            (.row ⟨123862991199, 126950446638, (.direct 5340438828596 5027973642345), (.chord .universal 0 10180665226)⟩)))
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.row ⟨123862991199, 126950446638, (.direct 824633666698 795991698633), (.variance 208076522951)⟩)
            (.row ⟨123862991199, 126950446638, (.direct 2002014560937 1902958453637), (.variance 165617136935)⟩))
          (.row ⟨123862991199, 126950446638, (.direct 3523554676644 3328518067527), (.variance 143060934194)⟩)))
      (.row ⟨123862991199, 126950446638, (.direct 824633666698 795991698633), (.variance 208076522951)⟩))

set_option maxRecDepth 16000 in
theorem CutTop4H5NegPart55_checked : CutTop4H5NegPart55Tree.commonOK CutTop4H5NegPart55Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
