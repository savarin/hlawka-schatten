/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H7NegPart16`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H7NegPart16Box : Box := ((⟨![63/136, 4/25, 0, -8], ![9/17, 17/100, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutTop1H7NegPart16Tree : CertTree :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cone)
          (.row ⟨114055813619, 117423580140, .zero, (.variance 308027857569)⟩))
        (.row ⟨114055813619, 117423580140, .zero, (.variance 308027857569)⟩))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (13/8)
            (.cut 3 (23/16)
              (.row ⟨114055813619, 117423580140, (.direct 391506126583 385420613501), (.variance 251594246364)⟩)
              (.row ⟨114055813619, 117423580140, (.direct 488587506629 477048116953), (.variance 237928099262)⟩))
            (.row ⟨114055813619, 117423580140, (.direct 593382169971 575692350726), (.variance 226501409539)⟩))
          (.row ⟨114055813619, 117423580140, (.direct 391506126583 385420613501), (.variance 251594246364)⟩))
        (.row ⟨114055813619, 117423580140, (.direct 391506126583 385420613501), (.variance 251594246364)⟩)))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.cut 3 (11/4)
              (.row ⟨114055813619, 117423580140, (.direct 824633666698 792728544161), (.variance 208300466975)⟩)
              (.row ⟨114055813619, 117423580140, (.direct 1366046989981 1298914978048), (.variance 183034797948)⟩))
            (.row ⟨114055813619, 117423580140, (.direct 2002014560937 1891708949956), (.variance 165874469856)⟩))
          (.cut 3 (13/2)
            (.row ⟨114055813619, 117423580140, (.direct 3523554676644 3306396652069), (.variance 143310952281)⟩)
            (.row ⟨114055813619, 117423580140, (.direct 5340438828596 4992557608432), (.chord .universal 0 10180665226)⟩)))
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.row ⟨114055813619, 117423580140, (.direct 824633666698 792728544161), (.variance 208300466975)⟩)
            (.row ⟨114055813619, 117423580140, (.direct 2002014560937 1891708949956), (.variance 165874469856)⟩))
          (.row ⟨114055813619, 117423580140, (.direct 3523554676644 3306396652069), (.variance 143310952281)⟩)))
      (.row ⟨114055813619, 117423580140, (.direct 824633666698 792728544161), (.variance 208300466975)⟩))

set_option maxRecDepth 16000 in
theorem CutTop1H7NegPart16_checked : CutTop1H7NegPart16Tree.commonOK CutTop1H7NegPart16Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
