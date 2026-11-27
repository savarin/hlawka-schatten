/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H7NegPart50`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H7NegPart50Box : Box := (((((⟨![63/136, 19/100, 0, -8], ![9/17, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).upperChild 3 (1/4)).upperChild 2 (1/2)

set_option maxRecDepth 16000 in
def CutTop4H7NegPart50Tree : CertTree :=
  .cut 2 (3/4)
    (.cut 3 (1/2)
      (.cut 3 (3/8)
        (.cut 2 (5/8)
          (.cut 2 (9/16)
            (.row ⟨123862991199, 126950446638, (.direct 58075547817 67355517179), (.chord (.secant 1072207778087 54507459483 563436869 94335703789) 91625974997 110431617683)⟩)
            (.row ⟨123862991199, 126950446638, (.direct 58075547817 67355517179), (.chord (.secant 1007076426392 34259453652 4159143017 79827396734) 110431617683 130502050762)⟩))
          (.row ⟨123862991199, 126950446638, (.direct 58075547817 67355517179), (.chord (.secant 956063728415 20698611742 13227572967 59793266465) 130502050762 174227471798)⟩))
        (.cut 2 (5/8)
          (.row ⟨123862991199, 126950446638, (.direct 91625662891 100314348286), (.chord (.secant 1246493552310 120902915877 9444084759 138406980499) 91625974997 130502050762)⟩)
          (.row ⟨123862991199, 126950446638, (.direct 91625662891 100314348286), (.chord (.secant 1089198307720 60256236540 219639761 103671243260) 130502050762 174227471798)⟩)))
      (.row ⟨123862991199, 126950446638, (.direct 174227225485 179673028498), (.variance 359352036895)⟩))
    (.cut 3 (1/2)
      (.cut 3 (3/8)
        (.row ⟨123862991199, 126950446638, (.direct 58075547817 67355517179), (.chord (.secant 881396650631 5605652642 29186591467 37899062295) 174227471798 274877906944)⟩)
        (.row ⟨123862991199, 126950446638, (.direct 91625662891 100314348286), (.chord (.secant 988745336339 29130326948 10054442718 65710457696) 174227471798 274877906944)⟩))
      (.row ⟨123862991199, 126950446638, (.direct 174227225485 179673028498), (.chord (.secant 1216776418985 108530744392 63899376 98787214060) 174227471798 274877906944)⟩))

set_option maxRecDepth 16000 in
theorem CutTop4H7NegPart50_checked : CutTop4H7NegPart50Tree.commonOK CutTop4H7NegPart50Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
