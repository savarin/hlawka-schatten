/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H0NegPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H0NegPart0Box : Box := (((⟨![0, 9/100, 0, -8], ![9/68, 11/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutMid2H0NegPart0Tree : CertTree :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.row ⟨86531900008, 95281442641, (.direct 3523554676644 3472098434714), (.variance 141487584709)⟩)
          (.row ⟨86531900008, 95281442641, (.direct 824633666698 809585452442), (.variance 207155922570)⟩))
        (.cut 3 (-5)
          (.row ⟨86531900008, 95281442641, (.direct 3523554676644 3472098434714), (.variance 141487584709)⟩)
          (.cut 3 (-7/2)
            (.row ⟨86531900008, 95281442641, (.direct 2002014560937 1970691318739), (.variance 164107288240)⟩)
            (.row ⟨86531900008, 95281442641, (.direct 824633666698 809585452442), (.variance 207155922570)⟩))))
      (.cut 3 (-5)
        (.row ⟨86531900008, 95281442641, (.direct 3523554676644 3472098434714), (.variance 141487584709)⟩)
        (.row ⟨86531900008, 95281442641, (.direct 824633666698 809585452442), (.variance 207155922570)⟩)))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-9/8)
          (.row ⟨86531900008, 95281442641, (.direct 331294831298 323687379078), (.variance 263361184440)⟩)
          (.row ⟨86531900008, 95281442641, (.direct 30541785600 28698659849), (.variance 496703179333)⟩))
        (.cut 3 (-9/8)
          (.row ⟨86531900008, 95281442641, (.direct 331294831298 323687379078), (.variance 263361184440)⟩)
          (.cut 3 (-11/16)
            (.row ⟨86531900008, 95281442641, (.direct 151782739331 147259639702), (.variance 323681943329)⟩)
            (.cut 0 (9/136)
              (.row ⟨86531900008, 95281442641, (.direct 30541785600 29615033338), (.variance 492631748294)⟩)
              (.row ⟨86531900008, 95281442641, (.direct 30541785600 28698659849), (.variance 496703179333)⟩)))))
      (.cut 3 (-9/8)
        (.row ⟨86531900008, 95281442641, (.direct 331294831298 323687379078), (.variance 263361184440)⟩)
        (.row ⟨86531900008, 95281442641, (.direct 30541785600 28698659849), (.chord .universal 91625974997 274877906944)⟩)))

set_option maxRecDepth 16000 in
theorem CutMid2H0NegPart0_checked : CutMid2H0NegPart0Tree.commonOK CutMid2H0NegPart0Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
