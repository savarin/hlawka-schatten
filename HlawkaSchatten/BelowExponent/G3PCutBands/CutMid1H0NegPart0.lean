/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid1H0NegPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid1H0NegPart0Box : Box := (((⟨![0, 7/100, 0, -8], ![9/68, 9/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutMid1H0NegPart0Tree : CertTree :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.row ⟨76698504228, 86531900009, (.direct 3523554676644 3481878700948), (.variance 141383408612)⟩)
          (.row ⟨76698504228, 86531900009, (.direct 824633666698 812443059617), (.variance 206964878531)⟩))
        (.cut 3 (-5)
          (.row ⟨76698504228, 86531900009, (.direct 3523554676644 3481878700948), (.variance 141383408612)⟩)
          (.cut 3 (-7/2)
            (.row ⟨76698504228, 86531900009, (.direct 2002014560937 1976643090336), (.variance 163977752070)⟩)
            (.row ⟨76698504228, 86531900009, (.direct 824633666698 812443059617), (.variance 206964878531)⟩))))
      (.cut 3 (-5)
        (.row ⟨76698504228, 86531900009, (.direct 3523554676644 3481878700948), (.variance 141383408612)⟩)
        (.row ⟨76698504228, 86531900009, (.direct 824633666698 812443059617), (.variance 206964878531)⟩)))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-9/8)
          (.row ⟨76698504228, 86531900009, (.direct 331294831298 325130734263), (.variance 263054535301)⟩)
          (.row ⟨76698504228, 86531900009, (.direct 30541785600 29046334734), (.variance 495139401389)⟩))
        (.cut 3 (-9/8)
          (.row ⟨76698504228, 86531900009, (.direct 331294831298 325130734263), (.variance 263054535301)⟩)
          (.row ⟨76698504228, 86531900009, (.direct 30541785600 29046334734), (.variance 495139401389)⟩)))
      (.row ⟨76698504228, 86531900009, (.direct 30541785600 29046334734), (.chord .universal 91625974997 274877906944)⟩))

set_option maxRecDepth 16000 in
theorem CutMid1H0NegPart0_checked : CutMid1H0NegPart0Tree.commonOK CutMid1H0NegPart0Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
