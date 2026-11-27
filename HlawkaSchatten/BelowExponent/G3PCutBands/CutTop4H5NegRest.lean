/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H5NegRestPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H5NegRestPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H5NegRestPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H5NegRestPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H5NegRestPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H5NegRestPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H5NegRestPart6

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H5NegRest`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H5NegRestBox : Box := ⟨![45/136, 19/100, 0, -8], ![27/68, 1/5, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop4H5NegRestTree : RatioRemainder :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutTop4H5NegRestPart0Tree) (.cut 3 (1/4) (CutTop4H5NegRestPart1Tree) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop4H5NegRestPart2Tree) (.cut 0 (99/272) (CutTop4H5NegRestPart3Tree) (CutTop4H5NegRestPart4Tree))) (CutTop4H5NegRestPart5Tree)))) (CutTop4H5NegRestPart6Tree)

set_option maxRecDepth 16000 in
theorem CutTop4H5NegRest_ok : CutTop4H5NegRestTree.ok CutTop4H5NegRestBox false (1) = true :=
  RatioRemainder.cut_ok (RatioRemainder.cut_ok (CutTop4H5NegRestPart0_ok) (RatioRemainder.cut_ok (CutTop4H5NegRestPart1_ok) (RatioRemainder.cut_ok (RatioRemainder.cut_ok (CutTop4H5NegRestPart2_ok) (RatioRemainder.cut_ok (CutTop4H5NegRestPart3_ok) (CutTop4H5NegRestPart4_ok))) (CutTop4H5NegRestPart5_ok)))) (CutTop4H5NegRestPart6_ok)

end HlawkaSchatten.BelowExponent.G3P
