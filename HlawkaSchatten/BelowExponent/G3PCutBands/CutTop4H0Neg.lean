/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegPart12
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegPart13
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegPart14
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegPart15
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegPart16
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegPart17
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegPart18
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegPart19
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegPart20
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegPart21
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegPart22
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegPart23
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegPart24
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegPart25
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegPart26
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegPart27
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegPart28
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegPart29
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegPart30
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegPart31
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegPart32

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H0Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H0NegBox : Box := ⟨![0, 19/100, 0, -8], ![9/136, 1/5, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop4H0NegTree : CertTree :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutTop4H0NegPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop4H0NegPart1Tree) (.cut 3 (0) (.cut 2 (5/16) (.cut 3 (-1/8) (CutTop4H0NegPart2Tree) (.cut 3 (-1/16) (CutTop4H0NegPart3Tree) (.cut 1 (39/200) (.cut 0 (9/272) (.cut 3 (-1/32) (CutTop4H0NegPart4Tree) (CutTop4H0NegPart5Tree)) (CutTop4H0NegPart6Tree)) (.cut 0 (9/272) (.cut 3 (-1/32) (CutTop4H0NegPart7Tree) (CutTop4H0NegPart8Tree)) (CutTop4H0NegPart9Tree))))) (.cut 3 (-1/8) (CutTop4H0NegPart10Tree) (.cut 2 (13/32) (.cut 3 (-1/16) (.cut 3 (-3/32) (CutTop4H0NegPart11Tree) (.cut 0 (9/272) (.cut 3 (-5/64) (CutTop4H0NegPart12Tree) (CutTop4H0NegPart13Tree)) (.cut 3 (-5/64) (CutTop4H0NegPart14Tree) (CutTop4H0NegPart15Tree)))) (.cut 1 (39/200) (.cut 0 (9/272) (CutTop4H0NegPart16Tree) (CutTop4H0NegPart17Tree)) (.cut 0 (9/272) (.cut 3 (-1/32) (.cut 3 (-3/64) (CutTop4H0NegPart18Tree) (CutTop4H0NegPart19Tree)) (CutTop4H0NegPart20Tree)) (.cut 3 (-1/32) (.cut 3 (-3/64) (CutTop4H0NegPart21Tree) (CutTop4H0NegPart22Tree)) (CutTop4H0NegPart23Tree))))) (.cut 3 (-1/16) (.cut 3 (-3/32) (CutTop4H0NegPart24Tree) (CutTop4H0NegPart25Tree)) (CutTop4H0NegPart26Tree))))) (CutTop4H0NegPart27Tree))) (CutTop4H0NegPart28Tree)) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop4H0NegPart29Tree) (CutTop4H0NegPart30Tree)) (CutTop4H0NegPart31Tree)))) (CutTop4H0NegPart32Tree)

set_option maxRecDepth 16000 in
theorem CutTop4H0Neg_checked : CutTop4H0NegTree.commonOK CutTop4H0NegBox false = true := CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H0NegPart0_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H0NegPart1_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H0NegPart2_checked) (CertTree.commonCut_ok (CutTop4H0NegPart3_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H0NegPart4_checked) (CutTop4H0NegPart5_checked)) (CutTop4H0NegPart6_checked)) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H0NegPart7_checked) (CutTop4H0NegPart8_checked)) (CutTop4H0NegPart9_checked))))) (CertTree.commonCut_ok (CutTop4H0NegPart10_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H0NegPart11_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H0NegPart12_checked) (CutTop4H0NegPart13_checked)) (CertTree.commonCut_ok (CutTop4H0NegPart14_checked) (CutTop4H0NegPart15_checked)))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H0NegPart16_checked) (CutTop4H0NegPart17_checked)) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H0NegPart18_checked) (CutTop4H0NegPart19_checked)) (CutTop4H0NegPart20_checked)) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H0NegPart21_checked) (CutTop4H0NegPart22_checked)) (CutTop4H0NegPart23_checked))))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H0NegPart24_checked) (CutTop4H0NegPart25_checked)) (CutTop4H0NegPart26_checked))))) (CutTop4H0NegPart27_checked))) (CutTop4H0NegPart28_checked)) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H0NegPart29_checked) (CutTop4H0NegPart30_checked)) (CutTop4H0NegPart31_checked)))) (CutTop4H0NegPart32_checked)

end HlawkaSchatten.BelowExponent.G3P
