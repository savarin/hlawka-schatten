/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3NegPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3NegPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3NegPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3NegPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3NegPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3NegPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3NegPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3NegPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3NegPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3NegPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3NegPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3NegPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3NegPart12
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3NegPart13
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3NegPart14
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3NegPart15
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3NegPart16
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3NegPart17
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3NegPart18
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3NegPart19
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3NegPart20
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3NegPart21
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3NegPart22
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3NegPart23
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3NegPart24
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3NegPart25
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3NegPart26
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3NegPart27
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3NegPart28
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3NegPart29
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3NegPart30
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3NegPart31
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3NegPart32

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid4H3Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid4H3NegBox : Box := ⟨![27/68, 13/100, 0, -8], ![9/17, 3/20, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutMid4H3NegTree : CertTree :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutMid4H3NegPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (CutMid4H3NegPart1Tree) (.cut 3 (0) (.cut 2 (5/16) (.cut 1 (7/50) (.cut 3 (-1/8) (CutMid4H3NegPart2Tree) (.cut 0 (63/136) (CutMid4H3NegPart3Tree) (CutMid4H3NegPart4Tree))) (.cut 3 (-1/8) (CutMid4H3NegPart5Tree) (.cut 0 (63/136) (.cut 1 (29/200) (CutMid4H3NegPart6Tree) (CutMid4H3NegPart7Tree)) (.cut 1 (29/200) (CutMid4H3NegPart8Tree) (CutMid4H3NegPart9Tree))))) (.cut 3 (-1/8) (CutMid4H3NegPart10Tree) (.cut 0 (63/136) (.cut 3 (-1/16) (CutMid4H3NegPart11Tree) (.cut 3 (-1/32) (CutMid4H3NegPart12Tree) (CutMid4H3NegPart13Tree))) (.cut 3 (-1/16) (CutMid4H3NegPart14Tree) (.cut 3 (-1/32) (CutMid4H3NegPart15Tree) (CutMid4H3NegPart16Tree)))))) (.cut 2 (5/16) (.cut 3 (1/8) (.cut 0 (63/136) (.cut 1 (7/50) (CutMid4H3NegPart17Tree) (.cut 3 (1/16) (CutMid4H3NegPart18Tree) (CutMid4H3NegPart19Tree))) (.cut 1 (7/50) (CutMid4H3NegPart20Tree) (.cut 3 (1/16) (.cut 2 (7/32) (CutMid4H3NegPart21Tree) (CutMid4H3NegPart22Tree)) (CutMid4H3NegPart23Tree)))) (CutMid4H3NegPart24Tree)) (.cut 3 (1/8) (.cut 3 (1/16) (.cut 3 (1/32) (.cut 0 (63/136) (CutMid4H3NegPart25Tree) (CutMid4H3NegPart26Tree)) (CutMid4H3NegPart27Tree)) (CutMid4H3NegPart28Tree)) (CutMid4H3NegPart29Tree))))) (CutMid4H3NegPart30Tree)) (CutMid4H3NegPart31Tree))) (CutMid4H3NegPart32Tree)

set_option maxRecDepth 16000 in
theorem CutMid4H3Neg_checked : CutMid4H3NegTree.commonOK CutMid4H3NegBox false = true := CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid4H3NegPart0_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid4H3NegPart1_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid4H3NegPart2_checked) (CertTree.commonCut_ok (CutMid4H3NegPart3_checked) (CutMid4H3NegPart4_checked))) (CertTree.commonCut_ok (CutMid4H3NegPart5_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid4H3NegPart6_checked) (CutMid4H3NegPart7_checked)) (CertTree.commonCut_ok (CutMid4H3NegPart8_checked) (CutMid4H3NegPart9_checked))))) (CertTree.commonCut_ok (CutMid4H3NegPart10_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid4H3NegPart11_checked) (CertTree.commonCut_ok (CutMid4H3NegPart12_checked) (CutMid4H3NegPart13_checked))) (CertTree.commonCut_ok (CutMid4H3NegPart14_checked) (CertTree.commonCut_ok (CutMid4H3NegPart15_checked) (CutMid4H3NegPart16_checked)))))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid4H3NegPart17_checked) (CertTree.commonCut_ok (CutMid4H3NegPart18_checked) (CutMid4H3NegPart19_checked))) (CertTree.commonCut_ok (CutMid4H3NegPart20_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid4H3NegPart21_checked) (CutMid4H3NegPart22_checked)) (CutMid4H3NegPart23_checked)))) (CutMid4H3NegPart24_checked)) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid4H3NegPart25_checked) (CutMid4H3NegPart26_checked)) (CutMid4H3NegPart27_checked)) (CutMid4H3NegPart28_checked)) (CutMid4H3NegPart29_checked))))) (CutMid4H3NegPart30_checked)) (CutMid4H3NegPart31_checked))) (CutMid4H3NegPart32_checked)

end HlawkaSchatten.BelowExponent.G3P
