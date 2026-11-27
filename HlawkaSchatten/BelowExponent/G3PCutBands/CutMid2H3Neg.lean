/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegPart12
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegPart13
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegPart14
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegPart15
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegPart16
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegPart17
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegPart18
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegPart19
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegPart20
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegPart21
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegPart22
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegPart23
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegPart24
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegPart25
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegPart26
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegPart27
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegPart28
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegPart29

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H3Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H3NegBox : Box := ⟨![27/68, 9/100, 0, -8], ![9/17, 11/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutMid2H3NegTree : CertTree :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutMid2H3NegPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (.cut 3 (0) (.cut 1 (1/10) (.cut 1 (19/200) (.cut 3 (-1/8) (CutMid2H3NegPart1Tree) (.cut 0 (63/136) (CutMid2H3NegPart2Tree) (CutMid2H3NegPart3Tree))) (.cut 3 (-1/8) (CutMid2H3NegPart4Tree) (.cut 0 (63/136) (CutMid2H3NegPart5Tree) (CutMid2H3NegPart6Tree)))) (.cut 1 (21/200) (.cut 3 (-1/8) (CutMid2H3NegPart7Tree) (.cut 0 (63/136) (CutMid2H3NegPart8Tree) (CutMid2H3NegPart9Tree))) (CutMid2H3NegPart10Tree))) (.cut 3 (1/8) (.cut 3 (1/16) (.cut 1 (1/10) (.cut 3 (1/32) (.cut 1 (19/200) (.cut 0 (63/136) (CutMid2H3NegPart11Tree) (CutMid2H3NegPart12Tree)) (.cut 0 (63/136) (CutMid2H3NegPart13Tree) (CutMid2H3NegPart14Tree))) (CutMid2H3NegPart15Tree)) (.cut 3 (1/32) (.cut 1 (21/200) (CutMid2H3NegPart16Tree) (CutMid2H3NegPart17Tree)) (CutMid2H3NegPart18Tree))) (CutMid2H3NegPart19Tree)) (CutMid2H3NegPart20Tree))) (.cut 2 (5/16) (.cut 3 (0) (.cut 1 (1/10) (CutMid2H3NegPart21Tree) (CutMid2H3NegPart22Tree)) (.cut 3 (1/8) (.cut 1 (1/10) (CutMid2H3NegPart23Tree) (CutMid2H3NegPart24Tree)) (CutMid2H3NegPart25Tree))) (CutMid2H3NegPart26Tree))) (CutMid2H3NegPart27Tree)) (CutMid2H3NegPart28Tree))) (CutMid2H3NegPart29Tree)

set_option maxRecDepth 16000 in
theorem CutMid2H3Neg_checked : CutMid2H3NegTree.commonOK CutMid2H3NegBox false = true := CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid2H3NegPart0_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid2H3NegPart1_checked) (CertTree.commonCut_ok (CutMid2H3NegPart2_checked) (CutMid2H3NegPart3_checked))) (CertTree.commonCut_ok (CutMid2H3NegPart4_checked) (CertTree.commonCut_ok (CutMid2H3NegPart5_checked) (CutMid2H3NegPart6_checked)))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid2H3NegPart7_checked) (CertTree.commonCut_ok (CutMid2H3NegPart8_checked) (CutMid2H3NegPart9_checked))) (CutMid2H3NegPart10_checked))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid2H3NegPart11_checked) (CutMid2H3NegPart12_checked)) (CertTree.commonCut_ok (CutMid2H3NegPart13_checked) (CutMid2H3NegPart14_checked))) (CutMid2H3NegPart15_checked)) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid2H3NegPart16_checked) (CutMid2H3NegPart17_checked)) (CutMid2H3NegPart18_checked))) (CutMid2H3NegPart19_checked)) (CutMid2H3NegPart20_checked))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid2H3NegPart21_checked) (CutMid2H3NegPart22_checked)) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid2H3NegPart23_checked) (CutMid2H3NegPart24_checked)) (CutMid2H3NegPart25_checked))) (CutMid2H3NegPart26_checked))) (CutMid2H3NegPart27_checked)) (CutMid2H3NegPart28_checked))) (CutMid2H3NegPart29_checked)

end HlawkaSchatten.BelowExponent.G3P
