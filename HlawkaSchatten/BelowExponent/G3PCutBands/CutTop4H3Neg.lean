/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegPart12
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegPart13
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegPart14
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegPart15
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegPart16
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegPart17
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegPart18
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegPart19
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegPart20
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegPart21
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegPart22
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegPart23
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegPart24
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegPart25
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegPart26
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegPart27
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegPart28
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegPart29
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegPart30
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegPart31
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegPart32
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegPart33
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegPart34
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegPart35
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegPart36
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegPart37
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegPart38
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegPart39
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegPart40
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegPart41
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegPart42
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegPart43
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegPart44
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegPart45
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegPart46
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegPart47
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegPart48
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegPart49

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H3Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H3NegBox : Box := ⟨![27/136, 19/100, 0, -8], ![9/34, 1/5, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop4H3NegTree : CertTree :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutTop4H3NegPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop4H3NegPart1Tree) (.cut 3 (0) (.cut 2 (5/16) (.cut 3 (-1/8) (CutTop4H3NegPart2Tree) (.cut 3 (-1/16) (CutTop4H3NegPart3Tree) (.cut 1 (39/200) (.cut 0 (63/272) (CutTop4H3NegPart4Tree) (CutTop4H3NegPart5Tree)) (.cut 0 (63/272) (.cut 3 (-1/32) (CutTop4H3NegPart6Tree) (CutTop4H3NegPart7Tree)) (CutTop4H3NegPart8Tree))))) (.cut 3 (-1/8) (CutTop4H3NegPart9Tree) (.cut 3 (-1/16) (.cut 3 (-3/32) (CutTop4H3NegPart10Tree) (.cut 2 (13/32) (CutTop4H3NegPart11Tree) (CutTop4H3NegPart12Tree))) (.cut 3 (-1/32) (.cut 3 (-3/64) (.cut 2 (13/32) (CutTop4H3NegPart13Tree) (CutTop4H3NegPart14Tree)) (.cut 0 (63/272) (CutTop4H3NegPart15Tree) (CutTop4H3NegPart16Tree))) (.cut 3 (-1/64) (.cut 0 (63/272) (.cut 3 (-3/128) (CutTop4H3NegPart17Tree) (.cut 0 (117/544) (CutTop4H3NegPart18Tree) (CutTop4H3NegPart19Tree))) (.cut 3 (-3/128) (.cut 0 (135/544) (CutTop4H3NegPart20Tree) (CutTop4H3NegPart21Tree)) (.cut 0 (135/544) (CutTop4H3NegPart22Tree) (CutTop4H3NegPart23Tree)))) (.cut 0 (63/272) (.cut 3 (-1/128) (.cut 2 (13/32) (CutTop4H3NegPart24Tree) (CutTop4H3NegPart25Tree)) (.cut 2 (13/32) (CutTop4H3NegPart26Tree) (CutTop4H3NegPart27Tree))) (.cut 2 (13/32) (.cut 3 (-1/128) (.cut 0 (135/544) (CutTop4H3NegPart28Tree) (CutTop4H3NegPart29Tree)) (CutTop4H3NegPart30Tree)) (CutTop4H3NegPart31Tree)))))))) (.cut 2 (5/16) (.cut 3 (1/8) (.cut 3 (1/16) (CutTop4H3NegPart32Tree) (CutTop4H3NegPart33Tree)) (CutTop4H3NegPart34Tree)) (.cut 3 (1/8) (.cut 3 (1/16) (.cut 3 (1/32) (.cut 3 (1/64) (.cut 0 (63/272) (CutTop4H3NegPart35Tree) (.cut 2 (13/32) (CutTop4H3NegPart36Tree) (CutTop4H3NegPart37Tree))) (CutTop4H3NegPart38Tree)) (CutTop4H3NegPart39Tree)) (CutTop4H3NegPart40Tree)) (CutTop4H3NegPart41Tree))))) (.cut 2 (3/4) (.cut 3 (0) (CutTop4H3NegPart42Tree) (CutTop4H3NegPart43Tree)) (CutTop4H3NegPart44Tree))) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop4H3NegPart45Tree) (.cut 0 (63/272) (CutTop4H3NegPart46Tree) (CutTop4H3NegPart47Tree))) (CutTop4H3NegPart48Tree)))) (CutTop4H3NegPart49Tree)

set_option maxRecDepth 16000 in
theorem CutTop4H3Neg_checked : CutTop4H3NegTree.commonOK CutTop4H3NegBox false = true := CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H3NegPart0_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H3NegPart1_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H3NegPart2_checked) (CertTree.commonCut_ok (CutTop4H3NegPart3_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H3NegPart4_checked) (CutTop4H3NegPart5_checked)) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H3NegPart6_checked) (CutTop4H3NegPart7_checked)) (CutTop4H3NegPart8_checked))))) (CertTree.commonCut_ok (CutTop4H3NegPart9_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H3NegPart10_checked) (CertTree.commonCut_ok (CutTop4H3NegPart11_checked) (CutTop4H3NegPart12_checked))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H3NegPart13_checked) (CutTop4H3NegPart14_checked)) (CertTree.commonCut_ok (CutTop4H3NegPart15_checked) (CutTop4H3NegPart16_checked))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H3NegPart17_checked) (CertTree.commonCut_ok (CutTop4H3NegPart18_checked) (CutTop4H3NegPart19_checked))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H3NegPart20_checked) (CutTop4H3NegPart21_checked)) (CertTree.commonCut_ok (CutTop4H3NegPart22_checked) (CutTop4H3NegPart23_checked)))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H3NegPart24_checked) (CutTop4H3NegPart25_checked)) (CertTree.commonCut_ok (CutTop4H3NegPart26_checked) (CutTop4H3NegPart27_checked))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H3NegPart28_checked) (CutTop4H3NegPart29_checked)) (CutTop4H3NegPart30_checked)) (CutTop4H3NegPart31_checked)))))))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H3NegPart32_checked) (CutTop4H3NegPart33_checked)) (CutTop4H3NegPart34_checked)) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H3NegPart35_checked) (CertTree.commonCut_ok (CutTop4H3NegPart36_checked) (CutTop4H3NegPart37_checked))) (CutTop4H3NegPart38_checked)) (CutTop4H3NegPart39_checked)) (CutTop4H3NegPart40_checked)) (CutTop4H3NegPart41_checked))))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H3NegPart42_checked) (CutTop4H3NegPart43_checked)) (CutTop4H3NegPart44_checked))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H3NegPart45_checked) (CertTree.commonCut_ok (CutTop4H3NegPart46_checked) (CutTop4H3NegPart47_checked))) (CutTop4H3NegPart48_checked)))) (CutTop4H3NegPart49_checked)

end HlawkaSchatten.BelowExponent.G3P
