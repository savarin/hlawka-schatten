/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegPart12
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegPart13
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegPart14
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegPart15
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegPart16
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegPart17
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegPart18
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegPart19
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegPart20
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegPart21
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegPart22
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegPart23
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegPart24
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegPart25
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegPart26
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegPart27
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegPart28
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegPart29
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegPart30
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegPart31
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegPart32
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegPart33
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegPart34
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegPart35
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegPart36
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegPart37
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegPart38
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegPart39
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegPart40
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegPart41
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegPart42
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegPart43
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegPart44
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegPart45
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegPart46
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegPart47
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegPart48
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegPart49
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegPart50

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H6Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H6NegBox : Box := ⟨![27/68, 19/100, 0, -8], ![63/136, 1/5, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop4H6NegTree : CertTree :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutTop4H6NegPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop4H6NegPart1Tree) (.cut 3 (0) (.cut 3 (-1/8) (CutTop4H6NegPart2Tree) (.cut 3 (-1/16) (CutTop4H6NegPart3Tree) (.cut 2 (5/16) (.cut 1 (39/200) (.cut 0 (117/272) (CutTop4H6NegPart4Tree) (CutTop4H6NegPart5Tree)) (.cut 0 (117/272) (CutTop4H6NegPart6Tree) (CutTop4H6NegPart7Tree))) (.cut 3 (-1/32) (.cut 3 (-3/64) (CutTop4H6NegPart8Tree) (.cut 0 (117/272) (.cut 2 (13/32) (CutTop4H6NegPart9Tree) (CutTop4H6NegPart10Tree)) (.cut 2 (13/32) (CutTop4H6NegPart11Tree) (CutTop4H6NegPart12Tree)))) (.cut 3 (-1/64) (.cut 0 (117/272) (.cut 2 (13/32) (.cut 3 (-3/128) (CutTop4H6NegPart13Tree) (CutTop4H6NegPart14Tree)) (CutTop4H6NegPart15Tree)) (.cut 2 (13/32) (.cut 3 (-3/128) (CutTop4H6NegPart16Tree) (CutTop4H6NegPart17Tree)) (CutTop4H6NegPart18Tree))) (.cut 0 (117/272) (.cut 2 (13/32) (.cut 3 (-1/128) (CutTop4H6NegPart19Tree) (CutTop4H6NegPart20Tree)) (.cut 3 (-1/128) (CutTop4H6NegPart21Tree) (CutTop4H6NegPart22Tree))) (.cut 2 (13/32) (.cut 3 (-1/128) (CutTop4H6NegPart23Tree) (CutTop4H6NegPart24Tree)) (.cut 3 (-1/128) (CutTop4H6NegPart25Tree) (CutTop4H6NegPart26Tree))))))))) (.cut 3 (1/8) (.cut 3 (1/16) (.cut 2 (5/16) (.cut 2 (7/32) (CutTop4H6NegPart27Tree) (.cut 3 (1/32) (CutTop4H6NegPart28Tree) (CutTop4H6NegPart29Tree))) (.cut 3 (1/32) (.cut 2 (13/32) (.cut 3 (1/64) (.cut 0 (117/272) (.cut 3 (1/128) (CutTop4H6NegPart30Tree) (CutTop4H6NegPart31Tree)) (.cut 3 (1/128) (CutTop4H6NegPart32Tree) (CutTop4H6NegPart33Tree))) (CutTop4H6NegPart34Tree)) (.cut 0 (117/272) (CutTop4H6NegPart35Tree) (CutTop4H6NegPart36Tree))) (CutTop4H6NegPart37Tree))) (CutTop4H6NegPart38Tree)) (CutTop4H6NegPart39Tree)))) (.cut 2 (3/4) (.cut 3 (0) (.cut 3 (-1/8) (CutTop4H6NegPart40Tree) (.cut 3 (-1/16) (CutTop4H6NegPart41Tree) (.cut 3 (-1/32) (CutTop4H6NegPart42Tree) (CutTop4H6NegPart43Tree)))) (CutTop4H6NegPart44Tree)) (CutTop4H6NegPart45Tree))) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop4H6NegPart46Tree) (.cut 0 (117/272) (CutTop4H6NegPart47Tree) (CutTop4H6NegPart48Tree))) (CutTop4H6NegPart49Tree)))) (CutTop4H6NegPart50Tree)

set_option maxRecDepth 16000 in
theorem CutTop4H6Neg_checked : CutTop4H6NegTree.commonOK CutTop4H6NegBox false = true := CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H6NegPart0_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H6NegPart1_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H6NegPart2_checked) (CertTree.commonCut_ok (CutTop4H6NegPart3_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H6NegPart4_checked) (CutTop4H6NegPart5_checked)) (CertTree.commonCut_ok (CutTop4H6NegPart6_checked) (CutTop4H6NegPart7_checked))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H6NegPart8_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H6NegPart9_checked) (CutTop4H6NegPart10_checked)) (CertTree.commonCut_ok (CutTop4H6NegPart11_checked) (CutTop4H6NegPart12_checked)))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H6NegPart13_checked) (CutTop4H6NegPart14_checked)) (CutTop4H6NegPart15_checked)) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H6NegPart16_checked) (CutTop4H6NegPart17_checked)) (CutTop4H6NegPart18_checked))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H6NegPart19_checked) (CutTop4H6NegPart20_checked)) (CertTree.commonCut_ok (CutTop4H6NegPart21_checked) (CutTop4H6NegPart22_checked))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H6NegPart23_checked) (CutTop4H6NegPart24_checked)) (CertTree.commonCut_ok (CutTop4H6NegPart25_checked) (CutTop4H6NegPart26_checked))))))))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H6NegPart27_checked) (CertTree.commonCut_ok (CutTop4H6NegPart28_checked) (CutTop4H6NegPart29_checked))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H6NegPart30_checked) (CutTop4H6NegPart31_checked)) (CertTree.commonCut_ok (CutTop4H6NegPart32_checked) (CutTop4H6NegPart33_checked))) (CutTop4H6NegPart34_checked)) (CertTree.commonCut_ok (CutTop4H6NegPart35_checked) (CutTop4H6NegPart36_checked))) (CutTop4H6NegPart37_checked))) (CutTop4H6NegPart38_checked)) (CutTop4H6NegPart39_checked)))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H6NegPart40_checked) (CertTree.commonCut_ok (CutTop4H6NegPart41_checked) (CertTree.commonCut_ok (CutTop4H6NegPart42_checked) (CutTop4H6NegPart43_checked)))) (CutTop4H6NegPart44_checked)) (CutTop4H6NegPart45_checked))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H6NegPart46_checked) (CertTree.commonCut_ok (CutTop4H6NegPart47_checked) (CutTop4H6NegPart48_checked))) (CutTop4H6NegPart49_checked)))) (CutTop4H6NegPart50_checked)

end HlawkaSchatten.BelowExponent.G3P
