/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegPart12
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegPart13
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegPart14
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegPart15
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegPart16
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegPart17
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegPart18
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegPart19
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegPart20
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegPart21
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegPart22
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegPart23
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegPart24
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegPart25
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegPart26
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegPart27
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegPart28
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegPart29
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegPart30
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegPart31
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegPart32
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegPart33
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegPart34
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegPart35
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegPart36
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegPart37
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegPart38
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegPart39
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegPart40
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegPart41
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegPart42
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegPart43
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegPart44
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegPart45
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegPart46
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegPart47
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegPart48
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegPart49
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegPart50
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegPart51

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H7Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H7NegBox : Box := ⟨![63/136, 19/100, 0, -8], ![9/17, 1/5, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop4H7NegTree : CertTree :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutTop4H7NegPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop4H7NegPart1Tree) (.cut 3 (0) (.cut 3 (-1/8) (CutTop4H7NegPart2Tree) (.cut 3 (-1/16) (CutTop4H7NegPart3Tree) (.cut 2 (5/16) (.cut 1 (39/200) (CutTop4H7NegPart4Tree) (.cut 0 (135/272) (CutTop4H7NegPart5Tree) (CutTop4H7NegPart6Tree))) (.cut 3 (-1/32) (.cut 3 (-3/64) (CutTop4H7NegPart7Tree) (.cut 0 (135/272) (.cut 2 (13/32) (CutTop4H7NegPart8Tree) (CutTop4H7NegPart9Tree)) (CutTop4H7NegPart10Tree))) (.cut 0 (135/272) (.cut 3 (-1/64) (.cut 2 (13/32) (.cut 3 (-3/128) (CutTop4H7NegPart11Tree) (CutTop4H7NegPart12Tree)) (CutTop4H7NegPart13Tree)) (.cut 2 (13/32) (.cut 3 (-1/128) (CutTop4H7NegPart14Tree) (CutTop4H7NegPart15Tree)) (.cut 3 (-1/128) (CutTop4H7NegPart16Tree) (CutTop4H7NegPart17Tree)))) (.cut 2 (13/32) (.cut 3 (-1/64) (CutTop4H7NegPart18Tree) (.cut 3 (-1/128) (CutTop4H7NegPart19Tree) (CutTop4H7NegPart20Tree))) (.cut 3 (-1/64) (CutTop4H7NegPart21Tree) (CutTop4H7NegPart22Tree)))))))) (.cut 3 (1/8) (.cut 3 (1/16) (.cut 2 (5/16) (.cut 2 (7/32) (CutTop4H7NegPart23Tree) (.cut 3 (1/32) (CutTop4H7NegPart24Tree) (CutTop4H7NegPart25Tree))) (.cut 3 (1/32) (.cut 2 (13/32) (.cut 3 (1/64) (.cut 0 (135/272) (CutTop4H7NegPart26Tree) (CutTop4H7NegPart27Tree)) (CutTop4H7NegPart28Tree)) (.cut 0 (135/272) (CutTop4H7NegPart29Tree) (.cut 3 (1/64) (CutTop4H7NegPart30Tree) (CutTop4H7NegPart31Tree)))) (.cut 2 (13/32) (CutTop4H7NegPart32Tree) (CutTop4H7NegPart33Tree)))) (CutTop4H7NegPart34Tree)) (CutTop4H7NegPart35Tree)))) (.cut 2 (3/4) (.cut 3 (0) (.cut 3 (-1/8) (CutTop4H7NegPart36Tree) (.cut 3 (-1/16) (CutTop4H7NegPart37Tree) (.cut 3 (-1/32) (CutTop4H7NegPart38Tree) (.cut 0 (135/272) (CutTop4H7NegPart39Tree) (CutTop4H7NegPart40Tree))))) (.cut 3 (1/8) (CutTop4H7NegPart41Tree) (CutTop4H7NegPart42Tree))) (CutTop4H7NegPart43Tree))) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop4H7NegPart44Tree) (.cut 0 (135/272) (CutTop4H7NegPart45Tree) (.cut 3 (1/2) (.cut 3 (3/8) (.cut 0 (279/544) (CutTop4H7NegPart46Tree) (CutTop4H7NegPart47Tree)) (CutTop4H7NegPart48Tree)) (CutTop4H7NegPart49Tree)))) (CutTop4H7NegPart50Tree)))) (CutTop4H7NegPart51Tree)

set_option maxRecDepth 16000 in
theorem CutTop4H7Neg_checked : CutTop4H7NegTree.commonOK CutTop4H7NegBox false = true := CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H7NegPart0_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H7NegPart1_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H7NegPart2_checked) (CertTree.commonCut_ok (CutTop4H7NegPart3_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H7NegPart4_checked) (CertTree.commonCut_ok (CutTop4H7NegPart5_checked) (CutTop4H7NegPart6_checked))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H7NegPart7_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H7NegPart8_checked) (CutTop4H7NegPart9_checked)) (CutTop4H7NegPart10_checked))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H7NegPart11_checked) (CutTop4H7NegPart12_checked)) (CutTop4H7NegPart13_checked)) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H7NegPart14_checked) (CutTop4H7NegPart15_checked)) (CertTree.commonCut_ok (CutTop4H7NegPart16_checked) (CutTop4H7NegPart17_checked)))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H7NegPart18_checked) (CertTree.commonCut_ok (CutTop4H7NegPart19_checked) (CutTop4H7NegPart20_checked))) (CertTree.commonCut_ok (CutTop4H7NegPart21_checked) (CutTop4H7NegPart22_checked)))))))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H7NegPart23_checked) (CertTree.commonCut_ok (CutTop4H7NegPart24_checked) (CutTop4H7NegPart25_checked))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H7NegPart26_checked) (CutTop4H7NegPart27_checked)) (CutTop4H7NegPart28_checked)) (CertTree.commonCut_ok (CutTop4H7NegPart29_checked) (CertTree.commonCut_ok (CutTop4H7NegPart30_checked) (CutTop4H7NegPart31_checked)))) (CertTree.commonCut_ok (CutTop4H7NegPart32_checked) (CutTop4H7NegPart33_checked)))) (CutTop4H7NegPart34_checked)) (CutTop4H7NegPart35_checked)))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H7NegPart36_checked) (CertTree.commonCut_ok (CutTop4H7NegPart37_checked) (CertTree.commonCut_ok (CutTop4H7NegPart38_checked) (CertTree.commonCut_ok (CutTop4H7NegPart39_checked) (CutTop4H7NegPart40_checked))))) (CertTree.commonCut_ok (CutTop4H7NegPart41_checked) (CutTop4H7NegPart42_checked))) (CutTop4H7NegPart43_checked))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H7NegPart44_checked) (CertTree.commonCut_ok (CutTop4H7NegPart45_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H7NegPart46_checked) (CutTop4H7NegPart47_checked)) (CutTop4H7NegPart48_checked)) (CutTop4H7NegPart49_checked)))) (CutTop4H7NegPart50_checked)))) (CutTop4H7NegPart51_checked)

end HlawkaSchatten.BelowExponent.G3P
