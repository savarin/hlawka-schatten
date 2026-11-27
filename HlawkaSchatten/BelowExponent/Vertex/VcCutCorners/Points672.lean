/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.VcCornerData.Points672

/-! Checked corner data shared by the vertex middle and band regions: `Points672`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

def vcCutP672 : SideCornerEntry := ⟨3/20, 1/8, 0, #v[456713681/10000000000, 460978407/10000000000, 230940813/10000000000]⟩
abbrev vcCutP672Roots := vcOuterP672Roots
theorem vcCutP672_roots : vcCutP672.cell.rootsOK vcCutP672Roots = true := by decide +kernel

def vcCutP673 : SideCornerEntry := ⟨3/20, 1/8, 1/36, #v[456713681/10000000000, 460978407/10000000000, 230940813/10000000000]⟩
abbrev vcCutP673Roots := vcOuterP673Roots
theorem vcCutP673_roots : vcCutP673.cell.rootsOK vcCutP673Roots = true := by decide +kernel

def vcCutP674 : SideCornerEntry := ⟨3/20, 1/8, 1/18, #v[68166737/2000000000, 345338239/10000000000, 153989173/10000000000]⟩
abbrev vcCutP674Roots := vcOuterP674Roots
theorem vcCutP674_roots : vcCutP674.cell.rootsOK vcCutP674Roots = true := by decide +kernel

def vcCutP675 : SideCornerEntry := ⟨3/20, 3/20, 0, #v[456713681/10000000000, 460978407/10000000000, 230940813/10000000000]⟩
abbrev vcCutP675Roots := vcOuterP675Roots
theorem vcCutP675_roots : vcCutP675.cell.rootsOK vcCutP675Roots = true := by decide +kernel

def vcCutP676 : SideCornerEntry := ⟨3/20, 3/20, 1/36, #v[456713681/10000000000, 460978407/10000000000, 230940813/10000000000]⟩
abbrev vcCutP676Roots := vcOuterP676Roots
theorem vcCutP676_roots : vcCutP676.cell.rootsOK vcCutP676Roots = true := by decide +kernel

def vcCutP677 : SideCornerEntry := ⟨3/20, 3/20, 1/18, #v[176001109/5000000000, 88689743/2500000000, 50224251/2500000000]⟩
abbrev vcCutP677Roots := vcOuterP677Roots
theorem vcCutP677_roots : vcCutP677.cell.rootsOK vcCutP677Roots = true := by decide +kernel

def vcCutP678 : SideCornerEntry := ⟨3/20, 7/40, 0, #v[193795713/5000000000, 378502271/10000000000, 125092609/5000000000]⟩
abbrev vcCutP678Roots := vcOuterP678Roots
theorem vcCutP678_roots : vcCutP678.cell.rootsOK vcCutP678Roots = true := by decide +kernel

def vcCutP679 : SideCornerEntry := ⟨3/20, 7/40, 1/36, #v[412918721/10000000000, 40326923/1000000000, 264752719/10000000000]⟩
abbrev vcCutP679Roots := vcOuterP679Roots
theorem vcCutP679_roots : vcCutP679.cell.rootsOK vcCutP679Roots = true := by decide +kernel

def vcCutP680 : SideCornerEntry := ⟨3/20, 7/40, 1/18, #v[412918721/10000000000, 40326923/1000000000, 264752719/10000000000]⟩
abbrev vcCutP680Roots := vcOuterP680Roots
theorem vcCutP680_roots : vcCutP680.cell.rootsOK vcCutP680Roots = true := by decide +kernel

def vcCutP681 : SideCornerEntry := ⟨3/20, 1/5, 0, #v[479069317/10000000000, 91319887/2000000000, 343586397/10000000000]⟩
abbrev vcCutP681Roots := vcOuterP681Roots
theorem vcCutP681_roots : vcCutP681.cell.rootsOK vcCutP681Roots = true := by decide +kernel

def vcCutP682 : SideCornerEntry := ⟨3/20, 1/5, 1/36, #v[479069317/10000000000, 91319887/2000000000, 343586397/10000000000]⟩
abbrev vcCutP682Roots := vcOuterP682Roots
theorem vcCutP682_roots : vcCutP682.cell.rootsOK vcCutP682Roots = true := by decide +kernel

def vcCutP683 : SideCornerEntry := ⟨3/20, 1/5, 1/18, #v[58320017/1250000000, 219016339/5000000000, 315127711/10000000000]⟩
abbrev vcCutP683Roots := vcOuterP683Roots
theorem vcCutP683_roots : vcCutP683.cell.rootsOK vcCutP683Roots = true := by decide +kernel

def vcCutP684 : SideCornerEntry := ⟨3/20, 9/40, 0, #v[479069317/10000000000, 91319887/2000000000, 343586397/10000000000]⟩
abbrev vcCutP684Roots := vcOuterP684Roots
theorem vcCutP684_roots : vcCutP684.cell.rootsOK vcCutP684Roots = true := by decide +kernel

def vcCutP685 : SideCornerEntry := ⟨3/20, 9/40, 1/36, #v[479069317/10000000000, 91319887/2000000000, 343586397/10000000000]⟩
abbrev vcCutP685Roots := vcOuterP685Roots
theorem vcCutP685_roots : vcCutP685.cell.rootsOK vcCutP685Roots = true := by decide +kernel

def vcCutP686 : SideCornerEntry := ⟨3/20, 9/40, 1/18, #v[58320017/1250000000, 219016339/5000000000, 315127711/10000000000]⟩
abbrev vcCutP686Roots := vcOuterP686Roots
theorem vcCutP686_roots : vcCutP686.cell.rootsOK vcCutP686Roots = true := by decide +kernel

def vcCutP687 : SideCornerEntry := ⟨3/20, 1/4, 0, #v[348598489/10000000000, 326601991/10000000000, 254975381/10000000000]⟩
abbrev vcCutP687Roots := vcOuterP687Roots
theorem vcCutP687_roots : vcCutP687.cell.rootsOK vcCutP687Roots = true := by decide +kernel

def vcCutP688 : SideCornerEntry := ⟨3/20, 1/4, 1/36, #v[371726047/10000000000, 348005567/10000000000, 54052089/2000000000]⟩
abbrev vcCutP688Roots := vcOuterP688Roots
theorem vcCutP688_roots : vcCutP688.cell.rootsOK vcCutP688Roots = true := by decide +kernel

def vcCutP689 : SideCornerEntry := ⟨3/20, 1/4, 1/18, #v[371726047/10000000000, 348005567/10000000000, 54052089/2000000000]⟩
abbrev vcCutP689Roots := vcOuterP689Roots
theorem vcCutP689_roots : vcCutP689.cell.rootsOK vcCutP689Roots = true := by decide +kernel

def vcCutP690 : SideCornerEntry := ⟨3/20, 11/40, 0, #v[272274463/10000000000, 31275289/1250000000, 50530079/2500000000]⟩
abbrev vcCutP690Roots := vcOuterP690Roots
theorem vcCutP690_roots : vcCutP690.cell.rootsOK vcCutP690Roots = true := by decide +kernel

def vcCutP691 : SideCornerEntry := ⟨3/20, 11/40, 1/36, #v[144946269/5000000000, 53215189/2000000000, 13384909/625000000]⟩
abbrev vcCutP691Roots := vcOuterP691Roots
theorem vcCutP691_roots : vcCutP691.cell.rootsOK vcCutP691Roots = true := by decide +kernel

def vcCutP692 : SideCornerEntry := ⟨3/20, 11/40, 1/18, #v[144946269/5000000000, 53215189/2000000000, 13384909/625000000]⟩
abbrev vcCutP692Roots := vcOuterP692Roots
theorem vcCutP692_roots : vcCutP692.cell.rootsOK vcCutP692Roots = true := by decide +kernel

def vcCutP693 : SideCornerEntry := ⟨3/20, 3/10, 0, #v[226392413/10000000000, 40750359/2000000000, 170286391/10000000000]⟩
abbrev vcCutP693Roots := vcOuterP693Roots
theorem vcCutP693_roots : vcCutP693.cell.rootsOK vcCutP693Roots = true := by decide +kernel

def vcCutP694 : SideCornerEntry := ⟨3/20, 3/10, 1/36, #v[240676223/10000000000, 6758679/312500000, 180344753/10000000000]⟩
abbrev vcCutP694Roots := vcOuterP694Roots
theorem vcCutP694_roots : vcCutP694.cell.rootsOK vcCutP694Roots = true := by decide +kernel

def vcCutP695 : SideCornerEntry := ⟨3/20, 3/10, 1/18, #v[240676223/10000000000, 6758679/312500000, 180344753/10000000000]⟩
abbrev vcCutP695Roots := vcOuterP695Roots
theorem vcCutP695_roots : vcCutP695.cell.rootsOK vcCutP695Roots = true := by decide +kernel

def vcCutP696 : SideCornerEntry := ⟨3/20, 13/40, 0, #v[9921907/500000000, 34962613/2000000000, 151241617/10000000000]⟩
abbrev vcCutP696Roots := vcOuterP696Roots
theorem vcCutP696_roots : vcCutP696.cell.rootsOK vcCutP696Roots = true := by decide +kernel

def vcCutP697 : SideCornerEntry := ⟨3/20, 13/40, 1/36, #v[210782111/10000000000, 185247493/10000000000, 160267747/10000000000]⟩
abbrev vcCutP697Roots := vcOuterP697Roots
theorem vcCutP697_roots : vcCutP697.cell.rootsOK vcCutP697Roots = true := by decide +kernel

def vcCutP698 : SideCornerEntry := ⟨3/20, 13/40, 1/18, #v[210782111/10000000000, 185247493/10000000000, 160267747/10000000000]⟩
abbrev vcCutP698Roots := vcOuterP698Roots
theorem vcCutP698_roots : vcCutP698.cell.rootsOK vcCutP698Roots = true := by decide +kernel

def vcCutP699 : SideCornerEntry := ⟨3/20, 7/20, 0, #v[91247133/5000000000, 157194577/10000000000, 7057731/500000000]⟩
abbrev vcCutP699Roots := vcOuterP699Roots
theorem vcCutP699_roots : vcCutP699.cell.rootsOK vcCutP699Roots = true := by decide +kernel

def vcCutP700 : SideCornerEntry := ⟨3/20, 7/20, 1/36, #v[38740443/2000000000, 83191031/5000000000, 18701441/1250000000]⟩
abbrev vcCutP700Roots := vcOuterP700Roots
theorem vcCutP700_roots : vcCutP700.cell.rootsOK vcCutP700Roots = true := by decide +kernel

def vcCutP701 : SideCornerEntry := ⟨3/20, 7/20, 1/18, #v[38740443/2000000000, 83191031/5000000000, 18701441/1250000000]⟩
abbrev vcCutP701Roots := vcOuterP701Roots
theorem vcCutP701_roots : vcCutP701.cell.rootsOK vcCutP701Roots = true := by decide +kernel

def vcCutP702 : SideCornerEntry := ⟨3/20, 3/8, 0, #v[87827373/5000000000, 36903721/2500000000, 35206571/2500000000]⟩
abbrev vcCutP702Roots := vcOuterP702Roots
theorem vcCutP702_roots : vcCutP702.cell.rootsOK vcCutP702Roots = true := by decide +kernel

def vcCutP703 : SideCornerEntry := ⟨3/20, 3/8, 1/36, #v[186396533/10000000000, 156130079/10000000000, 9336007/625000000]⟩
abbrev vcCutP703Roots := vcOuterP703Roots
theorem vcCutP703_roots : vcCutP703.cell.rootsOK vcCutP703Roots = true := by decide +kernel

def vcCutPoints672 : Array SideCornerEntry := #[
  vcCutP672,
  vcCutP673,
  vcCutP674,
  vcCutP675,
  vcCutP676,
  vcCutP677,
  vcCutP678,
  vcCutP679,
  vcCutP680,
  vcCutP681,
  vcCutP682,
  vcCutP683,
  vcCutP684,
  vcCutP685,
  vcCutP686,
  vcCutP687,
  vcCutP688,
  vcCutP689,
  vcCutP690,
  vcCutP691,
  vcCutP692,
  vcCutP693,
  vcCutP694,
  vcCutP695,
  vcCutP696,
  vcCutP697,
  vcCutP698,
  vcCutP699,
  vcCutP700,
  vcCutP701,
  vcCutP702,
  vcCutP703]

end HlawkaSchatten.BelowExponent.Vertex
