/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.VcCornerData.Points736

/-! Checked corner data shared by the vertex middle and band regions: `Points736`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

def vcCutP736 : SideCornerEntry := ⟨7/40, 13/40, 1/36, #v[28948021/1250000000, 6477049/312500000, 92404003/5000000000]⟩
abbrev vcCutP736Roots := vcOuterP736Roots
theorem vcCutP736_roots : vcCutP736.cell.rootsOK vcCutP736Roots = true := by decide +kernel

def vcCutP737 : SideCornerEntry := ⟨7/40, 13/40, 1/18, #v[28948021/1250000000, 6477049/312500000, 92404003/5000000000]⟩
abbrev vcCutP737Roots := vcOuterP737Roots
theorem vcCutP737_roots : vcCutP737.cell.rootsOK vcCutP737Roots = true := by decide +kernel

def vcCutP738 : SideCornerEntry := ⟨7/40, 7/20, 0, #v[8126047/400000000, 44580273/2500000000, 41193927/2500000000]⟩
abbrev vcCutP738Roots := vcOuterP738Roots
theorem vcCutP738_roots : vcCutP738.cell.rootsOK vcCutP738Roots = true := by decide +kernel

def vcCutP739 : SideCornerEntry := ⟨7/40, 7/20, 1/36, #v[108083027/5000000000, 94627409/5000000000, 43785507/2500000000]⟩
abbrev vcCutP739Roots := vcOuterP739Roots
theorem vcCutP739_roots : vcCutP739.cell.rootsOK vcCutP739Roots = true := by decide +kernel

def vcCutP740 : SideCornerEntry := ⟨7/40, 7/20, 1/18, #v[108083027/5000000000, 94627409/5000000000, 43785507/2500000000]⟩
abbrev vcCutP740Roots := vcOuterP740Roots
theorem vcCutP740_roots : vcCutP740.cell.rootsOK vcCutP740Roots = true := by decide +kernel

def vcCutP741 : SideCornerEntry := ⟨7/40, 3/8, 0, #v[205673351/10000000000, 43216261/2500000000, 172855559/10000000000]⟩
abbrev vcCutP741Roots := vcOuterP741Roots
theorem vcCutP741_roots : vcCutP741.cell.rootsOK vcCutP741Roots = true := by decide +kernel

def vcCutP742 : SideCornerEntry := ⟨7/40, 3/8, 1/36, #v[54730773/2500000000, 36676871/2000000000, 18395841/1000000000]⟩
abbrev vcCutP742Roots := vcOuterP742Roots
theorem vcCutP742_roots : vcCutP742.cell.rootsOK vcCutP742Roots = true := by decide +kernel

def vcCutP743 : SideCornerEntry := ⟨7/40, 3/8, 1/18, #v[54730773/2500000000, 36676871/2000000000, 18395841/1000000000]⟩
abbrev vcCutP743Roots := vcOuterP743Roots
theorem vcCutP743_roots : vcCutP743.cell.rootsOK vcCutP743Roots = true := by decide +kernel

def vcCutP744 : SideCornerEntry := ⟨7/40, 2/5, 0, #v[222435323/10000000000, 2862047/156250000, 47825371/2500000000]⟩
abbrev vcCutP744Roots := vcOuterP744Roots
theorem vcCutP744_roots : vcCutP744.cell.rootsOK vcCutP744Roots = true := by decide +kernel

def vcCutP745 : SideCornerEntry := ⟨7/40, 2/5, 1/36, #v[118485913/5000000000, 194414721/10000000000, 40761001/2000000000]⟩
abbrev vcCutP745Roots := vcOuterP745Roots
theorem vcCutP745_roots : vcCutP745.cell.rootsOK vcCutP745Roots = true := by decide +kernel

def vcCutP746 : SideCornerEntry := ⟨7/40, 2/5, 1/18, #v[118485913/5000000000, 194414721/10000000000, 40761001/2000000000]⟩
abbrev vcCutP746Roots := vcOuterP746Roots
theorem vcCutP746_roots : vcCutP746.cell.rootsOK vcCutP746Roots = true := by decide +kernel

def vcCutP747 : SideCornerEntry := ⟨7/40, 17/40, 0, #v[222435323/10000000000, 2862047/156250000, 47825371/2500000000]⟩
abbrev vcCutP747Roots := vcOuterP747Roots
theorem vcCutP747_roots : vcCutP747.cell.rootsOK vcCutP747Roots = true := by decide +kernel

def vcCutP748 : SideCornerEntry := ⟨7/40, 17/40, 1/36, #v[118485913/5000000000, 194414721/10000000000, 40761001/2000000000]⟩
abbrev vcCutP748Roots := vcOuterP748Roots
theorem vcCutP748_roots : vcCutP748.cell.rootsOK vcCutP748Roots = true := by decide +kernel

def vcCutP749 : SideCornerEntry := ⟨7/40, 17/40, 1/18, #v[118485913/5000000000, 194414721/10000000000, 40761001/2000000000]⟩
abbrev vcCutP749Roots := vcOuterP749Roots
theorem vcCutP749_roots : vcCutP749.cell.rootsOK vcCutP749Roots = true := by decide +kernel

def vcCutP750 : SideCornerEntry := ⟨1/5, 7/40, 0, #v[100702893/2500000000, 401737917/10000000000, 276239001/10000000000]⟩
abbrev vcCutP750Roots := vcOuterP750Roots
theorem vcCutP750_roots : vcCutP750.cell.rootsOK vcCutP750Roots = true := by decide +kernel

def vcCutP751 : SideCornerEntry := ⟨1/5, 7/40, 1/36, #v[429560631/10000000000, 214234939/5000000000, 292654513/10000000000]⟩
abbrev vcCutP751Roots := vcOuterP751Roots
theorem vcCutP751_roots : vcCutP751.cell.rootsOK vcCutP751Roots = true := by decide +kernel

def vcCutP752 : SideCornerEntry := ⟨1/5, 7/40, 1/18, #v[429560631/10000000000, 214234939/5000000000, 292654513/10000000000]⟩
abbrev vcCutP752Roots := vcOuterP752Roots
theorem vcCutP752_roots : vcCutP752.cell.rootsOK vcCutP752Roots = true := by decide +kernel

def vcCutP753 : SideCornerEntry := ⟨1/5, 1/5, 0, #v[68213639/1250000000, 26849617/500000000, 214246573/5000000000]⟩
abbrev vcCutP753Roots := vcOuterP753Roots
theorem vcCutP753_roots : vcCutP753.cell.rootsOK vcCutP753Roots = true := by decide +kernel

def vcCutP754 : SideCornerEntry := ⟨1/5, 1/5, 1/36, #v[68213639/1250000000, 26849617/500000000, 214246573/5000000000]⟩
abbrev vcCutP754Roots := vcOuterP754Roots
theorem vcCutP754_roots : vcCutP754.cell.rootsOK vcCutP754Roots = true := by decide +kernel

def vcCutP755 : SideCornerEntry := ⟨1/5, 1/5, 1/18, #v[429560631/10000000000, 214234939/5000000000, 292654513/10000000000]⟩
abbrev vcCutP755Roots := vcOuterP755Roots
theorem vcCutP755_roots : vcCutP755.cell.rootsOK vcCutP755Roots = true := by decide +kernel

def vcCutP756 : SideCornerEntry := ⟨1/5, 9/40, 0, #v[68213639/1250000000, 26849617/500000000, 214246573/5000000000]⟩
abbrev vcCutP756Roots := vcOuterP756Roots
theorem vcCutP756_roots : vcCutP756.cell.rootsOK vcCutP756Roots = true := by decide +kernel

def vcCutP757 : SideCornerEntry := ⟨1/5, 9/40, 1/36, #v[68213639/1250000000, 26849617/500000000, 214246573/5000000000]⟩
abbrev vcCutP757Roots := vcOuterP757Roots
theorem vcCutP757_roots : vcCutP757.cell.rootsOK vcCutP757Roots = true := by decide +kernel

def vcCutP758 : SideCornerEntry := ⟨1/5, 9/40, 1/18, #v[212652623/5000000000, 206112323/5000000000, 169330227/5000000000]⟩
abbrev vcCutP758Roots := vcOuterP758Roots
theorem vcCutP758_roots : vcCutP758.cell.rootsOK vcCutP758Roots = true := by decide +kernel

def vcCutP759 : SideCornerEntry := ⟨1/5, 1/4, 0, #v[398075439/10000000000, 385880283/10000000000, 159257381/5000000000]⟩
abbrev vcCutP759Roots := vcOuterP759Roots
theorem vcCutP759_roots : vcCutP759.cell.rootsOK vcCutP759Roots = true := by decide +kernel

def vcCutP760 : SideCornerEntry := ⟨1/5, 1/4, 1/36, #v[212652623/5000000000, 206112323/5000000000, 169330227/5000000000]⟩
abbrev vcCutP760Roots := vcOuterP760Roots
theorem vcCutP760_roots : vcCutP760.cell.rootsOK vcCutP760Roots = true := by decide +kernel

def vcCutP761 : SideCornerEntry := ⟨1/5, 1/4, 1/18, #v[212652623/5000000000, 206112323/5000000000, 169330227/5000000000]⟩
abbrev vcCutP761Roots := vcOuterP761Roots
theorem vcCutP761_roots : vcCutP761.cell.rootsOK vcCutP761Roots = true := by decide +kernel

def vcCutP762 : SideCornerEntry := ⟨1/5, 11/40, 0, #v[9817083/312500000, 14951027/500000000, 798431/31250000]⟩
abbrev vcCutP762Roots := vcOuterP762Roots
theorem vcCutP762_roots : vcCutP762.cell.rootsOK vcCutP762Roots = true := by decide +kernel

def vcCutP763 : SideCornerEntry := ⟨1/5, 11/40, 1/36, #v[8384189/250000000, 31902167/1000000000, 33970523/1250000000]⟩
abbrev vcCutP763Roots := vcOuterP763Roots
theorem vcCutP763_roots : vcCutP763.cell.rootsOK vcCutP763Roots = true := by decide +kernel

def vcCutP764 : SideCornerEntry := ⟨1/5, 11/40, 1/18, #v[8384189/250000000, 31902167/1000000000, 33970523/1250000000]⟩
abbrev vcCutP764Roots := vcOuterP764Roots
theorem vcCutP764_roots : vcCutP764.cell.rootsOK vcCutP764Roots = true := by decide +kernel

def vcCutP765 : SideCornerEntry := ⟨1/5, 3/10, 0, #v[53089983/2000000000, 247742387/10000000000, 218827233/10000000000]⟩
abbrev vcCutP765Roots := vcOuterP765Roots
theorem vcCutP765_roots : vcCutP765.cell.rootsOK vcCutP765Roots = true := by decide +kernel

def vcCutP766 : SideCornerEntry := ⟨1/5, 3/10, 1/36, #v[283177499/10000000000, 131987791/5000000000, 232872303/10000000000]⟩
abbrev vcCutP766Roots := vcOuterP766Roots
theorem vcCutP766_roots : vcCutP766.cell.rootsOK vcCutP766Roots = true := by decide +kernel

def vcCutP767 : SideCornerEntry := ⟨1/5, 3/10, 1/18, #v[283177499/10000000000, 131987791/5000000000, 232872303/10000000000]⟩
abbrev vcCutP767Roots := vcOuterP767Roots
theorem vcCutP767_roots : vcCutP767.cell.rootsOK vcCutP767Roots = true := by decide +kernel

def vcCutPoints736 : Array SideCornerEntry := #[
  vcCutP736,
  vcCutP737,
  vcCutP738,
  vcCutP739,
  vcCutP740,
  vcCutP741,
  vcCutP742,
  vcCutP743,
  vcCutP744,
  vcCutP745,
  vcCutP746,
  vcCutP747,
  vcCutP748,
  vcCutP749,
  vcCutP750,
  vcCutP751,
  vcCutP752,
  vcCutP753,
  vcCutP754,
  vcCutP755,
  vcCutP756,
  vcCutP757,
  vcCutP758,
  vcCutP759,
  vcCutP760,
  vcCutP761,
  vcCutP762,
  vcCutP763,
  vcCutP764,
  vcCutP765,
  vcCutP766,
  vcCutP767]

end HlawkaSchatten.BelowExponent.Vertex
