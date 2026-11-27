/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.VcCornerData.Points800

/-! Checked corner data shared by the vertex middle and band regions: `Points800`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

def vcCutP800 : SideCornerEntry := ⟨9/40, 13/40, 1/18, #v[69970569/2500000000, 130210819/5000000000, 121548991/5000000000]⟩
abbrev vcCutP800Roots := vcOuterP800Roots
theorem vcCutP800_roots : vcCutP800.cell.rootsOK vcCutP800Roots = true := by decide +kernel

def vcCutP801 : SideCornerEntry := ⟨9/40, 7/20, 0, #v[4198731/156250000, 240362997/10000000000, 9640063/400000000]⟩
abbrev vcCutP801Roots := vcOuterP801Roots
theorem vcCutP801_roots : vcCutP801.cell.rootsOK vcCutP801Roots = true := by decide +kernel

def vcCutP802 : SideCornerEntry := ⟨9/40, 7/20, 1/36, #v[287022597/10000000000, 5121381/200000000, 257447773/10000000000]⟩
abbrev vcCutP802Roots := vcOuterP802Roots
theorem vcCutP802_roots : vcCutP802.cell.rootsOK vcCutP802Roots = true := by decide +kernel

def vcCutP803 : SideCornerEntry := ⟨9/40, 7/20, 1/18, #v[287022597/10000000000, 5121381/200000000, 257447773/10000000000]⟩
abbrev vcCutP803Roots := vcOuterP803Roots
theorem vcCutP803_roots : vcCutP803.cell.rootsOK vcCutP803Roots = true := by decide +kernel

def vcCutP804 : SideCornerEntry := ⟨9/40, 3/8, 0, #v[299590847/10000000000, 52546423/2000000000, 54879333/2000000000]⟩
abbrev vcCutP804Roots := vcOuterP804Roots
theorem vcCutP804_roots : vcCutP804.cell.rootsOK vcCutP804Roots = true := by decide +kernel

def vcCutP805 : SideCornerEntry := ⟨9/40, 3/8, 1/36, #v[160120159/5000000000, 279989117/10000000000, 11735139/400000000]⟩
abbrev vcCutP805Roots := vcOuterP805Roots
theorem vcCutP805_roots : vcCutP805.cell.rootsOK vcCutP805Roots = true := by decide +kernel

def vcCutP806 : SideCornerEntry := ⟨9/40, 3/8, 1/18, #v[160120159/5000000000, 279989117/10000000000, 11735139/400000000]⟩
abbrev vcCutP806Roots := vcOuterP806Roots
theorem vcCutP806_roots : vcCutP806.cell.rootsOK vcCutP806Roots = true := by decide +kernel

def vcCutP807 : SideCornerEntry := ⟨9/40, 2/5, 0, #v[299590847/10000000000, 52546423/2000000000, 54879333/2000000000]⟩
abbrev vcCutP807Roots := vcOuterP807Roots
theorem vcCutP807_roots : vcCutP807.cell.rootsOK vcCutP807Roots = true := by decide +kernel

def vcCutP808 : SideCornerEntry := ⟨9/40, 2/5, 1/36, #v[160120159/5000000000, 279989117/10000000000, 11735139/400000000]⟩
abbrev vcCutP808Roots := vcOuterP808Roots
theorem vcCutP808_roots : vcCutP808.cell.rootsOK vcCutP808Roots = true := by decide +kernel

def vcCutP809 : SideCornerEntry := ⟨9/40, 2/5, 1/18, #v[160120159/5000000000, 279989117/10000000000, 11735139/400000000]⟩
abbrev vcCutP809Roots := vcOuterP809Roots
theorem vcCutP809_roots : vcCutP809.cell.rootsOK vcCutP809Roots = true := by decide +kernel

def vcCutP810 : SideCornerEntry := ⟨1/4, 9/40, 0, #v[104470591/2500000000, 20591987/500000000, 174085393/5000000000]⟩
abbrev vcCutP810Roots := vcOuterP810Roots
theorem vcCutP810_roots : vcCutP810.cell.rootsOK vcCutP810Roots = true := by decide +kernel

def vcCutP811 : SideCornerEntry := ⟨1/4, 9/40, 1/36, #v[223352881/5000000000, 55049617/1250000000, 370781631/10000000000]⟩
abbrev vcCutP811Roots := vcOuterP811Roots
theorem vcCutP811_roots : vcCutP811.cell.rootsOK vcCutP811Roots = true := by decide +kernel

def vcCutP812 : SideCornerEntry := ⟨1/4, 9/40, 1/18, #v[223352881/5000000000, 55049617/1250000000, 370781631/10000000000]⟩
abbrev vcCutP812Roots := vcOuterP812Roots
theorem vcCutP812_roots : vcCutP812.cell.rootsOK vcCutP812Roots = true := by decide +kernel

def vcCutP813 : SideCornerEntry := ⟨1/4, 1/4, 0, #v[104470591/2500000000, 20591987/500000000, 174085393/5000000000]⟩
abbrev vcCutP813Roots := vcOuterP813Roots
theorem vcCutP813_roots : vcCutP813.cell.rootsOK vcCutP813Roots = true := by decide +kernel

def vcCutP814 : SideCornerEntry := ⟨1/4, 1/4, 1/36, #v[223352881/5000000000, 55049617/1250000000, 370781631/10000000000]⟩
abbrev vcCutP814Roots := vcOuterP814Roots
theorem vcCutP814_roots : vcCutP814.cell.rootsOK vcCutP814Roots = true := by decide +kernel

def vcCutP815 : SideCornerEntry := ⟨1/4, 1/4, 1/18, #v[223352881/5000000000, 55049617/1250000000, 370781631/10000000000]⟩
abbrev vcCutP815Roots := vcOuterP815Roots
theorem vcCutP815_roots : vcCutP815.cell.rootsOK vcCutP815Roots = true := by decide +kernel

def vcCutP816 : SideCornerEntry := ⟨1/4, 11/40, 0, #v[350655417/10000000000, 345667543/10000000000, 4818209/156250000]⟩
abbrev vcCutP816Roots := vcOuterP816Roots
theorem vcCutP816_roots : vcCutP816.cell.rootsOK vcCutP816Roots = true := by decide +kernel

def vcCutP817 : SideCornerEntry := ⟨1/4, 11/40, 1/36, #v[374797883/10000000000, 18477023/500000000, 164503183/5000000000]⟩
abbrev vcCutP817Roots := vcOuterP817Roots
theorem vcCutP817_roots : vcCutP817.cell.rootsOK vcCutP817Roots = true := by decide +kernel

def vcCutP818 : SideCornerEntry := ⟨1/4, 11/40, 1/18, #v[374797883/10000000000, 18477023/500000000, 164503183/5000000000]⟩
abbrev vcCutP818Roots := vcOuterP818Roots
theorem vcCutP818_roots : vcCutP818.cell.rootsOK vcCutP818Roots = true := by decide +kernel

def vcCutP819 : SideCornerEntry := ⟨1/4, 3/10, 0, #v[76626621/2500000000, 296638161/10000000000, 273139623/10000000000]⟩
abbrev vcCutP819Roots := vcOuterP819Roots
theorem vcCutP819_roots : vcCutP819.cell.rootsOK vcCutP819Roots = true := by decide +kernel

def vcCutP820 : SideCornerEntry := ⟨1/4, 3/10, 1/36, #v[40945893/1250000000, 63359959/2000000000, 72905837/2500000000]⟩
abbrev vcCutP820Roots := vcOuterP820Roots
theorem vcCutP820_roots : vcCutP820.cell.rootsOK vcCutP820Roots = true := by decide +kernel

def vcCutP821 : SideCornerEntry := ⟨1/4, 3/10, 1/18, #v[40945893/1250000000, 63359959/2000000000, 72905837/2500000000]⟩
abbrev vcCutP821Roots := vcOuterP821Roots
theorem vcCutP821_roots : vcCutP821.cell.rootsOK vcCutP821Roots = true := by decide +kernel

def vcCutP822 : SideCornerEntry := ⟨1/4, 13/40, 0, #v[145919787/5000000000, 137062613/5000000000, 267253127/10000000000]⟩
abbrev vcCutP822Roots := vcOuterP822Roots
theorem vcCutP822_roots : vcCutP822.cell.rootsOK vcCutP822Roots = true := by decide +kernel

def vcCutP823 : SideCornerEntry := ⟨1/4, 13/40, 1/36, #v[77985121/2500000000, 29255883/1000000000, 285731951/10000000000]⟩
abbrev vcCutP823Roots := vcOuterP823Roots
theorem vcCutP823_roots : vcCutP823.cell.rootsOK vcCutP823Roots = true := by decide +kernel

def vcCutP824 : SideCornerEntry := ⟨1/4, 13/40, 1/18, #v[77985121/2500000000, 29255883/1000000000, 285731951/10000000000]⟩
abbrev vcCutP824Roots := vcOuterP824Roots
theorem vcCutP824_roots : vcCutP824.cell.rootsOK vcCutP824Roots = true := by decide +kernel

def vcCutP825 : SideCornerEntry := ⟨1/4, 7/20, 0, #v[10015561/312500000, 36522817/1250000000, 299253667/10000000000]⟩
abbrev vcCutP825Roots := vcOuterP825Roots
theorem vcCutP825_roots : vcCutP825.cell.rootsOK vcCutP825Roots = true := by decide +kernel

def vcCutP826 : SideCornerEntry := ⟨1/4, 7/20, 1/36, #v[8569821/250000000, 311841241/10000000000, 320277229/10000000000]⟩
abbrev vcCutP826Roots := vcOuterP826Roots
theorem vcCutP826_roots : vcCutP826.cell.rootsOK vcCutP826Roots = true := by decide +kernel

def vcCutP827 : SideCornerEntry := ⟨1/4, 7/20, 1/18, #v[8569821/250000000, 311841241/10000000000, 320277229/10000000000]⟩
abbrev vcCutP827Roots := vcOuterP827Roots
theorem vcCutP827_roots : vcCutP827.cell.rootsOK vcCutP827Roots = true := by decide +kernel

def vcCutP828 : SideCornerEntry := ⟨1/4, 3/8, 0, #v[10015561/312500000, 36522817/1250000000, 299253667/10000000000]⟩
abbrev vcCutP828Roots := vcOuterP828Roots
theorem vcCutP828_roots : vcCutP828.cell.rootsOK vcCutP828Roots = true := by decide +kernel

def vcCutP829 : SideCornerEntry := ⟨1/4, 3/8, 1/36, #v[8569821/250000000, 311841241/10000000000, 320277229/10000000000]⟩
abbrev vcCutP829Roots := vcOuterP829Roots
theorem vcCutP829_roots : vcCutP829.cell.rootsOK vcCutP829Roots = true := by decide +kernel

def vcCutP830 : SideCornerEntry := ⟨1/4, 3/8, 1/18, #v[8569821/250000000, 311841241/10000000000, 320277229/10000000000]⟩
abbrev vcCutP830Roots := vcOuterP830Roots
theorem vcCutP830_roots : vcCutP830.cell.rootsOK vcCutP830Roots = true := by decide +kernel

def vcCutP831 : SideCornerEntry := ⟨1/4, 2/5, 0, #v[299590847/10000000000, 52546423/2000000000, 54879333/2000000000]⟩
abbrev vcCutP831Roots := vcOuterP831Roots
theorem vcCutP831_roots : vcCutP831.cell.rootsOK vcCutP831Roots = true := by decide +kernel

def vcCutPoints800 : Array SideCornerEntry := #[
  vcCutP800,
  vcCutP801,
  vcCutP802,
  vcCutP803,
  vcCutP804,
  vcCutP805,
  vcCutP806,
  vcCutP807,
  vcCutP808,
  vcCutP809,
  vcCutP810,
  vcCutP811,
  vcCutP812,
  vcCutP813,
  vcCutP814,
  vcCutP815,
  vcCutP816,
  vcCutP817,
  vcCutP818,
  vcCutP819,
  vcCutP820,
  vcCutP821,
  vcCutP822,
  vcCutP823,
  vcCutP824,
  vcCutP825,
  vcCutP826,
  vcCutP827,
  vcCutP828,
  vcCutP829,
  vcCutP830,
  vcCutP831]

end HlawkaSchatten.BelowExponent.Vertex
