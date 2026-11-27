/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.VcCornerData.Points768

/-! Checked corner data shared by the vertex middle and band regions: `Points768`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

def vcCutP768 : SideCornerEntry := ⟨1/5, 13/40, 0, #v[11943297/500000000, 218359423/10000000000, 99738211/5000000000]⟩
abbrev vcCutP768Roots := vcOuterP768Roots
theorem vcCutP768_roots : vcCutP768.cell.rootsOK vcCutP768Roots = true := by decide +kernel

def vcCutP769 : SideCornerEntry := ⟨1/5, 13/40, 1/36, #v[127360433/5000000000, 7263201/312500000, 13277209/625000000]⟩
abbrev vcCutP769Roots := vcOuterP769Roots
theorem vcCutP769_roots : vcCutP769.cell.rootsOK vcCutP769Roots = true := by decide +kernel

def vcCutP770 : SideCornerEntry := ⟨1/5, 13/40, 1/18, #v[127360433/5000000000, 7263201/312500000, 13277209/625000000]⟩
abbrev vcCutP770Roots := vcOuterP770Roots
theorem vcCutP770_roots : vcCutP770.cell.rootsOK vcCutP770Roots = true := by decide +kernel

def vcCutP771 : SideCornerEntry := ⟨1/5, 7/20, 0, #v[22944889/1000000000, 40766789/2000000000, 197447917/10000000000]⟩
abbrev vcCutP771Roots := vcOuterP771Roots
theorem vcCutP771_roots : vcCutP771.cell.rootsOK vcCutP771Roots = true := by decide +kernel

def vcCutP772 : SideCornerEntry := ⟨1/5, 7/20, 1/36, #v[61163557/2500000000, 108396587/5000000000, 210491287/10000000000]⟩
abbrev vcCutP772Roots := vcOuterP772Roots
theorem vcCutP772_roots : vcCutP772.cell.rootsOK vcCutP772Roots = true := by decide +kernel

def vcCutP773 : SideCornerEntry := ⟨1/5, 7/20, 1/18, #v[61163557/2500000000, 108396587/5000000000, 210491287/10000000000]⟩
abbrev vcCutP773Roots := vcOuterP773Roots
theorem vcCutP773_roots : vcCutP773.cell.rootsOK vcCutP773Roots = true := by decide +kernel

def vcCutP774 : SideCornerEntry := ⟨1/5, 3/8, 0, #v[245804533/10000000000, 2111067/100000000, 215964999/10000000000]⟩
abbrev vcCutP774Roots := vcOuterP774Roots
theorem vcCutP774_roots : vcCutP774.cell.rootsOK vcCutP774Roots = true := by decide +kernel

def vcCutP775 : SideCornerEntry := ⟨1/5, 3/8, 1/36, #v[262269591/10000000000, 224526763/10000000000, 115220323/5000000000]⟩
abbrev vcCutP775Roots := vcOuterP775Roots
theorem vcCutP775_roots : vcCutP775.cell.rootsOK vcCutP775Roots = true := by decide +kernel

def vcCutP776 : SideCornerEntry := ⟨1/5, 3/8, 1/18, #v[262269591/10000000000, 224526763/10000000000, 115220323/5000000000]⟩
abbrev vcCutP776Roots := vcOuterP776Roots
theorem vcCutP776_roots : vcCutP776.cell.rootsOK vcCutP776Roots = true := by decide +kernel

def vcCutP777 : SideCornerEntry := ⟨1/5, 2/5, 0, #v[245804533/10000000000, 2111067/100000000, 215964999/10000000000]⟩
abbrev vcCutP777Roots := vcOuterP777Roots
theorem vcCutP777_roots : vcCutP777.cell.rootsOK vcCutP777Roots = true := by decide +kernel

def vcCutP778 : SideCornerEntry := ⟨1/5, 2/5, 1/36, #v[262269591/10000000000, 224526763/10000000000, 115220323/5000000000]⟩
abbrev vcCutP778Roots := vcOuterP778Roots
theorem vcCutP778_roots : vcCutP778.cell.rootsOK vcCutP778Roots = true := by decide +kernel

def vcCutP779 : SideCornerEntry := ⟨1/5, 2/5, 1/18, #v[262269591/10000000000, 224526763/10000000000, 115220323/5000000000]⟩
abbrev vcCutP779Roots := vcOuterP779Roots
theorem vcCutP779_roots : vcCutP779.cell.rootsOK vcCutP779Roots = true := by decide +kernel

def vcCutP780 : SideCornerEntry := ⟨1/5, 17/40, 0, #v[222435323/10000000000, 2862047/156250000, 47825371/2500000000]⟩
abbrev vcCutP780Roots := vcOuterP780Roots
theorem vcCutP780_roots : vcCutP780.cell.rootsOK vcCutP780Roots = true := by decide +kernel

def vcCutP781 : SideCornerEntry := ⟨1/5, 17/40, 1/36, #v[118485913/5000000000, 194414721/10000000000, 40761001/2000000000]⟩
abbrev vcCutP781Roots := vcOuterP781Roots
theorem vcCutP781_roots : vcCutP781.cell.rootsOK vcCutP781Roots = true := by decide +kernel

def vcCutP782 : SideCornerEntry := ⟨1/5, 17/40, 1/18, #v[118485913/5000000000, 194414721/10000000000, 40761001/2000000000]⟩
abbrev vcCutP782Roots := vcOuterP782Roots
theorem vcCutP782_roots : vcCutP782.cell.rootsOK vcCutP782Roots = true := by decide +kernel

def vcCutP783 : SideCornerEntry := ⟨9/40, 1/5, 0, #v[68213639/1250000000, 26849617/500000000, 214246573/5000000000]⟩
abbrev vcCutP783Roots := vcOuterP783Roots
theorem vcCutP783_roots : vcCutP783.cell.rootsOK vcCutP783Roots = true := by decide +kernel

def vcCutP784 : SideCornerEntry := ⟨9/40, 1/5, 1/36, #v[68213639/1250000000, 26849617/500000000, 214246573/5000000000]⟩
abbrev vcCutP784Roots := vcOuterP784Roots
theorem vcCutP784_roots : vcCutP784.cell.rootsOK vcCutP784Roots = true := by decide +kernel

def vcCutP785 : SideCornerEntry := ⟨9/40, 1/5, 1/18, #v[305717563/10000000000, 152625557/5000000000, 112154727/5000000000]⟩
abbrev vcCutP785Roots := vcOuterP785Roots
theorem vcCutP785_roots : vcCutP785.cell.rootsOK vcCutP785Roots = true := by decide +kernel

def vcCutP786 : SideCornerEntry := ⟨9/40, 9/40, 0, #v[68213639/1250000000, 26849617/500000000, 214246573/5000000000]⟩
abbrev vcCutP786Roots := vcOuterP786Roots
theorem vcCutP786_roots : vcCutP786.cell.rootsOK vcCutP786Roots = true := by decide +kernel

def vcCutP787 : SideCornerEntry := ⟨9/40, 9/40, 1/36, #v[68213639/1250000000, 26849617/500000000, 214246573/5000000000]⟩
abbrev vcCutP787Roots := vcOuterP787Roots
theorem vcCutP787_roots : vcCutP787.cell.rootsOK vcCutP787Roots = true := by decide +kernel

def vcCutP788 : SideCornerEntry := ⟨9/40, 9/40, 1/18, #v[223352881/5000000000, 55049617/1250000000, 370781631/10000000000]⟩
abbrev vcCutP788Roots := vcOuterP788Roots
theorem vcCutP788_roots : vcCutP788.cell.rootsOK vcCutP788Roots = true := by decide +kernel

def vcCutP789 : SideCornerEntry := ⟨9/40, 1/4, 0, #v[104470591/2500000000, 20591987/500000000, 174085393/5000000000]⟩
abbrev vcCutP789Roots := vcOuterP789Roots
theorem vcCutP789_roots : vcCutP789.cell.rootsOK vcCutP789Roots = true := by decide +kernel

def vcCutP790 : SideCornerEntry := ⟨9/40, 1/4, 1/36, #v[223352881/5000000000, 55049617/1250000000, 370781631/10000000000]⟩
abbrev vcCutP790Roots := vcOuterP790Roots
theorem vcCutP790_roots : vcCutP790.cell.rootsOK vcCutP790Roots = true := by decide +kernel

def vcCutP791 : SideCornerEntry := ⟨9/40, 1/4, 1/18, #v[223352881/5000000000, 55049617/1250000000, 370781631/10000000000]⟩
abbrev vcCutP791Roots := vcOuterP791Roots
theorem vcCutP791_roots : vcCutP791.cell.rootsOK vcCutP791Roots = true := by decide +kernel

def vcCutP792 : SideCornerEntry := ⟨9/40, 11/40, 0, #v[332838071/10000000000, 64506709/2000000000, 56346227/2000000000]⟩
abbrev vcCutP792Roots := vcOuterP792Roots
theorem vcCutP792_roots : vcCutP792.cell.rootsOK vcCutP792Roots = true := by decide +kernel

def vcCutP793 : SideCornerEntry := ⟨9/40, 11/40, 1/36, #v[177784857/5000000000, 172224919/5000000000, 150035683/5000000000]⟩
abbrev vcCutP793Roots := vcOuterP793Roots
theorem vcCutP793_roots : vcCutP793.cell.rootsOK vcCutP793Roots = true := by decide +kernel

def vcCutP794 : SideCornerEntry := ⟨9/40, 11/40, 1/18, #v[177784857/5000000000, 172224919/5000000000, 150035683/5000000000]⟩
abbrev vcCutP794Roots := vcOuterP794Roots
theorem vcCutP794_roots : vcCutP794.cell.rootsOK vcCutP794Roots = true := by decide +kernel

def vcCutP795 : SideCornerEntry := ⟨9/40, 3/10, 0, #v[35663487/1250000000, 271327063/10000000000, 244770563/10000000000]⟩
abbrev vcCutP795Roots := vcOuterP795Roots
theorem vcCutP795_roots : vcCutP795.cell.rootsOK vcCutP795Roots = true := by decide +kernel

def vcCutP796 : SideCornerEntry := ⟨9/40, 3/10, 1/36, #v[60935877/2000000000, 72363741/2500000000, 130461709/5000000000]⟩
abbrev vcCutP796Roots := vcOuterP796Roots
theorem vcCutP796_roots : vcCutP796.cell.rootsOK vcCutP796Roots = true := by decide +kernel

def vcCutP797 : SideCornerEntry := ⟨9/40, 3/10, 1/18, #v[60935877/2000000000, 72363741/2500000000, 130461709/5000000000]⟩
abbrev vcCutP797Roots := vcOuterP797Roots
theorem vcCutP797_roots : vcCutP797.cell.rootsOK vcCutP797Roots = true := by decide +kernel

def vcCutP798 : SideCornerEntry := ⟨9/40, 13/40, 0, #v[262141623/10000000000, 244306023/10000000000, 227876463/10000000000]⟩
abbrev vcCutP798Roots := vcOuterP798Roots
theorem vcCutP798_roots : vcCutP798.cell.rootsOK vcCutP798Roots = true := by decide +kernel

def vcCutP799 : SideCornerEntry := ⟨9/40, 13/40, 1/36, #v[69970569/2500000000, 130210819/5000000000, 121548991/5000000000]⟩
abbrev vcCutP799Roots := vcOuterP799Roots
theorem vcCutP799_roots : vcCutP799.cell.rootsOK vcCutP799Roots = true := by decide +kernel

def vcCutPoints768 : Array SideCornerEntry := #[
  vcCutP768,
  vcCutP769,
  vcCutP770,
  vcCutP771,
  vcCutP772,
  vcCutP773,
  vcCutP774,
  vcCutP775,
  vcCutP776,
  vcCutP777,
  vcCutP778,
  vcCutP779,
  vcCutP780,
  vcCutP781,
  vcCutP782,
  vcCutP783,
  vcCutP784,
  vcCutP785,
  vcCutP786,
  vcCutP787,
  vcCutP788,
  vcCutP789,
  vcCutP790,
  vcCutP791,
  vcCutP792,
  vcCutP793,
  vcCutP794,
  vcCutP795,
  vcCutP796,
  vcCutP797,
  vcCutP798,
  vcCutP799]

end HlawkaSchatten.BelowExponent.Vertex
