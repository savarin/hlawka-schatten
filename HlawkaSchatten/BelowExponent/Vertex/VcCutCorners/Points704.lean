/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.VcCornerData.Points704

/-! Checked corner data shared by the vertex middle and band regions: `Points704`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

def vcCutP704 : SideCornerEntry := ⟨3/20, 3/8, 1/18, #v[186396533/10000000000, 156130079/10000000000, 9336007/625000000]⟩
abbrev vcCutP704Roots := vcOuterP704Roots
theorem vcCutP704_roots : vcCutP704.cell.rootsOK vcCutP704Roots = true := by decide +kernel

def vcCutP705 : SideCornerEntry := ⟨3/20, 2/5, 0, #v[3667391/200000000, 3693387/250000000, 150515209/10000000000]⟩
abbrev vcCutP705Roots := vcOuterP705Roots
theorem vcCutP705_roots : vcCutP705.cell.rootsOK vcCutP705Roots = true := by decide +kernel

def vcCutP706 : SideCornerEntry := ⟨3/20, 2/5, 1/36, #v[97360377/5000000000, 78135697/5000000000, 159799077/10000000000]⟩
abbrev vcCutP706Roots := vcOuterP706Roots
theorem vcCutP706_roots : vcCutP706.cell.rootsOK vcCutP706Roots = true := by decide +kernel

def vcCutP707 : SideCornerEntry := ⟨3/20, 2/5, 1/18, #v[97360377/5000000000, 78135697/5000000000, 159799077/10000000000]⟩
abbrev vcCutP707Roots := vcOuterP707Roots
theorem vcCutP707_roots : vcCutP707.cell.rootsOK vcCutP707Roots = true := by decide +kernel

def vcCutP708 : SideCornerEntry := ⟨3/20, 17/40, 0, #v[3667391/200000000, 3693387/250000000, 150515209/10000000000]⟩
abbrev vcCutP708Roots := vcOuterP708Roots
theorem vcCutP708_roots : vcCutP708.cell.rootsOK vcCutP708Roots = true := by decide +kernel

def vcCutP709 : SideCornerEntry := ⟨3/20, 17/40, 1/36, #v[97360377/5000000000, 78135697/5000000000, 159799077/10000000000]⟩
abbrev vcCutP709Roots := vcOuterP709Roots
theorem vcCutP709_roots : vcCutP709.cell.rootsOK vcCutP709Roots = true := by decide +kernel

def vcCutP710 : SideCornerEntry := ⟨3/20, 17/40, 1/18, #v[97360377/5000000000, 78135697/5000000000, 159799077/10000000000]⟩
abbrev vcCutP710Roots := vcOuterP710Roots
theorem vcCutP710_roots : vcCutP710.cell.rootsOK vcCutP710Roots = true := by decide +kernel

def vcCutP711 : SideCornerEntry := ⟨3/20, 9/20, 0, #v[20305099/1250000000, 25087721/2000000000, 16282769/1250000000]⟩
abbrev vcCutP711Roots := vcOuterP711Roots
theorem vcCutP711_roots : vcCutP711.cell.rootsOK vcCutP711Roots = true := by decide +kernel

def vcCutP712 : SideCornerEntry := ⟨3/20, 9/20, 1/36, #v[171977467/10000000000, 33058573/2500000000, 68939599/5000000000]⟩
abbrev vcCutP712Roots := vcOuterP712Roots
theorem vcCutP712_roots : vcCutP712.cell.rootsOK vcCutP712Roots = true := by decide +kernel

def vcCutP713 : SideCornerEntry := ⟨3/20, 9/20, 1/18, #v[171977467/10000000000, 33058573/2500000000, 68939599/5000000000]⟩
abbrev vcCutP713Roots := vcOuterP713Roots
theorem vcCutP713_roots : vcCutP713.cell.rootsOK vcCutP713Roots = true := by decide +kernel

def vcCutP714 : SideCornerEntry := ⟨7/40, 3/20, 0, #v[4134979/125000000, 333453291/10000000000, 190092609/10000000000]⟩
abbrev vcCutP714Roots := vcOuterP714Roots
theorem vcCutP714_roots : vcCutP714.cell.rootsOK vcCutP714Roots = true := by decide +kernel

def vcCutP715 : SideCornerEntry := ⟨7/40, 3/20, 1/36, #v[176001109/5000000000, 88689743/2500000000, 50224251/2500000000]⟩
abbrev vcCutP715Roots := vcOuterP715Roots
theorem vcCutP715_roots : vcCutP715.cell.rootsOK vcCutP715Roots = true := by decide +kernel

def vcCutP716 : SideCornerEntry := ⟨7/40, 3/20, 1/18, #v[176001109/5000000000, 88689743/2500000000, 50224251/2500000000]⟩
abbrev vcCutP716Roots := vcOuterP716Roots
theorem vcCutP716_roots : vcCutP716.cell.rootsOK vcCutP716Roots = true := by decide +kernel

def vcCutP717 : SideCornerEntry := ⟨7/40, 7/40, 0, #v[100702893/2500000000, 401737917/10000000000, 276239001/10000000000]⟩
abbrev vcCutP717Roots := vcOuterP717Roots
theorem vcCutP717_roots : vcCutP717.cell.rootsOK vcCutP717Roots = true := by decide +kernel

def vcCutP718 : SideCornerEntry := ⟨7/40, 7/40, 1/36, #v[429560631/10000000000, 214234939/5000000000, 292654513/10000000000]⟩
abbrev vcCutP718Roots := vcOuterP718Roots
theorem vcCutP718_roots : vcCutP718.cell.rootsOK vcCutP718Roots = true := by decide +kernel

def vcCutP719 : SideCornerEntry := ⟨7/40, 7/40, 1/18, #v[429560631/10000000000, 214234939/5000000000, 292654513/10000000000]⟩
abbrev vcCutP719Roots := vcOuterP719Roots
theorem vcCutP719_roots : vcCutP719.cell.rootsOK vcCutP719Roots = true := by decide +kernel

def vcCutP720 : SideCornerEntry := ⟨7/40, 1/5, 0, #v[25761653/500000000, 124776579/2500000000, 387178607/10000000000]⟩
abbrev vcCutP720Roots := vcOuterP720Roots
theorem vcCutP720_roots : vcCutP720.cell.rootsOK vcCutP720Roots = true := by decide +kernel

def vcCutP721 : SideCornerEntry := ⟨7/40, 1/5, 1/36, #v[25761653/500000000, 124776579/2500000000, 387178607/10000000000]⟩
abbrev vcCutP721Roots := vcOuterP721Roots
theorem vcCutP721_roots : vcCutP721.cell.rootsOK vcCutP721Roots = true := by decide +kernel

def vcCutP722 : SideCornerEntry := ⟨7/40, 1/5, 1/18, #v[429560631/10000000000, 214234939/5000000000, 292654513/10000000000]⟩
abbrev vcCutP722Roots := vcOuterP722Roots
theorem vcCutP722_roots : vcCutP722.cell.rootsOK vcCutP722Roots = true := by decide +kernel

def vcCutP723 : SideCornerEntry := ⟨7/40, 9/40, 0, #v[25761653/500000000, 124776579/2500000000, 387178607/10000000000]⟩
abbrev vcCutP723Roots := vcOuterP723Roots
theorem vcCutP723_roots : vcCutP723.cell.rootsOK vcCutP723Roots = true := by decide +kernel

def vcCutP724 : SideCornerEntry := ⟨7/40, 9/40, 1/36, #v[25761653/500000000, 124776579/2500000000, 387178607/10000000000]⟩
abbrev vcCutP724Roots := vcOuterP724Roots
theorem vcCutP724_roots : vcCutP724.cell.rootsOK vcCutP724Roots = true := by decide +kernel

def vcCutP725 : SideCornerEntry := ⟨7/40, 9/40, 1/18, #v[400580341/10000000000, 381416307/10000000000, 305470341/10000000000]⟩
abbrev vcCutP725Roots := vcOuterP725Roots
theorem vcCutP725_roots : vcCutP725.cell.rootsOK vcCutP725Roots = true := by decide +kernel

def vcCutP726 : SideCornerEntry := ⟨7/40, 1/4, 0, #v[4690107/125000000, 178708563/5000000000, 71920509/2500000000]⟩
abbrev vcCutP726Roots := vcOuterP726Roots
theorem vcCutP726_roots : vcCutP726.cell.rootsOK vcCutP726Roots = true := by decide +kernel

def vcCutP727 : SideCornerEntry := ⟨7/40, 1/4, 1/36, #v[400580341/10000000000, 381416307/10000000000, 305470341/10000000000]⟩
abbrev vcCutP727Roots := vcOuterP727Roots
theorem vcCutP727_roots : vcCutP727.cell.rootsOK vcCutP727Roots = true := by decide +kernel

def vcCutP728 : SideCornerEntry := ⟨7/40, 1/4, 1/18, #v[400580341/10000000000, 381416307/10000000000, 305470341/10000000000]⟩
abbrev vcCutP728Roots := vcOuterP728Roots
theorem vcCutP728_roots : vcCutP728.cell.rootsOK vcCutP728Roots = true := by decide +kernel

def vcCutP729 : SideCornerEntry := ⟨7/40, 11/40, 0, #v[146956273/5000000000, 137382933/5000000000, 228917597/10000000000]⟩
abbrev vcCutP729Roots := vcOuterP729Roots
theorem vcCutP729_roots : vcCutP729.cell.rootsOK vcCutP729Roots = true := by decide +kernel

def vcCutP730 : SideCornerEntry := ⟨7/40, 11/40, 1/36, #v[9794741/312500000, 29274867/1000000000, 60774603/2500000000]⟩
abbrev vcCutP730Roots := vcOuterP730Roots
theorem vcCutP730_roots : vcCutP730.cell.rootsOK vcCutP730Roots = true := by decide +kernel

def vcCutP731 : SideCornerEntry := ⟨7/40, 11/40, 1/18, #v[9794741/312500000, 29274867/1000000000, 60774603/2500000000]⟩
abbrev vcCutP731Roots := vcOuterP731Roots
theorem vcCutP731_roots : vcCutP731.cell.rootsOK vcCutP731Roots = true := by decide +kernel

def vcCutP732 : SideCornerEntry := ⟨7/40, 3/10, 0, #v[49127549/2000000000, 225028669/10000000000, 24234879/1250000000]⟩
abbrev vcCutP732Roots := vcOuterP732Roots
theorem vcCutP732_roots : vcCutP732.cell.rootsOK vcCutP732Roots = true := by decide +kernel

def vcCutP733 : SideCornerEntry := ⟨7/40, 3/10, 1/36, #v[261660101/10000000000, 119690499/5000000000, 1608493/78125000]⟩
abbrev vcCutP733Roots := vcOuterP733Roots
theorem vcCutP733_roots : vcCutP733.cell.rootsOK vcCutP733Roots = true := by decide +kernel

def vcCutP734 : SideCornerEntry := ⟨7/40, 3/10, 1/18, #v[261660101/10000000000, 119690499/5000000000, 1608493/78125000]⟩
abbrev vcCutP734Roots := vcOuterP734Roots
theorem vcCutP734_roots : vcCutP734.cell.rootsOK vcCutP734Roots = true := by decide +kernel

def vcCutP735 : SideCornerEntry := ⟨7/40, 13/40, 0, #v[217522847/10000000000, 48776901/2500000000, 173905749/10000000000]⟩
abbrev vcCutP735Roots := vcOuterP735Roots
theorem vcCutP735_roots : vcCutP735.cell.rootsOK vcCutP735Roots = true := by decide +kernel

def vcCutPoints704 : Array SideCornerEntry := #[
  vcCutP704,
  vcCutP705,
  vcCutP706,
  vcCutP707,
  vcCutP708,
  vcCutP709,
  vcCutP710,
  vcCutP711,
  vcCutP712,
  vcCutP713,
  vcCutP714,
  vcCutP715,
  vcCutP716,
  vcCutP717,
  vcCutP718,
  vcCutP719,
  vcCutP720,
  vcCutP721,
  vcCutP722,
  vcCutP723,
  vcCutP724,
  vcCutP725,
  vcCutP726,
  vcCutP727,
  vcCutP728,
  vcCutP729,
  vcCutP730,
  vcCutP731,
  vcCutP732,
  vcCutP733,
  vcCutP734,
  vcCutP735]

end HlawkaSchatten.BelowExponent.Vertex
