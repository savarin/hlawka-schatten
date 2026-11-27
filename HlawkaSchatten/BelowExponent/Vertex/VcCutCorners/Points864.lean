/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.VcCornerData.Points864

/-! Checked corner data shared by the vertex middle and band regions: `Points864`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

def vcCutP864 : SideCornerEntry := ⟨3/10, 3/8, 0, #v[97292923/2500000000, 361692769/10000000000, 604683/16000000]⟩
abbrev vcCutP864Roots := vcOuterP864Roots
theorem vcCutP864_roots : vcCutP864.cell.rootsOK vcCutP864Roots = true := by decide +kernel

def vcCutP865 : SideCornerEntry := ⟨3/10, 3/8, 1/36, #v[208321207/5000000000, 96640801/2500000000, 405039121/10000000000]⟩
abbrev vcCutP865Roots := vcOuterP865Roots
theorem vcCutP865_roots : vcCutP865.cell.rootsOK vcCutP865Roots = true := by decide +kernel

def vcCutP866 : SideCornerEntry := ⟨3/10, 3/8, 1/18, #v[208321207/5000000000, 96640801/2500000000, 405039121/10000000000]⟩
abbrev vcCutP866Roots := vcOuterP866Roots
theorem vcCutP866_roots : vcCutP866.cell.rootsOK vcCutP866Roots = true := by decide +kernel

def vcCutP867 : SideCornerEntry := ⟨13/40, 3/10, 0, #v[7159239/200000000, 352230831/10000000000, 347655411/10000000000]⟩
abbrev vcCutP867Roots := vcOuterP867Roots
theorem vcCutP867_roots : vcCutP867.cell.rootsOK vcCutP867Roots = true := by decide +kernel

def vcCutP868 : SideCornerEntry := ⟨13/40, 3/10, 1/36, #v[382989207/10000000000, 75335057/2000000000, 186209343/5000000000]⟩
abbrev vcCutP868Roots := vcOuterP868Roots
theorem vcCutP868_roots : vcCutP868.cell.rootsOK vcCutP868Roots = true := by decide +kernel

def vcCutP869 : SideCornerEntry := ⟨13/40, 3/10, 1/18, #v[382989207/10000000000, 75335057/2000000000, 186209343/5000000000]⟩
abbrev vcCutP869Roots := vcOuterP869Roots
theorem vcCutP869_roots : vcCutP869.cell.rootsOK vcCutP869Roots = true := by decide +kernel

def vcCutP870 : SideCornerEntry := ⟨13/40, 13/40, 0, #v[244150583/5000000000, 480750933/10000000000, 502203541/10000000000]⟩
abbrev vcCutP870Roots := vcOuterP870Roots
theorem vcCutP870_roots : vcCutP870.cell.rootsOK vcCutP870Roots = true := by decide +kernel

def vcCutP871 : SideCornerEntry := ⟨13/40, 13/40, 1/36, #v[522961543/10000000000, 257308901/5000000000, 538886447/10000000000]⟩
abbrev vcCutP871Roots := vcOuterP871Roots
theorem vcCutP871_roots : vcCutP871.cell.rootsOK vcCutP871Roots = true := by decide +kernel

def vcCutP872 : SideCornerEntry := ⟨13/40, 13/40, 1/18, #v[522961543/10000000000, 257308901/5000000000, 538886447/10000000000]⟩
abbrev vcCutP872Roots := vcOuterP872Roots
theorem vcCutP872_roots : vcCutP872.cell.rootsOK vcCutP872Roots = true := by decide +kernel

def vcCutP873 : SideCornerEntry := ⟨13/40, 7/20, 0, #v[244150583/5000000000, 480750933/10000000000, 502203541/10000000000]⟩
abbrev vcCutP873Roots := vcOuterP873Roots
theorem vcCutP873_roots : vcCutP873.cell.rootsOK vcCutP873Roots = true := by decide +kernel

def vcCutP874 : SideCornerEntry := ⟨13/40, 7/20, 1/36, #v[522961543/10000000000, 257308901/5000000000, 538886447/10000000000]⟩
abbrev vcCutP874Roots := vcOuterP874Roots
theorem vcCutP874_roots : vcCutP874.cell.rootsOK vcCutP874Roots = true := by decide +kernel

def vcCutP875 : SideCornerEntry := ⟨13/40, 7/20, 1/18, #v[522961543/10000000000, 257308901/5000000000, 538886447/10000000000]⟩
abbrev vcCutP875Roots := vcOuterP875Roots
theorem vcCutP875_roots : vcCutP875.cell.rootsOK vcCutP875Roots = true := by decide +kernel

def vcCutP876 : SideCornerEntry := ⟨7/20, 13/40, 0, #v[244150583/5000000000, 480750933/10000000000, 502203541/10000000000]⟩
abbrev vcCutP876Roots := vcOuterP876Roots
theorem vcCutP876_roots : vcCutP876.cell.rootsOK vcCutP876Roots = true := by decide +kernel

def vcCutP877 : SideCornerEntry := ⟨7/20, 13/40, 1/36, #v[522961543/10000000000, 257308901/5000000000, 538886447/10000000000]⟩
abbrev vcCutP877Roots := vcOuterP877Roots
theorem vcCutP877_roots : vcCutP877.cell.rootsOK vcCutP877Roots = true := by decide +kernel

def vcCutP878 : SideCornerEntry := ⟨7/20, 13/40, 1/18, #v[522961543/10000000000, 257308901/5000000000, 538886447/10000000000]⟩
abbrev vcCutP878Roots := vcOuterP878Roots
theorem vcCutP878_roots : vcCutP878.cell.rootsOK vcCutP878Roots = true := by decide +kernel

def vcCutP879 : SideCornerEntry := ⟨7/20, 7/20, 0, #v[244150583/5000000000, 480750933/10000000000, 502203541/10000000000]⟩
abbrev vcCutP879Roots := vcOuterP879Roots
theorem vcCutP879_roots : vcCutP879.cell.rootsOK vcCutP879Roots = true := by decide +kernel

def vcCutP880 : SideCornerEntry := ⟨7/20, 7/20, 1/36, #v[522961543/10000000000, 257308901/5000000000, 538886447/10000000000]⟩
abbrev vcCutP880Roots := vcOuterP880Roots
theorem vcCutP880_roots : vcCutP880.cell.rootsOK vcCutP880Roots = true := by decide +kernel

def vcCutP881 : SideCornerEntry := ⟨7/20, 7/20, 1/18, #v[522961543/10000000000, 257308901/5000000000, 538886447/10000000000]⟩
abbrev vcCutP881Roots := vcOuterP881Roots
theorem vcCutP881_roots : vcCutP881.cell.rootsOK vcCutP881Roots = true := by decide +kernel

def vcCutPoints864 : Array SideCornerEntry := #[
  vcCutP864,
  vcCutP865,
  vcCutP866,
  vcCutP867,
  vcCutP868,
  vcCutP869,
  vcCutP870,
  vcCutP871,
  vcCutP872,
  vcCutP873,
  vcCutP874,
  vcCutP875,
  vcCutP876,
  vcCutP877,
  vcCutP878,
  vcCutP879,
  vcCutP880,
  vcCutP881]

end HlawkaSchatten.BelowExponent.Vertex
