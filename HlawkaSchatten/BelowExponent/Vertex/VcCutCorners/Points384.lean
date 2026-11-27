/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.VcCornerData.Points384

/-! Checked corner data shared by the vertex middle and band regions: `Points384`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

def vcCutP384 : SideCornerEntry := ⟨1/20, 7/20, 3/40, #v[16006943/5000000000, 24835383/10000000000, 15200179/10000000000]⟩
abbrev vcCutP384Roots := vcOuterP384Roots
theorem vcCutP384_roots : vcCutP384.cell.rootsOK vcCutP384Roots = true := by decide +kernel

def vcCutP385 : SideCornerEntry := ⟨1/20, 7/20, 1/10, #v[16006943/5000000000, 24835383/10000000000, 15200179/10000000000]⟩
abbrev vcCutP385Roots := vcOuterP385Roots
theorem vcCutP385_roots : vcCutP385.cell.rootsOK vcCutP385Roots = true := by decide +kernel

def vcCutP386 : SideCornerEntry := ⟨1/20, 29/80, 0, #v[14921943/5000000000, 11550739/5000000000, 14910867/10000000000]⟩
abbrev vcCutP386Roots := vcOuterP386Roots
theorem vcCutP386_roots : vcCutP386.cell.rootsOK vcCutP386Roots = true := by decide +kernel

def vcCutP387 : SideCornerEntry := ⟨1/20, 29/80, 1/40, #v[6010037/2000000000, 23153891/10000000000, 14910867/10000000000]⟩
abbrev vcCutP387Roots := vcOuterP387Roots
theorem vcCutP387_roots : vcCutP387.cell.rootsOK vcCutP387Roots = true := by decide +kernel

def vcCutP388 : SideCornerEntry := ⟨1/20, 29/80, 1/20, #v[3796913/1250000000, 11656083/5000000000, 744479/500000000]⟩
abbrev vcCutP388Roots := vcOuterP388Roots
theorem vcCutP388_roots : vcCutP388.cell.rootsOK vcCutP388Roots = true := by decide +kernel

def vcCutP389 : SideCornerEntry := ⟨1/20, 29/80, 3/40, #v[15397453/5000000000, 11778143/5000000000, 299691/200000000]⟩
abbrev vcCutP389Roots := vcOuterP389Roots
theorem vcCutP389_roots : vcCutP389.cell.rootsOK vcCutP389Roots = true := by decide +kernel

def vcCutP390 : SideCornerEntry := ⟨1/20, 29/80, 1/10, #v[15397453/5000000000, 11778143/5000000000, 299691/200000000]⟩
abbrev vcCutP390Roots := vcOuterP390Roots
theorem vcCutP390_roots : vcCutP390.cell.rootsOK vcCutP390Roots = true := by decide +kernel

def vcCutP391 : SideCornerEntry := ⟨1/20, 3/8, 0, #v[66664979/5000000000, 104557797/10000000000, 10088307/1250000000]⟩
abbrev vcCutP391Roots := vcOuterP391Roots
theorem vcCutP391_roots : vcCutP391.cell.rootsOK vcCutP391Roots = true := by decide +kernel

def vcCutP392 : SideCornerEntry := ⟨1/20, 3/8, 1/40, #v[14539441/5000000000, 4418111/2000000000, 7397123/5000000000]⟩
abbrev vcCutP392Roots := vcOuterP392Roots
theorem vcCutP392_roots : vcCutP392.cell.rootsOK vcCutP392Roots = true := by decide +kernel

def vcCutP393 : SideCornerEntry := ⟨1/20, 3/8, 1/36, #v[13934751/1000000000, 108961427/10000000000, 10523501/1250000000]⟩
abbrev vcCutP393Roots := vcOuterP393Roots
theorem vcCutP393_roots : vcCutP393.cell.rootsOK vcCutP393Roots = true := by decide +kernel

def vcCutP394 : SideCornerEntry := ⟨1/20, 3/8, 1/20, #v[14681477/5000000000, 11108277/5000000000, 2949589/2000000000]⟩
abbrev vcCutP394Roots := vcOuterP394Roots
theorem vcCutP394_roots : vcCutP394.cell.rootsOK vcCutP394Roots = true := by decide +kernel

def vcCutP395 : SideCornerEntry := ⟨1/20, 3/8, 1/18, #v[13934751/1000000000, 108961427/10000000000, 10523501/1250000000]⟩
abbrev vcCutP395Roots := vcOuterP395Roots
theorem vcCutP395_roots : vcCutP395.cell.rootsOK vcCutP395Roots = true := by decide +kernel

def vcCutP396 : SideCornerEntry := ⟨1/20, 3/8, 3/40, #v[7435389/2500000000, 5606731/2500000000, 14830061/10000000000]⟩
abbrev vcCutP396Roots := vcOuterP396Roots
theorem vcCutP396_roots : vcCutP396.cell.rootsOK vcCutP396Roots = true := by decide +kernel

def vcCutP397 : SideCornerEntry := ⟨1/20, 3/8, 1/10, #v[7435389/2500000000, 5606731/2500000000, 14830061/10000000000]⟩
abbrev vcCutP397Roots := vcOuterP397Roots
theorem vcCutP397_roots : vcCutP397.cell.rootsOK vcCutP397Roots = true := by decide +kernel

def vcCutP398 : SideCornerEntry := ⟨1/20, 31/80, 0, #v[5621769/2000000000, 21150729/10000000000, 14731333/10000000000]⟩
abbrev vcCutP398Roots := vcOuterP398Roots
theorem vcCutP398_roots : vcCutP398.cell.rootsOK vcCutP398Roots = true := by decide +kernel

def vcCutP399 : SideCornerEntry := ⟨1/20, 31/80, 1/40, #v[14121081/5000000000, 21150729/10000000000, 14731333/10000000000]⟩
abbrev vcCutP399Roots := vcOuterP399Roots
theorem vcCutP399_roots : vcCutP399.cell.rootsOK vcCutP399Roots = true := by decide +kernel

def vcCutP400 : SideCornerEntry := ⟨1/20, 31/80, 1/20, #v[14245571/5000000000, 10622811/5000000000, 14659879/10000000000]⟩
abbrev vcCutP400Roots := vcOuterP400Roots
theorem vcCutP400_roots : vcCutP400.cell.rootsOK vcCutP400Roots = true := by decide +kernel

def vcCutP401 : SideCornerEntry := ⟨1/20, 31/80, 3/40, #v[225271/78125000, 5356841/2500000000, 3682807/2500000000]⟩
abbrev vcCutP401Roots := vcOuterP401Roots
theorem vcCutP401_roots : vcCutP401.cell.rootsOK vcCutP401Roots = true := by decide +kernel

def vcCutP402 : SideCornerEntry := ⟨1/20, 31/80, 1/10, #v[225271/78125000, 5356841/2500000000, 3682807/2500000000]⟩
abbrev vcCutP402Roots := vcOuterP402Roots
theorem vcCutP402_roots : vcCutP402.cell.rootsOK vcCutP402Roots = true := by decide +kernel

def vcCutP403 : SideCornerEntry := ⟨1/20, 2/5, 0, #v[25052991/2000000000, 3826091/400000000, 3127589/400000000]⟩
abbrev vcCutP403Roots := vcOuterP403Roots
theorem vcCutP403_roots : vcCutP403.cell.rootsOK vcCutP403Roots = true := by decide +kernel

def vcCutP404 : SideCornerEntry := ⟨1/20, 2/5, 1/40, #v[13762951/5000000000, 5083579/2500000000, 3685233/2500000000]⟩
abbrev vcCutP404Roots := vcOuterP404Roots
theorem vcCutP404_roots : vcCutP404.cell.rootsOK vcCutP404Roots = true := by decide +kernel

def vcCutP405 : SideCornerEntry := ⟨1/20, 2/5, 1/36, #v[130802147/10000000000, 99570703/10000000000, 81519567/10000000000]⟩
abbrev vcCutP405Roots := vcOuterP405Roots
theorem vcCutP405_roots : vcCutP405.cell.rootsOK vcCutP405Roots = true := by decide +kernel

def vcCutP406 : SideCornerEntry := ⟨1/20, 2/5, 1/20, #v[27745101/10000000000, 4077003/2000000000, 14643567/10000000000]⟩
abbrev vcCutP406Roots := vcOuterP406Roots
theorem vcCutP406_roots : vcCutP406.cell.rootsOK vcCutP406Roots = true := by decide +kernel

def vcCutP407 : SideCornerEntry := ⟨1/20, 2/5, 1/18, #v[130802147/10000000000, 99570703/10000000000, 81519567/10000000000]⟩
abbrev vcCutP407Roots := vcOuterP407Roots
theorem vcCutP407_roots : vcCutP407.cell.rootsOK vcCutP407Roots = true := by decide +kernel

def vcCutP408 : SideCornerEntry := ⟨1/20, 2/5, 3/40, #v[2805889/1000000000, 20542489/10000000000, 3671539/2500000000]⟩
abbrev vcCutP408Roots := vcOuterP408Roots
theorem vcCutP408_roots : vcCutP408.cell.rootsOK vcCutP408Roots = true := by decide +kernel

def vcCutP409 : SideCornerEntry := ⟨1/20, 2/5, 1/10, #v[2805889/1000000000, 20542489/10000000000, 3671539/2500000000]⟩
abbrev vcCutP409Roots := vcOuterP409Roots
theorem vcCutP409_roots : vcCutP409.cell.rootsOK vcCutP409Roots = true := by decide +kernel

def vcCutP410 : SideCornerEntry := ⟨1/20, 33/80, 0, #v[26840159/10000000000, 9803417/5000000000, 14809373/10000000000]⟩
abbrev vcCutP410Roots := vcOuterP410Roots
theorem vcCutP410_roots : vcCutP410.cell.rootsOK vcCutP410Roots = true := by decide +kernel

def vcCutP411 : SideCornerEntry := ⟨1/20, 33/80, 1/40, #v[6729657/2500000000, 9803417/5000000000, 14809373/10000000000]⟩
abbrev vcCutP411Roots := vcOuterP411Roots
theorem vcCutP411_roots : vcCutP411.cell.rootsOK vcCutP411Roots = true := by decide +kernel

def vcCutP412 : SideCornerEntry := ⟨1/20, 33/80, 1/20, #v[27112809/10000000000, 2452621/1250000000, 7352143/5000000000]⟩
abbrev vcCutP412Roots := vcOuterP412Roots
theorem vcCutP412_roots : vcCutP412.cell.rootsOK vcCutP412Roots = true := by decide +kernel

def vcCutP413 : SideCornerEntry := ⟨1/20, 33/80, 3/40, #v[27401599/10000000000, 19758031/10000000000, 736769/500000000]⟩
abbrev vcCutP413Roots := vcOuterP413Roots
theorem vcCutP413_roots : vcCutP413.cell.rootsOK vcCutP413Roots = true := by decide +kernel

def vcCutP414 : SideCornerEntry := ⟨1/20, 33/80, 1/10, #v[27401599/10000000000, 19758031/10000000000, 736769/500000000]⟩
abbrev vcCutP414Roots := vcOuterP414Roots
theorem vcCutP414_roots : vcCutP414.cell.rootsOK vcCutP414Roots = true := by decide +kernel

def vcCutP415 : SideCornerEntry := ⟨1/20, 17/40, 0, #v[14999257/1250000000, 89207777/10000000000, 77963687/10000000000]⟩
abbrev vcCutP415Roots := vcOuterP415Roots
theorem vcCutP415_roots : vcCutP415.cell.rootsOK vcCutP415Roots = true := by decide +kernel

def vcCutPoints384 : Array SideCornerEntry := #[
  vcCutP384,
  vcCutP385,
  vcCutP386,
  vcCutP387,
  vcCutP388,
  vcCutP389,
  vcCutP390,
  vcCutP391,
  vcCutP392,
  vcCutP393,
  vcCutP394,
  vcCutP395,
  vcCutP396,
  vcCutP397,
  vcCutP398,
  vcCutP399,
  vcCutP400,
  vcCutP401,
  vcCutP402,
  vcCutP403,
  vcCutP404,
  vcCutP405,
  vcCutP406,
  vcCutP407,
  vcCutP408,
  vcCutP409,
  vcCutP410,
  vcCutP411,
  vcCutP412,
  vcCutP413,
  vcCutP414,
  vcCutP415]

end HlawkaSchatten.BelowExponent.Vertex
