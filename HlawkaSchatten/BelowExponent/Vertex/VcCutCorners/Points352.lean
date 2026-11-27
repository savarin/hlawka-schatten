/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.VcCornerData.Points352

/-! Checked corner data shared by the vertex middle and band regions: `Points352`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

def vcCutP352 : SideCornerEntry := ⟨1/20, 23/80, 1/20, #v[10224049/2500000000, 3392537/1000000000, 17440919/10000000000]⟩
abbrev vcCutP352Roots := vcOuterP352Roots
theorem vcCutP352_roots : vcCutP352.cell.rootsOK vcCutP352Roots = true := by decide +kernel

def vcCutP353 : SideCornerEntry := ⟨1/20, 23/80, 3/40, #v[41745299/10000000000, 17269979/5000000000, 4416277/2500000000]⟩
abbrev vcCutP353Roots := vcOuterP353Roots
theorem vcCutP353_roots : vcCutP353.cell.rootsOK vcCutP353Roots = true := by decide +kernel

def vcCutP354 : SideCornerEntry := ⟨1/20, 23/80, 1/10, #v[41745299/10000000000, 17269979/5000000000, 4416277/2500000000]⟩
abbrev vcCutP354Roots := vcOuterP354Roots
theorem vcCutP354_roots : vcCutP354.cell.rootsOK vcCutP354Roots = true := by decide +kernel

def vcCutP355 : SideCornerEntry := ⟨1/20, 3/10, 0, #v[183503427/10000000000, 15565733/1000000000, 102572969/10000000000]⟩
abbrev vcCutP355Roots := vcOuterP355Roots
theorem vcCutP355_roots : vcCutP355.cell.rootsOK vcCutP355Roots = true := by decide +kernel

def vcCutP356 : SideCornerEntry := ⟨1/20, 3/10, 1/40, #v[18895319/5000000000, 15530383/5000000000, 16637103/10000000000]⟩
abbrev vcCutP356Roots := vcOuterP356Roots
theorem vcCutP356_roots : vcCutP356.cell.rootsOK vcCutP356Roots = true := by decide +kernel

def vcCutP357 : SideCornerEntry := ⟨1/20, 3/10, 1/36, #v[96283743/5000000000, 162996739/10000000000, 107149069/10000000000]⟩
abbrev vcCutP357Roots := vcOuterP357Roots
theorem vcCutP357_roots : vcCutP357.cell.rootsOK vcCutP357Roots = true := by decide +kernel

def vcCutP358 : SideCornerEntry := ⟨1/20, 3/10, 1/20, #v[19218799/5000000000, 31493049/10000000000, 16768343/10000000000]⟩
abbrev vcCutP358Roots := vcOuterP358Roots
theorem vcCutP358_roots : vcCutP358.cell.rootsOK vcCutP358Roots = true := by decide +kernel

def vcCutP359 : SideCornerEntry := ⟨1/20, 3/10, 1/18, #v[96283743/5000000000, 162996739/10000000000, 107149069/10000000000]⟩
abbrev vcCutP359Roots := vcOuterP359Roots
theorem vcCutP359_roots : vcCutP359.cell.rootsOK vcCutP359Roots = true := by decide +kernel

def vcCutP360 : SideCornerEntry := ⟨1/20, 3/10, 3/40, #v[19591541/5000000000, 32017837/10000000000, 3391891/2000000000]⟩
abbrev vcCutP360Roots := vcOuterP360Roots
theorem vcCutP360_roots : vcCutP360.cell.rootsOK vcCutP360Roots = true := by decide +kernel

def vcCutP361 : SideCornerEntry := ⟨1/20, 3/10, 1/10, #v[19591541/5000000000, 32017837/10000000000, 3391891/2000000000]⟩
abbrev vcCutP361Roots := vcOuterP361Roots
theorem vcCutP361_roots : vcCutP361.cell.rootsOK vcCutP361Roots = true := by decide +kernel

def vcCutP362 : SideCornerEntry := ⟨1/20, 5/16, 0, #v[35325143/10000000000, 7196541/2500000000, 4021303/2500000000]⟩
abbrev vcCutP362Roots := vcOuterP362Roots
theorem vcCutP362_roots : vcCutP362.cell.rootsOK vcCutP362Roots = true := by decide +kernel

def vcCutP363 : SideCornerEntry := ⟨1/20, 5/16, 1/40, #v[7152309/2000000000, 14515587/5000000000, 3222239/2000000000]⟩
abbrev vcCutP363Roots := vcOuterP363Roots
theorem vcCutP363_roots : vcCutP363.cell.rootsOK vcCutP363Roots = true := by decide +kernel

def vcCutP364 : SideCornerEntry := ⟨1/20, 5/16, 1/20, #v[36323491/10000000000, 29389139/10000000000, 4053333/2500000000]⟩
abbrev vcCutP364Roots := vcOuterP364Roots
theorem vcCutP364_roots : vcCutP364.cell.rootsOK vcCutP364Roots = true := by decide +kernel

def vcCutP365 : SideCornerEntry := ⟨1/20, 5/16, 3/40, #v[4622569/1250000000, 5967631/2000000000, 16375863/10000000000]⟩
abbrev vcCutP365Roots := vcOuterP365Roots
theorem vcCutP365_roots : vcCutP365.cell.rootsOK vcCutP365Roots = true := by decide +kernel

def vcCutP366 : SideCornerEntry := ⟨1/20, 5/16, 1/10, #v[4622569/1250000000, 5967631/2000000000, 16375863/10000000000]⟩
abbrev vcCutP366Roots := vcOuterP366Roots
theorem vcCutP366_roots : vcCutP366.cell.rootsOK vcCutP366Roots = true := by decide +kernel

def vcCutP367 : SideCornerEntry := ⟨1/20, 13/40, 0, #v[80476871/5000000000, 26603711/2000000000, 11514657/1250000000]⟩
abbrev vcCutP367Roots := vcOuterP367Roots
theorem vcCutP367_roots : vcCutP367.cell.rootsOK vcCutP367Roots = true := by decide +kernel

def vcCutP368 : SideCornerEntry := ⟨1/20, 13/40, 1/40, #v[34011753/10000000000, 13631843/5000000000, 7841331/5000000000]⟩
abbrev vcCutP368Roots := vcOuterP368Roots
theorem vcCutP368_roots : vcCutP368.cell.rootsOK vcCutP368Roots = true := by decide +kernel

def vcCutP369 : SideCornerEntry := ⟨1/20, 13/40, 1/36, #v[84312271/5000000000, 139034153/10000000000, 96165127/10000000000]⟩
abbrev vcCutP369Roots := vcOuterP369Roots
theorem vcCutP369_roots : vcCutP369.cell.rootsOK vcCutP369Roots = true := by decide +kernel

def vcCutP370 : SideCornerEntry := ⟨1/20, 13/40, 1/20, #v[34498409/10000000000, 13779299/5000000000, 492441/312500000]⟩
abbrev vcCutP370Roots := vcOuterP370Roots
theorem vcCutP370_roots : vcCutP370.cell.rootsOK vcCutP370Roots = true := by decide +kernel

def vcCutP371 : SideCornerEntry := ⟨1/20, 13/40, 1/18, #v[84312271/5000000000, 139034153/10000000000, 96165127/10000000000]⟩
abbrev vcCutP371Roots := vcOuterP371Roots
theorem vcCutP371_roots : vcCutP371.cell.rootsOK vcCutP371Roots = true := by decide +kernel

def vcCutP372 : SideCornerEntry := ⟨1/20, 13/40, 3/40, #v[7015937/2000000000, 27943451/10000000000, 993497/625000000]⟩
abbrev vcCutP372Roots := vcOuterP372Roots
theorem vcCutP372_roots : vcCutP372.cell.rootsOK vcCutP372Roots = true := by decide +kernel

def vcCutP373 : SideCornerEntry := ⟨1/20, 13/40, 1/10, #v[7015937/2000000000, 27943451/10000000000, 993497/625000000]⟩
abbrev vcCutP373Roots := vcOuterP373Roots
theorem vcCutP373_roots : vcCutP373.cell.rootsOK vcCutP373Roots = true := by decide +kernel

def vcCutP374 : SideCornerEntry := ⟨1/20, 27/80, 0, #v[32196649/10000000000, 6396003/2500000000, 7679723/5000000000]⟩
abbrev vcCutP374Roots := vcOuterP374Roots
theorem vcCutP374_roots : vcCutP374.cell.rootsOK vcCutP374Roots = true := by decide +kernel

def vcCutP375 : SideCornerEntry := ⟨1/20, 27/80, 1/40, #v[406213/125000000, 12858181/5000000000, 7679723/5000000000]⟩
abbrev vcCutP375Roots := vcOuterP375Roots
theorem vcCutP375_roots : vcCutP375.cell.rootsOK vcCutP375Roots = true := by decide +kernel

def vcCutP376 : SideCornerEntry := ⟨1/20, 27/80, 1/20, #v[3291841/1000000000, 25957933/10000000000, 7694317/5000000000]⟩
abbrev vcCutP376Roots := vcOuterP376Roots
theorem vcCutP376_roots : vcCutP376.cell.rootsOK vcCutP376Roots = true := by decide +kernel

def vcCutP377 : SideCornerEntry := ⟨1/20, 27/80, 3/40, #v[33434547/10000000000, 26287931/10000000000, 620191/400000000]⟩
abbrev vcCutP377Roots := vcOuterP377Roots
theorem vcCutP377_roots : vcCutP377.cell.rootsOK vcCutP377Roots = true := by decide +kernel

def vcCutP378 : SideCornerEntry := ⟨1/20, 27/80, 1/10, #v[33434547/10000000000, 26287931/10000000000, 620191/400000000]⟩
abbrev vcCutP378Roots := vcOuterP378Roots
theorem vcCutP378_roots : vcCutP378.cell.rootsOK vcCutP378Roots = true := by decide +kernel

def vcCutP379 : SideCornerEntry := ⟨1/20, 7/20, 0, #v[28967543/2000000000, 116610879/10000000000, 85138283/10000000000]⟩
abbrev vcCutP379Roots := vcOuterP379Roots
theorem vcCutP379_roots : vcCutP379.cell.rootsOK vcCutP379Roots = true := by decide +kernel

def vcCutP380 : SideCornerEntry := ⟨1/20, 7/20, 1/40, #v[389791/125000000, 24355411/10000000000, 236013/156250000]⟩
abbrev vcCutP380Roots := vcOuterP380Roots
theorem vcCutP380_roots : vcCutP380.cell.rootsOK vcCutP380Roots = true := by decide +kernel

def vcCutP381 : SideCornerEntry := ⟨1/20, 7/20, 1/36, #v[75778723/5000000000, 24337637/2000000000, 44438629/5000000000]⟩
abbrev vcCutP381Roots := vcOuterP381Roots
theorem vcCutP381_roots : vcCutP381.cell.rootsOK vcCutP381Roots = true := by decide +kernel

def vcCutP382 : SideCornerEntry := ⟨1/20, 7/20, 1/20, #v[15774219/5000000000, 6137967/2500000000, 15093437/10000000000]⟩
abbrev vcCutP382Roots := vcOuterP382Roots
theorem vcCutP382_roots : vcCutP382.cell.rootsOK vcCutP382Roots = true := by decide +kernel

def vcCutP383 : SideCornerEntry := ⟨1/20, 7/20, 1/18, #v[75778723/5000000000, 24337637/2000000000, 44438629/5000000000]⟩
abbrev vcCutP383Roots := vcOuterP383Roots
theorem vcCutP383_roots : vcCutP383.cell.rootsOK vcCutP383Roots = true := by decide +kernel

def vcCutPoints352 : Array SideCornerEntry := #[
  vcCutP352,
  vcCutP353,
  vcCutP354,
  vcCutP355,
  vcCutP356,
  vcCutP357,
  vcCutP358,
  vcCutP359,
  vcCutP360,
  vcCutP361,
  vcCutP362,
  vcCutP363,
  vcCutP364,
  vcCutP365,
  vcCutP366,
  vcCutP367,
  vcCutP368,
  vcCutP369,
  vcCutP370,
  vcCutP371,
  vcCutP372,
  vcCutP373,
  vcCutP374,
  vcCutP375,
  vcCutP376,
  vcCutP377,
  vcCutP378,
  vcCutP379,
  vcCutP380,
  vcCutP381,
  vcCutP382,
  vcCutP383]

end HlawkaSchatten.BelowExponent.Vertex
