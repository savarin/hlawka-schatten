/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.VcCornerData.Points480

/-! Checked corner data shared by the vertex middle and band regions: `Points480`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

def vcCutP480 : SideCornerEntry := ⟨3/40, 3/20, 1/24, #v[75357011/5000000000, 143698317/10000000000, 70691731/10000000000]⟩
abbrev vcCutP480Roots := vcOuterP480Roots
theorem vcCutP480_roots : vcCutP480.cell.rootsOK vcCutP480Roots = true := by decide +kernel

def vcCutP481 : SideCornerEntry := ⟨3/40, 3/20, 1/18, #v[162333583/5000000000, 150312867/5000000000, 130902089/10000000000]⟩
abbrev vcCutP481Roots := vcOuterP481Roots
theorem vcCutP481_roots : vcCutP481.cell.rootsOK vcCutP481Roots = true := by decide +kernel

def vcCutP482 : SideCornerEntry := ⟨3/40, 7/40, 0, #v[508953261/10000000000, 238123827/5000000000, 295136237/10000000000]⟩
abbrev vcCutP482Roots := vcOuterP482Roots
theorem vcCutP482_roots : vcCutP482.cell.rootsOK vcCutP482Roots = true := by decide +kernel

def vcCutP483 : SideCornerEntry := ⟨3/40, 7/40, 1/36, #v[508953261/10000000000, 238123827/5000000000, 295136237/10000000000]⟩
abbrev vcCutP483Roots := vcOuterP483Roots
theorem vcCutP483_roots : vcCutP483.cell.rootsOK vcCutP483Roots = true := by decide +kernel

def vcCutP484 : SideCornerEntry := ⟨3/40, 7/40, 1/18, #v[33554737/1000000000, 62419967/2000000000, 42081869/2500000000]⟩
abbrev vcCutP484Roots := vcOuterP484Roots
theorem vcCutP484_roots : vcCutP484.cell.rootsOK vcCutP484Roots = true := by decide +kernel

def vcCutP485 : SideCornerEntry := ⟨3/40, 1/5, 0, #v[508953261/10000000000, 238123827/5000000000, 295136237/10000000000]⟩
abbrev vcCutP485Roots := vcOuterP485Roots
theorem vcCutP485_roots : vcCutP485.cell.rootsOK vcCutP485Roots = true := by decide +kernel

def vcCutP486 : SideCornerEntry := ⟨3/40, 1/5, 1/36, #v[508953261/10000000000, 238123827/5000000000, 295136237/10000000000]⟩
abbrev vcCutP486Roots := vcOuterP486Roots
theorem vcCutP486_roots : vcCutP486.cell.rootsOK vcCutP486Roots = true := by decide +kernel

def vcCutP487 : SideCornerEntry := ⟨3/40, 1/5, 1/18, #v[188876461/5000000000, 86973001/2500000000, 221322989/10000000000]⟩
abbrev vcCutP487Roots := vcOuterP487Roots
theorem vcCutP487_roots : vcCutP487.cell.rootsOK vcCutP487Roots = true := by decide +kernel

def vcCutP488 : SideCornerEntry := ⟨3/40, 9/40, 0, #v[35627429/1000000000, 328587879/10000000000, 210481213/10000000000]⟩
abbrev vcCutP488Roots := vcOuterP488Roots
theorem vcCutP488_roots : vcCutP488.cell.rootsOK vcCutP488Roots = true := by decide +kernel

def vcCutP489 : SideCornerEntry := ⟨3/40, 9/40, 1/36, #v[188876461/5000000000, 86973001/2500000000, 221322989/10000000000]⟩
abbrev vcCutP489Roots := vcOuterP489Roots
theorem vcCutP489_roots : vcCutP489.cell.rootsOK vcCutP489Roots = true := by decide +kernel

def vcCutP490 : SideCornerEntry := ⟨3/40, 9/40, 1/18, #v[188876461/5000000000, 86973001/2500000000, 221322989/10000000000]⟩
abbrev vcCutP490Roots := vcOuterP490Roots
theorem vcCutP490_roots : vcCutP490.cell.rootsOK vcCutP490Roots = true := by decide +kernel

def vcCutP491 : SideCornerEntry := ⟨3/40, 1/4, 0, #v[263426/9765625, 61075673/2500000000, 16175763/1000000000]⟩
abbrev vcCutP491Roots := vcOuterP491Roots
theorem vcCutP491_roots : vcCutP491.cell.rootsOK vcCutP491Roots = true := by decide +kernel

def vcCutP492 : SideCornerEntry := ⟨3/40, 1/4, 1/36, #v[57066831/2000000000, 257972971/10000000000, 21245777/1250000000]⟩
abbrev vcCutP492Roots := vcOuterP492Roots
theorem vcCutP492_roots : vcCutP492.cell.rootsOK vcCutP492Roots = true := by decide +kernel

def vcCutP493 : SideCornerEntry := ⟨3/40, 1/4, 1/18, #v[57066831/2000000000, 257972971/10000000000, 21245777/1250000000]⟩
abbrev vcCutP493Roots := vcOuterP493Roots
theorem vcCutP493_roots : vcCutP493.cell.rootsOK vcCutP493Roots = true := by decide +kernel

def vcCutP494 : SideCornerEntry := ⟨3/40, 11/40, 0, #v[4341311/200000000, 48111279/2500000000, 132010927/10000000000]⟩
abbrev vcCutP494Roots := vcOuterP494Roots
theorem vcCutP494_roots : vcCutP494.cell.rootsOK vcCutP494Roots = true := by decide +kernel

def vcCutP495 : SideCornerEntry := ⟨3/40, 11/40, 1/36, #v[229065657/10000000000, 101335249/5000000000, 69281309/5000000000]⟩
abbrev vcCutP495Roots := vcOuterP495Roots
theorem vcCutP495_roots : vcCutP495.cell.rootsOK vcCutP495Roots = true := by decide +kernel

def vcCutP496 : SideCornerEntry := ⟨3/40, 11/40, 1/18, #v[229065657/10000000000, 101335249/5000000000, 69281309/5000000000]⟩
abbrev vcCutP496Roots := vcOuterP496Roots
theorem vcCutP496_roots : vcCutP496.cell.rootsOK vcCutP496Roots = true := by decide +kernel

def vcCutP497 : SideCornerEntry := ⟨3/40, 3/10, 0, #v[183893777/10000000000, 158858191/10000000000, 56713529/5000000000]⟩
abbrev vcCutP497Roots := vcOuterP497Roots
theorem vcCutP497_roots : vcCutP497.cell.rootsOK vcCutP497Roots = true := by decide +kernel

def vcCutP498 : SideCornerEntry := ⟨3/40, 3/10, 1/36, #v[48411279/2500000000, 41734253/2500000000, 118926689/10000000000]⟩
abbrev vcCutP498Roots := vcOuterP498Roots
theorem vcCutP498_roots : vcCutP498.cell.rootsOK vcCutP498Roots = true := by decide +kernel

def vcCutP499 : SideCornerEntry := ⟨3/40, 3/10, 1/18, #v[48411279/2500000000, 41734253/2500000000, 118926689/10000000000]⟩
abbrev vcCutP499Roots := vcOuterP499Roots
theorem vcCutP499_roots : vcCutP499.cell.rootsOK vcCutP499Roots = true := by decide +kernel

def vcCutP500 : SideCornerEntry := ⟨3/40, 13/40, 0, #v[80728167/5000000000, 6792749/500000000, 25315541/2500000000]⟩
abbrev vcCutP500Roots := vcOuterP500Roots
theorem vcCutP500_roots : vcCutP500.cell.rootsOK vcCutP500Roots = true := by decide +kernel

def vcCutP501 : SideCornerEntry := ⟨3/40, 13/40, 1/36, #v[84905037/5000000000, 35624571/2500000000, 106112289/10000000000]⟩
abbrev vcCutP501Roots := vcOuterP501Roots
theorem vcCutP501_roots : vcCutP501.cell.rootsOK vcCutP501Roots = true := by decide +kernel

def vcCutP502 : SideCornerEntry := ⟨3/40, 13/40, 1/18, #v[84905037/5000000000, 35624571/2500000000, 106112289/10000000000]⟩
abbrev vcCutP502Roots := vcOuterP502Roots
theorem vcCutP502_roots : vcCutP502.cell.rootsOK vcCutP502Roots = true := by decide +kernel

def vcCutP503 : SideCornerEntry := ⟨3/40, 7/20, 0, #v[146041059/10000000000, 29929109/2500000000, 3736651/400000000]⟩
abbrev vcCutP503Roots := vcOuterP503Roots
theorem vcCutP503_roots : vcCutP503.cell.rootsOK vcCutP503Roots = true := by decide +kernel

def vcCutP504 : SideCornerEntry := ⟨3/40, 7/20, 1/36, #v[153447389/10000000000, 62685707/5000000000, 24483441/2500000000]⟩
abbrev vcCutP504Roots := vcOuterP504Roots
theorem vcCutP504_roots : vcCutP504.cell.rootsOK vcCutP504Roots = true := by decide +kernel

def vcCutP505 : SideCornerEntry := ⟨3/40, 7/20, 1/18, #v[153447389/10000000000, 62685707/5000000000, 24483441/2500000000]⟩
abbrev vcCutP505Roots := vcOuterP505Roots
theorem vcCutP505_roots : vcCutP505.cell.rootsOK vcCutP505Roots = true := by decide +kernel

def vcCutP506 : SideCornerEntry := ⟨3/40, 3/8, 0, #v[16950313/1250000000, 108266717/10000000000, 22191487/2500000000]⟩
abbrev vcCutP506Roots := vcOuterP506Roots
theorem vcCutP506_roots : vcCutP506.cell.rootsOK vcCutP506Roots = true := by decide +kernel

def vcCutP507 : SideCornerEntry := ⟨3/40, 3/8, 1/36, #v[8894979/625000000, 113235999/10000000000, 93007541/10000000000]⟩
abbrev vcCutP507Roots := vcOuterP507Roots
theorem vcCutP507_roots : vcCutP507.cell.rootsOK vcCutP507Roots = true := by decide +kernel

def vcCutP508 : SideCornerEntry := ⟨3/40, 3/8, 1/18, #v[8894979/625000000, 113235999/10000000000, 93007541/10000000000]⟩
abbrev vcCutP508Roots := vcOuterP508Roots
theorem vcCutP508_roots : vcCutP508.cell.rootsOK vcCutP508Roots = true := by decide +kernel

def vcCutP509 : SideCornerEntry := ⟨3/40, 2/5, 0, #v[5156413/400000000, 20052229/2000000000, 86549041/10000000000]⟩
abbrev vcCutP509Roots := vcOuterP509Roots
theorem vcCutP509_roots : vcCutP509.cell.rootsOK vcCutP509Roots = true := by decide +kernel

def vcCutP510 : SideCornerEntry := ⟨3/40, 2/5, 1/36, #v[67599433/5000000000, 26191589/2500000000, 22665019/2500000000]⟩
abbrev vcCutP510Roots := vcOuterP510Roots
theorem vcCutP510_roots : vcCutP510.cell.rootsOK vcCutP510Roots = true := by decide +kernel

def vcCutP511 : SideCornerEntry := ⟨3/40, 2/5, 1/18, #v[67599433/5000000000, 26191589/2500000000, 22665019/2500000000]⟩
abbrev vcCutP511Roots := vcOuterP511Roots
theorem vcCutP511_roots : vcCutP511.cell.rootsOK vcCutP511Roots = true := by decide +kernel

def vcCutPoints480 : Array SideCornerEntry := #[
  vcCutP480,
  vcCutP481,
  vcCutP482,
  vcCutP483,
  vcCutP484,
  vcCutP485,
  vcCutP486,
  vcCutP487,
  vcCutP488,
  vcCutP489,
  vcCutP490,
  vcCutP491,
  vcCutP492,
  vcCutP493,
  vcCutP494,
  vcCutP495,
  vcCutP496,
  vcCutP497,
  vcCutP498,
  vcCutP499,
  vcCutP500,
  vcCutP501,
  vcCutP502,
  vcCutP503,
  vcCutP504,
  vcCutP505,
  vcCutP506,
  vcCutP507,
  vcCutP508,
  vcCutP509,
  vcCutP510,
  vcCutP511]

end HlawkaSchatten.BelowExponent.Vertex
