/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.VcCornerData.Points416

/-! Checked corner data shared by the vertex middle and band regions: `Points416`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

def vcCutP416 : SideCornerEntry := ⟨1/20, 17/40, 1/40, #v[1056449/400000000, 18958703/10000000000, 14919453/10000000000]⟩
abbrev vcCutP416Roots := vcOuterP416Roots
theorem vcCutP416_roots : vcCutP416.cell.rootsOK vcCutP416Roots = true := by decide +kernel

def vcCutP417 : SideCornerEntry := ⟨1/20, 17/40, 1/36, #v[25046391/2000000000, 46397241/5000000000, 20319447/2500000000]⟩
abbrev vcCutP417Roots := vcOuterP417Roots
theorem vcCutP417_roots : vcCutP417.cell.rootsOK vcCutP417Roots = true := by decide +kernel

def vcCutP418 : SideCornerEntry := ⟨1/20, 17/40, 1/20, #v[13292369/5000000000, 9471539/5000000000, 7404217/5000000000]⟩
abbrev vcCutP418Roots := vcOuterP418Roots
theorem vcCutP418_roots : vcCutP418.cell.rootsOK vcCutP418Roots = true := by decide +kernel

def vcCutP419 : SideCornerEntry := ⟨1/20, 17/40, 1/18, #v[25046391/2000000000, 46397241/5000000000, 20319447/2500000000]⟩
abbrev vcCutP419Roots := vcOuterP419Roots
theorem vcCutP419_roots : vcCutP419.cell.rootsOK vcCutP419Roots = true := by decide +kernel

def vcCutP420 : SideCornerEntry := ⟨1/20, 17/40, 3/40, #v[26852871/10000000000, 4765787/2500000000, 14831637/10000000000]⟩
abbrev vcCutP420Roots := vcOuterP420Roots
theorem vcCutP420_roots : vcCutP420.cell.rootsOK vcCutP420Roots = true := by decide +kernel

def vcCutP421 : SideCornerEntry := ⟨1/20, 17/40, 1/10, #v[26852871/10000000000, 4765787/2500000000, 14831637/10000000000]⟩
abbrev vcCutP421Roots := vcOuterP421Roots
theorem vcCutP421_roots : vcCutP421.cell.rootsOK vcCutP421Roots = true := by decide +kernel

def vcCutP422 : SideCornerEntry := ⟨1/20, 7/16, 0, #v[12977857/5000000000, 18382773/10000000000, 15070817/10000000000]⟩
abbrev vcCutP422Roots := vcOuterP422Roots
theorem vcCutP422_roots : vcCutP422.cell.rootsOK vcCutP422Roots = true := by decide +kernel

def vcCutP423 : SideCornerEntry := ⟨1/20, 7/16, 1/40, #v[2599689/1000000000, 18382773/10000000000, 15070817/10000000000]⟩
abbrev vcCutP423Roots := vcOuterP423Roots
theorem vcCutP423_roots : vcCutP423.cell.rootsOK vcCutP423Roots = true := by decide +kernel

def vcCutP424 : SideCornerEntry := ⟨1/20, 7/16, 1/20, #v[26153801/10000000000, 9171777/5000000000, 3738913/2500000000]⟩
abbrev vcCutP424Roots := vcOuterP424Roots
theorem vcCutP424_roots : vcCutP424.cell.rootsOK vcCutP424Roots = true := by decide +kernel

def vcCutP425 : SideCornerEntry := ⟨1/20, 7/16, 3/40, #v[26405341/10000000000, 288277/156250000, 7487281/5000000000]⟩
abbrev vcCutP425Roots := vcOuterP425Roots
theorem vcCutP425_roots : vcCutP425.cell.rootsOK vcCutP425Roots = true := by decide +kernel

def vcCutP426 : SideCornerEntry := ⟨1/20, 7/16, 1/10, #v[26405341/10000000000, 288277/156250000, 7487281/5000000000]⟩
abbrev vcCutP426Roots := vcOuterP426Roots
theorem vcCutP426_roots : vcCutP426.cell.rootsOK vcCutP426Roots = true := by decide +kernel

def vcCutP427 : SideCornerEntry := ⟨1/20, 9/20, 0, #v[58550351/5000000000, 42359223/5000000000, 10035689/1250000000]⟩
abbrev vcCutP427Roots := vcOuterP427Roots
theorem vcCutP427_roots : vcCutP427.cell.rootsOK vcCutP427Roots = true := by decide +kernel

def vcCutP428 : SideCornerEntry := ⟨1/20, 9/20, 1/40, #v[802189/312500000, 17872257/10000000000, 610549/400000000]⟩
abbrev vcCutP428Roots := vcOuterP428Roots
theorem vcCutP428_roots : vcCutP428.cell.rootsOK vcCutP428Roots = true := by decide +kernel

def vcCutP429 : SideCornerEntry := ⟨1/20, 9/20, 1/36, #v[122193559/10000000000, 22022501/2500000000, 10468309/1250000000]⟩
abbrev vcCutP429Roots := vcOuterP429Roots
theorem vcCutP429_roots : vcCutP429.cell.rootsOK vcCutP429Roots = true := by decide +kernel

def vcCutP430 : SideCornerEntry := ⟨1/20, 9/20, 1/20, #v[3226771/1250000000, 2226873/1250000000, 946639/625000000]⟩
abbrev vcCutP430Roots := vcOuterP430Roots
theorem vcCutP430_roots : vcCutP430.cell.rootsOK vcCutP430Roots = true := by decide +kernel

def vcCutP431 : SideCornerEntry := ⟨1/20, 9/20, 1/18, #v[122193559/10000000000, 22022501/2500000000, 10468309/1250000000]⟩
abbrev vcCutP431Roots := vcOuterP431Roots
theorem vcCutP431_roots : vcCutP431.cell.rootsOK vcCutP431Roots = true := by decide +kernel

def vcCutP432 : SideCornerEntry := ⟨1/20, 9/20, 3/40, #v[26052921/10000000000, 17910043/10000000000, 15164489/10000000000]⟩
abbrev vcCutP432Roots := vcOuterP432Roots
theorem vcCutP432_roots : vcCutP432.cell.rootsOK vcCutP432Roots = true := by decide +kernel

def vcCutP433 : SideCornerEntry := ⟨1/20, 9/20, 1/10, #v[26052921/10000000000, 17910043/10000000000, 15164489/10000000000]⟩
abbrev vcCutP433Roots := vcOuterP433Roots
theorem vcCutP433_roots : vcCutP433.cell.rootsOK vcCutP433Roots = true := by decide +kernel

def vcCutP434 : SideCornerEntry := ⟨1/20, 37/80, 0, #v[25407393/10000000000, 8710759/5000000000, 15499549/10000000000]⟩
abbrev vcCutP434Roots := vcOuterP434Roots
theorem vcCutP434_roots : vcCutP434.cell.rootsOK vcCutP434Roots = true := by decide +kernel

def vcCutP435 : SideCornerEntry := ⟨1/20, 37/80, 1/40, #v[25426607/10000000000, 8710759/5000000000, 15499549/10000000000]⟩
abbrev vcCutP435Roots := vcOuterP435Roots
theorem vcCutP435_roots : vcCutP435.cell.rootsOK vcCutP435Roots = true := by decide +kernel

def vcCutP436 : SideCornerEntry := ⟨1/20, 37/80, 1/20, #v[25561559/10000000000, 17351209/10000000000, 15381659/10000000000]⟩
abbrev vcCutP436Roots := vcOuterP436Roots
theorem vcCutP436_roots : vcCutP436.cell.rootsOK vcCutP436Roots = true := by decide +kernel

def vcCutP437 : SideCornerEntry := ⟨1/20, 37/80, 3/40, #v[12895571/5000000000, 8718839/5000000000, 15403197/10000000000]⟩
abbrev vcCutP437Roots := vcOuterP437Roots
theorem vcCutP437_roots : vcCutP437.cell.rootsOK vcCutP437Roots = true := by decide +kernel

def vcCutP438 : SideCornerEntry := ⟨1/20, 37/80, 1/10, #v[12895571/5000000000, 8718839/5000000000, 15403197/10000000000]⟩
abbrev vcCutP438Roots := vcOuterP438Roots
theorem vcCutP438_roots : vcCutP438.cell.rootsOK vcCutP438Roots = true := by decide +kernel

def vcCutP439 : SideCornerEntry := ⟨1/20, 19/40, 0, #v[11648393/1000000000, 16406153/2000000000, 10035689/1250000000]⟩
abbrev vcCutP439Roots := vcOuterP439Roots
theorem vcCutP439_roots : vcCutP439.cell.rootsOK vcCutP439Roots = true := by decide +kernel

def vcCutP440 : SideCornerEntry := ⟨1/20, 19/40, 1/40, #v[6316037/2500000000, 17026403/10000000000, 15809103/10000000000]⟩
abbrev vcCutP440Roots := vcOuterP440Roots
theorem vcCutP440_roots : vcCutP440.cell.rootsOK vcCutP440Roots = true := by decide +kernel

def vcCutP441 : SideCornerEntry := ⟨1/20, 19/40, 1/36, #v[60801499/5000000000, 42648203/5000000000, 10468309/1250000000]⟩
abbrev vcCutP441Roots := vcOuterP441Roots
theorem vcCutP441_roots : vcCutP441.cell.rootsOK vcCutP441Roots = true := by decide +kernel

def vcCutP442 : SideCornerEntry := ⟨1/20, 19/40, 1/20, #v[6348369/2500000000, 16947719/10000000000, 1961787/1250000000]⟩
abbrev vcCutP442Roots := vcOuterP442Roots
theorem vcCutP442_roots : vcCutP442.cell.rootsOK vcCutP442Roots = true := by decide +kernel

def vcCutP443 : SideCornerEntry := ⟨1/20, 19/40, 1/18, #v[60801499/5000000000, 42648203/5000000000, 10468309/1250000000]⟩
abbrev vcCutP443Roots := vcOuterP443Roots
theorem vcCutP443_roots : vcCutP443.cell.rootsOK vcCutP443Roots = true := by decide +kernel

def vcCutP444 : SideCornerEntry := ⟨1/20, 19/40, 3/40, #v[3202179/1250000000, 2128493/1250000000, 7863023/5000000000]⟩
abbrev vcCutP444Roots := vcOuterP444Roots
theorem vcCutP444_roots : vcCutP444.cell.rootsOK vcCutP444Roots = true := by decide +kernel

def vcCutP445 : SideCornerEntry := ⟨1/20, 19/40, 1/10, #v[3202179/1250000000, 2128493/1250000000, 7863023/5000000000]⟩
abbrev vcCutP445Roots := vcOuterP445Roots
theorem vcCutP445_roots : vcCutP445.cell.rootsOK vcCutP445Roots = true := by decide +kernel

def vcCutP446 : SideCornerEntry := ⟨1/20, 39/80, 0, #v[6296491/2500000000, 3340283/2000000000, 15809103/10000000000]⟩
abbrev vcCutP446Roots := vcOuterP446Roots
theorem vcCutP446_roots : vcCutP446.cell.rootsOK vcCutP446Roots = true := by decide +kernel

def vcCutP447 : SideCornerEntry := ⟨1/20, 39/80, 1/40, #v[2519867/1000000000, 3340283/2000000000, 15809103/10000000000]⟩
abbrev vcCutP447Roots := vcOuterP447Roots
theorem vcCutP447_roots : vcCutP447.cell.rootsOK vcCutP447Roots = true := by decide +kernel

def vcCutPoints416 : Array SideCornerEntry := #[
  vcCutP416,
  vcCutP417,
  vcCutP418,
  vcCutP419,
  vcCutP420,
  vcCutP421,
  vcCutP422,
  vcCutP423,
  vcCutP424,
  vcCutP425,
  vcCutP426,
  vcCutP427,
  vcCutP428,
  vcCutP429,
  vcCutP430,
  vcCutP431,
  vcCutP432,
  vcCutP433,
  vcCutP434,
  vcCutP435,
  vcCutP436,
  vcCutP437,
  vcCutP438,
  vcCutP439,
  vcCutP440,
  vcCutP441,
  vcCutP442,
  vcCutP443,
  vcCutP444,
  vcCutP445,
  vcCutP446,
  vcCutP447]

end HlawkaSchatten.BelowExponent.Vertex
