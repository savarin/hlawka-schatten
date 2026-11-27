/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.VcCornerData.Points608

/-! Checked corner data shared by the vertex middle and band regions: `Points608`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

def vcCutP608 : SideCornerEntry := ⟨9/80, 9/80, 1/18, #v[171754339/5000000000, 339200307/10000000000, 36196617/2000000000]⟩
abbrev vcCutP608Roots := vcOuterP608Roots
theorem vcCutP608_roots : vcCutP608.cell.rootsOK vcCutP608Roots = true := by decide +kernel

def vcCutP609 : SideCornerEntry := ⟨9/80, 1/8, 1/36, #v[20805553/625000000, 328613921/10000000000, 176453159/10000000000]⟩
abbrev vcCutP609Roots := vcOuterP609Roots
theorem vcCutP609_roots : vcCutP609.cell.rootsOK vcCutP609Roots = true := by decide +kernel

def vcCutP610 : SideCornerEntry := ⟨9/80, 1/8, 1/24, #v[171754339/5000000000, 339200307/10000000000, 36196617/2000000000]⟩
abbrev vcCutP610Roots := vcOuterP610Roots
theorem vcCutP610_roots : vcCutP610.cell.rootsOK vcCutP610Roots = true := by decide +kernel

def vcCutP611 : SideCornerEntry := ⟨9/80, 1/8, 1/18, #v[171754339/5000000000, 339200307/10000000000, 36196617/2000000000]⟩
abbrev vcCutP611Roots := vcOuterP611Roots
theorem vcCutP611_roots : vcCutP611.cell.rootsOK vcCutP611Roots = true := by decide +kernel

def vcCutP612 : SideCornerEntry := ⟨9/80, 11/80, 1/36, #v[235185943/10000000000, 230665843/10000000000, 25401301/2000000000]⟩
abbrev vcCutP612Roots := vcOuterP612Roots
theorem vcCutP612_roots : vcCutP612.cell.rootsOK vcCutP612Roots = true := by decide +kernel

def vcCutP613 : SideCornerEntry := ⟨9/80, 11/80, 1/24, #v[60667781/2500000000, 47610477/2000000000, 32577193/2500000000]⟩
abbrev vcCutP613Roots := vcOuterP613Roots
theorem vcCutP613_roots : vcCutP613.cell.rootsOK vcCutP613Roots = true := by decide +kernel

def vcCutP614 : SideCornerEntry := ⟨9/80, 11/80, 1/18, #v[60667781/2500000000, 47610477/2000000000, 32577193/2500000000]⟩
abbrev vcCutP614Roots := vcOuterP614Roots
theorem vcCutP614_roots : vcCutP614.cell.rootsOK vcCutP614Roots = true := by decide +kernel

def vcCutP615 : SideCornerEntry := ⟨9/80, 3/20, 1/36, #v[173323343/10000000000, 168698413/10000000000, 94991517/10000000000]⟩
abbrev vcCutP615Roots := vcOuterP615Roots
theorem vcCutP615_roots : vcCutP615.cell.rootsOK vcCutP615Roots = true := by decide +kernel

def vcCutP616 : SideCornerEntry := ⟨9/80, 3/20, 1/24, #v[44703179/2500000000, 43515461/2500000000, 48747859/5000000000]⟩
abbrev vcCutP616Roots := vcOuterP616Roots
theorem vcCutP616_roots : vcCutP616.cell.rootsOK vcCutP616Roots = true := by decide +kernel

def vcCutP617 : SideCornerEntry := ⟨9/80, 3/20, 1/18, #v[44703179/2500000000, 43515461/2500000000, 48747859/5000000000]⟩
abbrev vcCutP617Roots := vcOuterP617Roots
theorem vcCutP617_roots : vcCutP617.cell.rootsOK vcCutP617Roots = true := by decide +kernel

def vcCutP618 : SideCornerEntry := ⟨1/8, 1/10, 0, #v[372714199/10000000000, 378284381/10000000000, 25284539/2000000000]⟩
abbrev vcCutP618Roots := vcOuterP618Roots
theorem vcCutP618_roots : vcCutP618.cell.rootsOK vcCutP618Roots = true := by decide +kernel

def vcCutP619 : SideCornerEntry := ⟨1/8, 1/10, 1/36, #v[372714199/10000000000, 378284381/10000000000, 25284539/2000000000]⟩
abbrev vcCutP619Roots := vcOuterP619Roots
theorem vcCutP619_roots : vcCutP619.cell.rootsOK vcCutP619Roots = true := by decide +kernel

def vcCutP620 : SideCornerEntry := ⟨1/8, 1/10, 1/24, #v[268868589/10000000000, 135442859/5000000000, 63949469/5000000000]⟩
abbrev vcCutP620Roots := vcOuterP620Roots
theorem vcCutP620_roots : vcCutP620.cell.rootsOK vcCutP620Roots = true := by decide +kernel

def vcCutP621 : SideCornerEntry := ⟨1/8, 1/10, 1/18, #v[268868589/10000000000, 135442859/5000000000, 63949469/5000000000]⟩
abbrev vcCutP621Roots := vcOuterP621Roots
theorem vcCutP621_roots : vcCutP621.cell.rootsOK vcCutP621Roots = true := by decide +kernel

def vcCutP622 : SideCornerEntry := ⟨1/8, 9/80, 1/36, #v[20805553/625000000, 328613921/10000000000, 176453159/10000000000]⟩
abbrev vcCutP622Roots := vcOuterP622Roots
theorem vcCutP622_roots : vcCutP622.cell.rootsOK vcCutP622Roots = true := by decide +kernel

def vcCutP623 : SideCornerEntry := ⟨1/8, 9/80, 1/24, #v[171754339/5000000000, 339200307/10000000000, 36196617/2000000000]⟩
abbrev vcCutP623Roots := vcOuterP623Roots
theorem vcCutP623_roots : vcCutP623.cell.rootsOK vcCutP623Roots = true := by decide +kernel

def vcCutP624 : SideCornerEntry := ⟨1/8, 9/80, 1/18, #v[171754339/5000000000, 339200307/10000000000, 36196617/2000000000]⟩
abbrev vcCutP624Roots := vcOuterP624Roots
theorem vcCutP624_roots : vcCutP624.cell.rootsOK vcCutP624Roots = true := by decide +kernel

def vcCutP625 : SideCornerEntry := ⟨1/8, 1/8, 0, #v[456713681/10000000000, 460978407/10000000000, 230940813/10000000000]⟩
abbrev vcCutP625Roots := vcOuterP625Roots
theorem vcCutP625_roots : vcCutP625.cell.rootsOK vcCutP625Roots = true := by decide +kernel

def vcCutP626 : SideCornerEntry := ⟨1/8, 1/8, 1/36, #v[456713681/10000000000, 460978407/10000000000, 230940813/10000000000]⟩
abbrev vcCutP626Roots := vcOuterP626Roots
theorem vcCutP626_roots : vcCutP626.cell.rootsOK vcCutP626Roots = true := by decide +kernel

def vcCutP627 : SideCornerEntry := ⟨1/8, 1/8, 1/24, #v[171754339/5000000000, 339200307/10000000000, 36196617/2000000000]⟩
abbrev vcCutP627Roots := vcOuterP627Roots
theorem vcCutP627_roots : vcCutP627.cell.rootsOK vcCutP627Roots = true := by decide +kernel

def vcCutP628 : SideCornerEntry := ⟨1/8, 1/8, 1/18, #v[171754339/5000000000, 345338239/10000000000, 36196617/2000000000]⟩
abbrev vcCutP628Roots := vcOuterP628Roots
theorem vcCutP628_roots : vcCutP628.cell.rootsOK vcCutP628Roots = true := by decide +kernel

def vcCutP629 : SideCornerEntry := ⟨1/8, 11/80, 1/36, #v[235185943/10000000000, 230665843/10000000000, 25401301/2000000000]⟩
abbrev vcCutP629Roots := vcOuterP629Roots
theorem vcCutP629_roots : vcCutP629.cell.rootsOK vcCutP629Roots = true := by decide +kernel

def vcCutP630 : SideCornerEntry := ⟨1/8, 11/80, 1/24, #v[60667781/2500000000, 47610477/2000000000, 32577193/2500000000]⟩
abbrev vcCutP630Roots := vcOuterP630Roots
theorem vcCutP630_roots : vcCutP630.cell.rootsOK vcCutP630Roots = true := by decide +kernel

def vcCutP631 : SideCornerEntry := ⟨1/8, 11/80, 1/18, #v[60667781/2500000000, 47610477/2000000000, 32577193/2500000000]⟩
abbrev vcCutP631Roots := vcOuterP631Roots
theorem vcCutP631_roots : vcCutP631.cell.rootsOK vcCutP631Roots = true := by decide +kernel

def vcCutP632 : SideCornerEntry := ⟨1/8, 3/20, 0, #v[456713681/10000000000, 460978407/10000000000, 230940813/10000000000]⟩
abbrev vcCutP632Roots := vcOuterP632Roots
theorem vcCutP632_roots : vcCutP632.cell.rootsOK vcCutP632Roots = true := by decide +kernel

def vcCutP633 : SideCornerEntry := ⟨1/8, 3/20, 1/36, #v[456713681/10000000000, 460978407/10000000000, 230940813/10000000000]⟩
abbrev vcCutP633Roots := vcOuterP633Roots
theorem vcCutP633_roots : vcCutP633.cell.rootsOK vcCutP633Roots = true := by decide +kernel

def vcCutP634 : SideCornerEntry := ⟨1/8, 3/20, 1/24, #v[44703179/2500000000, 43515461/2500000000, 48747859/5000000000]⟩
abbrev vcCutP634Roots := vcOuterP634Roots
theorem vcCutP634_roots : vcCutP634.cell.rootsOK vcCutP634Roots = true := by decide +kernel

def vcCutP635 : SideCornerEntry := ⟨1/8, 3/20, 1/18, #v[345307059/10000000000, 345338239/10000000000, 44825007/2500000000]⟩
abbrev vcCutP635Roots := vcOuterP635Roots
theorem vcCutP635_roots : vcCutP635.cell.rootsOK vcCutP635Roots = true := by decide +kernel

def vcCutP636 : SideCornerEntry := ⟨1/8, 7/40, 0, #v[366741977/10000000000, 351037321/10000000000, 6912197/312500000]⟩
abbrev vcCutP636Roots := vcOuterP636Roots
theorem vcCutP636_roots : vcCutP636.cell.rootsOK vcCutP636Roots = true := by decide +kernel

def vcCutP637 : SideCornerEntry := ⟨1/8, 7/40, 1/36, #v[390105421/10000000000, 74683361/2000000000, 233679099/10000000000]⟩
abbrev vcCutP637Roots := vcOuterP637Roots
theorem vcCutP637_roots : vcCutP637.cell.rootsOK vcCutP637Roots = true := by decide +kernel

def vcCutP638 : SideCornerEntry := ⟨1/8, 7/40, 1/18, #v[390105421/10000000000, 74683361/2000000000, 233679099/10000000000]⟩
abbrev vcCutP638Roots := vcOuterP638Roots
theorem vcCutP638_roots : vcCutP638.cell.rootsOK vcCutP638Roots = true := by decide +kernel

def vcCutP639 : SideCornerEntry := ⟨1/8, 1/5, 0, #v[43756697/1000000000, 51388469/1250000000, 9309799/312500000]⟩
abbrev vcCutP639Roots := vcOuterP639Roots
theorem vcCutP639_roots : vcCutP639.cell.rootsOK vcCutP639Roots = true := by decide +kernel

def vcCutPoints608 : Array SideCornerEntry := #[
  vcCutP608,
  vcCutP609,
  vcCutP610,
  vcCutP611,
  vcCutP612,
  vcCutP613,
  vcCutP614,
  vcCutP615,
  vcCutP616,
  vcCutP617,
  vcCutP618,
  vcCutP619,
  vcCutP620,
  vcCutP621,
  vcCutP622,
  vcCutP623,
  vcCutP624,
  vcCutP625,
  vcCutP626,
  vcCutP627,
  vcCutP628,
  vcCutP629,
  vcCutP630,
  vcCutP631,
  vcCutP632,
  vcCutP633,
  vcCutP634,
  vcCutP635,
  vcCutP636,
  vcCutP637,
  vcCutP638,
  vcCutP639]

end HlawkaSchatten.BelowExponent.Vertex
