/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.VcCornerData.Points544

/-! Checked corner data shared by the vertex middle and band regions: `Points544`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

def vcCutP544 : SideCornerEntry := ⟨1/10, 1/10, 1/36, #v[372714199/10000000000, 378284381/10000000000, 25284539/2000000000]⟩
abbrev vcCutP544Roots := vcOuterP544Roots
theorem vcCutP544_roots : vcCutP544.cell.rootsOK vcCutP544Roots = true := by decide +kernel

def vcCutP545 : SideCornerEntry := ⟨1/10, 1/10, 1/24, #v[261955489/10000000000, 65313951/2500000000, 11855449/1000000000]⟩
abbrev vcCutP545Roots := vcOuterP545Roots
theorem vcCutP545_roots : vcCutP545.cell.rootsOK vcCutP545Roots = true := by decide +kernel

def vcCutP546 : SideCornerEntry := ⟨1/10, 1/10, 1/18, #v[261955489/10000000000, 65313951/2500000000, 11855449/1000000000]⟩
abbrev vcCutP546Roots := vcOuterP546Roots
theorem vcCutP546_roots : vcCutP546.cell.rootsOK vcCutP546Roots = true := by decide +kernel

def vcCutP547 : SideCornerEntry := ⟨1/10, 9/80, 0, #v[102856179/2500000000, 401898043/10000000000, 199968729/10000000000]⟩
abbrev vcCutP547Roots := vcOuterP547Roots
theorem vcCutP547_roots : vcCutP547.cell.rootsOK vcCutP547Roots = true := by decide +kernel

def vcCutP548 : SideCornerEntry := ⟨1/10, 9/80, 1/72, #v[102856179/2500000000, 401898043/10000000000, 199968729/10000000000]⟩
abbrev vcCutP548Roots := vcOuterP548Roots
theorem vcCutP548_roots : vcCutP548.cell.rootsOK vcCutP548Roots = true := by decide +kernel

def vcCutP549 : SideCornerEntry := ⟨1/10, 9/80, 1/36, #v[78816761/2500000000, 77196551/2500000000, 5021629/312500000]⟩
abbrev vcCutP549Roots := vcOuterP549Roots
theorem vcCutP549_roots : vcCutP549.cell.rootsOK vcCutP549Roots = true := by decide +kernel

def vcCutP550 : SideCornerEntry := ⟨1/10, 9/80, 1/24, #v[325241307/10000000000, 6372337/200000000, 16472771/1000000000]⟩
abbrev vcCutP550Roots := vcOuterP550Roots
theorem vcCutP550_roots : vcCutP550.cell.rootsOK vcCutP550Roots = true := by decide +kernel

def vcCutP551 : SideCornerEntry := ⟨1/10, 9/80, 1/18, #v[325241307/10000000000, 6372337/200000000, 16472771/1000000000]⟩
abbrev vcCutP551Roots := vcOuterP551Roots
theorem vcCutP551_roots : vcCutP551.cell.rootsOK vcCutP551Roots = true := by decide +kernel

def vcCutP552 : SideCornerEntry := ⟨1/10, 1/8, 0, #v[447956069/10000000000, 440189073/10000000000, 201855253/10000000000]⟩
abbrev vcCutP552Roots := vcOuterP552Roots
theorem vcCutP552_roots : vcCutP552.cell.rootsOK vcCutP552Roots = true := by decide +kernel

def vcCutP553 : SideCornerEntry := ⟨1/10, 1/8, 1/72, #v[142886429/5000000000, 277954941/10000000000, 140529157/10000000000]⟩
abbrev vcCutP553Roots := vcOuterP553Roots
theorem vcCutP553_roots : vcCutP553.cell.rootsOK vcCutP553Roots = true := by decide +kernel

def vcCutP554 : SideCornerEntry := ⟨1/10, 1/8, 1/36, #v[447956069/10000000000, 440189073/10000000000, 201855253/10000000000]⟩
abbrev vcCutP554Roots := vcOuterP554Roots
theorem vcCutP554_roots : vcCutP554.cell.rootsOK vcCutP554Roots = true := by decide +kernel

def vcCutP555 : SideCornerEntry := ⟨1/10, 1/8, 1/24, #v[325241307/10000000000, 6372337/200000000, 16472771/1000000000]⟩
abbrev vcCutP555Roots := vcOuterP555Roots
theorem vcCutP555_roots : vcCutP555.cell.rootsOK vcCutP555Roots = true := by decide +kernel

def vcCutP556 : SideCornerEntry := ⟨1/10, 1/8, 1/18, #v[325241307/10000000000, 6372337/200000000, 16472771/1000000000]⟩
abbrev vcCutP556Roots := vcOuterP556Roots
theorem vcCutP556_roots : vcCutP556.cell.rootsOK vcCutP556Roots = true := by decide +kernel

def vcCutP557 : SideCornerEntry := ⟨1/10, 11/80, 1/36, #v[222928631/10000000000, 108470217/5000000000, 115630643/10000000000]⟩
abbrev vcCutP557Roots := vcOuterP557Roots
theorem vcCutP557_roots : vcCutP557.cell.rootsOK vcCutP557Roots = true := by decide +kernel

def vcCutP558 : SideCornerEntry := ⟨1/10, 11/80, 1/24, #v[45990407/2000000000, 223791821/10000000000, 29642123/2500000000]⟩
abbrev vcCutP558Roots := vcOuterP558Roots
theorem vcCutP558_roots : vcCutP558.cell.rootsOK vcCutP558Roots = true := by decide +kernel

def vcCutP559 : SideCornerEntry := ⟨1/10, 11/80, 1/18, #v[45990407/2000000000, 223791821/10000000000, 29642123/2500000000]⟩
abbrev vcCutP559Roots := vcOuterP559Roots
theorem vcCutP559_roots : vcCutP559.cell.rootsOK vcCutP559Roots = true := by decide +kernel

def vcCutP560 : SideCornerEntry := ⟨1/10, 3/20, 0, #v[482846967/10000000000, 229191061/5000000000, 47438/1953125]⟩
abbrev vcCutP560Roots := vcOuterP560Roots
theorem vcCutP560_roots : vcCutP560.cell.rootsOK vcCutP560Roots = true := by decide +kernel

def vcCutP561 : SideCornerEntry := ⟨1/10, 3/20, 1/36, #v[482846967/10000000000, 229191061/5000000000, 47438/1953125]⟩
abbrev vcCutP561Roots := vcOuterP561Roots
theorem vcCutP561_roots : vcCutP561.cell.rootsOK vcCutP561Roots = true := by decide +kernel

def vcCutP562 : SideCornerEntry := ⟨1/10, 3/20, 1/24, #v[169765891/10000000000, 163909787/10000000000, 11075671/1250000000]⟩
abbrev vcCutP562Roots := vcOuterP562Roots
theorem vcCutP562_roots : vcCutP562.cell.rootsOK vcCutP562Roots = true := by decide +kernel

def vcCutP563 : SideCornerEntry := ⟨1/10, 3/20, 1/18, #v[8335303/250000000, 63717133/2000000000, 7775103/500000000]⟩
abbrev vcCutP563Roots := vcOuterP563Roots
theorem vcCutP563_roots : vcCutP563.cell.rootsOK vcCutP563Roots = true := by decide +kernel

def vcCutP564 : SideCornerEntry := ⟨1/10, 7/40, 0, #v[508953261/10000000000, 238123827/5000000000, 295136237/10000000000]⟩
abbrev vcCutP564Roots := vcOuterP564Roots
theorem vcCutP564_roots : vcCutP564.cell.rootsOK vcCutP564Roots = true := by decide +kernel

def vcCutP565 : SideCornerEntry := ⟨1/10, 7/40, 1/36, #v[508953261/10000000000, 238123827/5000000000, 295136237/10000000000]⟩
abbrev vcCutP565Roots := vcOuterP565Roots
theorem vcCutP565_roots : vcCutP565.cell.rootsOK vcCutP565Roots = true := by decide +kernel

def vcCutP566 : SideCornerEntry := ⟨1/10, 7/40, 1/18, #v[362836759/10000000000, 17069007/500000000, 12571381/625000000]⟩
abbrev vcCutP566Roots := vcOuterP566Roots
theorem vcCutP566_roots : vcCutP566.cell.rootsOK vcCutP566Roots = true := by decide +kernel

def vcCutP567 : SideCornerEntry := ⟨1/10, 1/5, 0, #v[508953261/10000000000, 238123827/5000000000, 295136237/10000000000]⟩
abbrev vcCutP567Roots := vcOuterP567Roots
theorem vcCutP567_roots : vcCutP567.cell.rootsOK vcCutP567Roots = true := by decide +kernel

def vcCutP568 : SideCornerEntry := ⟨1/10, 1/5, 1/36, #v[508953261/10000000000, 238123827/5000000000, 295136237/10000000000]⟩
abbrev vcCutP568Roots := vcOuterP568Roots
theorem vcCutP568_roots : vcCutP568.cell.rootsOK vcCutP568Roots = true := by decide +kernel

def vcCutP569 : SideCornerEntry := ⟨1/10, 1/5, 1/18, #v[419368977/10000000000, 12165229/312500000, 266119687/10000000000]⟩
abbrev vcCutP569Roots := vcOuterP569Roots
theorem vcCutP569_roots : vcCutP569.cell.rootsOK vcCutP569Roots = true := by decide +kernel

def vcCutP570 : SideCornerEntry := ⟨1/10, 9/40, 0, #v[98537097/2500000000, 366361411/10000000000, 252301849/10000000000]⟩
abbrev vcCutP570Roots := vcOuterP570Roots
theorem vcCutP570_roots : vcCutP570.cell.rootsOK vcCutP570Roots = true := by decide +kernel

def vcCutP571 : SideCornerEntry := ⟨1/10, 9/40, 1/36, #v[419368977/10000000000, 12165229/312500000, 266119687/10000000000]⟩
abbrev vcCutP571Roots := vcOuterP571Roots
theorem vcCutP571_roots : vcCutP571.cell.rootsOK vcCutP571Roots = true := by decide +kernel

def vcCutP572 : SideCornerEntry := ⟨1/10, 9/40, 1/18, #v[419368977/10000000000, 12165229/312500000, 266119687/10000000000]⟩
abbrev vcCutP572Roots := vcOuterP572Roots
theorem vcCutP572_roots : vcCutP572.cell.rootsOK vcCutP572Roots = true := by decide +kernel

def vcCutP573 : SideCornerEntry := ⟨1/10, 1/4, 0, #v[292144709/10000000000, 266691541/10000000000, 19002179/1000000000]⟩
abbrev vcCutP573Roots := vcOuterP573Roots
theorem vcCutP573_roots : vcCutP573.cell.rootsOK vcCutP573Roots = true := by decide +kernel

def vcCutP574 : SideCornerEntry := ⟨1/10, 1/4, 1/36, #v[155089853/5000000000, 282670273/10000000000, 50073411/2500000000]⟩
abbrev vcCutP574Roots := vcOuterP574Roots
theorem vcCutP574_roots : vcCutP574.cell.rootsOK vcCutP574Roots = true := by decide +kernel

def vcCutP575 : SideCornerEntry := ⟨1/10, 1/4, 1/18, #v[155089853/5000000000, 282670273/10000000000, 50073411/2500000000]⟩
abbrev vcCutP575Roots := vcOuterP575Roots
theorem vcCutP575_roots : vcCutP575.cell.rootsOK vcCutP575Roots = true := by decide +kernel

def vcCutPoints544 : Array SideCornerEntry := #[
  vcCutP544,
  vcCutP545,
  vcCutP546,
  vcCutP547,
  vcCutP548,
  vcCutP549,
  vcCutP550,
  vcCutP551,
  vcCutP552,
  vcCutP553,
  vcCutP554,
  vcCutP555,
  vcCutP556,
  vcCutP557,
  vcCutP558,
  vcCutP559,
  vcCutP560,
  vcCutP561,
  vcCutP562,
  vcCutP563,
  vcCutP564,
  vcCutP565,
  vcCutP566,
  vcCutP567,
  vcCutP568,
  vcCutP569,
  vcCutP570,
  vcCutP571,
  vcCutP572,
  vcCutP573,
  vcCutP574,
  vcCutP575]

end HlawkaSchatten.BelowExponent.Vertex
