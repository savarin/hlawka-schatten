/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.VcCornerData.Points448

/-! Checked corner data shared by the vertex middle and band regions: `Points448`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

def vcCutP448 : SideCornerEntry := ⟨1/20, 39/80, 1/20, #v[25327081/10000000000, 8310509/5000000000, 1961787/1250000000]⟩
abbrev vcCutP448Roots := vcOuterP448Roots
theorem vcCutP448_roots : vcCutP448.cell.rootsOK vcCutP448Roots = true := by decide +kernel

def vcCutP449 : SideCornerEntry := ⟨1/20, 39/80, 3/40, #v[25550099/10000000000, 16698323/10000000000, 7863023/5000000000]⟩
abbrev vcCutP449Roots := vcOuterP449Roots
theorem vcCutP449_roots : vcCutP449.cell.rootsOK vcCutP449Roots = true := by decide +kernel

def vcCutP450 : SideCornerEntry := ⟨1/20, 39/80, 1/10, #v[25550099/10000000000, 16698323/10000000000, 7863023/5000000000]⟩
abbrev vcCutP450Roots := vcOuterP450Roots
theorem vcCutP450_roots : vcCutP450.cell.rootsOK vcCutP450Roots = true := by decide +kernel

def vcCutP451 : SideCornerEntry := ⟨1/16, 1/8, 1/36, #v[36376961/2000000000, 17417227/1000000000, 79865969/10000000000]⟩
abbrev vcCutP451Roots := vcOuterP451Roots
theorem vcCutP451_roots : vcCutP451.cell.rootsOK vcCutP451Roots = true := by decide +kernel

def vcCutP452 : SideCornerEntry := ⟨1/16, 1/8, 1/24, #v[187247651/10000000000, 179299759/10000000000, 16346597/2000000000]⟩
abbrev vcCutP452Roots := vcOuterP452Roots
theorem vcCutP452_roots : vcCutP452.cell.rootsOK vcCutP452Roots = true := by decide +kernel

def vcCutP453 : SideCornerEntry := ⟨1/16, 1/8, 1/18, #v[187247651/10000000000, 179299759/10000000000, 16346597/2000000000]⟩
abbrev vcCutP453Roots := vcOuterP453Roots
theorem vcCutP453_roots : vcCutP453.cell.rootsOK vcCutP453Roots = true := by decide +kernel

def vcCutP454 : SideCornerEntry := ⟨1/16, 11/80, 1/36, #v[36376961/2000000000, 17417227/1000000000, 79865969/10000000000]⟩
abbrev vcCutP454Roots := vcOuterP454Roots
theorem vcCutP454_roots : vcCutP454.cell.rootsOK vcCutP454Roots = true := by decide +kernel

def vcCutP455 : SideCornerEntry := ⟨1/16, 11/80, 1/24, #v[187247651/10000000000, 179299759/10000000000, 16346597/2000000000]⟩
abbrev vcCutP455Roots := vcOuterP455Roots
theorem vcCutP455_roots : vcCutP455.cell.rootsOK vcCutP455Roots = true := by decide +kernel

def vcCutP456 : SideCornerEntry := ⟨1/16, 11/80, 1/18, #v[187247651/10000000000, 179299759/10000000000, 16346597/2000000000]⟩
abbrev vcCutP456Roots := vcOuterP456Roots
theorem vcCutP456_roots : vcCutP456.cell.rootsOK vcCutP456Roots = true := by decide +kernel

def vcCutP457 : SideCornerEntry := ⟨1/16, 3/20, 1/36, #v[138133463/10000000000, 131236751/10000000000, 60730543/10000000000]⟩
abbrev vcCutP457Roots := vcOuterP457Roots
theorem vcCutP457_roots : vcCutP457.cell.rootsOK vcCutP457Roots = true := by decide +kernel

def vcCutP458 : SideCornerEntry := ⟨1/16, 3/20, 1/24, #v[142135511/10000000000, 67513933/5000000000, 31083259/5000000000]⟩
abbrev vcCutP458Roots := vcOuterP458Roots
theorem vcCutP458_roots : vcCutP458.cell.rootsOK vcCutP458Roots = true := by decide +kernel

def vcCutP459 : SideCornerEntry := ⟨1/16, 3/20, 1/18, #v[142135511/10000000000, 67513933/5000000000, 31083259/5000000000]⟩
abbrev vcCutP459Roots := vcOuterP459Roots
theorem vcCutP459_roots : vcCutP459.cell.rootsOK vcCutP459Roots = true := by decide +kernel

def vcCutP460 : SideCornerEntry := ⟨3/40, 1/10, 0, #v[379252457/10000000000, 184072683/5000000000, 43932261/2500000000]⟩
abbrev vcCutP460Roots := vcOuterP460Roots
theorem vcCutP460_roots : vcCutP460.cell.rootsOK vcCutP460Roots = true := by decide +kernel

def vcCutP461 : SideCornerEntry := ⟨3/40, 1/10, 1/72, #v[379252457/10000000000, 184072683/5000000000, 43932261/2500000000]⟩
abbrev vcCutP461Roots := vcOuterP461Roots
theorem vcCutP461_roots : vcCutP461.cell.rootsOK vcCutP461Roots = true := by decide +kernel

def vcCutP462 : SideCornerEntry := ⟨3/40, 1/10, 1/36, #v[14606231/625000000, 228400907/10000000000, 94132987/10000000000]⟩
abbrev vcCutP462Roots := vcOuterP462Roots
theorem vcCutP462_roots : vcCutP462.cell.rootsOK vcCutP462Roots = true := by decide +kernel

def vcCutP463 : SideCornerEntry := ⟨3/40, 1/10, 1/24, #v[9625247/400000000, 235210011/10000000000, 96354981/10000000000]⟩
abbrev vcCutP463Roots := vcOuterP463Roots
theorem vcCutP463_roots : vcCutP463.cell.rootsOK vcCutP463Roots = true := by decide +kernel

def vcCutP464 : SideCornerEntry := ⟨3/40, 1/10, 1/18, #v[9625247/400000000, 235210011/10000000000, 96354981/10000000000]⟩
abbrev vcCutP464Roots := vcOuterP464Roots
theorem vcCutP464_roots : vcCutP464.cell.rootsOK vcCutP464Roots = true := by decide +kernel

def vcCutP465 : SideCornerEntry := ⟨3/40, 9/80, 0, #v[379252457/10000000000, 184072683/5000000000, 43932261/2500000000]⟩
abbrev vcCutP465Roots := vcOuterP465Roots
theorem vcCutP465_roots : vcCutP465.cell.rootsOK vcCutP465Roots = true := by decide +kernel

def vcCutP466 : SideCornerEntry := ⟨3/40, 9/80, 1/72, #v[379252457/10000000000, 184072683/5000000000, 43932261/2500000000]⟩
abbrev vcCutP466Roots := vcOuterP466Roots
theorem vcCutP466_roots : vcCutP466.cell.rootsOK vcCutP466Roots = true := by decide +kernel

def vcCutP467 : SideCornerEntry := ⟨3/40, 9/80, 1/36, #v[136512061/5000000000, 66033547/2500000000, 126774457/10000000000]⟩
abbrev vcCutP467Roots := vcOuterP467Roots
theorem vcCutP467_roots : vcCutP467.cell.rootsOK vcCutP467Roots = true := by decide +kernel

def vcCutP468 : SideCornerEntry := ⟨3/40, 9/80, 1/24, #v[281368977/10000000000, 272259179/10000000000, 25954931/2000000000]⟩
abbrev vcCutP468Roots := vcOuterP468Roots
theorem vcCutP468_roots : vcCutP468.cell.rootsOK vcCutP468Roots = true := by decide +kernel

def vcCutP469 : SideCornerEntry := ⟨3/40, 9/80, 1/18, #v[281368977/10000000000, 272259179/10000000000, 25954931/2000000000]⟩
abbrev vcCutP469Roots := vcOuterP469Roots
theorem vcCutP469_roots : vcCutP469.cell.rootsOK vcCutP469Roots = true := by decide +kernel

def vcCutP470 : SideCornerEntry := ⟨3/40, 1/8, 0, #v[395057129/10000000000, 365348519/10000000000, 60395093/5000000000]⟩
abbrev vcCutP470Roots := vcOuterP470Roots
theorem vcCutP470_roots : vcCutP470.cell.rootsOK vcCutP470Roots = true := by decide +kernel

def vcCutP471 : SideCornerEntry := ⟨3/40, 1/8, 1/72, #v[3307971/125000000, 255963377/10000000000, 123788799/10000000000]⟩
abbrev vcCutP471Roots := vcOuterP471Roots
theorem vcCutP471_roots : vcCutP471.cell.rootsOK vcCutP471Roots = true := by decide +kernel

def vcCutP472 : SideCornerEntry := ⟨3/40, 1/8, 1/36, #v[395057129/10000000000, 365348519/10000000000, 126774457/10000000000]⟩
abbrev vcCutP472Roots := vcOuterP472Roots
theorem vcCutP472_roots : vcCutP472.cell.rootsOK vcCutP472Roots = true := by decide +kernel

def vcCutP473 : SideCornerEntry := ⟨3/40, 1/8, 1/24, #v[281368977/10000000000, 272259179/10000000000, 25954931/2000000000]⟩
abbrev vcCutP473Roots := vcOuterP473Roots
theorem vcCutP473_roots : vcCutP473.cell.rootsOK vcCutP473Roots = true := by decide +kernel

def vcCutP474 : SideCornerEntry := ⟨3/40, 1/8, 1/18, #v[281368977/10000000000, 272259179/10000000000, 25954931/2000000000]⟩
abbrev vcCutP474Roots := vcOuterP474Roots
theorem vcCutP474_roots : vcCutP474.cell.rootsOK vcCutP474Roots = true := by decide +kernel

def vcCutP475 : SideCornerEntry := ⟨3/40, 11/80, 1/36, #v[195213747/10000000000, 11730133/625000000, 5727653/625000000]⟩
abbrev vcCutP475Roots := vcOuterP475Roots
theorem vcCutP475_roots : vcCutP475.cell.rootsOK vcCutP475Roots = true := by decide +kernel

def vcCutP476 : SideCornerEntry := ⟨3/40, 11/80, 1/24, #v[100576449/5000000000, 193374913/10000000000, 93833117/10000000000]⟩
abbrev vcCutP476Roots := vcOuterP476Roots
theorem vcCutP476_roots : vcCutP476.cell.rootsOK vcCutP476Roots = true := by decide +kernel

def vcCutP477 : SideCornerEntry := ⟨3/40, 11/80, 1/18, #v[100576449/5000000000, 193374913/10000000000, 93833117/10000000000]⟩
abbrev vcCutP477Roots := vcOuterP477Roots
theorem vcCutP477_roots : vcCutP477.cell.rootsOK vcCutP477Roots = true := by decide +kernel

def vcCutP478 : SideCornerEntry := ⟨3/40, 3/20, 0, #v[482846967/10000000000, 229191061/5000000000, 47438/1953125]⟩
abbrev vcCutP478Roots := vcOuterP478Roots
theorem vcCutP478_roots : vcCutP478.cell.rootsOK vcCutP478Roots = true := by decide +kernel

def vcCutP479 : SideCornerEntry := ⟨3/40, 3/20, 1/36, #v[482846967/10000000000, 229191061/5000000000, 47438/1953125]⟩
abbrev vcCutP479Roots := vcOuterP479Roots
theorem vcCutP479_roots : vcCutP479.cell.rootsOK vcCutP479Roots = true := by decide +kernel

def vcCutPoints448 : Array SideCornerEntry := #[
  vcCutP448,
  vcCutP449,
  vcCutP450,
  vcCutP451,
  vcCutP452,
  vcCutP453,
  vcCutP454,
  vcCutP455,
  vcCutP456,
  vcCutP457,
  vcCutP458,
  vcCutP459,
  vcCutP460,
  vcCutP461,
  vcCutP462,
  vcCutP463,
  vcCutP464,
  vcCutP465,
  vcCutP466,
  vcCutP467,
  vcCutP468,
  vcCutP469,
  vcCutP470,
  vcCutP471,
  vcCutP472,
  vcCutP473,
  vcCutP474,
  vcCutP475,
  vcCutP476,
  vcCutP477,
  vcCutP478,
  vcCutP479]

end HlawkaSchatten.BelowExponent.Vertex
