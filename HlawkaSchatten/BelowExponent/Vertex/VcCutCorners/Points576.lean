/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.VcCornerData.Points576

/-! Checked corner data shared by the vertex middle and band regions: `Points576`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

def vcCutP576 : SideCornerEntry := ⟨1/10, 11/40, 0, #v[231159293/10000000000, 206734377/10000000000, 30478661/2000000000]⟩
abbrev vcCutP576Roots := vcOuterP576Roots
theorem vcCutP576_roots : vcCutP576.cell.rootsOK vcCutP576Roots = true := by decide +kernel

def vcCutP577 : SideCornerEntry := ⟨1/10, 11/40, 1/36, #v[48979247/2000000000, 27323757/1250000000, 80258487/5000000000]⟩
abbrev vcCutP577Roots := vcOuterP577Roots
theorem vcCutP577_roots : vcCutP577.cell.rootsOK vcCutP577Roots = true := by decide +kernel

def vcCutP578 : SideCornerEntry := ⟨1/10, 11/40, 1/18, #v[48979247/2000000000, 27323757/1250000000, 80258487/5000000000]⟩
abbrev vcCutP578Roots := vcOuterP578Roots
theorem vcCutP578_roots : vcCutP578.cell.rootsOK vcCutP578Roots = true := by decide +kernel

def vcCutP579 : SideCornerEntry := ⟨1/10, 3/10, 0, #v[48307241/2500000000, 33793117/2000000000, 5160863/400000000]⟩
abbrev vcCutP579Roots := vcOuterP579Roots
theorem vcCutP579_roots : vcCutP579.cell.rootsOK vcCutP579Roots = true := by decide +kernel

def vcCutP580 : SideCornerEntry := ⟨1/10, 3/10, 1/36, #v[40856989/2000000000, 89115627/5000000000, 848547/62500000]⟩
abbrev vcCutP580Roots := vcOuterP580Roots
theorem vcCutP580_roots : vcCutP580.cell.rootsOK vcCutP580Roots = true := by decide +kernel

def vcCutP581 : SideCornerEntry := ⟨1/10, 3/10, 1/18, #v[40856989/2000000000, 89115627/5000000000, 848547/62500000]⟩
abbrev vcCutP581Roots := vcOuterP581Roots
theorem vcCutP581_roots : vcCutP581.cell.rootsOK vcCutP581Roots = true := by decide +kernel

def vcCutP582 : SideCornerEntry := ⟨1/10, 13/40, 0, #v[42188883/2500000000, 144166789/10000000000, 57147399/5000000000]⟩
abbrev vcCutP582Roots := vcOuterP582Roots
theorem vcCutP582_roots : vcCutP582.cell.rootsOK vcCutP582Roots = true := by decide +kernel

def vcCutP583 : SideCornerEntry := ⟨1/10, 13/40, 1/36, #v[44534103/2500000000, 30354557/2000000000, 7515577/625000000]⟩
abbrev vcCutP583Roots := vcOuterP583Roots
theorem vcCutP583_roots : vcCutP583.cell.rootsOK vcCutP583Roots = true := by decide +kernel

def vcCutP584 : SideCornerEntry := ⟨1/10, 13/40, 1/18, #v[44534103/2500000000, 30354557/2000000000, 7515577/625000000]⟩
abbrev vcCutP584Roots := vcOuterP584Roots
theorem vcCutP584_roots : vcCutP584.cell.rootsOK vcCutP584Roots = true := by decide +kernel

def vcCutP585 : SideCornerEntry := ⟨1/10, 7/20, 0, #v[152797859/10000000000, 6373841/500000000, 52621853/5000000000]⟩
abbrev vcCutP585Roots := vcOuterP585Roots
theorem vcCutP585_roots : vcCutP585.cell.rootsOK vcCutP585Roots = true := by decide +kernel

def vcCutP586 : SideCornerEntry := ⟨1/10, 7/20, 1/36, #v[161131633/10000000000, 133988551/10000000000, 110770181/10000000000]⟩
abbrev vcCutP586Roots := vcOuterP586Roots
theorem vcCutP586_roots : vcCutP586.cell.rootsOK vcCutP586Roots = true := by decide +kernel

def vcCutP587 : SideCornerEntry := ⟨1/10, 7/20, 1/18, #v[161131633/10000000000, 133988551/10000000000, 110770181/10000000000]⟩
abbrev vcCutP587Roots := vcOuterP587Roots
theorem vcCutP587_roots : vcCutP587.cell.rootsOK vcCutP587Roots = true := by decide +kernel

def vcCutP588 : SideCornerEntry := ⟨1/10, 3/8, 0, #v[17858633/1250000000, 23263127/2000000000, 50186847/5000000000]⟩
abbrev vcCutP588Roots := vcOuterP588Roots
theorem vcCutP588_roots : vcCutP588.cell.rootsOK vcCutP588Roots = true := by decide +kernel

def vcCutP589 : SideCornerEntry := ⟨1/10, 3/8, 1/36, #v[4703817/312500000, 122112567/10000000000, 10560969/1000000000]⟩
abbrev vcCutP589Roots := vcOuterP589Roots
theorem vcCutP589_roots : vcCutP589.cell.rootsOK vcCutP589Roots = true := by decide +kernel

def vcCutP590 : SideCornerEntry := ⟨1/10, 3/8, 1/18, #v[4703817/312500000, 122112567/10000000000, 10560969/1000000000]⟩
abbrev vcCutP590Roots := vcOuterP590Roots
theorem vcCutP590_roots : vcCutP590.cell.rootsOK vcCutP590Roots = true := by decide +kernel

def vcCutP591 : SideCornerEntry := ⟨1/10, 2/5, 0, #v[27508637/2000000000, 109223577/10000000000, 100315051/10000000000]⟩
abbrev vcCutP591Roots := vcOuterP591Roots
theorem vcCutP591_roots : vcCutP591.cell.rootsOK vcCutP591Roots = true := by decide +kernel

def vcCutP592 : SideCornerEntry := ⟨1/10, 2/5, 1/36, #v[144842103/10000000000, 5729133/500000000, 105591611/10000000000]⟩
abbrev vcCutP592Roots := vcOuterP592Roots
theorem vcCutP592_roots : vcCutP592.cell.rootsOK vcCutP592Roots = true := by decide +kernel

def vcCutP593 : SideCornerEntry := ⟨1/10, 2/5, 1/18, #v[144842103/10000000000, 5729133/500000000, 105591611/10000000000]⟩
abbrev vcCutP593Roots := vcOuterP593Roots
theorem vcCutP593_roots : vcCutP593.cell.rootsOK vcCutP593Roots = true := by decide +kernel

def vcCutP594 : SideCornerEntry := ⟨1/10, 17/40, 0, #v[69375663/5000000000, 105605723/10000000000, 105067747/10000000000]⟩
abbrev vcCutP594Roots := vcOuterP594Roots
theorem vcCutP594_roots : vcCutP594.cell.rootsOK vcCutP594Roots = true := by decide +kernel

def vcCutP595 : SideCornerEntry := ⟨1/10, 17/40, 1/36, #v[14620889/1000000000, 110768401/10000000000, 110684611/10000000000]⟩
abbrev vcCutP595Roots := vcOuterP595Roots
theorem vcCutP595_roots : vcCutP595.cell.rootsOK vcCutP595Roots = true := by decide +kernel

def vcCutP596 : SideCornerEntry := ⟨1/10, 17/40, 1/18, #v[14620889/1000000000, 110768401/10000000000, 110684611/10000000000]⟩
abbrev vcCutP596Roots := vcOuterP596Roots
theorem vcCutP596_roots : vcCutP596.cell.rootsOK vcCutP596Roots = true := by decide +kernel

def vcCutP597 : SideCornerEntry := ⟨1/10, 9/20, 0, #v[69375663/5000000000, 52513709/5000000000, 105067747/10000000000]⟩
abbrev vcCutP597Roots := vcOuterP597Roots
theorem vcCutP597_roots : vcCutP597.cell.rootsOK vcCutP597Roots = true := by decide +kernel

def vcCutP598 : SideCornerEntry := ⟨1/10, 9/20, 1/36, #v[14620889/1000000000, 2754909/250000000, 110684611/10000000000]⟩
abbrev vcCutP598Roots := vcOuterP598Roots
theorem vcCutP598_roots : vcCutP598.cell.rootsOK vcCutP598Roots = true := by decide +kernel

def vcCutP599 : SideCornerEntry := ⟨1/10, 9/20, 1/18, #v[14620889/1000000000, 2754909/250000000, 110684611/10000000000]⟩
abbrev vcCutP599Roots := vcOuterP599Roots
theorem vcCutP599_roots : vcCutP599.cell.rootsOK vcCutP599Roots = true := by decide +kernel

def vcCutP600 : SideCornerEntry := ⟨1/10, 19/40, 0, #v[25401917/2000000000, 22891161/2500000000, 93242191/10000000000]⟩
abbrev vcCutP600Roots := vcOuterP600Roots
theorem vcCutP600_roots : vcCutP600.cell.rootsOK vcCutP600Roots = true := by decide +kernel

def vcCutP601 : SideCornerEntry := ⟨1/10, 19/40, 1/36, #v[133284271/10000000000, 47834919/5000000000, 24453891/2500000000]⟩
abbrev vcCutP601Roots := vcOuterP601Roots
theorem vcCutP601_roots : vcCutP601.cell.rootsOK vcCutP601Roots = true := by decide +kernel

def vcCutP602 : SideCornerEntry := ⟨1/10, 19/40, 1/18, #v[133284271/10000000000, 47834919/5000000000, 24453891/2500000000]⟩
abbrev vcCutP602Roots := vcOuterP602Roots
theorem vcCutP602_roots : vcCutP602.cell.rootsOK vcCutP602Roots = true := by decide +kernel

def vcCutP603 : SideCornerEntry := ⟨9/80, 1/10, 1/36, #v[52157707/2000000000, 262723843/10000000000, 62403219/5000000000]⟩
abbrev vcCutP603Roots := vcOuterP603Roots
theorem vcCutP603_roots : vcCutP603.cell.rootsOK vcCutP603Roots = true := by decide +kernel

def vcCutP604 : SideCornerEntry := ⟨9/80, 1/10, 1/24, #v[268868589/10000000000, 135442859/5000000000, 63949469/5000000000]⟩
abbrev vcCutP604Roots := vcOuterP604Roots
theorem vcCutP604_roots : vcCutP604.cell.rootsOK vcCutP604Roots = true := by decide +kernel

def vcCutP605 : SideCornerEntry := ⟨9/80, 1/10, 1/18, #v[268868589/10000000000, 135442859/5000000000, 63949469/5000000000]⟩
abbrev vcCutP605Roots := vcOuterP605Roots
theorem vcCutP605_roots : vcCutP605.cell.rootsOK vcCutP605Roots = true := by decide +kernel

def vcCutP606 : SideCornerEntry := ⟨9/80, 9/80, 1/36, #v[20805553/625000000, 328613921/10000000000, 176453159/10000000000]⟩
abbrev vcCutP606Roots := vcOuterP606Roots
theorem vcCutP606_roots : vcCutP606.cell.rootsOK vcCutP606Roots = true := by decide +kernel

def vcCutP607 : SideCornerEntry := ⟨9/80, 9/80, 1/24, #v[171754339/5000000000, 339200307/10000000000, 36196617/2000000000]⟩
abbrev vcCutP607Roots := vcOuterP607Roots
theorem vcCutP607_roots : vcCutP607.cell.rootsOK vcCutP607Roots = true := by decide +kernel

def vcCutPoints576 : Array SideCornerEntry := #[
  vcCutP576,
  vcCutP577,
  vcCutP578,
  vcCutP579,
  vcCutP580,
  vcCutP581,
  vcCutP582,
  vcCutP583,
  vcCutP584,
  vcCutP585,
  vcCutP586,
  vcCutP587,
  vcCutP588,
  vcCutP589,
  vcCutP590,
  vcCutP591,
  vcCutP592,
  vcCutP593,
  vcCutP594,
  vcCutP595,
  vcCutP596,
  vcCutP597,
  vcCutP598,
  vcCutP599,
  vcCutP600,
  vcCutP601,
  vcCutP602,
  vcCutP603,
  vcCutP604,
  vcCutP605,
  vcCutP606,
  vcCutP607]

end HlawkaSchatten.BelowExponent.Vertex
