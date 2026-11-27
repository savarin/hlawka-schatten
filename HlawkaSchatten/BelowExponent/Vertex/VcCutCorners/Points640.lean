/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.VcCornerData.Points640

/-! Checked corner data shared by the vertex middle and band regions: `Points640`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

def vcCutP640 : SideCornerEntry := ⟨1/8, 1/5, 1/36, #v[58320017/1250000000, 219016339/5000000000, 315127711/10000000000]⟩
abbrev vcCutP640Roots := vcOuterP640Roots
theorem vcCutP640_roots : vcCutP640.cell.rootsOK vcCutP640Roots = true := by decide +kernel

def vcCutP641 : SideCornerEntry := ⟨1/8, 1/5, 1/18, #v[58320017/1250000000, 219016339/5000000000, 315127711/10000000000]⟩
abbrev vcCutP641Roots := vcOuterP641Roots
theorem vcCutP641_roots : vcCutP641.cell.rootsOK vcCutP641Roots = true := by decide +kernel

def vcCutP642 : SideCornerEntry := ⟨1/8, 9/40, 0, #v[43756697/1000000000, 51388469/1250000000, 9309799/312500000]⟩
abbrev vcCutP642Roots := vcOuterP642Roots
theorem vcCutP642_roots : vcCutP642.cell.rootsOK vcCutP642Roots = true := by decide +kernel

def vcCutP643 : SideCornerEntry := ⟨1/8, 9/40, 1/36, #v[58320017/1250000000, 219016339/5000000000, 315127711/10000000000]⟩
abbrev vcCutP643Roots := vcOuterP643Roots
theorem vcCutP643_roots : vcCutP643.cell.rootsOK vcCutP643Roots = true := by decide +kernel

def vcCutP644 : SideCornerEntry := ⟨1/8, 9/40, 1/18, #v[58320017/1250000000, 219016339/5000000000, 315127711/10000000000]⟩
abbrev vcCutP644Roots := vcOuterP644Roots
theorem vcCutP644_roots : vcCutP644.cell.rootsOK vcCutP644Roots = true := by decide +kernel

def vcCutP645 : SideCornerEntry := ⟨1/8, 1/4, 0, #v[159950839/5000000000, 295330527/10000000000, 110860937/5000000000]⟩
abbrev vcCutP645Roots := vcOuterP645Roots
theorem vcCutP645_roots : vcCutP645.cell.rootsOK vcCutP645Roots = true := by decide +kernel

def vcCutP646 : SideCornerEntry := ⟨1/8, 1/4, 1/36, #v[68099719/2000000000, 156985097/5000000000, 117208971/5000000000]⟩
abbrev vcCutP646Roots := vcOuterP646Roots
theorem vcCutP646_roots : vcCutP646.cell.rootsOK vcCutP646Roots = true := by decide +kernel

def vcCutP647 : SideCornerEntry := ⟨1/8, 1/4, 1/18, #v[68099719/2000000000, 156985097/5000000000, 117208971/5000000000]⟩
abbrev vcCutP647Roots := vcOuterP647Roots
theorem vcCutP647_roots : vcCutP647.cell.rootsOK vcCutP647Roots = true := by decide +kernel

def vcCutP648 : SideCornerEntry := ⟨1/8, 11/40, 0, #v[50181147/2000000000, 227081101/10000000000, 88199271/5000000000]⟩
abbrev vcCutP648Roots := vcOuterP648Roots
theorem vcCutP648_roots : vcCutP648.cell.rootsOK vcCutP648Roots = true := by decide +kernel

def vcCutP649 : SideCornerEntry := ⟨1/8, 11/40, 1/36, #v[133275469/5000000000, 240871397/10000000000, 93183599/5000000000]⟩
abbrev vcCutP649Roots := vcOuterP649Roots
theorem vcCutP649_roots : vcCutP649.cell.rootsOK vcCutP649Roots = true := by decide +kernel

def vcCutP650 : SideCornerEntry := ⟨1/8, 11/40, 1/18, #v[133275469/5000000000, 240871397/10000000000, 93183599/5000000000]⟩
abbrev vcCutP650Roots := vcOuterP650Roots
theorem vcCutP650_roots : vcCutP650.cell.rootsOK vcCutP650Roots = true := by decide +kernel

def vcCutP651 : SideCornerEntry := ⟨1/8, 3/10, 0, #v[208356533/10000000000, 184582153/10000000000, 74194087/5000000000]⟩
abbrev vcCutP651Roots := vcOuterP651Roots
theorem vcCutP651_roots : vcCutP651.cell.rootsOK vcCutP651Roots = true := by decide +kernel

def vcCutP652 : SideCornerEntry := ⟨1/8, 3/10, 1/36, #v[2761731/125000000, 9768453/500000000, 78328729/5000000000]⟩
abbrev vcCutP652Roots := vcOuterP652Roots
theorem vcCutP652_roots : vcCutP652.cell.rootsOK vcCutP652Roots = true := by decide +kernel

def vcCutP653 : SideCornerEntry := ⟨1/8, 3/10, 1/18, #v[2761731/125000000, 9768453/500000000, 78328729/5000000000]⟩
abbrev vcCutP653Roots := vcOuterP653Roots
theorem vcCutP653_roots : vcCutP653.cell.rootsOK vcCutP653Roots = true := by decide +kernel

def vcCutP654 : SideCornerEntry := ⟨1/8, 13/40, 0, #v[181729689/10000000000, 31488407/2000000000, 32801103/2500000000]⟩
abbrev vcCutP654Roots := vcOuterP654Roots
theorem vcCutP654_roots : vcCutP654.cell.rootsOK vcCutP654Roots = true := by decide +kernel

def vcCutP655 : SideCornerEntry := ⟨1/8, 13/40, 1/36, #v[7699127/400000000, 5198131/312500000, 69284171/5000000000]⟩
abbrev vcCutP655Roots := vcOuterP655Roots
theorem vcCutP655_roots : vcCutP655.cell.rootsOK vcCutP655Roots = true := by decide +kernel

def vcCutP656 : SideCornerEntry := ⟨1/8, 13/40, 1/18, #v[7699127/400000000, 5198131/312500000, 69284171/5000000000]⟩
abbrev vcCutP656Roots := vcOuterP656Roots
theorem vcCutP656_roots : vcCutP656.cell.rootsOK vcCutP656Roots = true := by decide +kernel

def vcCutP657 : SideCornerEntry := ⟨1/8, 7/20, 0, #v[165430633/10000000000, 3499843/250000000, 60652213/5000000000]⟩
abbrev vcCutP657Roots := vcOuterP657Roots
theorem vcCutP657_roots : vcCutP657.cell.rootsOK vcCutP657Roots = true := by decide +kernel

def vcCutP658 : SideCornerEntry := ⟨1/8, 7/20, 1/36, #v[87529517/5000000000, 147695759/10000000000, 128148237/10000000000]⟩
abbrev vcCutP658Roots := vcOuterP658Roots
theorem vcCutP658_roots : vcCutP658.cell.rootsOK vcCutP658Roots = true := by decide +kernel

def vcCutP659 : SideCornerEntry := ⟨1/8, 7/20, 1/18, #v[87529517/5000000000, 147695759/10000000000, 128148237/10000000000]⟩
abbrev vcCutP659Roots := vcOuterP659Roots
theorem vcCutP659_roots : vcCutP659.cell.rootsOK vcCutP659Roots = true := by decide +kernel

def vcCutP660 : SideCornerEntry := ⟨1/8, 3/8, 0, #v[39110513/2500000000, 129284267/10000000000, 58381007/5000000000]⟩
abbrev vcCutP660Roots := vcOuterP660Roots
theorem vcCutP660_roots : vcCutP660.cell.rootsOK vcCutP660Roots = true := by decide +kernel

def vcCutP661 : SideCornerEntry := ⟨1/8, 3/8, 1/36, #v[2584901/156250000, 68131563/5000000000, 123341463/10000000000]⟩
abbrev vcCutP661Roots := vcOuterP661Roots
theorem vcCutP661_roots : vcCutP661.cell.rootsOK vcCutP661Roots = true := by decide +kernel

def vcCutP662 : SideCornerEntry := ⟨1/8, 3/8, 1/18, #v[2584901/156250000, 68131563/5000000000, 123341463/10000000000]⟩
abbrev vcCutP662Roots := vcOuterP662Roots
theorem vcCutP662_roots : vcCutP662.cell.rootsOK vcCutP662Roots = true := by decide +kernel

def vcCutP663 : SideCornerEntry := ⟨1/8, 2/5, 0, #v[155025257/10000000000, 15438421/1250000000, 120943741/10000000000]⟩
abbrev vcCutP663Roots := vcOuterP663Roots
theorem vcCutP663_roots : vcCutP663.cell.rootsOK vcCutP663Roots = true := by decide +kernel

def vcCutP664 : SideCornerEntry := ⟨1/8, 2/5, 1/36, #v[40993743/2500000000, 65054243/5000000000, 127881117/10000000000]⟩
abbrev vcCutP664Roots := vcOuterP664Roots
theorem vcCutP664_roots : vcCutP664.cell.rootsOK vcCutP664Roots = true := by decide +kernel

def vcCutP665 : SideCornerEntry := ⟨1/8, 2/5, 1/18, #v[40993743/2500000000, 65054243/5000000000, 127881117/10000000000]⟩
abbrev vcCutP665Roots := vcOuterP665Roots
theorem vcCutP665_roots : vcCutP665.cell.rootsOK vcCutP665Roots = true := by decide +kernel

def vcCutP666 : SideCornerEntry := ⟨1/8, 17/40, 0, #v[20305099/1250000000, 25087721/2000000000, 16282769/1250000000]⟩
abbrev vcCutP666Roots := vcOuterP666Roots
theorem vcCutP666_roots : vcCutP666.cell.rootsOK vcCutP666Roots = true := by decide +kernel

def vcCutP667 : SideCornerEntry := ⟨1/8, 17/40, 1/36, #v[171977467/10000000000, 33058573/2500000000, 68939599/5000000000]⟩
abbrev vcCutP667Roots := vcOuterP667Roots
theorem vcCutP667_roots : vcCutP667.cell.rootsOK vcCutP667Roots = true := by decide +kernel

def vcCutP668 : SideCornerEntry := ⟨1/8, 17/40, 1/18, #v[171977467/10000000000, 33058573/2500000000, 68939599/5000000000]⟩
abbrev vcCutP668Roots := vcOuterP668Roots
theorem vcCutP668_roots : vcCutP668.cell.rootsOK vcCutP668Roots = true := by decide +kernel

def vcCutP669 : SideCornerEntry := ⟨1/8, 9/20, 0, #v[20305099/1250000000, 25087721/2000000000, 16282769/1250000000]⟩
abbrev vcCutP669Roots := vcOuterP669Roots
theorem vcCutP669_roots : vcCutP669.cell.rootsOK vcCutP669Roots = true := by decide +kernel

def vcCutP670 : SideCornerEntry := ⟨1/8, 9/20, 1/36, #v[171977467/10000000000, 33058573/2500000000, 68939599/5000000000]⟩
abbrev vcCutP670Roots := vcOuterP670Roots
theorem vcCutP670_roots : vcCutP670.cell.rootsOK vcCutP670Roots = true := by decide +kernel

def vcCutP671 : SideCornerEntry := ⟨1/8, 9/20, 1/18, #v[171977467/10000000000, 33058573/2500000000, 68939599/5000000000]⟩
abbrev vcCutP671Roots := vcOuterP671Roots
theorem vcCutP671_roots : vcCutP671.cell.rootsOK vcCutP671Roots = true := by decide +kernel

def vcCutPoints640 : Array SideCornerEntry := #[
  vcCutP640,
  vcCutP641,
  vcCutP642,
  vcCutP643,
  vcCutP644,
  vcCutP645,
  vcCutP646,
  vcCutP647,
  vcCutP648,
  vcCutP649,
  vcCutP650,
  vcCutP651,
  vcCutP652,
  vcCutP653,
  vcCutP654,
  vcCutP655,
  vcCutP656,
  vcCutP657,
  vcCutP658,
  vcCutP659,
  vcCutP660,
  vcCutP661,
  vcCutP662,
  vcCutP663,
  vcCutP664,
  vcCutP665,
  vcCutP666,
  vcCutP667,
  vcCutP668,
  vcCutP669,
  vcCutP670,
  vcCutP671]

end HlawkaSchatten.BelowExponent.Vertex
