/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.VcCornerData.Points096

/-! Checked corner data shared by the vertex middle and band regions: `Points096`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

def vcCutP096 : SideCornerEntry := ⟨1/40, 2/5, 1/40, #v[3528339/1250000000, 10404613/5000000000, 3643897/2500000000]⟩
abbrev vcCutP096Roots := vcOuterP096Roots
theorem vcCutP096_roots : vcCutP096.cell.rootsOK vcCutP096Roots = true := by decide +kernel

def vcCutP097 : SideCornerEntry := ⟨1/40, 2/5, 1/20, #v[14216163/5000000000, 20843831/10000000000, 14456437/10000000000]⟩
abbrev vcCutP097Roots := vcOuterP097Roots
theorem vcCutP097_roots : vcCutP097.cell.rootsOK vcCutP097Roots = true := by decide +kernel

def vcCutP098 : SideCornerEntry := ⟨1/40, 2/5, 3/40, #v[28738737/10000000000, 20995723/10000000000, 14471521/10000000000]⟩
abbrev vcCutP098Roots := vcOuterP098Roots
theorem vcCutP098_roots : vcCutP098.cell.rootsOK vcCutP098Roots = true := by decide +kernel

def vcCutP099 : SideCornerEntry := ⟨1/40, 2/5, 1/10, #v[28738737/10000000000, 20995723/10000000000, 14471521/10000000000]⟩
abbrev vcCutP099Roots := vcOuterP099Roots
theorem vcCutP099_roots : vcCutP099.cell.rootsOK vcCutP099Roots = true := by decide +kernel

def vcCutP100 : SideCornerEntry := ⟨1/40, 33/80, 0, #v[3435267/1250000000, 5003753/2500000000, 731389/500000000]⟩
abbrev vcCutP100Roots := vcOuterP100Roots
theorem vcCutP100_roots : vcCutP100.cell.rootsOK vcCutP100Roots = true := by decide +kernel

def vcCutP101 : SideCornerEntry := ⟨1/40, 33/80, 1/40, #v[27537663/10000000000, 5003753/2500000000, 731389/500000000]⟩
abbrev vcCutP101Roots := vcOuterP101Roots
theorem vcCutP101_roots : vcCutP101.cell.rootsOK vcCutP101Roots = true := by decide +kernel

def vcCutP102 : SideCornerEntry := ⟨1/40, 33/80, 1/20, #v[27716707/10000000000, 10004889/5000000000, 7249947/5000000000]⟩
abbrev vcCutP102Roots := vcOuterP102Roots
theorem vcCutP102_roots : vcCutP102.cell.rootsOK vcCutP102Roots = true := by decide +kernel

def vcCutP103 : SideCornerEntry := ⟨1/40, 33/80, 3/40, #v[27995211/10000000000, 4027899/2000000000, 3622131/2500000000]⟩
abbrev vcCutP103Roots := vcOuterP103Roots
theorem vcCutP103_roots : vcCutP103.cell.rootsOK vcCutP103Roots = true := by decide +kernel

def vcCutP104 : SideCornerEntry := ⟨1/40, 33/80, 1/10, #v[27995211/10000000000, 4027899/2000000000, 3622131/2500000000]⟩
abbrev vcCutP104Roots := vcOuterP104Roots
theorem vcCutP104_roots : vcCutP104.cell.rootsOK vcCutP104Roots = true := by decide +kernel

def vcCutP105 : SideCornerEntry := ⟨1/40, 17/40, 0, #v[26919221/10000000000, 19303833/10000000000, 2943587/2000000000]⟩
abbrev vcCutP105Roots := vcOuterP105Roots
theorem vcCutP105_roots : vcCutP105.cell.rootsOK vcCutP105Roots = true := by decide +kernel

def vcCutP106 : SideCornerEntry := ⟨1/40, 17/40, 1/40, #v[13475661/5000000000, 19303833/10000000000, 2943587/2000000000]⟩
abbrev vcCutP106Roots := vcOuterP106Roots
theorem vcCutP106_roots : vcCutP106.cell.rootsOK vcCutP106Roots = true := by decide +kernel

def vcCutP107 : SideCornerEntry := ⟨1/40, 17/40, 1/20, #v[3388493/1250000000, 19265569/10000000000, 7291409/5000000000]⟩
abbrev vcCutP107Roots := vcOuterP107Roots
theorem vcCutP107_roots : vcCutP107.cell.rootsOK vcCutP107Roots = true := by decide +kernel

def vcCutP108 : SideCornerEntry := ⟨1/40, 17/40, 3/40, #v[13681433/5000000000, 19376543/10000000000, 7280693/5000000000]⟩
abbrev vcCutP108Roots := vcOuterP108Roots
theorem vcCutP108_roots : vcCutP108.cell.rootsOK vcCutP108Roots = true := by decide +kernel

def vcCutP109 : SideCornerEntry := ⟨1/40, 17/40, 1/10, #v[13681433/5000000000, 19376543/10000000000, 7280693/5000000000]⟩
abbrev vcCutP109Roots := vcOuterP109Roots
theorem vcCutP109_roots : vcCutP109.cell.rootsOK vcCutP109Roots = true := by decide +kernel

def vcCutP110 : SideCornerEntry := ⟨1/40, 7/16, 0, #v[26446763/10000000000, 18666809/10000000000, 7422773/5000000000]⟩
abbrev vcCutP110Roots := vcOuterP110Roots
theorem vcCutP110_roots : vcCutP110.cell.rootsOK vcCutP110Roots = true := by decide +kernel

def vcCutP111 : SideCornerEntry := ⟨1/40, 7/16, 1/40, #v[3307423/1250000000, 18666809/10000000000, 7422773/5000000000]⟩
abbrev vcCutP111Roots := vcOuterP111Roots
theorem vcCutP111_roots : vcCutP111.cell.rootsOK vcCutP111Roots = true := by decide +kernel

def vcCutP112 : SideCornerEntry := ⟨1/40, 7/16, 1/20, #v[13298697/5000000000, 3720309/2000000000, 1838121/1250000000]⟩
abbrev vcCutP112Roots := vcOuterP112Roots
theorem vcCutP112_roots : vcCutP112.cell.rootsOK vcCutP112Roots = true := by decide +kernel

def vcCutP113 : SideCornerEntry := ⟨1/40, 7/16, 3/40, #v[26832691/10000000000, 1168551/625000000, 2935239/2000000000]⟩
abbrev vcCutP113Roots := vcOuterP113Roots
theorem vcCutP113_roots : vcCutP113.cell.rootsOK vcCutP113Roots = true := by decide +kernel

def vcCutP114 : SideCornerEntry := ⟨1/40, 7/16, 1/10, #v[26832691/10000000000, 1168551/625000000, 2935239/2000000000]⟩
abbrev vcCutP114Roots := vcOuterP114Roots
theorem vcCutP114_roots : vcCutP114.cell.rootsOK vcCutP114Roots = true := by decide +kernel

def vcCutP115 : SideCornerEntry := ⟨1/40, 9/20, 0, #v[26058491/10000000000, 1809657/1000000000, 3752707/2500000000]⟩
abbrev vcCutP115Roots := vcOuterP115Roots
theorem vcCutP115_roots : vcCutP115.cell.rootsOK vcCutP115Roots = true := by decide +kernel

def vcCutP116 : SideCornerEntry := ⟨1/40, 9/20, 1/40, #v[26058491/10000000000, 1809657/1000000000, 3752707/2500000000]⟩
abbrev vcCutP116Roots := vcOuterP116Roots
theorem vcCutP116_roots : vcCutP116.cell.rootsOK vcCutP116Roots = true := by decide +kernel

def vcCutP117 : SideCornerEntry := ⟨1/40, 9/20, 1/20, #v[26178237/10000000000, 2251211/1250000000, 7433149/5000000000]⟩
abbrev vcCutP117Roots := vcOuterP117Roots
theorem vcCutP117_roots : vcCutP117.cell.rootsOK vcCutP117Roots = true := by decide +kernel

def vcCutP118 : SideCornerEntry := ⟨1/40, 9/20, 3/40, #v[26397577/10000000000, 4522993/2500000000, 927077/625000000]⟩
abbrev vcCutP118Roots := vcOuterP118Roots
theorem vcCutP118_roots : vcCutP118.cell.rootsOK vcCutP118Roots = true := by decide +kernel

def vcCutP119 : SideCornerEntry := ⟨1/40, 9/20, 1/10, #v[26397577/10000000000, 4522993/2500000000, 927077/625000000]⟩
abbrev vcCutP119Roots := vcOuterP119Roots
theorem vcCutP119_roots : vcCutP119.cell.rootsOK vcCutP119Roots = true := by decide +kernel

def vcCutP120 : SideCornerEntry := ⟨1/40, 37/80, 0, #v[643741/250000000, 17587147/10000000000, 15214577/10000000000]⟩
abbrev vcCutP120Roots := vcOuterP120Roots
theorem vcCutP120_roots : vcCutP120.cell.rootsOK vcCutP120Roots = true := by decide +kernel

def vcCutP121 : SideCornerEntry := ⟨1/40, 37/80, 1/40, #v[643741/250000000, 17587147/10000000000, 15214577/10000000000]⟩
abbrev vcCutP121Roots := vcOuterP121Roots
theorem vcCutP121_roots : vcCutP121.cell.rootsOK vcCutP121Roots = true := by decide +kernel

def vcCutP122 : SideCornerEntry := ⟨1/40, 37/80, 1/20, #v[2584531/1000000000, 8744059/5000000000, 7533821/5000000000]⟩
abbrev vcCutP122Roots := vcOuterP122Roots
theorem vcCutP122_roots : vcCutP122.cell.rootsOK vcCutP122Roots = true := by decide +kernel

def vcCutP123 : SideCornerEntry := ⟨1/40, 37/80, 3/40, #v[6513039/2500000000, 17555269/10000000000, 3006689/2000000000]⟩
abbrev vcCutP123Roots := vcOuterP123Roots
theorem vcCutP123_roots : vcCutP123.cell.rootsOK vcCutP123Roots = true := by decide +kernel

def vcCutP124 : SideCornerEntry := ⟨1/40, 37/80, 1/10, #v[6513039/2500000000, 17555269/10000000000, 3006689/2000000000]⟩
abbrev vcCutP124Roots := vcOuterP124Roots
theorem vcCutP124_roots : vcCutP124.cell.rootsOK vcCutP124Roots = true := by decide +kernel

def vcCutP125 : SideCornerEntry := ⟨1/40, 19/40, 0, #v[6379189/2500000000, 4283407/2500000000, 15470979/10000000000]⟩
abbrev vcCutP125Roots := vcOuterP125Roots
theorem vcCutP125_roots : vcCutP125.cell.rootsOK vcCutP125Roots = true := by decide +kernel

def vcCutP126 : SideCornerEntry := ⟨1/40, 19/40, 1/40, #v[6379189/2500000000, 4283407/2500000000, 15470979/10000000000]⟩
abbrev vcCutP126Roots := vcOuterP126Roots
theorem vcCutP126_roots : vcCutP126.cell.rootsOK vcCutP126Roots = true := by decide +kernel

def vcCutP127 : SideCornerEntry := ⟨1/40, 19/40, 1/20, #v[25594883/10000000000, 17029273/10000000000, 7661999/5000000000]⟩
abbrev vcCutP127Roots := vcOuterP127Roots
theorem vcCutP127_roots : vcCutP127.cell.rootsOK vcCutP127Roots = true := by decide +kernel

def vcCutPoints096 : Array SideCornerEntry := #[
  vcCutP096,
  vcCutP097,
  vcCutP098,
  vcCutP099,
  vcCutP100,
  vcCutP101,
  vcCutP102,
  vcCutP103,
  vcCutP104,
  vcCutP105,
  vcCutP106,
  vcCutP107,
  vcCutP108,
  vcCutP109,
  vcCutP110,
  vcCutP111,
  vcCutP112,
  vcCutP113,
  vcCutP114,
  vcCutP115,
  vcCutP116,
  vcCutP117,
  vcCutP118,
  vcCutP119,
  vcCutP120,
  vcCutP121,
  vcCutP122,
  vcCutP123,
  vcCutP124,
  vcCutP125,
  vcCutP126,
  vcCutP127]

end HlawkaSchatten.BelowExponent.Vertex
