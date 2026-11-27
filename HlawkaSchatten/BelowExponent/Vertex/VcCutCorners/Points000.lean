/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.VcCornerData.Points000

/-! Checked corner data shared by the vertex middle and band regions: `Points000`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

def vcCutP000 : SideCornerEntry := ⟨1/40, 13/80, 0, #v[100886543/10000000000, 93293277/10000000000, 8479539/2500000000]⟩
abbrev vcCutP000Roots := vcOuterP000Roots
theorem vcCutP000_roots : vcCutP000.cell.rootsOK vcCutP000Roots = true := by decide +kernel

def vcCutP001 : SideCornerEntry := ⟨1/40, 13/80, 1/40, #v[104366629/10000000000, 96269849/10000000000, 6947903/2000000000]⟩
abbrev vcCutP001Roots := vcOuterP001Roots
theorem vcCutP001_roots : vcCutP001.cell.rootsOK vcCutP001Roots = true := by decide +kernel

def vcCutP002 : SideCornerEntry := ⟨1/40, 13/80, 1/20, #v[13492929/1250000000, 19873087/2000000000, 35616437/10000000000]⟩
abbrev vcCutP002Roots := vcOuterP002Roots
theorem vcCutP002_roots : vcCutP002.cell.rootsOK vcCutP002Roots = true := by decide +kernel

def vcCutP003 : SideCornerEntry := ⟨1/40, 13/80, 3/40, #v[111598613/10000000000, 102559359/10000000000, 9134963/2500000000]⟩
abbrev vcCutP003Roots := vcOuterP003Roots
theorem vcCutP003_roots : vcCutP003.cell.rootsOK vcCutP003Roots = true := by decide +kernel

def vcCutP004 : SideCornerEntry := ⟨1/40, 13/80, 1/10, #v[111598613/10000000000, 102559359/10000000000, 9134963/2500000000]⟩
abbrev vcCutP004Roots := vcOuterP004Roots
theorem vcCutP004_roots : vcCutP004.cell.rootsOK vcCutP004Roots = true := by decide +kernel

def vcCutP005 : SideCornerEntry := ⟨1/40, 7/40, 0, #v[100886543/10000000000, 93293277/10000000000, 8479539/2500000000]⟩
abbrev vcCutP005Roots := vcOuterP005Roots
theorem vcCutP005_roots : vcCutP005.cell.rootsOK vcCutP005Roots = true := by decide +kernel

def vcCutP006 : SideCornerEntry := ⟨1/40, 7/40, 1/40, #v[104366629/10000000000, 96269849/10000000000, 6947903/2000000000]⟩
abbrev vcCutP006Roots := vcOuterP006Roots
theorem vcCutP006_roots : vcCutP006.cell.rootsOK vcCutP006Roots = true := by decide +kernel

def vcCutP007 : SideCornerEntry := ⟨1/40, 7/40, 1/20, #v[13492929/1250000000, 19873087/2000000000, 35616437/10000000000]⟩
abbrev vcCutP007Roots := vcOuterP007Roots
theorem vcCutP007_roots : vcCutP007.cell.rootsOK vcCutP007Roots = true := by decide +kernel

def vcCutP008 : SideCornerEntry := ⟨1/40, 7/40, 3/40, #v[111598613/10000000000, 102559359/10000000000, 9134963/2500000000]⟩
abbrev vcCutP008Roots := vcOuterP008Roots
theorem vcCutP008_roots : vcCutP008.cell.rootsOK vcCutP008Roots = true := by decide +kernel

def vcCutP009 : SideCornerEntry := ⟨1/40, 7/40, 1/10, #v[111598613/10000000000, 102559359/10000000000, 9134963/2500000000]⟩
abbrev vcCutP009Roots := vcOuterP009Roots
theorem vcCutP009_roots : vcCutP009.cell.rootsOK vcCutP009Roots = true := by decide +kernel

def vcCutP010 : SideCornerEntry := ⟨1/40, 3/16, 0, #v[8742853/1000000000, 15983261/2000000000, 29899073/10000000000]⟩
abbrev vcCutP010Roots := vcOuterP010Roots
theorem vcCutP010_roots : vcCutP010.cell.rootsOK vcCutP010Roots = true := by decide +kernel

def vcCutP011 : SideCornerEntry := ⟨1/40, 3/16, 1/40, #v[90234051/10000000000, 16453699/2000000000, 30553659/10000000000]⟩
abbrev vcCutP011Roots := vcOuterP011Roots
theorem vcCutP011_roots : vcCutP011.cell.rootsOK vcCutP011Roots = true := by decide +kernel

def vcCutP012 : SideCornerEntry := ⟨1/40, 3/16, 1/20, #v[46580803/5000000000, 84756191/10000000000, 3908787/1250000000]⟩
abbrev vcCutP012Roots := vcOuterP012Roots
theorem vcCutP012_roots : vcCutP012.cell.rootsOK vcCutP012Roots = true := by decide +kernel

def vcCutP013 : SideCornerEntry := ⟨1/40, 3/16, 3/40, #v[96171363/10000000000, 10917603/1250000000, 4004149/1250000000]⟩
abbrev vcCutP013Roots := vcOuterP013Roots
theorem vcCutP013_roots : vcCutP013.cell.rootsOK vcCutP013Roots = true := by decide +kernel

def vcCutP014 : SideCornerEntry := ⟨1/40, 3/16, 1/10, #v[96171363/10000000000, 10917603/1250000000, 4004149/1250000000]⟩
abbrev vcCutP014Roots := vcOuterP014Roots
theorem vcCutP014_roots : vcCutP014.cell.rootsOK vcCutP014Roots = true := by decide +kernel

def vcCutP015 : SideCornerEntry := ⟨1/40, 1/5, 0, #v[76881061/10000000000, 34740741/5000000000, 6697009/2500000000]⟩
abbrev vcCutP015Roots := vcOuterP015Roots
theorem vcCutP015_roots : vcCutP015.cell.rootsOK vcCutP015Roots = true := by decide +kernel

def vcCutP016 : SideCornerEntry := ⟨1/40, 1/5, 1/40, #v[39588287/5000000000, 35679767/5000000000, 6827983/2500000000]⟩
abbrev vcCutP016Roots := vcOuterP016Roots
theorem vcCutP016_roots : vcCutP016.cell.rootsOK vcCutP016Roots = true := by decide +kernel

def vcCutP017 : SideCornerEntry := ⟨1/40, 1/5, 1/20, #v[40791299/5000000000, 7336313/1000000000, 348703/125000000]⟩
abbrev vcCutP017Roots := vcOuterP017Roots
theorem vcCutP017_roots : vcCutP017.cell.rootsOK vcCutP017Roots = true := by decide +kernel

def vcCutP018 : SideCornerEntry := ⟨1/40, 1/5, 3/40, #v[3363483/400000000, 18868529/2500000000, 28531519/10000000000]⟩
abbrev vcCutP018Roots := vcOuterP018Roots
theorem vcCutP018_roots : vcCutP018.cell.rootsOK vcCutP018Roots = true := by decide +kernel

def vcCutP019 : SideCornerEntry := ⟨1/40, 1/5, 1/10, #v[3363483/400000000, 18868529/2500000000, 28531519/10000000000]⟩
abbrev vcCutP019Roots := vcOuterP019Roots
theorem vcCutP019_roots : vcCutP019.cell.rootsOK vcCutP019Roots = true := by decide +kernel

def vcCutP020 : SideCornerEntry := ⟨1/40, 17/80, 0, #v[17112789/2500000000, 61164531/10000000000, 12160947/5000000000]⟩
abbrev vcCutP020Roots := vcOuterP020Roots
theorem vcCutP020_roots : vcCutP020.cell.rootsOK vcCutP020Roots = true := by decide +kernel

def vcCutP021 : SideCornerEntry := ⟨1/40, 17/80, 1/40, #v[35173299/5000000000, 31338661/5000000000, 12370331/5000000000]⟩
abbrev vcCutP021Roots := vcOuterP021Roots
theorem vcCutP021_roots : vcCutP021.cell.rootsOK vcCutP021Roots = true := by decide +kernel

def vcCutP022 : SideCornerEntry := ⟨1/40, 17/80, 1/20, #v[18088719/2500000000, 2009857/312500000, 25221409/10000000000]⟩
abbrev vcCutP022Roots := vcOuterP022Roots
theorem vcCutP022_roots : vcCutP022.cell.rootsOK vcCutP022Roots = true := by decide +kernel

def vcCutP023 : SideCornerEntry := ⟨1/40, 17/80, 3/40, #v[4653431/625000000, 16513633/2500000000, 25752277/10000000000]⟩
abbrev vcCutP023Roots := vcOuterP023Roots
theorem vcCutP023_roots : vcCutP023.cell.rootsOK vcCutP023Roots = true := by decide +kernel

def vcCutP024 : SideCornerEntry := ⟨1/40, 17/80, 1/10, #v[4653431/625000000, 16513633/2500000000, 25752277/10000000000]⟩
abbrev vcCutP024Roots := vcOuterP024Roots
theorem vcCutP024_roots : vcCutP024.cell.rootsOK vcCutP024Roots = true := by decide +kernel

def vcCutP025 : SideCornerEntry := ⟨1/40, 9/40, 0, #v[7700983/1250000000, 27223023/5000000000, 11186287/5000000000]⟩
abbrev vcCutP025Roots := vcOuterP025Roots
theorem vcCutP025_roots : vcCutP025.cell.rootsOK vcCutP025Roots = true := by decide +kernel

def vcCutP026 : SideCornerEntry := ⟨1/40, 9/40, 1/40, #v[63182367/10000000000, 55668487/10000000000, 45407/20000000]⟩
abbrev vcCutP026Roots := vcOuterP026Roots
theorem vcCutP026_roots : vcCutP026.cell.rootsOK vcCutP026Roots = true := by decide +kernel

def vcCutP027 : SideCornerEntry := ⟨1/40, 9/40, 1/20, #v[202723/31250000, 285079/50000000, 5774597/2500000000]⟩
abbrev vcCutP027Roots := vcOuterP027Roots
theorem vcCutP027_roots : vcCutP027.cell.rootsOK vcCutP027Roots = true := by decide +kernel

def vcCutP028 : SideCornerEntry := ⟨1/40, 9/40, 3/40, #v[66653583/10000000000, 29231959/5000000000, 23545093/10000000000]⟩
abbrev vcCutP028Roots := vcOuterP028Roots
theorem vcCutP028_roots : vcCutP028.cell.rootsOK vcCutP028Roots = true := by decide +kernel

def vcCutP029 : SideCornerEntry := ⟨1/40, 9/40, 1/10, #v[66653583/10000000000, 29231959/5000000000, 23545093/10000000000]⟩
abbrev vcCutP029Roots := vcOuterP029Roots
theorem vcCutP029_roots : vcCutP029.cell.rootsOK vcCutP029Roots = true := by decide +kernel

def vcCutP030 : SideCornerEntry := ⟨1/40, 19/80, 0, #v[55979711/10000000000, 61163/12500000, 20797297/10000000000]⟩
abbrev vcCutP030Roots := vcOuterP030Roots
theorem vcCutP030_roots : vcCutP030.cell.rootsOK vcCutP030Roots = true := by decide +kernel

def vcCutP031 : SideCornerEntry := ⟨1/40, 19/80, 1/40, #v[57294893/10000000000, 49920433/10000000000, 2632419/1250000000]⟩
abbrev vcCutP031Roots := vcOuterP031Roots
theorem vcCutP031_roots : vcCutP031.cell.rootsOK vcCutP031Roots = true := by decide +kernel

def vcCutPoints000 : Array SideCornerEntry := #[
  vcCutP000,
  vcCutP001,
  vcCutP002,
  vcCutP003,
  vcCutP004,
  vcCutP005,
  vcCutP006,
  vcCutP007,
  vcCutP008,
  vcCutP009,
  vcCutP010,
  vcCutP011,
  vcCutP012,
  vcCutP013,
  vcCutP014,
  vcCutP015,
  vcCutP016,
  vcCutP017,
  vcCutP018,
  vcCutP019,
  vcCutP020,
  vcCutP021,
  vcCutP022,
  vcCutP023,
  vcCutP024,
  vcCutP025,
  vcCutP026,
  vcCutP027,
  vcCutP028,
  vcCutP029,
  vcCutP030,
  vcCutP031]

end HlawkaSchatten.BelowExponent.Vertex
