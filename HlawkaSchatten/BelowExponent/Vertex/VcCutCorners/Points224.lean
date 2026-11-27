/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.VcCornerData.Points224

/-! Checked corner data shared by the vertex middle and band regions: `Points224`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

def vcCutP224 : SideCornerEntry := ⟨3/80, 29/80, 1/10, #v[31759927/10000000000, 24251983/10000000000, 299691/200000000]⟩
abbrev vcCutP224Roots := vcOuterP224Roots
theorem vcCutP224_roots : vcCutP224.cell.rootsOK vcCutP224Roots = true := by decide +kernel

def vcCutP225 : SideCornerEntry := ⟨3/80, 3/8, 0, #v[3725299/1250000000, 1134471/500000000, 7397123/5000000000]⟩
abbrev vcCutP225Roots := vcOuterP225Roots
theorem vcCutP225_roots : vcCutP225.cell.rootsOK vcCutP225Roots = true := by decide +kernel

def vcCutP226 : SideCornerEntry := ⟨3/80, 3/8, 1/40, #v[29955921/10000000000, 44347/19531250, 7397123/5000000000]⟩
abbrev vcCutP226Roots := vcOuterP226Roots
theorem vcCutP226_roots : vcCutP226.cell.rootsOK vcCutP226Roots = true := by decide +kernel

def vcCutP227 : SideCornerEntry := ⟨3/80, 3/8, 1/20, #v[18893/6250000, 22827883/10000000000, 2949589/2000000000]⟩
abbrev vcCutP227Roots := vcOuterP227Roots
theorem vcCutP227_roots : vcCutP227.cell.rootsOK vcCutP227Roots = true := by decide +kernel

def vcCutP228 : SideCornerEntry := ⟨3/80, 3/8, 3/40, #v[30605847/10000000000, 1439769/625000000, 14830061/10000000000]⟩
abbrev vcCutP228Roots := vcOuterP228Roots
theorem vcCutP228_roots : vcCutP228.cell.rootsOK vcCutP228Roots = true := by decide +kernel

def vcCutP229 : SideCornerEntry := ⟨3/80, 3/8, 1/10, #v[30605847/10000000000, 1439769/625000000, 14830061/10000000000]⟩
abbrev vcCutP229Roots := vcOuterP229Roots
theorem vcCutP229_roots : vcCutP229.cell.rootsOK vcCutP229Roots = true := by decide +kernel

def vcCutP230 : SideCornerEntry := ⟨3/80, 31/80, 0, #v[28912843/10000000000, 21696529/10000000000, 14731333/10000000000]⟩
abbrev vcCutP230Roots := vcOuterP230Roots
theorem vcCutP230_roots : vcCutP230.cell.rootsOK vcCutP230Roots = true := by decide +kernel

def vcCutP231 : SideCornerEntry := ⟨3/80, 31/80, 1/40, #v[29028589/10000000000, 21696529/10000000000, 14731333/10000000000]⟩
abbrev vcCutP231Roots := vcOuterP231Roots
theorem vcCutP231_roots : vcCutP231.cell.rootsOK vcCutP231Roots = true := by decide +kernel

def vcCutP232 : SideCornerEntry := ⟨3/80, 31/80, 1/20, #v[914541/312500000, 10889331/5000000000, 14659879/10000000000]⟩
abbrev vcCutP232Roots := vcOuterP232Roots
theorem vcCutP232_roots : vcCutP232.cell.rootsOK vcCutP232Roots = true := by decide +kernel

def vcCutP233 : SideCornerEntry := ⟨3/80, 31/80, 3/40, #v[14802193/5000000000, 5489151/2500000000, 3682807/2500000000]⟩
abbrev vcCutP233Roots := vcOuterP233Roots
theorem vcCutP233_roots : vcCutP233.cell.rootsOK vcCutP233Roots = true := by decide +kernel

def vcCutP234 : SideCornerEntry := ⟨3/80, 31/80, 1/10, #v[14802193/5000000000, 5489151/2500000000, 3682807/2500000000]⟩
abbrev vcCutP234Roots := vcOuterP234Roots
theorem vcCutP234_roots : vcCutP234.cell.rootsOK vcCutP234Roots = true := by decide +kernel

def vcCutP235 : SideCornerEntry := ⟨3/80, 2/5, 0, #v[28143447/10000000000, 10404613/5000000000, 3685233/2500000000]⟩
abbrev vcCutP235Roots := vcOuterP235Roots
theorem vcCutP235_roots : vcCutP235.cell.rootsOK vcCutP235Roots = true := by decide +kernel

def vcCutP236 : SideCornerEntry := ⟨3/80, 2/5, 1/40, #v[3528339/1250000000, 10404613/5000000000, 3685233/2500000000]⟩
abbrev vcCutP236Roots := vcOuterP236Roots
theorem vcCutP236_roots : vcCutP236.cell.rootsOK vcCutP236Roots = true := by decide +kernel

def vcCutP237 : SideCornerEntry := ⟨3/80, 2/5, 1/20, #v[14216163/5000000000, 20843831/10000000000, 14643567/10000000000]⟩
abbrev vcCutP237Roots := vcOuterP237Roots
theorem vcCutP237_roots : vcCutP237.cell.rootsOK vcCutP237Roots = true := by decide +kernel

def vcCutP238 : SideCornerEntry := ⟨3/80, 2/5, 3/40, #v[28738737/10000000000, 20995723/10000000000, 3671539/2500000000]⟩
abbrev vcCutP238Roots := vcOuterP238Roots
theorem vcCutP238_roots : vcCutP238.cell.rootsOK vcCutP238Roots = true := by decide +kernel

def vcCutP239 : SideCornerEntry := ⟨3/80, 2/5, 1/10, #v[28738737/10000000000, 20995723/10000000000, 3671539/2500000000]⟩
abbrev vcCutP239Roots := vcOuterP239Roots
theorem vcCutP239_roots : vcCutP239.cell.rootsOK vcCutP239Roots = true := by decide +kernel

def vcCutP240 : SideCornerEntry := ⟨3/80, 33/80, 0, #v[3435267/1250000000, 5003753/2500000000, 14809373/10000000000]⟩
abbrev vcCutP240Roots := vcOuterP240Roots
theorem vcCutP240_roots : vcCutP240.cell.rootsOK vcCutP240Roots = true := by decide +kernel

def vcCutP241 : SideCornerEntry := ⟨3/80, 33/80, 1/40, #v[27537663/10000000000, 5003753/2500000000, 14809373/10000000000]⟩
abbrev vcCutP241Roots := vcOuterP241Roots
theorem vcCutP241_roots : vcCutP241.cell.rootsOK vcCutP241Roots = true := by decide +kernel

def vcCutP242 : SideCornerEntry := ⟨3/80, 33/80, 1/20, #v[27716707/10000000000, 10004889/5000000000, 7352143/5000000000]⟩
abbrev vcCutP242Roots := vcOuterP242Roots
theorem vcCutP242_roots : vcCutP242.cell.rootsOK vcCutP242Roots = true := by decide +kernel

def vcCutP243 : SideCornerEntry := ⟨3/80, 33/80, 3/40, #v[27995211/10000000000, 4027899/2000000000, 736769/500000000]⟩
abbrev vcCutP243Roots := vcOuterP243Roots
theorem vcCutP243_roots : vcCutP243.cell.rootsOK vcCutP243Roots = true := by decide +kernel

def vcCutP244 : SideCornerEntry := ⟨3/80, 33/80, 1/10, #v[27995211/10000000000, 4027899/2000000000, 736769/500000000]⟩
abbrev vcCutP244Roots := vcOuterP244Roots
theorem vcCutP244_roots : vcCutP244.cell.rootsOK vcCutP244Roots = true := by decide +kernel

def vcCutP245 : SideCornerEntry := ⟨3/80, 17/40, 0, #v[26919221/10000000000, 19303833/10000000000, 14919453/10000000000]⟩
abbrev vcCutP245Roots := vcOuterP245Roots
theorem vcCutP245_roots : vcCutP245.cell.rootsOK vcCutP245Roots = true := by decide +kernel

def vcCutP246 : SideCornerEntry := ⟨3/80, 17/40, 1/40, #v[13475661/5000000000, 19303833/10000000000, 14919453/10000000000]⟩
abbrev vcCutP246Roots := vcOuterP246Roots
theorem vcCutP246_roots : vcCutP246.cell.rootsOK vcCutP246Roots = true := by decide +kernel

def vcCutP247 : SideCornerEntry := ⟨3/80, 17/40, 1/20, #v[3388493/1250000000, 19265569/10000000000, 7404217/5000000000]⟩
abbrev vcCutP247Roots := vcOuterP247Roots
theorem vcCutP247_roots : vcCutP247.cell.rootsOK vcCutP247Roots = true := by decide +kernel

def vcCutP248 : SideCornerEntry := ⟨3/80, 17/40, 3/40, #v[13681433/5000000000, 19376543/10000000000, 14831637/10000000000]⟩
abbrev vcCutP248Roots := vcOuterP248Roots
theorem vcCutP248_roots : vcCutP248.cell.rootsOK vcCutP248Roots = true := by decide +kernel

def vcCutP249 : SideCornerEntry := ⟨3/80, 17/40, 1/10, #v[13681433/5000000000, 19376543/10000000000, 14831637/10000000000]⟩
abbrev vcCutP249Roots := vcOuterP249Roots
theorem vcCutP249_roots : vcCutP249.cell.rootsOK vcCutP249Roots = true := by decide +kernel

def vcCutP250 : SideCornerEntry := ⟨3/80, 7/16, 0, #v[26446763/10000000000, 18666809/10000000000, 15070817/10000000000]⟩
abbrev vcCutP250Roots := vcOuterP250Roots
theorem vcCutP250_roots : vcCutP250.cell.rootsOK vcCutP250Roots = true := by decide +kernel

def vcCutP251 : SideCornerEntry := ⟨3/80, 7/16, 1/40, #v[3307423/1250000000, 18666809/10000000000, 15070817/10000000000]⟩
abbrev vcCutP251Roots := vcOuterP251Roots
theorem vcCutP251_roots : vcCutP251.cell.rootsOK vcCutP251Roots = true := by decide +kernel

def vcCutP252 : SideCornerEntry := ⟨3/80, 7/16, 1/20, #v[13298697/5000000000, 3720309/2000000000, 3738913/2500000000]⟩
abbrev vcCutP252Roots := vcOuterP252Roots
theorem vcCutP252_roots : vcCutP252.cell.rootsOK vcCutP252Roots = true := by decide +kernel

def vcCutP253 : SideCornerEntry := ⟨3/80, 7/16, 3/40, #v[26832691/10000000000, 1168551/625000000, 7487281/5000000000]⟩
abbrev vcCutP253Roots := vcOuterP253Roots
theorem vcCutP253_roots : vcCutP253.cell.rootsOK vcCutP253Roots = true := by decide +kernel

def vcCutP254 : SideCornerEntry := ⟨3/80, 7/16, 1/10, #v[26832691/10000000000, 1168551/625000000, 7487281/5000000000]⟩
abbrev vcCutP254Roots := vcOuterP254Roots
theorem vcCutP254_roots : vcCutP254.cell.rootsOK vcCutP254Roots = true := by decide +kernel

def vcCutP255 : SideCornerEntry := ⟨3/80, 9/20, 0, #v[26058491/10000000000, 1809657/1000000000, 610549/400000000]⟩
abbrev vcCutP255Roots := vcOuterP255Roots
theorem vcCutP255_roots : vcCutP255.cell.rootsOK vcCutP255Roots = true := by decide +kernel

def vcCutPoints224 : Array SideCornerEntry := #[
  vcCutP224,
  vcCutP225,
  vcCutP226,
  vcCutP227,
  vcCutP228,
  vcCutP229,
  vcCutP230,
  vcCutP231,
  vcCutP232,
  vcCutP233,
  vcCutP234,
  vcCutP235,
  vcCutP236,
  vcCutP237,
  vcCutP238,
  vcCutP239,
  vcCutP240,
  vcCutP241,
  vcCutP242,
  vcCutP243,
  vcCutP244,
  vcCutP245,
  vcCutP246,
  vcCutP247,
  vcCutP248,
  vcCutP249,
  vcCutP250,
  vcCutP251,
  vcCutP252,
  vcCutP253,
  vcCutP254,
  vcCutP255]

end HlawkaSchatten.BelowExponent.Vertex
