/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.VcCornerData.Points128

/-! Checked corner data shared by the vertex middle and band regions: `Points128`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

def vcCutP128 : SideCornerEntry := ⟨1/40, 19/40, 3/40, #v[12896273/5000000000, 8540581/5000000000, 15293437/10000000000]⟩
abbrev vcCutP128Roots := vcOuterP128Roots
theorem vcCutP128_roots : vcCutP128.cell.rootsOK vcCutP128Roots = true := by decide +kernel

def vcCutP129 : SideCornerEntry := ⟨1/40, 19/40, 1/10, #v[12896273/5000000000, 8540581/5000000000, 15293437/10000000000]⟩
abbrev vcCutP129Roots := vcOuterP129Roots
theorem vcCutP129_roots : vcCutP129.cell.rootsOK vcCutP129Roots = true := by decide +kernel

def vcCutP130 : SideCornerEntry := ⟨1/40, 39/80, 0, #v[25362249/10000000000, 16739051/10000000000, 15470979/10000000000]⟩
abbrev vcCutP130Roots := vcOuterP130Roots
theorem vcCutP130_roots : vcCutP130.cell.rootsOK vcCutP130Roots = true := by decide +kernel

def vcCutP131 : SideCornerEntry := ⟨1/40, 39/80, 1/40, #v[25362249/10000000000, 16739051/10000000000, 15470979/10000000000]⟩
abbrev vcCutP131Roots := vcOuterP131Roots
theorem vcCutP131_roots : vcCutP131.cell.rootsOK vcCutP131Roots = true := by decide +kernel

def vcCutP132 : SideCornerEntry := ⟨1/40, 39/80, 1/20, #v[5086037/2000000000, 16631917/10000000000, 7661999/5000000000]⟩
abbrev vcCutP132Roots := vcOuterP132Roots
theorem vcCutP132_roots : vcCutP132.cell.rootsOK vcCutP132Roots = true := by decide +kernel

def vcCutP133 : SideCornerEntry := ⟨1/40, 39/80, 3/40, #v[6405593/2500000000, 8336839/5000000000, 15293437/10000000000]⟩
abbrev vcCutP133Roots := vcOuterP133Roots
theorem vcCutP133_roots : vcCutP133.cell.rootsOK vcCutP133Roots = true := by decide +kernel

def vcCutP134 : SideCornerEntry := ⟨1/40, 39/80, 1/10, #v[6405593/2500000000, 8336839/5000000000, 15293437/10000000000]⟩
abbrev vcCutP134Roots := vcOuterP134Roots
theorem vcCutP134_roots : vcCutP134.cell.rootsOK vcCutP134Roots = true := by decide +kernel

def vcCutP135 : SideCornerEntry := ⟨3/80, 3/20, 0, #v[113923871/10000000000, 13378701/1250000000, 42147873/10000000000]⟩
abbrev vcCutP135Roots := vcOuterP135Roots
theorem vcCutP135_roots : vcCutP135.cell.rootsOK vcCutP135Roots = true := by decide +kernel

def vcCutP136 : SideCornerEntry := ⟨3/80, 3/20, 1/40, #v[29571917/2500000000, 693069/62500000, 10838269/2500000000]⟩
abbrev vcCutP136Roots := vcOuterP136Roots
theorem vcCutP136_roots : vcCutP136.cell.rootsOK vcCutP136Roots = true := by decide +kernel

def vcCutP137 : SideCornerEntry := ⟨3/80, 3/20, 1/20, #v[122735409/10000000000, 28715171/2500000000, 8922097/2000000000]⟩
abbrev vcCutP137Roots := vcOuterP137Roots
theorem vcCutP137_roots : vcCutP137.cell.rootsOK vcCutP137Roots = true := by decide +kernel

def vcCutP138 : SideCornerEntry := ⟨3/80, 3/20, 3/40, #v[7953169/625000000, 5945827/500000000, 45909811/10000000000]⟩
abbrev vcCutP138Roots := vcOuterP138Roots
theorem vcCutP138_roots : vcCutP138.cell.rootsOK vcCutP138Roots = true := by decide +kernel

def vcCutP139 : SideCornerEntry := ⟨3/80, 3/20, 1/10, #v[7953169/625000000, 5945827/500000000, 45909811/10000000000]⟩
abbrev vcCutP139Roots := vcOuterP139Roots
theorem vcCutP139_roots : vcCutP139.cell.rootsOK vcCutP139Roots = true := by decide +kernel

def vcCutP140 : SideCornerEntry := ⟨3/80, 13/80, 0, #v[113923871/10000000000, 13378701/1250000000, 42147873/10000000000]⟩
abbrev vcCutP140Roots := vcOuterP140Roots
theorem vcCutP140_roots : vcCutP140.cell.rootsOK vcCutP140Roots = true := by decide +kernel

def vcCutP141 : SideCornerEntry := ⟨3/80, 13/80, 1/40, #v[29571917/2500000000, 693069/62500000, 10838269/2500000000]⟩
abbrev vcCutP141Roots := vcOuterP141Roots
theorem vcCutP141_roots : vcCutP141.cell.rootsOK vcCutP141Roots = true := by decide +kernel

def vcCutP142 : SideCornerEntry := ⟨3/80, 13/80, 1/20, #v[122735409/10000000000, 28715171/2500000000, 8922097/2000000000]⟩
abbrev vcCutP142Roots := vcOuterP142Roots
theorem vcCutP142_roots : vcCutP142.cell.rootsOK vcCutP142Roots = true := by decide +kernel

def vcCutP143 : SideCornerEntry := ⟨3/80, 13/80, 3/40, #v[7953169/625000000, 5945827/500000000, 45909811/10000000000]⟩
abbrev vcCutP143Roots := vcOuterP143Roots
theorem vcCutP143_roots : vcCutP143.cell.rootsOK vcCutP143Roots = true := by decide +kernel

def vcCutP144 : SideCornerEntry := ⟨3/80, 13/80, 1/10, #v[7953169/625000000, 5945827/500000000, 45909811/10000000000]⟩
abbrev vcCutP144Roots := vcOuterP144Roots
theorem vcCutP144_roots : vcCutP144.cell.rootsOK vcCutP144Roots = true := by decide +kernel

def vcCutP145 : SideCornerEntry := ⟨3/80, 7/40, 0, #v[100886543/10000000000, 93293277/10000000000, 35952343/10000000000]⟩
abbrev vcCutP145Roots := vcOuterP145Roots
theorem vcCutP145_roots : vcCutP145.cell.rootsOK vcCutP145Roots = true := by decide +kernel

def vcCutP146 : SideCornerEntry := ⟨3/80, 7/40, 1/40, #v[104366629/10000000000, 96269849/10000000000, 18451737/5000000000]⟩
abbrev vcCutP146Roots := vcOuterP146Roots
theorem vcCutP146_roots : vcCutP146.cell.rootsOK vcCutP146Roots = true := by decide +kernel

def vcCutP147 : SideCornerEntry := ⟨3/80, 7/40, 1/20, #v[13492929/1250000000, 19873087/2000000000, 18954679/5000000000]⟩
abbrev vcCutP147Roots := vcOuterP147Roots
theorem vcCutP147_roots : vcCutP147.cell.rootsOK vcCutP147Roots = true := by decide +kernel

def vcCutP148 : SideCornerEntry := ⟨3/80, 7/40, 3/40, #v[111598613/10000000000, 102559359/10000000000, 19479739/5000000000]⟩
abbrev vcCutP148Roots := vcOuterP148Roots
theorem vcCutP148_roots : vcCutP148.cell.rootsOK vcCutP148Roots = true := by decide +kernel

def vcCutP149 : SideCornerEntry := ⟨3/80, 7/40, 1/10, #v[111598613/10000000000, 102559359/10000000000, 19479739/5000000000]⟩
abbrev vcCutP149Roots := vcOuterP149Roots
theorem vcCutP149_roots : vcCutP149.cell.rootsOK vcCutP149Roots = true := by decide +kernel

def vcCutP150 : SideCornerEntry := ⟨3/80, 3/16, 0, #v[8742853/1000000000, 15983261/2000000000, 15665821/5000000000]⟩
abbrev vcCutP150Roots := vcOuterP150Roots
theorem vcCutP150_roots : vcCutP150.cell.rootsOK vcCutP150Roots = true := by decide +kernel

def vcCutP151 : SideCornerEntry := ⟨3/80, 3/16, 1/40, #v[90234051/10000000000, 16453699/2000000000, 62667/19531250]⟩
abbrev vcCutP151Roots := vcOuterP151Roots
theorem vcCutP151_roots : vcCutP151.cell.rootsOK vcCutP151Roots = true := by decide +kernel

def vcCutP152 : SideCornerEntry := ⟨3/80, 3/16, 1/20, #v[46580803/5000000000, 84756191/10000000000, 16448211/5000000000]⟩
abbrev vcCutP152Roots := vcOuterP152Roots
theorem vcCutP152_roots : vcCutP152.cell.rootsOK vcCutP152Roots = true := by decide +kernel

def vcCutP153 : SideCornerEntry := ⟨3/80, 3/16, 3/40, #v[96171363/10000000000, 10917603/1250000000, 3375659/1000000000]⟩
abbrev vcCutP153Roots := vcOuterP153Roots
theorem vcCutP153_roots : vcCutP153.cell.rootsOK vcCutP153Roots = true := by decide +kernel

def vcCutP154 : SideCornerEntry := ⟨3/80, 3/16, 1/10, #v[96171363/10000000000, 10917603/1250000000, 3375659/1000000000]⟩
abbrev vcCutP154Roots := vcOuterP154Roots
theorem vcCutP154_roots : vcCutP154.cell.rootsOK vcCutP154Roots = true := by decide +kernel

def vcCutP155 : SideCornerEntry := ⟨3/80, 1/5, 0, #v[76881061/10000000000, 34740741/5000000000, 5559907/2000000000]⟩
abbrev vcCutP155Roots := vcOuterP155Roots
theorem vcCutP155_roots : vcCutP155.cell.rootsOK vcCutP155Roots = true := by decide +kernel

def vcCutP156 : SideCornerEntry := ⟨3/80, 1/5, 1/40, #v[39588287/5000000000, 35679767/5000000000, 7100587/2500000000]⟩
abbrev vcCutP156Roots := vcOuterP156Roots
theorem vcCutP156_roots : vcCutP156.cell.rootsOK vcCutP156Roots = true := by decide +kernel

def vcCutP157 : SideCornerEntry := ⟨3/80, 1/5, 1/20, #v[40791299/5000000000, 7336313/1000000000, 3632979/1250000000]⟩
abbrev vcCutP157Roots := vcOuterP157Roots
theorem vcCutP157_roots : vcCutP157.cell.rootsOK vcCutP157Roots = true := by decide +kernel

def vcCutP158 : SideCornerEntry := ⟨3/80, 1/5, 3/40, #v[3363483/400000000, 18868529/2500000000, 7443201/2500000000]⟩
abbrev vcCutP158Roots := vcOuterP158Roots
theorem vcCutP158_roots : vcCutP158.cell.rootsOK vcCutP158Roots = true := by decide +kernel

def vcCutP159 : SideCornerEntry := ⟨3/80, 1/5, 1/10, #v[3363483/400000000, 18868529/2500000000, 7443201/2500000000]⟩
abbrev vcCutP159Roots := vcOuterP159Roots
theorem vcCutP159_roots : vcCutP159.cell.rootsOK vcCutP159Roots = true := by decide +kernel

def vcCutPoints128 : Array SideCornerEntry := #[
  vcCutP128,
  vcCutP129,
  vcCutP130,
  vcCutP131,
  vcCutP132,
  vcCutP133,
  vcCutP134,
  vcCutP135,
  vcCutP136,
  vcCutP137,
  vcCutP138,
  vcCutP139,
  vcCutP140,
  vcCutP141,
  vcCutP142,
  vcCutP143,
  vcCutP144,
  vcCutP145,
  vcCutP146,
  vcCutP147,
  vcCutP148,
  vcCutP149,
  vcCutP150,
  vcCutP151,
  vcCutP152,
  vcCutP153,
  vcCutP154,
  vcCutP155,
  vcCutP156,
  vcCutP157,
  vcCutP158,
  vcCutP159]

end HlawkaSchatten.BelowExponent.Vertex
