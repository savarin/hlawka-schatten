/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.VcCornerData.Points288

/-! Checked corner data shared by the vertex middle and band regions: `Points288`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

def vcCutP288 : SideCornerEntry := ⟨1/20, 3/20, 3/40, #v[7953169/625000000, 5945827/500000000, 45909811/10000000000]⟩
abbrev vcCutP288Roots := vcOuterP288Roots
theorem vcCutP288_roots : vcCutP288.cell.rootsOK vcCutP288Roots = true := by decide +kernel

def vcCutP289 : SideCornerEntry := ⟨1/20, 3/20, 1/10, #v[7953169/625000000, 5945827/500000000, 45909811/10000000000]⟩
abbrev vcCutP289Roots := vcOuterP289Roots
theorem vcCutP289_roots : vcCutP289.cell.rootsOK vcCutP289Roots = true := by decide +kernel

def vcCutP290 : SideCornerEntry := ⟨1/20, 13/80, 0, #v[113923871/10000000000, 13378701/1250000000, 42147873/10000000000]⟩
abbrev vcCutP290Roots := vcOuterP290Roots
theorem vcCutP290_roots : vcCutP290.cell.rootsOK vcCutP290Roots = true := by decide +kernel

def vcCutP291 : SideCornerEntry := ⟨1/20, 13/80, 1/40, #v[29571917/2500000000, 693069/62500000, 10838269/2500000000]⟩
abbrev vcCutP291Roots := vcOuterP291Roots
theorem vcCutP291_roots : vcCutP291.cell.rootsOK vcCutP291Roots = true := by decide +kernel

def vcCutP292 : SideCornerEntry := ⟨1/20, 13/80, 1/20, #v[122735409/10000000000, 28715171/2500000000, 8922097/2000000000]⟩
abbrev vcCutP292Roots := vcOuterP292Roots
theorem vcCutP292_roots : vcCutP292.cell.rootsOK vcCutP292Roots = true := by decide +kernel

def vcCutP293 : SideCornerEntry := ⟨1/20, 13/80, 3/40, #v[7953169/625000000, 5945827/500000000, 45909811/10000000000]⟩
abbrev vcCutP293Roots := vcOuterP293Roots
theorem vcCutP293_roots : vcCutP293.cell.rootsOK vcCutP293Roots = true := by decide +kernel

def vcCutP294 : SideCornerEntry := ⟨1/20, 13/80, 1/10, #v[7953169/625000000, 5945827/500000000, 45909811/10000000000]⟩
abbrev vcCutP294Roots := vcOuterP294Roots
theorem vcCutP294_roots : vcCutP294.cell.rootsOK vcCutP294Roots = true := by decide +kernel

def vcCutP295 : SideCornerEntry := ⟨1/20, 7/40, 0, #v[114069291/2500000000, 213920261/5000000000, 238239683/10000000000]⟩
abbrev vcCutP295Roots := vcOuterP295Roots
theorem vcCutP295_roots : vcCutP295.cell.rootsOK vcCutP295Roots = true := by decide +kernel

def vcCutP296 : SideCornerEntry := ⟨1/20, 7/40, 1/40, #v[781629/78125000, 46314189/5000000000, 18451737/5000000000]⟩
abbrev vcCutP296Roots := vcOuterP296Roots
theorem vcCutP296_roots : vcCutP296.cell.rootsOK vcCutP296Roots = true := by decide +kernel

def vcCutP297 : SideCornerEntry := ⟨1/20, 7/40, 1/36, #v[114069291/2500000000, 213920261/5000000000, 238239683/10000000000]⟩
abbrev vcCutP297Roots := vcOuterP297Roots
theorem vcCutP297_roots : vcCutP297.cell.rootsOK vcCutP297Roots = true := by decide +kernel

def vcCutP298 : SideCornerEntry := ⟨1/20, 7/40, 1/20, #v[51800447/5000000000, 5984181/625000000, 18954679/5000000000]⟩
abbrev vcCutP298Roots := vcOuterP298Roots
theorem vcCutP298_roots : vcCutP298.cell.rootsOK vcCutP298Roots = true := by decide +kernel

def vcCutP299 : SideCornerEntry := ⟨1/20, 7/40, 1/18, #v[163088753/5000000000, 298575849/10000000000, 140104323/10000000000]⟩
abbrev vcCutP299Roots := vcOuterP299Roots
theorem vcCutP299_roots : vcCutP299.cell.rootsOK vcCutP299Roots = true := by decide +kernel

def vcCutP300 : SideCornerEntry := ⟨1/20, 7/40, 3/40, #v[5361397/500000000, 49478027/5000000000, 19479739/5000000000]⟩
abbrev vcCutP300Roots := vcOuterP300Roots
theorem vcCutP300_roots : vcCutP300.cell.rootsOK vcCutP300Roots = true := by decide +kernel

def vcCutP301 : SideCornerEntry := ⟨1/20, 7/40, 1/10, #v[5361397/500000000, 49478027/5000000000, 19479739/5000000000]⟩
abbrev vcCutP301Roots := vcOuterP301Roots
theorem vcCutP301_roots : vcCutP301.cell.rootsOK vcCutP301Roots = true := by decide +kernel

def vcCutP302 : SideCornerEntry := ⟨1/20, 3/16, 0, #v[5214979/625000000, 76497927/10000000000, 15665821/5000000000]⟩
abbrev vcCutP302Roots := vcOuterP302Roots
theorem vcCutP302_roots : vcCutP302.cell.rootsOK vcCutP302Roots = true := by decide +kernel

def vcCutP303 : SideCornerEntry := ⟨1/20, 3/16, 1/40, #v[2155671/250000000, 39431719/5000000000, 62667/19531250]⟩
abbrev vcCutP303Roots := vcOuterP303Roots
theorem vcCutP303_roots : vcCutP303.cell.rootsOK vcCutP303Roots = true := by decide +kernel

def vcCutP304 : SideCornerEntry := ⟨1/20, 3/16, 1/20, #v[44555981/5000000000, 81345509/10000000000, 16448211/5000000000]⟩
abbrev vcCutP304Roots := vcOuterP304Roots
theorem vcCutP304_roots : vcCutP304.cell.rootsOK vcCutP304Roots = true := by decide +kernel

def vcCutP305 : SideCornerEntry := ⟨1/20, 3/16, 3/40, #v[5754771/625000000, 83926131/10000000000, 3375659/1000000000]⟩
abbrev vcCutP305Roots := vcOuterP305Roots
theorem vcCutP305_roots : vcCutP305.cell.rootsOK vcCutP305Roots = true := by decide +kernel

def vcCutP306 : SideCornerEntry := ⟨1/20, 3/16, 1/10, #v[5754771/625000000, 83926131/10000000000, 3375659/1000000000]⟩
abbrev vcCutP306Roots := vcOuterP306Roots
theorem vcCutP306_roots : vcCutP306.cell.rootsOK vcCutP306Roots = true := by decide +kernel

def vcCutP307 : SideCornerEntry := ⟨1/20, 1/5, 0, #v[114069291/2500000000, 213920261/5000000000, 238239683/10000000000]⟩
abbrev vcCutP307Roots := vcOuterP307Roots
theorem vcCutP307_roots : vcCutP307.cell.rootsOK vcCutP307Roots = true := by decide +kernel

def vcCutP308 : SideCornerEntry := ⟨1/20, 1/5, 1/40, #v[9437463/1250000000, 68241349/10000000000, 7100587/2500000000]⟩
abbrev vcCutP308Roots := vcOuterP308Roots
theorem vcCutP308_roots : vcCutP308.cell.rootsOK vcCutP308Roots = true := by decide +kernel

def vcCutP309 : SideCornerEntry := ⟨1/20, 1/5, 1/36, #v[114069291/2500000000, 213920261/5000000000, 238239683/10000000000]⟩
abbrev vcCutP309Roots := vcOuterP309Roots
theorem vcCutP309_roots : vcCutP309.cell.rootsOK vcCutP309Roots = true := by decide +kernel

def vcCutP310 : SideCornerEntry := ⟨1/20, 1/5, 1/20, #v[1557473/200000000, 14048439/2000000000, 3632979/1250000000]⟩
abbrev vcCutP310Roots := vcOuterP310Roots
theorem vcCutP310_roots : vcCutP310.cell.rootsOK vcCutP310Roots = true := by decide +kernel

def vcCutP311 : SideCornerEntry := ⟨1/20, 1/5, 1/18, #v[176216117/5000000000, 16163309/500000000, 185427063/10000000000]⟩
abbrev vcCutP311Roots := vcOuterP311Roots
theorem vcCutP311_roots : vcCutP311.cell.rootsOK vcCutP311Roots = true := by decide +kernel

def vcCutP312 : SideCornerEntry := ⟨1/20, 1/5, 3/40, #v[40164899/5000000000, 18084267/2500000000, 7443201/2500000000]⟩
abbrev vcCutP312Roots := vcOuterP312Roots
theorem vcCutP312_roots : vcCutP312.cell.rootsOK vcCutP312Roots = true := by decide +kernel

def vcCutP313 : SideCornerEntry := ⟨1/20, 1/5, 1/10, #v[40164899/5000000000, 18084267/2500000000, 7443201/2500000000]⟩
abbrev vcCutP313Roots := vcOuterP313Roots
theorem vcCutP313_roots : vcCutP313.cell.rootsOK vcCutP313Roots = true := by decide +kernel

def vcCutP314 : SideCornerEntry := ⟨1/20, 17/80, 0, #v[32574149/5000000000, 58359227/10000000000, 12528409/5000000000]⟩
abbrev vcCutP314Roots := vcOuterP314Roots
theorem vcCutP314_roots : vcCutP314.cell.rootsOK vcCutP314Roots = true := by decide +kernel

def vcCutP315 : SideCornerEntry := ⟨1/20, 17/80, 1/40, #v[6700163/1000000000, 11971819/2000000000, 3191639/1250000000]⟩
abbrev vcCutP315Roots := vcOuterP315Roots
theorem vcCutP315_roots : vcCutP315.cell.rootsOK vcCutP315Roots = true := by decide +kernel

def vcCutP316 : SideCornerEntry := ⟨1/20, 17/80, 1/20, #v[13794919/2000000000, 30744109/5000000000, 5214963/2000000000]⟩
abbrev vcCutP316Roots := vcOuterP316Roots
theorem vcCutP316_roots : vcCutP316.cell.rootsOK vcCutP316Roots = true := by decide +kernel

def vcCutP317 : SideCornerEntry := ⟨1/20, 17/80, 3/40, #v[71035403/10000000000, 6321459/1000000000, 266669/100000000]⟩
abbrev vcCutP317Roots := vcOuterP317Roots
theorem vcCutP317_roots : vcCutP317.cell.rootsOK vcCutP317Roots = true := by decide +kernel

def vcCutP318 : SideCornerEntry := ⟨1/20, 17/80, 1/10, #v[71035403/10000000000, 6321459/1000000000, 266669/100000000]⟩
abbrev vcCutP318Roots := vcOuterP318Roots
theorem vcCutP318_roots : vcCutP318.cell.rootsOK vcCutP318Roots = true := by decide +kernel

def vcCutP319 : SideCornerEntry := ⟨1/20, 9/40, 0, #v[333561317/10000000000, 306664657/10000000000, 88459109/5000000000]⟩
abbrev vcCutP319Roots := vcOuterP319Roots
theorem vcCutP319_roots : vcCutP319.cell.rootsOK vcCutP319Roots = true := by decide +kernel

def vcCutPoints288 : Array SideCornerEntry := #[
  vcCutP288,
  vcCutP289,
  vcCutP290,
  vcCutP291,
  vcCutP292,
  vcCutP293,
  vcCutP294,
  vcCutP295,
  vcCutP296,
  vcCutP297,
  vcCutP298,
  vcCutP299,
  vcCutP300,
  vcCutP301,
  vcCutP302,
  vcCutP303,
  vcCutP304,
  vcCutP305,
  vcCutP306,
  vcCutP307,
  vcCutP308,
  vcCutP309,
  vcCutP310,
  vcCutP311,
  vcCutP312,
  vcCutP313,
  vcCutP314,
  vcCutP315,
  vcCutP316,
  vcCutP317,
  vcCutP318,
  vcCutP319]

end HlawkaSchatten.BelowExponent.Vertex
