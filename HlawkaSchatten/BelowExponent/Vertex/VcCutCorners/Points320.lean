/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.VcCornerData.Points320

/-! Checked corner data shared by the vertex middle and band regions: `Points320`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

def vcCutP320 : SideCornerEntry := ⟨1/20, 9/40, 1/40, #v[12033339/2000000000, 2657423/500000000, 23300547/10000000000]⟩
abbrev vcCutP320Roots := vcOuterP320Roots
theorem vcCutP320_roots : vcCutP320.cell.rootsOK vcCutP320Roots = true := by decide +kernel

def vcCutP321 : SideCornerEntry := ⟨1/20, 9/40, 1/36, #v[176216117/5000000000, 16163309/500000000, 185427063/10000000000]⟩
abbrev vcCutP321Roots := vcOuterP321Roots
theorem vcCutP321_roots : vcCutP321.cell.rootsOK vcCutP321Roots = true := by decide +kernel

def vcCutP322 : SideCornerEntry := ⟨1/20, 9/40, 1/20, #v[12362243/2000000000, 54477483/10000000000, 23743603/10000000000]⟩
abbrev vcCutP322Roots := vcOuterP322Roots
theorem vcCutP322_roots : vcCutP322.cell.rootsOK vcCutP322Roots = true := by decide +kernel

def vcCutP323 : SideCornerEntry := ⟨1/20, 9/40, 1/18, #v[176216117/5000000000, 16163309/500000000, 185427063/10000000000]⟩
abbrev vcCutP323Roots := vcOuterP323Roots
theorem vcCutP323_roots : vcCutP323.cell.rootsOK vcCutP323Roots = true := by decide +kernel

def vcCutP324 : SideCornerEntry := ⟨1/20, 9/40, 3/40, #v[63552589/10000000000, 55907861/10000000000, 24242951/10000000000]⟩
abbrev vcCutP324Roots := vcOuterP324Roots
theorem vcCutP324_roots : vcCutP324.cell.rootsOK vcCutP324Roots = true := by decide +kernel

def vcCutP325 : SideCornerEntry := ⟨1/20, 9/40, 1/10, #v[63552589/10000000000, 55907861/10000000000, 24242951/10000000000]⟩
abbrev vcCutP325Roots := vcOuterP325Roots
theorem vcCutP325_roots : vcCutP325.cell.rootsOK vcCutP325Roots = true := by decide +kernel

def vcCutP326 : SideCornerEntry := ⟨1/20, 19/80, 0, #v[13331343/2500000000, 4669493/1000000000, 21255347/10000000000]⟩
abbrev vcCutP326Roots := vcOuterP326Roots
theorem vcCutP326_roots : vcCutP326.cell.rootsOK vcCutP326Roots = true := by decide +kernel

def vcCutP327 : SideCornerEntry := ⟨1/20, 19/80, 1/40, #v[1365097/250000000, 23835171/5000000000, 21558091/10000000000]⟩
abbrev vcCutP327Roots := vcOuterP327Roots
theorem vcCutP327_roots : vcCutP327.cell.rootsOK vcCutP327Roots = true := by decide +kernel

def vcCutP328 : SideCornerEntry := ⟨1/20, 19/80, 1/20, #v[55994437/10000000000, 24383/5000000, 21926359/10000000000]⟩
abbrev vcCutP328Roots := vcOuterP328Roots
theorem vcCutP328_roots : vcCutP328.cell.rootsOK vcCutP328Roots = true := by decide +kernel

def vcCutP329 : SideCornerEntry := ⟨1/20, 19/80, 3/40, #v[1436909/250000000, 780607/156250000, 4469549/2000000000]⟩
abbrev vcCutP329Roots := vcOuterP329Roots
theorem vcCutP329_roots : vcCutP329.cell.rootsOK vcCutP329Roots = true := by decide +kernel

def vcCutP330 : SideCornerEntry := ⟨1/20, 19/80, 1/10, #v[1436909/250000000, 780607/156250000, 4469549/2000000000]⟩
abbrev vcCutP330Roots := vcOuterP330Roots
theorem vcCutP330_roots : vcCutP330.cell.rootsOK vcCutP330Roots = true := by decide +kernel

def vcCutP331 : SideCornerEntry := ⟨1/20, 1/4, 0, #v[8189697/312500000, 58602759/2500000000, 70476729/5000000000]⟩
abbrev vcCutP331Roots := vcOuterP331Roots
theorem vcCutP331_roots : vcCutP331.cell.rootsOK vcCutP331Roots = true := by decide +kernel

def vcCutP332 : SideCornerEntry := ⟨1/20, 1/4, 1/40, #v[25001171/5000000000, 43138243/10000000000, 10074459/5000000000]⟩
abbrev vcCutP332Roots := vcOuterP332Roots
theorem vcCutP332_roots : vcCutP332.cell.rootsOK vcCutP332Roots = true := by decide +kernel

def vcCutP333 : SideCornerEntry := ⟨1/20, 1/4, 1/36, #v[138110159/5000000000, 246551957/10000000000, 147598321/10000000000]⟩
abbrev vcCutP333Roots := vcOuterP333Roots
theorem vcCutP333_roots : vcCutP333.cell.rootsOK vcCutP333Roots = true := by decide +kernel

def vcCutP334 : SideCornerEntry := ⟨1/20, 1/4, 1/20, #v[1279591/250000000, 11011267/2500000000, 10226221/5000000000]⟩
abbrev vcCutP334Roots := vcOuterP334Roots
theorem vcCutP334_roots : vcCutP334.cell.rootsOK vcCutP334Roots = true := by decide +kernel

def vcCutP335 : SideCornerEntry := ⟨1/20, 1/4, 1/18, #v[138110159/5000000000, 246551957/10000000000, 147598321/10000000000]⟩
abbrev vcCutP335Roots := vcOuterP335Roots
theorem vcCutP335_roots : vcCutP335.cell.rootsOK vcCutP335Roots = true := by decide +kernel

def vcCutP336 : SideCornerEntry := ⟨1/20, 1/4, 3/40, #v[5245723/1000000000, 9009671/2000000000, 416207/200000000]⟩
abbrev vcCutP336Roots := vcOuterP336Roots
theorem vcCutP336_roots : vcCutP336.cell.rootsOK vcCutP336Roots = true := by decide +kernel

def vcCutP337 : SideCornerEntry := ⟨1/20, 1/4, 1/10, #v[5245723/1000000000, 9009671/2000000000, 416207/200000000]⟩
abbrev vcCutP337Roots := vcOuterP337Roots
theorem vcCutP337_roots : vcCutP337.cell.rootsOK vcCutP337Roots = true := by decide +kernel

def vcCutP338 : SideCornerEntry := ⟨1/20, 21/80, 0, #v[22629977/5000000000, 7742087/2000000000, 18817393/10000000000]⟩
abbrev vcCutP338Roots := vcOuterP338Roots
theorem vcCutP338_roots : vcCutP338.cell.rootsOK vcCutP338Roots = true := by decide +kernel

def vcCutP339 : SideCornerEntry := ⟨1/20, 21/80, 1/40, #v[23077127/5000000000, 39344771/10000000000, 1187371/625000000]⟩
abbrev vcCutP339Roots := vcOuterP339Roots
theorem vcCutP339_roots : vcCutP339.cell.rootsOK vcCutP339Roots = true := by decide +kernel

def vcCutP340 : SideCornerEntry := ⟨1/20, 21/80, 1/20, #v[471631/100000000, 8019567/2000000000, 4811903/2500000000]⟩
abbrev vcCutP340Roots := vcOuterP340Roots
theorem vcCutP340_roots : vcCutP340.cell.rootsOK vcCutP340Roots = true := by decide +kernel

def vcCutP341 : SideCornerEntry := ⟨1/20, 21/80, 3/40, #v[48270697/10000000000, 8189489/2000000000, 4888541/2500000000]⟩
abbrev vcCutP341Roots := vcOuterP341Roots
theorem vcCutP341_roots : vcCutP341.cell.rootsOK vcCutP341Roots = true := by decide +kernel

def vcCutP342 : SideCornerEntry := ⟨1/20, 21/80, 1/10, #v[48270697/10000000000, 8189489/2000000000, 4888541/2500000000]⟩
abbrev vcCutP342Roots := vcOuterP342Roots
theorem vcCutP342_roots : vcCutP342.cell.rootsOK vcCutP342Roots = true := by decide +kernel

def vcCutP343 : SideCornerEntry := ⟨1/20, 11/40, 0, #v[107720587/5000000000, 93799343/5000000000, 7370807/625000000]⟩
abbrev vcCutP343Roots := vcOuterP343Roots
theorem vcCutP343_roots : vcCutP343.cell.rootsOK vcCutP343Roots = true := by decide +kernel

def vcCutP344 : SideCornerEntry := ⟨1/20, 11/40, 1/40, #v[42908707/10000000000, 36138457/10000000000, 1805367/1000000000]⟩
abbrev vcCutP344Roots := vcOuterP344Roots
theorem vcCutP344_roots : vcCutP344.cell.rootsOK vcCutP344Roots = true := by decide +kernel

def vcCutP345 : SideCornerEntry := ⟨1/20, 11/40, 1/36, #v[113274277/5000000000, 98422257/5000000000, 15417241/1250000000]⟩
abbrev vcCutP345Roots := vcOuterP345Roots
theorem vcCutP345_roots : vcCutP345.cell.rootsOK vcCutP345Roots = true := by decide +kernel

def vcCutP346 : SideCornerEntry := ⟨1/20, 11/40, 1/20, #v[21886759/5000000000, 18382331/5000000000, 4564391/2500000000]⟩
abbrev vcCutP346Roots := vcOuterP346Roots
theorem vcCutP346_roots : vcCutP346.cell.rootsOK vcCutP346Roots = true := by decide +kernel

def vcCutP347 : SideCornerEntry := ⟨1/20, 11/40, 1/18, #v[113274277/5000000000, 98422257/5000000000, 15417241/1250000000]⟩
abbrev vcCutP347Roots := vcOuterP347Roots
theorem vcCutP347_roots : vcCutP347.cell.rootsOK vcCutP347Roots = true := by decide +kernel

def vcCutP348 : SideCornerEntry := ⟨1/20, 11/40, 3/40, #v[5592859/1250000000, 37486129/10000000000, 18519927/10000000000]⟩
abbrev vcCutP348Roots := vcOuterP348Roots
theorem vcCutP348_roots : vcCutP348.cell.rootsOK vcCutP348Roots = true := by decide +kernel

def vcCutP349 : SideCornerEntry := ⟨1/20, 11/40, 1/10, #v[5592859/1250000000, 37486129/10000000000, 18519927/10000000000]⟩
abbrev vcCutP349Roots := vcOuterP349Roots
theorem vcCutP349_roots : vcCutP349.cell.rootsOK vcCutP349Roots = true := by decide +kernel

def vcCutP350 : SideCornerEntry := ⟨1/20, 23/80, 0, #v[39521871/10000000000, 16499843/5000000000, 1718329/1000000000]⟩
abbrev vcCutP350Roots := vcOuterP350Roots
theorem vcCutP350_roots : vcCutP350.cell.rootsOK vcCutP350Roots = true := by decide +kernel

def vcCutP351 : SideCornerEntry := ⟨1/20, 23/80, 1/40, #v[20074987/5000000000, 16702387/5000000000, 8638079/5000000000]⟩
abbrev vcCutP351Roots := vcOuterP351Roots
theorem vcCutP351_roots : vcCutP351.cell.rootsOK vcCutP351Roots = true := by decide +kernel

def vcCutPoints320 : Array SideCornerEntry := #[
  vcCutP320,
  vcCutP321,
  vcCutP322,
  vcCutP323,
  vcCutP324,
  vcCutP325,
  vcCutP326,
  vcCutP327,
  vcCutP328,
  vcCutP329,
  vcCutP330,
  vcCutP331,
  vcCutP332,
  vcCutP333,
  vcCutP334,
  vcCutP335,
  vcCutP336,
  vcCutP337,
  vcCutP338,
  vcCutP339,
  vcCutP340,
  vcCutP341,
  vcCutP342,
  vcCutP343,
  vcCutP344,
  vcCutP345,
  vcCutP346,
  vcCutP347,
  vcCutP348,
  vcCutP349,
  vcCutP350,
  vcCutP351]

end HlawkaSchatten.BelowExponent.Vertex
