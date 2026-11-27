/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.VcCornerData.Points256

/-! Checked corner data shared by the vertex middle and band regions: `Points256`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

def vcCutP256 : SideCornerEntry := ⟨3/80, 9/20, 1/40, #v[26058491/10000000000, 1809657/1000000000, 610549/400000000]⟩
abbrev vcCutP256Roots := vcOuterP256Roots
theorem vcCutP256_roots : vcCutP256.cell.rootsOK vcCutP256Roots = true := by decide +kernel

def vcCutP257 : SideCornerEntry := ⟨3/80, 9/20, 1/20, #v[26178237/10000000000, 2251211/1250000000, 946639/625000000]⟩
abbrev vcCutP257Roots := vcOuterP257Roots
theorem vcCutP257_roots : vcCutP257.cell.rootsOK vcCutP257Roots = true := by decide +kernel

def vcCutP258 : SideCornerEntry := ⟨3/80, 9/20, 3/40, #v[26397577/10000000000, 4522993/2500000000, 15164489/10000000000]⟩
abbrev vcCutP258Roots := vcOuterP258Roots
theorem vcCutP258_roots : vcCutP258.cell.rootsOK vcCutP258Roots = true := by decide +kernel

def vcCutP259 : SideCornerEntry := ⟨3/80, 9/20, 1/10, #v[26397577/10000000000, 4522993/2500000000, 15164489/10000000000]⟩
abbrev vcCutP259Roots := vcOuterP259Roots
theorem vcCutP259_roots : vcCutP259.cell.rootsOK vcCutP259Roots = true := by decide +kernel

def vcCutP260 : SideCornerEntry := ⟨3/80, 37/80, 0, #v[643741/250000000, 17587147/10000000000, 15499549/10000000000]⟩
abbrev vcCutP260Roots := vcOuterP260Roots
theorem vcCutP260_roots : vcCutP260.cell.rootsOK vcCutP260Roots = true := by decide +kernel

def vcCutP261 : SideCornerEntry := ⟨3/80, 37/80, 1/40, #v[643741/250000000, 17587147/10000000000, 15499549/10000000000]⟩
abbrev vcCutP261Roots := vcOuterP261Roots
theorem vcCutP261_roots : vcCutP261.cell.rootsOK vcCutP261Roots = true := by decide +kernel

def vcCutP262 : SideCornerEntry := ⟨3/80, 37/80, 1/20, #v[2584531/1000000000, 8744059/5000000000, 15381659/10000000000]⟩
abbrev vcCutP262Roots := vcOuterP262Roots
theorem vcCutP262_roots : vcCutP262.cell.rootsOK vcCutP262Roots = true := by decide +kernel

def vcCutP263 : SideCornerEntry := ⟨3/80, 37/80, 3/40, #v[6513039/2500000000, 17555269/10000000000, 15403197/10000000000]⟩
abbrev vcCutP263Roots := vcOuterP263Roots
theorem vcCutP263_roots : vcCutP263.cell.rootsOK vcCutP263Roots = true := by decide +kernel

def vcCutP264 : SideCornerEntry := ⟨3/80, 37/80, 1/10, #v[6513039/2500000000, 17555269/10000000000, 15403197/10000000000]⟩
abbrev vcCutP264Roots := vcOuterP264Roots
theorem vcCutP264_roots : vcCutP264.cell.rootsOK vcCutP264Roots = true := by decide +kernel

def vcCutP265 : SideCornerEntry := ⟨3/80, 19/40, 0, #v[6379189/2500000000, 4283407/2500000000, 15809103/10000000000]⟩
abbrev vcCutP265Roots := vcOuterP265Roots
theorem vcCutP265_roots : vcCutP265.cell.rootsOK vcCutP265Roots = true := by decide +kernel

def vcCutP266 : SideCornerEntry := ⟨3/80, 19/40, 1/40, #v[6379189/2500000000, 4283407/2500000000, 15809103/10000000000]⟩
abbrev vcCutP266Roots := vcOuterP266Roots
theorem vcCutP266_roots : vcCutP266.cell.rootsOK vcCutP266Roots = true := by decide +kernel

def vcCutP267 : SideCornerEntry := ⟨3/80, 19/40, 1/20, #v[25594883/10000000000, 17029273/10000000000, 1961787/1250000000]⟩
abbrev vcCutP267Roots := vcOuterP267Roots
theorem vcCutP267_roots : vcCutP267.cell.rootsOK vcCutP267Roots = true := by decide +kernel

def vcCutP268 : SideCornerEntry := ⟨3/80, 19/40, 3/40, #v[12896273/5000000000, 8540581/5000000000, 7863023/5000000000]⟩
abbrev vcCutP268Roots := vcOuterP268Roots
theorem vcCutP268_roots : vcCutP268.cell.rootsOK vcCutP268Roots = true := by decide +kernel

def vcCutP269 : SideCornerEntry := ⟨3/80, 19/40, 1/10, #v[12896273/5000000000, 8540581/5000000000, 7863023/5000000000]⟩
abbrev vcCutP269Roots := vcOuterP269Roots
theorem vcCutP269_roots : vcCutP269.cell.rootsOK vcCutP269Roots = true := by decide +kernel

def vcCutP270 : SideCornerEntry := ⟨3/80, 39/80, 0, #v[25362249/10000000000, 16739051/10000000000, 15809103/10000000000]⟩
abbrev vcCutP270Roots := vcOuterP270Roots
theorem vcCutP270_roots : vcCutP270.cell.rootsOK vcCutP270Roots = true := by decide +kernel

def vcCutP271 : SideCornerEntry := ⟨3/80, 39/80, 1/40, #v[25362249/10000000000, 16739051/10000000000, 15809103/10000000000]⟩
abbrev vcCutP271Roots := vcOuterP271Roots
theorem vcCutP271_roots : vcCutP271.cell.rootsOK vcCutP271Roots = true := by decide +kernel

def vcCutP272 : SideCornerEntry := ⟨3/80, 39/80, 1/20, #v[5086037/2000000000, 16631917/10000000000, 1961787/1250000000]⟩
abbrev vcCutP272Roots := vcOuterP272Roots
theorem vcCutP272_roots : vcCutP272.cell.rootsOK vcCutP272Roots = true := by decide +kernel

def vcCutP273 : SideCornerEntry := ⟨3/80, 39/80, 3/40, #v[6405593/2500000000, 16698323/10000000000, 7863023/5000000000]⟩
abbrev vcCutP273Roots := vcOuterP273Roots
theorem vcCutP273_roots : vcCutP273.cell.rootsOK vcCutP273Roots = true := by decide +kernel

def vcCutP274 : SideCornerEntry := ⟨3/80, 39/80, 1/10, #v[6405593/2500000000, 16698323/10000000000, 7863023/5000000000]⟩
abbrev vcCutP274Roots := vcOuterP274Roots
theorem vcCutP274_roots : vcCutP274.cell.rootsOK vcCutP274Roots = true := by decide +kernel

def vcCutP275 : SideCornerEntry := ⟨1/20, 1/8, 0, #v[395057129/10000000000, 365348519/10000000000, 4656573/400000000]⟩
abbrev vcCutP275Roots := vcOuterP275Roots
theorem vcCutP275_roots : vcCutP275.cell.rootsOK vcCutP275Roots = true := by decide +kernel

def vcCutP276 : SideCornerEntry := ⟨1/20, 1/8, 1/36, #v[395057129/10000000000, 365348519/10000000000, 4656573/400000000]⟩
abbrev vcCutP276Roots := vcOuterP276Roots
theorem vcCutP276_roots : vcCutP276.cell.rootsOK vcCutP276Roots = true := by decide +kernel

def vcCutP277 : SideCornerEntry := ⟨1/20, 1/8, 1/24, #v[3512453/200000000, 167987487/10000000000, 17625981/2500000000]⟩
abbrev vcCutP277Roots := vcOuterP277Roots
theorem vcCutP277_roots : vcCutP277.cell.rootsOK vcCutP277Roots = true := by decide +kernel

def vcCutP278 : SideCornerEntry := ⟨1/20, 1/8, 1/18, #v[3512453/200000000, 167987487/10000000000, 17625981/2500000000]⟩
abbrev vcCutP278Roots := vcOuterP278Roots
theorem vcCutP278_roots : vcCutP278.cell.rootsOK vcCutP278Roots = true := by decide +kernel

def vcCutP279 : SideCornerEntry := ⟨1/20, 11/80, 1/36, #v[170743659/10000000000, 40840873/2500000000, 34467261/5000000000]⟩
abbrev vcCutP279Roots := vcOuterP279Roots
theorem vcCutP279_roots : vcCutP279.cell.rootsOK vcCutP279Roots = true := by decide +kernel

def vcCutP280 : SideCornerEntry := ⟨1/20, 11/80, 1/24, #v[3512453/200000000, 167987487/10000000000, 17625981/2500000000]⟩
abbrev vcCutP280Roots := vcOuterP280Roots
theorem vcCutP280_roots : vcCutP280.cell.rootsOK vcCutP280Roots = true := by decide +kernel

def vcCutP281 : SideCornerEntry := ⟨1/20, 11/80, 1/18, #v[3512453/200000000, 167987487/10000000000, 17625981/2500000000]⟩
abbrev vcCutP281Roots := vcOuterP281Roots
theorem vcCutP281_roots : vcCutP281.cell.rootsOK vcCutP281Roots = true := by decide +kernel

def vcCutP282 : SideCornerEntry := ⟨1/20, 3/20, 0, #v[86269947/2000000000, 406483281/10000000000, 189057877/10000000000]⟩
abbrev vcCutP282Roots := vcOuterP282Roots
theorem vcCutP282_roots : vcCutP282.cell.rootsOK vcCutP282Roots = true := by decide +kernel

def vcCutP283 : SideCornerEntry := ⟨1/20, 3/20, 1/40, #v[29571917/2500000000, 693069/62500000, 10838269/2500000000]⟩
abbrev vcCutP283Roots := vcOuterP283Roots
theorem vcCutP283_roots : vcCutP283.cell.rootsOK vcCutP283Roots = true := by decide +kernel

def vcCutP284 : SideCornerEntry := ⟨1/20, 3/20, 1/36, #v[86269947/2000000000, 406483281/10000000000, 189057877/10000000000]⟩
abbrev vcCutP284Roots := vcOuterP284Roots
theorem vcCutP284_roots : vcCutP284.cell.rootsOK vcCutP284Roots = true := by decide +kernel

def vcCutP285 : SideCornerEntry := ⟨1/20, 3/20, 1/24, #v[27175251/2000000000, 16102481/1250000000, 54469197/10000000000]⟩
abbrev vcCutP285Roots := vcOuterP285Roots
theorem vcCutP285_roots : vcCutP285.cell.rootsOK vcCutP285Roots = true := by decide +kernel

def vcCutP286 : SideCornerEntry := ⟨1/20, 3/20, 1/20, #v[122735409/10000000000, 28715171/2500000000, 8922097/2000000000]⟩
abbrev vcCutP286Roots := vcOuterP286Roots
theorem vcCutP286_roots : vcCutP286.cell.rootsOK vcCutP286Roots = true := by decide +kernel

def vcCutP287 : SideCornerEntry := ⟨1/20, 3/20, 1/18, #v[162333583/5000000000, 295146511/10000000000, 4305089/400000000]⟩
abbrev vcCutP287Roots := vcOuterP287Roots
theorem vcCutP287_roots : vcCutP287.cell.rootsOK vcCutP287Roots = true := by decide +kernel

def vcCutPoints256 : Array SideCornerEntry := #[
  vcCutP256,
  vcCutP257,
  vcCutP258,
  vcCutP259,
  vcCutP260,
  vcCutP261,
  vcCutP262,
  vcCutP263,
  vcCutP264,
  vcCutP265,
  vcCutP266,
  vcCutP267,
  vcCutP268,
  vcCutP269,
  vcCutP270,
  vcCutP271,
  vcCutP272,
  vcCutP273,
  vcCutP274,
  vcCutP275,
  vcCutP276,
  vcCutP277,
  vcCutP278,
  vcCutP279,
  vcCutP280,
  vcCutP281,
  vcCutP282,
  vcCutP283,
  vcCutP284,
  vcCutP285,
  vcCutP286,
  vcCutP287]

end HlawkaSchatten.BelowExponent.Vertex
