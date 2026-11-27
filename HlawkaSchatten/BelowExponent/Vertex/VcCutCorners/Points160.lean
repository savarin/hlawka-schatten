/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.VcCornerData.Points160

/-! Checked corner data shared by the vertex middle and band regions: `Points160`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

def vcCutP160 : SideCornerEntry := ⟨3/80, 17/80, 0, #v[17112789/2500000000, 61164531/10000000000, 12528409/5000000000]⟩
abbrev vcCutP160Roots := vcOuterP160Roots
theorem vcCutP160_roots : vcCutP160.cell.rootsOK vcCutP160Roots = true := by decide +kernel

def vcCutP161 : SideCornerEntry := ⟨3/80, 17/80, 1/40, #v[35173299/5000000000, 31338661/5000000000, 3191639/1250000000]⟩
abbrev vcCutP161Roots := vcOuterP161Roots
theorem vcCutP161_roots : vcCutP161.cell.rootsOK vcCutP161Roots = true := by decide +kernel

def vcCutP162 : SideCornerEntry := ⟨3/80, 17/80, 1/20, #v[18088719/2500000000, 2009857/312500000, 5214963/2000000000]⟩
abbrev vcCutP162Roots := vcOuterP162Roots
theorem vcCutP162_roots : vcCutP162.cell.rootsOK vcCutP162Roots = true := by decide +kernel

def vcCutP163 : SideCornerEntry := ⟨3/80, 17/80, 3/40, #v[4653431/625000000, 16513633/2500000000, 266669/100000000]⟩
abbrev vcCutP163Roots := vcOuterP163Roots
theorem vcCutP163_roots : vcCutP163.cell.rootsOK vcCutP163Roots = true := by decide +kernel

def vcCutP164 : SideCornerEntry := ⟨3/80, 17/80, 1/10, #v[4653431/625000000, 16513633/2500000000, 266669/100000000]⟩
abbrev vcCutP164Roots := vcOuterP164Roots
theorem vcCutP164_roots : vcCutP164.cell.rootsOK vcCutP164Roots = true := by decide +kernel

def vcCutP165 : SideCornerEntry := ⟨3/80, 9/40, 0, #v[7700983/1250000000, 27223023/5000000000, 114609/50000000]⟩
abbrev vcCutP165Roots := vcOuterP165Roots
theorem vcCutP165_roots : vcCutP165.cell.rootsOK vcCutP165Roots = true := by decide +kernel

def vcCutP166 : SideCornerEntry := ⟨3/80, 9/40, 1/40, #v[63182367/10000000000, 55668487/10000000000, 23300547/10000000000]⟩
abbrev vcCutP166Roots := vcOuterP166Roots
theorem vcCutP166_roots : vcCutP166.cell.rootsOK vcCutP166Roots = true := by decide +kernel

def vcCutP167 : SideCornerEntry := ⟨3/80, 9/40, 1/20, #v[202723/31250000, 285079/50000000, 23743603/10000000000]⟩
abbrev vcCutP167Roots := vcOuterP167Roots
theorem vcCutP167_roots : vcCutP167.cell.rootsOK vcCutP167Roots = true := by decide +kernel

def vcCutP168 : SideCornerEntry := ⟨3/80, 9/40, 3/40, #v[66653583/10000000000, 29231959/5000000000, 24242951/10000000000]⟩
abbrev vcCutP168Roots := vcOuterP168Roots
theorem vcCutP168_roots : vcCutP168.cell.rootsOK vcCutP168Roots = true := by decide +kernel

def vcCutP169 : SideCornerEntry := ⟨3/80, 9/40, 1/10, #v[66653583/10000000000, 29231959/5000000000, 24242951/10000000000]⟩
abbrev vcCutP169Roots := vcOuterP169Roots
theorem vcCutP169_roots : vcCutP169.cell.rootsOK vcCutP169Roots = true := by decide +kernel

def vcCutP170 : SideCornerEntry := ⟨3/80, 19/80, 0, #v[55979711/10000000000, 61163/12500000, 21255347/10000000000]⟩
abbrev vcCutP170Roots := vcOuterP170Roots
theorem vcCutP170_roots : vcCutP170.cell.rootsOK vcCutP170Roots = true := by decide +kernel

def vcCutP171 : SideCornerEntry := ⟨3/80, 19/80, 1/40, #v[57294893/10000000000, 49920433/10000000000, 21558091/10000000000]⟩
abbrev vcCutP171Roots := vcOuterP171Roots
theorem vcCutP171_roots : vcCutP171.cell.rootsOK vcCutP171Roots = true := by decide +kernel

def vcCutP172 : SideCornerEntry := ⟨3/80, 19/80, 1/20, #v[11745139/2000000000, 51034277/10000000000, 21926359/10000000000]⟩
abbrev vcCutP172Roots := vcOuterP172Roots
theorem vcCutP172_roots : vcCutP172.cell.rootsOK vcCutP172Roots = true := by decide +kernel

def vcCutP173 : SideCornerEntry := ⟨3/80, 19/80, 3/40, #v[3012537/500000000, 52248161/10000000000, 4469549/2000000000]⟩
abbrev vcCutP173Roots := vcOuterP173Roots
theorem vcCutP173_roots : vcCutP173.cell.rootsOK vcCutP173Roots = true := by decide +kernel

def vcCutP174 : SideCornerEntry := ⟨3/80, 19/80, 1/10, #v[3012537/500000000, 52248161/10000000000, 4469549/2000000000]⟩
abbrev vcCutP174Roots := vcOuterP174Roots
theorem vcCutP174_roots : vcCutP174.cell.rootsOK vcCutP174Roots = true := by decide +kernel

def vcCutP175 : SideCornerEntry := ⟨3/80, 1/4, 0, #v[10264781/2000000000, 22171467/5000000000, 19912441/10000000000]⟩
abbrev vcCutP175Roots := vcOuterP175Roots
theorem vcCutP175_roots : vcCutP175.cell.rootsOK vcCutP175Roots = true := by decide +kernel

def vcCutP176 : SideCornerEntry := ⟨3/80, 1/4, 1/40, #v[10484989/2000000000, 22572089/5000000000, 10074459/5000000000]⟩
abbrev vcCutP176Roots := vcOuterP176Roots
theorem vcCutP176_roots : vcCutP176.cell.rootsOK vcCutP176Roots = true := by decide +kernel

def vcCutP177 : SideCornerEntry := ⟨3/80, 1/4, 1/20, #v[6705313/1250000000, 23033969/5000000000, 10226221/5000000000]⟩
abbrev vcCutP177Roots := vcOuterP177Roots
theorem vcCutP177_roots : vcCutP177.cell.rootsOK vcCutP177Roots = true := by decide +kernel

def vcCutP178 : SideCornerEntry := ⟨3/80, 1/4, 3/40, #v[27477557/5000000000, 1177269/250000000, 416207/200000000]⟩
abbrev vcCutP178Roots := vcOuterP178Roots
theorem vcCutP178_roots : vcCutP178.cell.rootsOK vcCutP178Roots = true := by decide +kernel

def vcCutP179 : SideCornerEntry := ⟨3/80, 1/4, 1/10, #v[27477557/5000000000, 1177269/250000000, 416207/200000000]⟩
abbrev vcCutP179Roots := vcOuterP179Roots
theorem vcCutP179_roots : vcCutP179.cell.rootsOK vcCutP179Roots = true := by decide +kernel

def vcCutP180 : SideCornerEntry := ⟨3/80, 21/80, 0, #v[5926787/1250000000, 20242927/5000000000, 18817393/10000000000]⟩
abbrev vcCutP180Roots := vcOuterP180Roots
theorem vcCutP180_roots : vcCutP180.cell.rootsOK vcCutP180Roots = true := by decide +kernel

def vcCutP181 : SideCornerEntry := ⟨3/80, 21/80, 1/40, #v[48337239/10000000000, 8226453/2000000000, 1187371/625000000]⟩
abbrev vcCutP181Roots := vcOuterP181Roots
theorem vcCutP181_roots : vcCutP181.cell.rootsOK vcCutP181Roots = true := by decide +kernel

def vcCutP182 : SideCornerEntry := ⟨3/80, 21/80, 1/20, #v[24689077/5000000000, 83801/20000000, 4811903/2500000000]⟩
abbrev vcCutP182Roots := vcOuterP182Roots
theorem vcCutP182_roots : vcCutP182.cell.rootsOK vcCutP182Roots = true := by decide +kernel

def vcCutP183 : SideCornerEntry := ⟨3/80, 21/80, 3/40, #v[12628807/2500000000, 1069179/250000000, 4888541/2500000000]⟩
abbrev vcCutP183Roots := vcOuterP183Roots
theorem vcCutP183_roots : vcCutP183.cell.rootsOK vcCutP183Roots = true := by decide +kernel

def vcCutP184 : SideCornerEntry := ⟨3/80, 21/80, 1/10, #v[12628807/2500000000, 1069179/250000000, 4888541/2500000000]⟩
abbrev vcCutP184Roots := vcOuterP184Roots
theorem vcCutP184_roots : vcCutP184.cell.rootsOK vcCutP184Roots = true := by decide +kernel

def vcCutP185 : SideCornerEntry := ⟨3/80, 11/40, 0, #v[11025961/2500000000, 37212029/10000000000, 4479933/2500000000]⟩
abbrev vcCutP185Roots := vcOuterP185Roots
theorem vcCutP185_roots : vcCutP185.cell.rootsOK vcCutP185Roots = true := by decide +kernel

def vcCutP186 : SideCornerEntry := ⟨3/80, 11/40, 1/40, #v[5609809/1250000000, 18865773/5000000000, 1805367/1000000000]⟩
abbrev vcCutP186Roots := vcOuterP186Roots
theorem vcCutP186_roots : vcCutP186.cell.rootsOK vcCutP186Roots = true := by decide +kernel

def vcCutP187 : SideCornerEntry := ⟨3/80, 11/40, 1/20, #v[22885437/5000000000, 9592657/2500000000, 4564391/2500000000]⟩
abbrev vcCutP187Roots := vcOuterP187Roots
theorem vcCutP187_roots : vcCutP187.cell.rootsOK vcCutP187Roots = true := by decide +kernel

def vcCutP188 : SideCornerEntry := ⟨3/80, 11/40, 3/40, #v[46759451/10000000000, 19553241/5000000000, 18519927/10000000000]⟩
abbrev vcCutP188Roots := vcOuterP188Roots
theorem vcCutP188_roots : vcCutP188.cell.rootsOK vcCutP188Roots = true := by decide +kernel

def vcCutP189 : SideCornerEntry := ⟨3/80, 11/40, 1/10, #v[46759451/10000000000, 19553241/5000000000, 18519927/10000000000]⟩
abbrev vcCutP189Roots := vcOuterP189Roots
theorem vcCutP189_roots : vcCutP189.cell.rootsOK vcCutP189Roots = true := by decide +kernel

def vcCutP190 : SideCornerEntry := ⟨3/80, 23/80, 0, #v[20640613/5000000000, 34410363/10000000000, 1718329/1000000000]⟩
abbrev vcCutP190Roots := vcOuterP190Roots
theorem vcCutP190_roots : vcCutP190.cell.rootsOK vcCutP190Roots = true := by decide +kernel

def vcCutP191 : SideCornerEntry := ⟨3/80, 23/80, 1/40, #v[10482361/2500000000, 4352913/1250000000, 8638079/5000000000]⟩
abbrev vcCutP191Roots := vcOuterP191Roots
theorem vcCutP191_roots : vcCutP191.cell.rootsOK vcCutP191Roots = true := by decide +kernel

def vcCutPoints160 : Array SideCornerEntry := #[
  vcCutP160,
  vcCutP161,
  vcCutP162,
  vcCutP163,
  vcCutP164,
  vcCutP165,
  vcCutP166,
  vcCutP167,
  vcCutP168,
  vcCutP169,
  vcCutP170,
  vcCutP171,
  vcCutP172,
  vcCutP173,
  vcCutP174,
  vcCutP175,
  vcCutP176,
  vcCutP177,
  vcCutP178,
  vcCutP179,
  vcCutP180,
  vcCutP181,
  vcCutP182,
  vcCutP183,
  vcCutP184,
  vcCutP185,
  vcCutP186,
  vcCutP187,
  vcCutP188,
  vcCutP189,
  vcCutP190,
  vcCutP191]

end HlawkaSchatten.BelowExponent.Vertex
