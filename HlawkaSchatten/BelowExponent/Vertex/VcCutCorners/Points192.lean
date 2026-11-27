/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.VcCornerData.Points192

/-! Checked corner data shared by the vertex middle and band regions: `Points192`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

def vcCutP192 : SideCornerEntry := ⟨3/80, 23/80, 1/20, #v[42695817/10000000000, 552409/156250000, 17440919/10000000000]⟩
abbrev vcCutP192Roots := vcOuterP192Roots
theorem vcCutP192_roots : vcCutP192.cell.rootsOK vcCutP192Roots = true := by decide +kernel

def vcCutP193 : SideCornerEntry := ⟨3/80, 23/80, 3/40, #v[43558717/10000000000, 35980533/10000000000, 4416277/2500000000]⟩
abbrev vcCutP193Roots := vcOuterP193Roots
theorem vcCutP193_roots : vcCutP193.cell.rootsOK vcCutP193Roots = true := by decide +kernel

def vcCutP194 : SideCornerEntry := ⟨3/80, 23/80, 1/10, #v[43558717/10000000000, 35980533/10000000000, 4416277/2500000000]⟩
abbrev vcCutP194Roots := vcOuterP194Roots
theorem vcCutP194_roots : vcCutP194.cell.rootsOK vcCutP194Roots = true := by decide +kernel

def vcCutP195 : SideCornerEntry := ⟨3/80, 3/10, 0, #v[9714707/2500000000, 15997767/5000000000, 16579857/10000000000]⟩
abbrev vcCutP195Roots := vcOuterP195Roots
theorem vcCutP195_roots : vcCutP195.cell.rootsOK vcCutP195Roots = true := by decide +kernel

def vcCutP196 : SideCornerEntry := ⟨3/80, 3/10, 1/40, #v[39399463/10000000000, 16159723/5000000000, 16637103/10000000000]⟩
abbrev vcCutP196Roots := vcOuterP196Roots
theorem vcCutP196_roots : vcCutP196.cell.rootsOK vcCutP196Roots = true := by decide +kernel

def vcCutP197 : SideCornerEntry := ⟨3/80, 3/10, 1/20, #v[40058553/10000000000, 32759639/10000000000, 16768343/10000000000]⟩
abbrev vcCutP197Roots := vcOuterP197Roots
theorem vcCutP197_roots : vcCutP197.cell.rootsOK vcCutP197Roots = true := by decide +kernel

def vcCutP198 : SideCornerEntry := ⟨3/80, 3/10, 3/40, #v[1632577/400000000, 8323499/2500000000, 3391891/2000000000]⟩
abbrev vcCutP198Roots := vcOuterP198Roots
theorem vcCutP198_roots : vcCutP198.cell.rootsOK vcCutP198Roots = true := by decide +kernel

def vcCutP199 : SideCornerEntry := ⟨3/80, 3/10, 1/10, #v[1632577/400000000, 8323499/2500000000, 3391891/2000000000]⟩
abbrev vcCutP199Roots := vcOuterP199Roots
theorem vcCutP199_roots : vcCutP199.cell.rootsOK vcCutP199Roots = true := by decide +kernel

def vcCutP200 : SideCornerEntry := ⟨3/80, 5/16, 0, #v[18384821/5000000000, 14952227/5000000000, 4021303/2500000000]⟩
abbrev vcCutP200Roots := vcOuterP200Roots
theorem vcCutP200_roots : vcCutP200.cell.rootsOK vcCutP200Roots = true := by decide +kernel

def vcCutP201 : SideCornerEntry := ⟨3/80, 5/16, 1/40, #v[9304561/2500000000, 30153477/10000000000, 3222239/2000000000]⟩
abbrev vcCutP201Roots := vcOuterP201Roots
theorem vcCutP201_roots : vcCutP201.cell.rootsOK vcCutP201Roots = true := by decide +kernel

def vcCutP202 : SideCornerEntry := ⟨3/80, 5/16, 1/20, #v[7557103/2000000000, 15258551/5000000000, 4053333/2500000000]⟩
abbrev vcCutP202Roots := vcOuterP202Roots
theorem vcCutP202_roots : vcCutP202.cell.rootsOK vcCutP202Roots = true := by decide +kernel

def vcCutP203 : SideCornerEntry := ⟨3/80, 5/16, 3/40, #v[38449761/10000000000, 1238941/400000000, 16375863/10000000000]⟩
abbrev vcCutP203Roots := vcOuterP203Roots
theorem vcCutP203_roots : vcCutP203.cell.rootsOK vcCutP203Roots = true := by decide +kernel

def vcCutP204 : SideCornerEntry := ⟨3/80, 5/16, 1/10, #v[38449761/10000000000, 1238941/400000000, 16375863/10000000000]⟩
abbrev vcCutP204Roots := vcOuterP204Roots
theorem vcCutP204_roots : vcCutP204.cell.rootsOK vcCutP204Roots = true := by decide +kernel

def vcCutP205 : SideCornerEntry := ⟨3/80, 13/40, 0, #v[34959847/10000000000, 28077887/10000000000, 7841331/5000000000]⟩
abbrev vcCutP205Roots := vcOuterP205Roots
theorem vcCutP205_roots : vcCutP205.cell.rootsOK vcCutP205Roots = true := by decide +kernel

def vcCutP206 : SideCornerEntry := ⟨3/80, 13/40, 1/40, #v[4416159/1250000000, 883231/312500000, 7841331/5000000000]⟩
abbrev vcCutP206Roots := vcOuterP206Roots
theorem vcCutP206_roots : vcCutP206.cell.rootsOK vcCutP206Roots = true := by decide +kernel

def vcCutP207 : SideCornerEntry := ⟨3/80, 13/40, 1/20, #v[35817531/10000000000, 892563/312500000, 492441/312500000]⟩
abbrev vcCutP207Roots := vcOuterP207Roots
theorem vcCutP207_roots : vcCutP207.cell.rootsOK vcCutP207Roots = true := by decide +kernel

def vcCutP208 : SideCornerEntry := ⟨3/80, 13/40, 3/40, #v[36402909/10000000000, 1809507/625000000, 993497/625000000]⟩
abbrev vcCutP208Roots := vcOuterP208Roots
theorem vcCutP208_roots : vcCutP208.cell.rootsOK vcCutP208Roots = true := by decide +kernel

def vcCutP209 : SideCornerEntry := ⟨3/80, 13/40, 1/10, #v[36402909/10000000000, 1809507/625000000, 993497/625000000]⟩
abbrev vcCutP209Roots := vcOuterP209Roots
theorem vcCutP209_roots : vcCutP209.cell.rootsOK vcCutP209Roots = true := by decide +kernel

def vcCutP210 : SideCornerEntry := ⟨3/80, 27/80, 0, #v[8346789/2500000000, 26473523/10000000000, 7679723/5000000000]⟩
abbrev vcCutP210Roots := vcOuterP210Roots
theorem vcCutP210_roots : vcCutP210.cell.rootsOK vcCutP210Roots = true := by decide +kernel

def vcCutP211 : SideCornerEntry := ⟨3/80, 27/80, 1/40, #v[3368821/1000000000, 26605573/10000000000, 7679723/5000000000]⟩
abbrev vcCutP211Roots := vcOuterP211Roots
theorem vcCutP211_roots : vcCutP211.cell.rootsOK vcCutP211Roots = true := by decide +kernel

def vcCutP212 : SideCornerEntry := ⟨3/80, 27/80, 1/20, #v[3410823/1000000000, 5369749/2000000000, 7694317/5000000000]⟩
abbrev vcCutP212Roots := vcOuterP212Roots
theorem vcCutP212_roots : vcCutP212.cell.rootsOK vcCutP212Roots = true := by decide +kernel

def vcCutP213 : SideCornerEntry := ⟨3/80, 27/80, 3/40, #v[17313859/5000000000, 13591113/5000000000, 620191/400000000]⟩
abbrev vcCutP213Roots := vcOuterP213Roots
theorem vcCutP213_roots : vcCutP213.cell.rootsOK vcCutP213Roots = true := by decide +kernel

def vcCutP214 : SideCornerEntry := ⟨3/80, 27/80, 1/10, #v[17313859/5000000000, 13591113/5000000000, 620191/400000000]⟩
abbrev vcCutP214Roots := vcOuterP214Roots
theorem vcCutP214_roots : vcCutP214.cell.rootsOK vcCutP214Roots = true := by decide +kernel

def vcCutP215 : SideCornerEntry := ⟨3/80, 7/20, 0, #v[6403517/2000000000, 25057739/10000000000, 236013/156250000]⟩
abbrev vcCutP215Roots := vcOuterP215Roots
theorem vcCutP215_roots : vcCutP215.cell.rootsOK vcCutP215Roots = true := by decide +kernel

def vcCutP216 : SideCornerEntry := ⟨3/80, 7/20, 1/40, #v[32259457/10000000000, 25144507/10000000000, 236013/156250000]⟩
abbrev vcCutP216Roots := vcOuterP216Roots
theorem vcCutP216_roots : vcCutP216.cell.rootsOK vcCutP216Roots = true := by decide +kernel

def vcCutP217 : SideCornerEntry := ⟨3/80, 7/20, 1/20, #v[32620401/10000000000, 25340671/10000000000, 15093437/10000000000]⟩
abbrev vcCutP217Roots := vcOuterP217Roots
theorem vcCutP217_roots : vcCutP217.cell.rootsOK vcCutP217Roots = true := by decide +kernel

def vcCutP218 : SideCornerEntry := ⟨3/80, 7/20, 3/40, #v[33087307/10000000000, 25625747/10000000000, 15200179/10000000000]⟩
abbrev vcCutP218Roots := vcOuterP218Roots
theorem vcCutP218_roots : vcCutP218.cell.rootsOK vcCutP218Roots = true := by decide +kernel

def vcCutP219 : SideCornerEntry := ⟨3/80, 7/20, 1/10, #v[33087307/10000000000, 25625747/10000000000, 15200179/10000000000]⟩
abbrev vcCutP219Roots := vcOuterP219Roots
theorem vcCutP219_roots : vcCutP219.cell.rootsOK vcCutP219Roots = true := by decide +kernel

def vcCutP220 : SideCornerEntry := ⟨3/80, 29/80, 0, #v[30826897/10000000000, 23803291/10000000000, 14910867/10000000000]⟩
abbrev vcCutP220Roots := vcOuterP220Roots
theorem vcCutP220_roots : vcCutP220.cell.rootsOK vcCutP220Roots = true := by decide +kernel

def vcCutP221 : SideCornerEntry := ⟨3/80, 29/80, 1/40, #v[15512101/5000000000, 11925901/5000000000, 14910867/10000000000]⟩
abbrev vcCutP221Roots := vcOuterP221Roots
theorem vcCutP221_roots : vcCutP221.cell.rootsOK vcCutP221Roots = true := by decide +kernel

def vcCutP222 : SideCornerEntry := ⟨3/80, 29/80, 1/20, #v[31340253/10000000000, 750253/312500000, 744479/500000000]⟩
abbrev vcCutP222Roots := vcOuterP222Roots
theorem vcCutP222_roots : vcCutP222.cell.rootsOK vcCutP222Roots = true := by decide +kernel

def vcCutP223 : SideCornerEntry := ⟨3/80, 29/80, 3/40, #v[31759927/10000000000, 24251983/10000000000, 299691/200000000]⟩
abbrev vcCutP223Roots := vcOuterP223Roots
theorem vcCutP223_roots : vcCutP223.cell.rootsOK vcCutP223Roots = true := by decide +kernel

def vcCutPoints192 : Array SideCornerEntry := #[
  vcCutP192,
  vcCutP193,
  vcCutP194,
  vcCutP195,
  vcCutP196,
  vcCutP197,
  vcCutP198,
  vcCutP199,
  vcCutP200,
  vcCutP201,
  vcCutP202,
  vcCutP203,
  vcCutP204,
  vcCutP205,
  vcCutP206,
  vcCutP207,
  vcCutP208,
  vcCutP209,
  vcCutP210,
  vcCutP211,
  vcCutP212,
  vcCutP213,
  vcCutP214,
  vcCutP215,
  vcCutP216,
  vcCutP217,
  vcCutP218,
  vcCutP219,
  vcCutP220,
  vcCutP221,
  vcCutP222,
  vcCutP223]

end HlawkaSchatten.BelowExponent.Vertex
