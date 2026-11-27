/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.VcCornerData.Points064

/-! Checked corner data shared by the vertex middle and band regions: `Points064`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

def vcCutP064 : SideCornerEntry := ⟨1/40, 5/16, 1/10, #v[38449761/10000000000, 1238941/400000000, 8080343/5000000000]⟩
abbrev vcCutP064Roots := vcOuterP064Roots
theorem vcCutP064_roots : vcCutP064.cell.rootsOK vcCutP064Roots = true := by decide +kernel

def vcCutP065 : SideCornerEntry := ⟨1/40, 13/40, 0, #v[34959847/10000000000, 28077887/10000000000, 15536879/10000000000]⟩
abbrev vcCutP065Roots := vcOuterP065Roots
theorem vcCutP065_roots : vcCutP065.cell.rootsOK vcCutP065Roots = true := by decide +kernel

def vcCutP066 : SideCornerEntry := ⟨1/40, 13/40, 1/40, #v[4416159/1250000000, 883231/312500000, 15536879/10000000000]⟩
abbrev vcCutP066Roots := vcOuterP066Roots
theorem vcCutP066_roots : vcCutP066.cell.rootsOK vcCutP066Roots = true := by decide +kernel

def vcCutP067 : SideCornerEntry := ⟨1/40, 13/40, 1/20, #v[35817531/10000000000, 892563/312500000, 3115457/2000000000]⟩
abbrev vcCutP067Roots := vcOuterP067Roots
theorem vcCutP067_roots : vcCutP067.cell.rootsOK vcCutP067Roots = true := by decide +kernel

def vcCutP068 : SideCornerEntry := ⟨1/40, 13/40, 3/40, #v[36402909/10000000000, 1809507/625000000, 15696017/10000000000]⟩
abbrev vcCutP068Roots := vcOuterP068Roots
theorem vcCutP068_roots : vcCutP068.cell.rootsOK vcCutP068Roots = true := by decide +kernel

def vcCutP069 : SideCornerEntry := ⟨1/40, 13/40, 1/10, #v[36402909/10000000000, 1809507/625000000, 15696017/10000000000]⟩
abbrev vcCutP069Roots := vcOuterP069Roots
theorem vcCutP069_roots : vcCutP069.cell.rootsOK vcCutP069Roots = true := by decide +kernel

def vcCutP070 : SideCornerEntry := ⟨1/40, 27/80, 0, #v[8346789/2500000000, 26473523/10000000000, 7610039/5000000000]⟩
abbrev vcCutP070Roots := vcOuterP070Roots
theorem vcCutP070_roots : vcCutP070.cell.rootsOK vcCutP070Roots = true := by decide +kernel

def vcCutP071 : SideCornerEntry := ⟨1/40, 27/80, 1/40, #v[3368821/1000000000, 26605573/10000000000, 7610039/5000000000]⟩
abbrev vcCutP071Roots := vcOuterP071Roots
theorem vcCutP071_roots : vcCutP071.cell.rootsOK vcCutP071Roots = true := by decide +kernel

def vcCutP072 : SideCornerEntry := ⟨1/40, 27/80, 1/20, #v[3410823/1000000000, 5369749/2000000000, 3803851/2500000000]⟩
abbrev vcCutP072Roots := vcOuterP072Roots
theorem vcCutP072_roots : vcCutP072.cell.rootsOK vcCutP072Roots = true := by decide +kernel

def vcCutP073 : SideCornerEntry := ⟨1/40, 27/80, 3/40, #v[17313859/5000000000, 13591113/5000000000, 15313907/10000000000]⟩
abbrev vcCutP073Roots := vcOuterP073Roots
theorem vcCutP073_roots : vcCutP073.cell.rootsOK vcCutP073Roots = true := by decide +kernel

def vcCutP074 : SideCornerEntry := ⟨1/40, 27/80, 1/10, #v[17313859/5000000000, 13591113/5000000000, 15313907/10000000000]⟩
abbrev vcCutP074Roots := vcOuterP074Roots
theorem vcCutP074_roots : vcCutP074.cell.rootsOK vcCutP074Roots = true := by decide +kernel

def vcCutP075 : SideCornerEntry := ⟨1/40, 7/20, 0, #v[6403517/2000000000, 25057739/10000000000, 14967473/10000000000]⟩
abbrev vcCutP075Roots := vcOuterP075Roots
theorem vcCutP075_roots : vcCutP075.cell.rootsOK vcCutP075Roots = true := by decide +kernel

def vcCutP076 : SideCornerEntry := ⟨1/40, 7/20, 1/40, #v[32259457/10000000000, 25144507/10000000000, 14967473/10000000000]⟩
abbrev vcCutP076Roots := vcOuterP076Roots
theorem vcCutP076_roots : vcCutP076.cell.rootsOK vcCutP076Roots = true := by decide +kernel

def vcCutP077 : SideCornerEntry := ⟨1/40, 7/20, 1/20, #v[32620401/10000000000, 25340671/10000000000, 14922857/10000000000]⟩
abbrev vcCutP077Roots := vcOuterP077Roots
theorem vcCutP077_roots : vcCutP077.cell.rootsOK vcCutP077Roots = true := by decide +kernel

def vcCutP078 : SideCornerEntry := ⟨1/40, 7/20, 3/40, #v[33087307/10000000000, 25625747/10000000000, 3752659/2500000000]⟩
abbrev vcCutP078Roots := vcOuterP078Roots
theorem vcCutP078_roots : vcCutP078.cell.rootsOK vcCutP078Roots = true := by decide +kernel

def vcCutP079 : SideCornerEntry := ⟨1/40, 7/20, 1/10, #v[33087307/10000000000, 25625747/10000000000, 3752659/2500000000]⟩
abbrev vcCutP079Roots := vcOuterP079Roots
theorem vcCutP079_roots : vcCutP079.cell.rootsOK vcCutP079Roots = true := by decide +kernel

def vcCutP080 : SideCornerEntry := ⟨1/40, 29/80, 0, #v[30826897/10000000000, 23803291/10000000000, 14777273/10000000000]⟩
abbrev vcCutP080Roots := vcOuterP080Roots
theorem vcCutP080_roots : vcCutP080.cell.rootsOK vcCutP080Roots = true := by decide +kernel

def vcCutP081 : SideCornerEntry := ⟨1/40, 29/80, 1/40, #v[15512101/5000000000, 11925901/5000000000, 14777273/10000000000]⟩
abbrev vcCutP081Roots := vcOuterP081Roots
theorem vcCutP081_roots : vcCutP081.cell.rootsOK vcCutP081Roots = true := by decide +kernel

def vcCutP082 : SideCornerEntry := ⟨1/40, 29/80, 1/20, #v[31340253/10000000000, 750253/312500000, 7359779/5000000000]⟩
abbrev vcCutP082Roots := vcOuterP082Roots
theorem vcCutP082_roots : vcCutP082.cell.rootsOK vcCutP082Roots = true := by decide +kernel

def vcCutP083 : SideCornerEntry := ⟨1/40, 29/80, 3/40, #v[31759927/10000000000, 24251983/10000000000, 739771/500000000]⟩
abbrev vcCutP083Roots := vcOuterP083Roots
theorem vcCutP083_roots : vcCutP083.cell.rootsOK vcCutP083Roots = true := by decide +kernel

def vcCutP084 : SideCornerEntry := ⟨1/40, 29/80, 1/10, #v[31759927/10000000000, 24251983/10000000000, 739771/500000000]⟩
abbrev vcCutP084Roots := vcOuterP084Roots
theorem vcCutP084_roots : vcCutP084.cell.rootsOK vcCutP084Roots = true := by decide +kernel

def vcCutP085 : SideCornerEntry := ⟨1/40, 3/8, 0, #v[3725299/1250000000, 1134471/500000000, 2932089/2000000000]⟩
abbrev vcCutP085Roots := vcOuterP085Roots
theorem vcCutP085_roots : vcCutP085.cell.rootsOK vcCutP085Roots = true := by decide +kernel

def vcCutP086 : SideCornerEntry := ⟨1/40, 3/8, 1/40, #v[29955921/10000000000, 44347/19531250, 2932089/2000000000]⟩
abbrev vcCutP086Roots := vcOuterP086Roots
theorem vcCutP086_roots : vcCutP086.cell.rootsOK vcCutP086Roots = true := by decide +kernel

def vcCutP087 : SideCornerEntry := ⟨1/40, 3/8, 1/20, #v[18893/6250000, 22827883/10000000000, 7288497/5000000000]⟩
abbrev vcCutP087Roots := vcOuterP087Roots
theorem vcCutP087_roots : vcCutP087.cell.rootsOK vcCutP087Roots = true := by decide +kernel

def vcCutP088 : SideCornerEntry := ⟨1/40, 3/8, 3/40, #v[30605847/10000000000, 1439769/625000000, 14636941/10000000000]⟩
abbrev vcCutP088Roots := vcOuterP088Roots
theorem vcCutP088_roots : vcCutP088.cell.rootsOK vcCutP088Roots = true := by decide +kernel

def vcCutP089 : SideCornerEntry := ⟨1/40, 3/8, 1/10, #v[30605847/10000000000, 1439769/625000000, 14636941/10000000000]⟩
abbrev vcCutP089Roots := vcOuterP089Roots
theorem vcCutP089_roots : vcCutP089.cell.rootsOK vcCutP089Roots = true := by decide +kernel

def vcCutP090 : SideCornerEntry := ⟨1/40, 31/80, 0, #v[28912843/10000000000, 21696529/10000000000, 14589983/10000000000]⟩
abbrev vcCutP090Roots := vcOuterP090Roots
theorem vcCutP090_roots : vcCutP090.cell.rootsOK vcCutP090Roots = true := by decide +kernel

def vcCutP091 : SideCornerEntry := ⟨1/40, 31/80, 1/40, #v[29028589/10000000000, 21696529/10000000000, 14589983/10000000000]⟩
abbrev vcCutP091Roots := vcOuterP091Roots
theorem vcCutP091_roots : vcCutP091.cell.rootsOK vcCutP091Roots = true := by decide +kernel

def vcCutP092 : SideCornerEntry := ⟨1/40, 31/80, 1/20, #v[914541/312500000, 10889331/5000000000, 14492979/10000000000]⟩
abbrev vcCutP092Roots := vcOuterP092Roots
theorem vcCutP092_roots : vcCutP092.cell.rootsOK vcCutP092Roots = true := by decide +kernel

def vcCutP093 : SideCornerEntry := ⟨1/40, 31/80, 3/40, #v[14802193/5000000000, 5489151/2500000000, 7265107/5000000000]⟩
abbrev vcCutP093Roots := vcOuterP093Roots
theorem vcCutP093_roots : vcCutP093.cell.rootsOK vcCutP093Roots = true := by decide +kernel

def vcCutP094 : SideCornerEntry := ⟨1/40, 31/80, 1/10, #v[14802193/5000000000, 5489151/2500000000, 7265107/5000000000]⟩
abbrev vcCutP094Roots := vcOuterP094Roots
theorem vcCutP094_roots : vcCutP094.cell.rootsOK vcCutP094Roots = true := by decide +kernel

def vcCutP095 : SideCornerEntry := ⟨1/40, 2/5, 0, #v[28143447/10000000000, 10404613/5000000000, 3643897/2500000000]⟩
abbrev vcCutP095Roots := vcOuterP095Roots
theorem vcCutP095_roots : vcCutP095.cell.rootsOK vcCutP095Roots = true := by decide +kernel

def vcCutPoints064 : Array SideCornerEntry := #[
  vcCutP064,
  vcCutP065,
  vcCutP066,
  vcCutP067,
  vcCutP068,
  vcCutP069,
  vcCutP070,
  vcCutP071,
  vcCutP072,
  vcCutP073,
  vcCutP074,
  vcCutP075,
  vcCutP076,
  vcCutP077,
  vcCutP078,
  vcCutP079,
  vcCutP080,
  vcCutP081,
  vcCutP082,
  vcCutP083,
  vcCutP084,
  vcCutP085,
  vcCutP086,
  vcCutP087,
  vcCutP088,
  vcCutP089,
  vcCutP090,
  vcCutP091,
  vcCutP092,
  vcCutP093,
  vcCutP094,
  vcCutP095]

end HlawkaSchatten.BelowExponent.Vertex
