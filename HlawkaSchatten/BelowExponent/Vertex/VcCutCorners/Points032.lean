/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.VcCornerData.Points032

/-! Checked corner data shared by the vertex middle and band regions: `Points032`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

def vcCutP032 : SideCornerEntry := ⟨1/40, 19/80, 1/20, #v[11745139/2000000000, 51034277/10000000000, 10693339/5000000000]⟩
abbrev vcCutP032Roots := vcOuterP032Roots
theorem vcCutP032_roots : vcCutP032.cell.rootsOK vcCutP032Roots = true := by decide +kernel

def vcCutP033 : SideCornerEntry := ⟨1/40, 19/80, 3/40, #v[3012537/500000000, 52248161/10000000000, 21766909/10000000000]⟩
abbrev vcCutP033Roots := vcOuterP033Roots
theorem vcCutP033_roots : vcCutP033.cell.rootsOK vcCutP033Roots = true := by decide +kernel

def vcCutP034 : SideCornerEntry := ⟨1/40, 19/80, 1/10, #v[3012537/500000000, 52248161/10000000000, 21766909/10000000000]⟩
abbrev vcCutP034Roots := vcOuterP034Roots
theorem vcCutP034_roots : vcCutP034.cell.rootsOK vcCutP034Roots = true := by decide +kernel

def vcCutP035 : SideCornerEntry := ⟨1/40, 1/4, 0, #v[10264781/2000000000, 22171467/5000000000, 3910357/2000000000]⟩
abbrev vcCutP035Roots := vcOuterP035Roots
theorem vcCutP035_roots : vcCutP035.cell.rootsOK vcCutP035Roots = true := by decide +kernel

def vcCutP036 : SideCornerEntry := ⟨1/40, 1/4, 1/40, #v[10484989/2000000000, 22572089/5000000000, 19754479/10000000000]⟩
abbrev vcCutP036Roots := vcOuterP036Roots
theorem vcCutP036_roots : vcCutP036.cell.rootsOK vcCutP036Roots = true := by decide +kernel

def vcCutP037 : SideCornerEntry := ⟨1/40, 1/4, 1/20, #v[6705313/1250000000, 23033969/5000000000, 312873/156250000]⟩
abbrev vcCutP037Roots := vcOuterP037Roots
theorem vcCutP037_roots : vcCutP037.cell.rootsOK vcCutP037Roots = true := by decide +kernel

def vcCutP038 : SideCornerEntry := ⟨1/40, 1/4, 3/40, #v[27477557/5000000000, 1177269/250000000, 20347353/10000000000]⟩
abbrev vcCutP038Roots := vcOuterP038Roots
theorem vcCutP038_roots : vcCutP038.cell.rootsOK vcCutP038Roots = true := by decide +kernel

def vcCutP039 : SideCornerEntry := ⟨1/40, 1/4, 1/10, #v[27477557/5000000000, 1177269/250000000, 20347353/10000000000]⟩
abbrev vcCutP039Roots := vcOuterP039Roots
theorem vcCutP039_roots : vcCutP039.cell.rootsOK vcCutP039Roots = true := by decide +kernel

def vcCutP040 : SideCornerEntry := ⟨1/40, 21/80, 0, #v[5926787/1250000000, 20242927/5000000000, 741107/400000000]⟩
abbrev vcCutP040Roots := vcOuterP040Roots
theorem vcCutP040_roots : vcCutP040.cell.rootsOK vcCutP040Roots = true := by decide +kernel

def vcCutP041 : SideCornerEntry := ⟨1/40, 21/80, 1/40, #v[48337239/10000000000, 8226453/2000000000, 4669927/2500000000]⟩
abbrev vcCutP041Roots := vcOuterP041Roots
theorem vcCutP041_roots : vcCutP041.cell.rootsOK vcCutP041Roots = true := by decide +kernel

def vcCutP042 : SideCornerEntry := ⟨1/40, 21/80, 1/20, #v[24689077/5000000000, 83801/20000000, 18900533/10000000000]⟩
abbrev vcCutP042Roots := vcOuterP042Roots
theorem vcCutP042_roots : vcCutP042.cell.rootsOK vcCutP042Roots = true := by decide +kernel

def vcCutP043 : SideCornerEntry := ⟨1/40, 21/80, 3/40, #v[12628807/2500000000, 1069179/250000000, 19177/10000000]⟩
abbrev vcCutP043Roots := vcOuterP043Roots
theorem vcCutP043_roots : vcCutP043.cell.rootsOK vcCutP043Roots = true := by decide +kernel

def vcCutP044 : SideCornerEntry := ⟨1/40, 21/80, 1/10, #v[12628807/2500000000, 1069179/250000000, 19177/10000000]⟩
abbrev vcCutP044Roots := vcOuterP044Roots
theorem vcCutP044_roots : vcCutP044.cell.rootsOK vcCutP044Roots = true := by decide +kernel

def vcCutP045 : SideCornerEntry := ⟨1/40, 11/40, 0, #v[11025961/2500000000, 37212029/10000000000, 3536367/2000000000]⟩
abbrev vcCutP045Roots := vcOuterP045Roots
theorem vcCutP045_roots : vcCutP045.cell.rootsOK vcCutP045Roots = true := by decide +kernel

def vcCutP046 : SideCornerEntry := ⟨1/40, 11/40, 1/40, #v[5609809/1250000000, 18865773/5000000000, 17791237/10000000000]⟩
abbrev vcCutP046Roots := vcOuterP046Roots
theorem vcCutP046_roots : vcCutP046.cell.rootsOK vcCutP046Roots = true := by decide +kernel

def vcCutP047 : SideCornerEntry := ⟨1/40, 11/40, 1/20, #v[22885437/5000000000, 9592657/2500000000, 8985063/5000000000]⟩
abbrev vcCutP047Roots := vcOuterP047Roots
theorem vcCutP047_roots : vcCutP047.cell.rootsOK vcCutP047Roots = true := by decide +kernel

def vcCutP048 : SideCornerEntry := ⟨1/40, 11/40, 3/40, #v[46759451/10000000000, 19553241/5000000000, 3641081/2000000000]⟩
abbrev vcCutP048Roots := vcOuterP048Roots
theorem vcCutP048_roots : vcCutP048.cell.rootsOK vcCutP048Roots = true := by decide +kernel

def vcCutP049 : SideCornerEntry := ⟨1/40, 11/40, 1/10, #v[46759451/10000000000, 19553241/5000000000, 3641081/2000000000]⟩
abbrev vcCutP049Roots := vcOuterP049Roots
theorem vcCutP049_roots : vcCutP049.cell.rootsOK vcCutP049Roots = true := by decide +kernel

def vcCutP050 : SideCornerEntry := ⟨1/40, 23/80, 0, #v[20640613/5000000000, 34410363/10000000000, 16982203/10000000000]⟩
abbrev vcCutP050Roots := vcOuterP050Roots
theorem vcCutP050_roots : vcCutP050.cell.rootsOK vcCutP050Roots = true := by decide +kernel

def vcCutP051 : SideCornerEntry := ⟨1/40, 23/80, 1/40, #v[10482361/2500000000, 4352913/1250000000, 682143/400000000]⟩
abbrev vcCutP051Roots := vcOuterP051Roots
theorem vcCutP051_roots : vcCutP051.cell.rootsOK vcCutP051Roots = true := by decide +kernel

def vcCutP052 : SideCornerEntry := ⟨1/40, 23/80, 1/20, #v[42695817/10000000000, 552409/156250000, 17195811/10000000000]⟩
abbrev vcCutP052Roots := vcOuterP052Roots
theorem vcCutP052_roots : vcCutP052.cell.rootsOK vcCutP052Roots = true := by decide +kernel

def vcCutP053 : SideCornerEntry := ⟨1/40, 23/80, 3/40, #v[43558717/10000000000, 35980533/10000000000, 17395569/10000000000]⟩
abbrev vcCutP053Roots := vcOuterP053Roots
theorem vcCutP053_roots : vcCutP053.cell.rootsOK vcCutP053Roots = true := by decide +kernel

def vcCutP054 : SideCornerEntry := ⟨1/40, 23/80, 1/10, #v[43558717/10000000000, 35980533/10000000000, 17395569/10000000000]⟩
abbrev vcCutP054Roots := vcOuterP054Roots
theorem vcCutP054_roots : vcCutP054.cell.rootsOK vcCutP054Roots = true := by decide +kernel

def vcCutP055 : SideCornerEntry := ⟨1/40, 3/10, 0, #v[9714707/2500000000, 15997767/5000000000, 8201567/5000000000]⟩
abbrev vcCutP055Roots := vcOuterP055Roots
theorem vcCutP055_roots : vcCutP055.cell.rootsOK vcCutP055Roots = true := by decide +kernel

def vcCutP056 : SideCornerEntry := ⟨1/40, 3/10, 1/40, #v[39399463/10000000000, 16159723/5000000000, 8220621/5000000000]⟩
abbrev vcCutP056Roots := vcOuterP056Roots
theorem vcCutP056_roots : vcCutP056.cell.rootsOK vcCutP056Roots = true := by decide +kernel

def vcCutP057 : SideCornerEntry := ⟨1/40, 3/10, 1/20, #v[40058553/10000000000, 32759639/10000000000, 16551601/10000000000]⟩
abbrev vcCutP057Roots := vcOuterP057Roots
theorem vcCutP057_roots : vcCutP057.cell.rootsOK vcCutP057Roots = true := by decide +kernel

def vcCutP058 : SideCornerEntry := ⟨1/40, 3/10, 3/40, #v[1632577/400000000, 8323499/2500000000, 8360309/5000000000]⟩
abbrev vcCutP058Roots := vcOuterP058Roots
theorem vcCutP058_roots : vcCutP058.cell.rootsOK vcCutP058Roots = true := by decide +kernel

def vcCutP059 : SideCornerEntry := ⟨1/40, 3/10, 1/10, #v[1632577/400000000, 8323499/2500000000, 8360309/5000000000]⟩
abbrev vcCutP059Roots := vcOuterP059Roots
theorem vcCutP059_roots : vcCutP059.cell.rootsOK vcCutP059Roots = true := by decide +kernel

def vcCutP060 : SideCornerEntry := ⟨1/40, 5/16, 0, #v[18384821/5000000000, 14952227/5000000000, 7963569/5000000000]⟩
abbrev vcCutP060Roots := vcOuterP060Roots
theorem vcCutP060_roots : vcCutP060.cell.rootsOK vcCutP060Roots = true := by decide +kernel

def vcCutP061 : SideCornerEntry := ⟨1/40, 5/16, 1/40, #v[9304561/2500000000, 30153477/10000000000, 7967983/5000000000]⟩
abbrev vcCutP061Roots := vcOuterP061Roots
theorem vcCutP061_roots : vcCutP061.cell.rootsOK vcCutP061Roots = true := by decide +kernel

def vcCutP062 : SideCornerEntry := ⟨1/40, 5/16, 1/20, #v[7557103/2000000000, 15258551/5000000000, 3203687/2000000000]⟩
abbrev vcCutP062Roots := vcOuterP062Roots
theorem vcCutP062_roots : vcCutP062.cell.rootsOK vcCutP062Roots = true := by decide +kernel

def vcCutP063 : SideCornerEntry := ⟨1/40, 5/16, 3/40, #v[38449761/10000000000, 1238941/400000000, 8080343/5000000000]⟩
abbrev vcCutP063Roots := vcOuterP063Roots
theorem vcCutP063_roots : vcCutP063.cell.rootsOK vcCutP063Roots = true := by decide +kernel

def vcCutPoints032 : Array SideCornerEntry := #[
  vcCutP032,
  vcCutP033,
  vcCutP034,
  vcCutP035,
  vcCutP036,
  vcCutP037,
  vcCutP038,
  vcCutP039,
  vcCutP040,
  vcCutP041,
  vcCutP042,
  vcCutP043,
  vcCutP044,
  vcCutP045,
  vcCutP046,
  vcCutP047,
  vcCutP048,
  vcCutP049,
  vcCutP050,
  vcCutP051,
  vcCutP052,
  vcCutP053,
  vcCutP054,
  vcCutP055,
  vcCutP056,
  vcCutP057,
  vcCutP058,
  vcCutP059,
  vcCutP060,
  vcCutP061,
  vcCutP062,
  vcCutP063]

end HlawkaSchatten.BelowExponent.Vertex
