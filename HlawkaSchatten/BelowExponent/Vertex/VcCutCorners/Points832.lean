/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.VcCornerData.Points832

/-! Checked corner data shared by the vertex middle and band regions: `Points832`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

def vcCutP832 : SideCornerEntry := ⟨1/4, 2/5, 1/36, #v[160120159/5000000000, 279989117/10000000000, 11735139/400000000]⟩
abbrev vcCutP832Roots := vcOuterP832Roots
theorem vcCutP832_roots : vcCutP832.cell.rootsOK vcCutP832Roots = true := by decide +kernel

def vcCutP833 : SideCornerEntry := ⟨1/4, 2/5, 1/18, #v[160120159/5000000000, 279989117/10000000000, 11735139/400000000]⟩
abbrev vcCutP833Roots := vcOuterP833Roots
theorem vcCutP833_roots : vcCutP833.cell.rootsOK vcCutP833Roots = true := by decide +kernel

def vcCutP834 : SideCornerEntry := ⟨11/40, 1/4, 0, #v[350655417/10000000000, 345667543/10000000000, 4818209/156250000]⟩
abbrev vcCutP834Roots := vcOuterP834Roots
theorem vcCutP834_roots : vcCutP834.cell.rootsOK vcCutP834Roots = true := by decide +kernel

def vcCutP835 : SideCornerEntry := ⟨11/40, 1/4, 1/36, #v[374797883/10000000000, 18477023/500000000, 164503183/5000000000]⟩
abbrev vcCutP835Roots := vcOuterP835Roots
theorem vcCutP835_roots : vcCutP835.cell.rootsOK vcCutP835Roots = true := by decide +kernel

def vcCutP836 : SideCornerEntry := ⟨11/40, 1/4, 1/18, #v[374797883/10000000000, 18477023/500000000, 164503183/5000000000]⟩
abbrev vcCutP836Roots := vcOuterP836Roots
theorem vcCutP836_roots : vcCutP836.cell.rootsOK vcCutP836Roots = true := by decide +kernel

def vcCutP837 : SideCornerEntry := ⟨11/40, 11/40, 0, #v[350655417/10000000000, 345667543/10000000000, 4818209/156250000]⟩
abbrev vcCutP837Roots := vcOuterP837Roots
theorem vcCutP837_roots : vcCutP837.cell.rootsOK vcCutP837Roots = true := by decide +kernel

def vcCutP838 : SideCornerEntry := ⟨11/40, 11/40, 1/36, #v[374797883/10000000000, 18477023/500000000, 164503183/5000000000]⟩
abbrev vcCutP838Roots := vcOuterP838Roots
theorem vcCutP838_roots : vcCutP838.cell.rootsOK vcCutP838Roots = true := by decide +kernel

def vcCutP839 : SideCornerEntry := ⟨11/40, 11/40, 1/18, #v[374797883/10000000000, 18477023/500000000, 164503183/5000000000]⟩
abbrev vcCutP839Roots := vcOuterP839Roots
theorem vcCutP839_roots : vcCutP839.cell.rootsOK vcCutP839Roots = true := by decide +kernel

def vcCutP840 : SideCornerEntry := ⟨11/40, 3/10, 0, #v[164627837/5000000000, 64867693/2000000000, 60870811/2000000000]⟩
abbrev vcCutP840Roots := vcOuterP840Roots
theorem vcCutP840_roots : vcCutP840.cell.rootsOK vcCutP840Roots = true := by decide +kernel

def vcCutP841 : SideCornerEntry := ⟨11/40, 3/10, 1/36, #v[352066297/10000000000, 346738993/10000000000, 325483531/10000000000]⟩
abbrev vcCutP841Roots := vcOuterP841Roots
theorem vcCutP841_roots : vcCutP841.cell.rootsOK vcCutP841Roots = true := by decide +kernel

def vcCutP842 : SideCornerEntry := ⟨11/40, 3/10, 1/18, #v[352066297/10000000000, 346738993/10000000000, 325483531/10000000000]⟩
abbrev vcCutP842Roots := vcOuterP842Roots
theorem vcCutP842_roots : vcCutP842.cell.rootsOK vcCutP842Roots = true := by decide +kernel

def vcCutP843 : SideCornerEntry := ⟨11/40, 13/40, 0, #v[338969389/10000000000, 321113023/10000000000, 161315939/5000000000]⟩
abbrev vcCutP843Roots := vcOuterP843Roots
theorem vcCutP843_roots : vcCutP843.cell.rootsOK vcCutP843Roots = true := by decide +kernel

def vcCutP844 : SideCornerEntry := ⟨11/40, 13/40, 1/36, #v[45331803/1250000000, 34309841/1000000000, 345507529/10000000000]⟩
abbrev vcCutP844Roots := vcOuterP844Roots
theorem vcCutP844_roots : vcCutP844.cell.rootsOK vcCutP844Roots = true := by decide +kernel

def vcCutP845 : SideCornerEntry := ⟨11/40, 13/40, 1/18, #v[45331803/1250000000, 34309841/1000000000, 345507529/10000000000]⟩
abbrev vcCutP845Roots := vcOuterP845Roots
theorem vcCutP845_roots : vcCutP845.cell.rootsOK vcCutP845Roots = true := by decide +kernel

def vcCutP846 : SideCornerEntry := ⟨11/40, 7/20, 0, #v[97292923/2500000000, 361692769/10000000000, 604683/16000000]⟩
abbrev vcCutP846Roots := vcOuterP846Roots
theorem vcCutP846_roots : vcCutP846.cell.rootsOK vcCutP846Roots = true := by decide +kernel

def vcCutP847 : SideCornerEntry := ⟨11/40, 7/20, 1/36, #v[208321207/5000000000, 96640801/2500000000, 405039121/10000000000]⟩
abbrev vcCutP847Roots := vcOuterP847Roots
theorem vcCutP847_roots : vcCutP847.cell.rootsOK vcCutP847Roots = true := by decide +kernel

def vcCutP848 : SideCornerEntry := ⟨11/40, 7/20, 1/18, #v[208321207/5000000000, 96640801/2500000000, 405039121/10000000000]⟩
abbrev vcCutP848Roots := vcOuterP848Roots
theorem vcCutP848_roots : vcCutP848.cell.rootsOK vcCutP848Roots = true := by decide +kernel

def vcCutP849 : SideCornerEntry := ⟨11/40, 3/8, 0, #v[97292923/2500000000, 361692769/10000000000, 604683/16000000]⟩
abbrev vcCutP849Roots := vcOuterP849Roots
theorem vcCutP849_roots : vcCutP849.cell.rootsOK vcCutP849Roots = true := by decide +kernel

def vcCutP850 : SideCornerEntry := ⟨11/40, 3/8, 1/36, #v[208321207/5000000000, 96640801/2500000000, 405039121/10000000000]⟩
abbrev vcCutP850Roots := vcOuterP850Roots
theorem vcCutP850_roots : vcCutP850.cell.rootsOK vcCutP850Roots = true := by decide +kernel

def vcCutP851 : SideCornerEntry := ⟨11/40, 3/8, 1/18, #v[208321207/5000000000, 96640801/2500000000, 405039121/10000000000]⟩
abbrev vcCutP851Roots := vcOuterP851Roots
theorem vcCutP851_roots : vcCutP851.cell.rootsOK vcCutP851Roots = true := by decide +kernel

def vcCutP852 : SideCornerEntry := ⟨3/10, 11/40, 0, #v[164627837/5000000000, 64867693/2000000000, 60870811/2000000000]⟩
abbrev vcCutP852Roots := vcOuterP852Roots
theorem vcCutP852_roots : vcCutP852.cell.rootsOK vcCutP852Roots = true := by decide +kernel

def vcCutP853 : SideCornerEntry := ⟨3/10, 11/40, 1/36, #v[352066297/10000000000, 346738993/10000000000, 325483531/10000000000]⟩
abbrev vcCutP853Roots := vcOuterP853Roots
theorem vcCutP853_roots : vcCutP853.cell.rootsOK vcCutP853Roots = true := by decide +kernel

def vcCutP854 : SideCornerEntry := ⟨3/10, 11/40, 1/18, #v[352066297/10000000000, 346738993/10000000000, 325483531/10000000000]⟩
abbrev vcCutP854Roots := vcOuterP854Roots
theorem vcCutP854_roots : vcCutP854.cell.rootsOK vcCutP854Roots = true := by decide +kernel

def vcCutP855 : SideCornerEntry := ⟨3/10, 3/10, 0, #v[7159239/200000000, 352230831/10000000000, 347655411/10000000000]⟩
abbrev vcCutP855Roots := vcOuterP855Roots
theorem vcCutP855_roots : vcCutP855.cell.rootsOK vcCutP855Roots = true := by decide +kernel

def vcCutP856 : SideCornerEntry := ⟨3/10, 3/10, 1/36, #v[382989207/10000000000, 75335057/2000000000, 186209343/5000000000]⟩
abbrev vcCutP856Roots := vcOuterP856Roots
theorem vcCutP856_roots : vcCutP856.cell.rootsOK vcCutP856Roots = true := by decide +kernel

def vcCutP857 : SideCornerEntry := ⟨3/10, 3/10, 1/18, #v[382989207/10000000000, 75335057/2000000000, 186209343/5000000000]⟩
abbrev vcCutP857Roots := vcOuterP857Roots
theorem vcCutP857_roots : vcCutP857.cell.rootsOK vcCutP857Roots = true := by decide +kernel

def vcCutP858 : SideCornerEntry := ⟨3/10, 13/40, 0, #v[401319241/10000000000, 77504493/2000000000, 49632809/1250000000]⟩
abbrev vcCutP858Roots := vcOuterP858Roots
theorem vcCutP858_roots : vcCutP858.cell.rootsOK vcCutP858Roots = true := by decide +kernel

def vcCutP859 : SideCornerEntry := ⟨3/10, 13/40, 1/36, #v[429630519/10000000000, 414478211/10000000000, 425687591/10000000000]⟩
abbrev vcCutP859Roots := vcOuterP859Roots
theorem vcCutP859_roots : vcCutP859.cell.rootsOK vcCutP859Roots = true := by decide +kernel

def vcCutP860 : SideCornerEntry := ⟨3/10, 13/40, 1/18, #v[429630519/10000000000, 414478211/10000000000, 425687591/10000000000]⟩
abbrev vcCutP860Roots := vcOuterP860Roots
theorem vcCutP860_roots : vcCutP860.cell.rootsOK vcCutP860Roots = true := by decide +kernel

def vcCutP861 : SideCornerEntry := ⟨3/10, 7/20, 0, #v[401319241/10000000000, 77504493/2000000000, 49632809/1250000000]⟩
abbrev vcCutP861Roots := vcOuterP861Roots
theorem vcCutP861_roots : vcCutP861.cell.rootsOK vcCutP861Roots = true := by decide +kernel

def vcCutP862 : SideCornerEntry := ⟨3/10, 7/20, 1/36, #v[429630519/10000000000, 414478211/10000000000, 425687591/10000000000]⟩
abbrev vcCutP862Roots := vcOuterP862Roots
theorem vcCutP862_roots : vcCutP862.cell.rootsOK vcCutP862Roots = true := by decide +kernel

def vcCutP863 : SideCornerEntry := ⟨3/10, 7/20, 1/18, #v[429630519/10000000000, 414478211/10000000000, 425687591/10000000000]⟩
abbrev vcCutP863Roots := vcOuterP863Roots
theorem vcCutP863_roots : vcCutP863.cell.rootsOK vcCutP863Roots = true := by decide +kernel

def vcCutPoints832 : Array SideCornerEntry := #[
  vcCutP832,
  vcCutP833,
  vcCutP834,
  vcCutP835,
  vcCutP836,
  vcCutP837,
  vcCutP838,
  vcCutP839,
  vcCutP840,
  vcCutP841,
  vcCutP842,
  vcCutP843,
  vcCutP844,
  vcCutP845,
  vcCutP846,
  vcCutP847,
  vcCutP848,
  vcCutP849,
  vcCutP850,
  vcCutP851,
  vcCutP852,
  vcCutP853,
  vcCutP854,
  vcCutP855,
  vcCutP856,
  vcCutP857,
  vcCutP858,
  vcCutP859,
  vcCutP860,
  vcCutP861,
  vcCutP862,
  vcCutP863]

end HlawkaSchatten.BelowExponent.Vertex
