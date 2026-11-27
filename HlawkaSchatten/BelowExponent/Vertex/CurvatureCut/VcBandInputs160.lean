/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCheck
meta import Mathlib.Tactic.FinCases

/-! Parameter boxes and exact curvature budgets for the cut. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def vcS1160CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨13/40, 27/80⟩, ⟨0, 1/40⟩⟩
def vcS1160CutRoots : Fin 3 → RatBounds := ![⟨464999831097485/281474976710656, 496447764914043/281474976710656⟩, ⟨400908923510439/281474976710656, 430039002049319/281474976710656⟩, ⟨313625557547419/281474976710656, 43051655153287/35184372088832⟩]
def vcS1160CutCaps : Fin 3 → Fin 3 → ℚ := ![![8796059649/100000000, 1426728489/25000000, 34912041/1000000], ![138841197/4000000, 3579773921/100000000, 1750021831/100000000], ![527199303/50000000, 953081541/100000000, 163925623/25000000]]
def vcS1160CutWeightFloor : ℚ := 5571109/5000000
def vcS1160CutMargins : Fin 3 → ℚ := ![32196649/10000000000, 6396003/2500000000, 7679723/5000000000]

theorem vcS1160Cut_roots_ok : vcS1160CutCell.rootsOK vcS1160CutRoots = true := by decide +kernel

theorem vcS1160Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1160CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1160Cut_margin_le (i : Fin 3) : curvatureLoss vcS1160CutCell vcS1160CutCaps i ≤ vcS1160CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1161CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨13/40, 27/80⟩, ⟨1/40, 1/20⟩⟩
def vcS1161CutRoots : Fin 3 → RatBounds := ![⟨230754782219059/140737488355328, 123103762231585/70368744177664⟩, ⟨12365869005221/8796093022208, 424115172336737/281474976710656⟩, ⟨308308166957061/281474976710656, 169124873152393/140737488355328⟩]
def vcS1161CutCaps : Fin 3 → Fin 3 → ℚ := ![![4609296001/50000000, 376229717/6250000, 1837758071/50000000], ![1819558189/50000000, 3742631531/100000000, 366744813/20000000], ![472596963/50000000, 212779369/25000000, 29278773/5000000]]
def vcS1161CutWeightFloor : ℚ := 116210327/100000000
def vcS1161CutMargins : Fin 3 → ℚ := ![406213/125000000, 12858181/5000000000, 3833761/2500000000]

theorem vcS1161Cut_roots_ok : vcS1161CutCell.rootsOK vcS1161CutRoots = true := by decide +kernel

theorem vcS1161Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1161CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1161Cut_margin_le (i : Fin 3) : curvatureLoss vcS1161CutCell vcS1161CutCaps i ≤ vcS1161CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1162CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨13/40, 27/80⟩, ⟨1/20, 3/40⟩⟩
def vcS1162CutRoots : Fin 3 → RatBounds := ![⟨229146685976179/140737488355328, 488718336779043/281474976710656⟩, ⟨24433831434635/17592186044416, 209354700859653/140737488355328⟩, ⟨303449011985295/281474976710656, 332641910601747/281474976710656⟩]
def vcS1162CutCaps : Fin 3 → Fin 3 → ℚ := ![![4821098013/50000000, 6329437943/100000000, 771835659/20000000], ![29732441/781250, 3904265633/100000000, 1916615427/100000000], ![851569321/100000000, 764189453/100000000, 525796603/100000000]]
def vcS1162CutWeightFloor : ℚ := 121008369/100000000
def vcS1162CutMargins : Fin 3 → ℚ := ![3291841/1000000000, 25957933/10000000000, 7694317/5000000000]

theorem vcS1162Cut_roots_ok : vcS1162CutCell.rootsOK vcS1162CutRoots = true := by decide +kernel

theorem vcS1162Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1162CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1162Cut_margin_le (i : Fin 3) : curvatureLoss vcS1162CutCell vcS1162CutCaps i ≤ vcS1162CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1163CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨13/40, 27/80⟩, ⟨3/40, 1/10⟩⟩
def vcS1163CutRoots : Fin 3 → RatBounds := ![⟨455319862638129/281474976710656, 242658441749321/140737488355328⟩, ⟨386556576311133/281474976710656, 413755892122645/281474976710656⟩, ⟨298991144817085/281474976710656, 163758805298445/140737488355328⟩]
def vcS1163CutCaps : Fin 3 → Fin 3 → ℚ := ![![5032182133/50000000, 6636463593/100000000, 4041804149/100000000], ![1985536529/50000000, 4064802051/100000000, 999390927/50000000], ![385381313/50000000, 689538653/100000000, 237232347/50000000]]
def vcS1163CutWeightFloor : ℚ := 31453651/25000000
def vcS1163CutMargins : Fin 3 → ℚ := ![33434547/10000000000, 26287931/10000000000, 620191/400000000]

theorem vcS1163Cut_roots_ok : vcS1163CutCell.rootsOK vcS1163CutRoots = true := by decide +kernel

theorem vcS1163Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1163CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1163Cut_margin_le (i : Fin 3) : curvatureLoss vcS1163CutCell vcS1163CutCaps i ≤ vcS1163CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1164CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨27/80, 7/20⟩, ⟨0, 1/40⟩⟩
def vcS1164CutRoots : Fin 3 → RatBounds := ![⟨462490856209183/281474976710656, 246790190125435/140737488355328⟩, ⟨395647909818673/281474976710656, 212177556966095/140737488355328⟩, ⟨158124747534273/140737488355328, 346788713207127/281474976710656⟩]
def vcS1164CutCaps : Fin 3 → Fin 3 → ℚ := ![![4197027367/50000000, 538144839/10000000, 3368158937/100000000], ![3255781453/100000000, 414194517/12500000, 68320527/4000000], ![1047471139/100000000, 29136067/3125000, 166093867/25000000]]
def vcS1164CutWeightFloor : ℚ := 11235439/10000000
def vcS1164CutMargins : Fin 3 → ℚ := ![6187391/2000000000, 1516653/625000000, 236013/156250000]

theorem vcS1164Cut_roots_ok : vcS1164CutCell.rootsOK vcS1164CutRoots = true := by decide +kernel

theorem vcS1164Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1164CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1164Cut_margin_le (i : Fin 3) : curvatureLoss vcS1164CutCell vcS1164CutCaps i ≤ vcS1164CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1165CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨27/80, 7/20⟩, ⟨1/40, 1/20⟩⟩
def vcS1165CutRoots : Fin 3 → RatBounds := ![⟨114758976695501/70368744177664, 244793666495215/140737488355328⟩, ⟨390449907761937/281474976710656, 209217030110571/140737488355328⟩, ⟨310940774534245/281474976710656, 340645045528983/281474976710656⟩]
def vcS1165CutCaps : Fin 3 → Fin 3 → ℚ := ![![8797419041/100000000, 2838098479/50000000, 141925561/4000000], ![341329813/10000000, 3464030287/100000000, 357885103/20000000], ![938780459/100000000, 832435693/100000000, 593244897/100000000]]
def vcS1165CutWeightFloor : ℚ := 11716209/10000000
def vcS1165CutMargins : Fin 3 → ℚ := ![389791/125000000, 24355411/10000000000, 15059657/10000000000]

theorem vcS1165Cut_roots_ok : vcS1165CutCell.rootsOK vcS1165CutRoots = true := by decide +kernel

theorem vcS1165Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1165CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1165Cut_margin_le (i : Fin 3) : curvatureLoss vcS1165CutCell vcS1165CutCaps i ≤ vcS1165CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1166CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨27/80, 7/20⟩, ⟨1/20, 3/40⟩⟩
def vcS1166CutRoots : Fin 3 → RatBounds := ![⟨455852337915165/281474976710656, 242963619970327/140737488355328⟩, ⟨192843563720413/140737488355328, 103257972774509/70368744177664⟩, ⟨306089212591807/281474976710656, 335054830889565/281474976710656⟩]
def vcS1166CutCaps : Fin 3 → Fin 3 → ℚ := ![![9200863283/100000000, 46625683/781250, 186364839/5000000], ![892363517/25000000, 1806690551/50000000, 233758359/12500000], ![105702587/12500000, 186817993/25000000, 66577371/12500000]]
def vcS1166CutWeightFloor : ℚ := 121980213/100000000
def vcS1166CutMargins : Fin 3 → ℚ := ![15774219/5000000000, 6137967/2500000000, 15093437/10000000000]

theorem vcS1166Cut_roots_ok : vcS1166CutCell.rootsOK vcS1166CutRoots = true := by decide +kernel

theorem vcS1166Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1166CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1166Cut_margin_le (i : Fin 3) : curvatureLoss vcS1166CutCell vcS1166CutCaps i ≤ vcS1166CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1167CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨27/80, 7/20⟩, ⟨3/40, 1/10⟩⟩
def vcS1167CutRoots : Fin 3 → RatBounds := ![⟨452909062449343/281474976710656, 30159981359227/17592186044416⟩, ⟨95326645405265/70368744177664, 408082599970765/281474976710656⟩, ⟨301638022066727/281474976710656, 41243283434697/35184372088832⟩]
def vcS1167CutCaps : Fin 3 → Fin 3 → ℚ := ![![9605796777/100000000, 6257396921/100000000, 3910216219/100000000], ![465546783/12500000, 3761708379/100000000, 1950008991/100000000], ![9565433/1250000, 674152637/100000000, 480566521/100000000]]
def vcS1167CutWeightFloor : ℚ := 25361393/20000000
def vcS1167CutMargins : Fin 3 → ℚ := ![16006943/5000000000, 24835383/10000000000, 15200179/10000000000]

theorem vcS1167Cut_roots_ok : vcS1167CutCell.rootsOK vcS1167CutRoots = true := by decide +kernel

theorem vcS1167Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1167CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1167Cut_margin_le (i : Fin 3) : curvatureLoss vcS1167CutCell vcS1167CutCaps i ≤ vcS1167CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1168CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨7/20, 29/80⟩, ⟨0, 1/40⟩⟩
def vcS1168CutRoots : Fin 3 → RatBounds := ![⟨460240920774515/281474976710656, 491023799342173/281474976710656⟩, ⟨390606505141535/281474976710656, 209469520942097/140737488355328⟩, ⟨79730927521569/70368744177664, 87313613137919/70368744177664⟩]
def vcS1168CutCaps : Fin 3 → Fin 3 → ℚ := ![![804384117/10000000, 509912721/10000000, 652857369/20000000], ![383840737/12500000, 1539273997/50000000, 1676460883/100000000], ![16271493/1562500, 36502813/4000000, 84175503/12500000]]
def vcS1168CutWeightFloor : ℚ := 56652231/50000000
def vcS1168CutMargins : Fin 3 → ℚ := ![14921943/5000000000, 11550739/5000000000, 14910867/10000000000]

theorem vcS1168Cut_roots_ok : vcS1168CutCell.rootsOK vcS1168CutRoots = true := by decide +kernel

theorem vcS1168Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1168CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1168Cut_margin_le (i : Fin 3) : curvatureLoss vcS1168CutCell vcS1168CutCaps i ≤ vcS1168CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1169CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨7/20, 29/80⟩, ⟨1/40, 1/20⟩⟩
def vcS1169CutRoots : Fin 3 → RatBounds := ![⟨456817691737371/281474976710656, 60883288319257/35184372088832⟩, ⟨385410373618093/281474976710656, 413018986311271/281474976710656⟩, ⟨156811821043267/140737488355328, 343129837866189/281474976710656⟩]
def vcS1169CutCaps : Fin 3 → Fin 3 → ℚ := ![![4217000919/50000000, 268908651/5000000, 3446639439/100000000], ![100598501/3125000, 3218143557/100000000, 878034563/50000000], ![466567561/50000000, 407309417/50000000, 601237483/100000000]]
def vcS1169CutWeightFloor : ℚ := 7383251/6250000
def vcS1169CutMargins : Fin 3 → ℚ := ![6010037/2000000000, 23153891/10000000000, 14858709/10000000000]

theorem vcS1169Cut_roots_ok : vcS1169CutCell.rootsOK vcS1169CutRoots = true := by decide +kernel

theorem vcS1169Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1169CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1169Cut_margin_le (i : Fin 3) : curvatureLoss vcS1169CutCell vcS1169CutCaps i ≤ vcS1169CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1170CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨7/20, 29/80⟩, ⟨1/20, 3/40⟩⟩
def vcS1170CutRoots : Fin 3 → RatBounds := ![⟨453663422714753/281474976710656, 120859758758665/70368744177664⟩, ⟨380650145198293/281474976710656, 407618753518603/281474976710656⟩, ⟨308779641212425/281474976710656, 84389130127531/70368744177664⟩]
def vcS1170CutCaps : Fin 3 → Fin 3 → ℚ := ![![8824329271/100000000, 5654486019/100000000, 907390219/25000000], ![1683147061/50000000, 1678371789/50000000, 1834958749/100000000], ![420191497/50000000, 731149781/100000000, 26986813/5000000]]
def vcS1170CutWeightFloor : ℚ := 122970523/100000000
def vcS1170CutMargins : Fin 3 → ℚ := ![3796913/1250000000, 11656083/5000000000, 744479/500000000]

theorem vcS1170Cut_roots_ok : vcS1170CutCell.rootsOK vcS1170CutRoots = true := by decide +kernel

theorem vcS1170Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1170CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1170Cut_margin_le (i : Fin 3) : curvatureLoss vcS1170CutCell vcS1170CutCaps i ≤ vcS1170CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1171CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨7/20, 29/80⟩, ⟨3/40, 1/10⟩⟩
def vcS1171CutRoots : Fin 3 → RatBounds := ![⟨450747299688177/281474976710656, 240050947531709/140737488355328⟩, ⟨376272671991841/281474976710656, 201336059327767/140737488355328⟩, ⟨304335084166119/281474976710656, 166231507838121/140737488355328⟩]
def vcS1171CutCaps : Fin 3 → Fin 3 → ℚ := ![![4606629299/50000000, 2964178351/50000000, 762225453/20000000], ![35122687/1000000, 1747230593/50000000, 478301953/25000000], ![152073227/20000000, 659500031/100000000, 486938567/100000000]]
def vcS1171CutWeightFloor : ℚ := 127818099/100000000
def vcS1171CutMargins : Fin 3 → ℚ := ![15397453/5000000000, 11778143/5000000000, 299691/200000000]

theorem vcS1171Cut_roots_ok : vcS1171CutCell.rootsOK vcS1171CutRoots = true := by decide +kernel

theorem vcS1171Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1171CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1171Cut_margin_le (i : Fin 3) : curvatureLoss vcS1171CutCell vcS1171CutCaps i ≤ vcS1171CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1172CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨29/80, 3/8⟩, ⟨0, 1/40⟩⟩
def vcS1172CutRoots : Fin 3 → RatBounds := ![⟨458237908665431/281474976710656, 30547653553525/17592186044416⟩, ⟨385768664782657/281474976710656, 206885449928129/140737488355328⟩, ⟨40206531299181/35184372088832, 175906259035007/140737488355328⟩]
def vcS1172CutCaps : Fin 3 → Fin 3 → ℚ := ![![3873061871/50000000, 4854089949/100000000, 1594575589/50000000], ![1455918591/50000000, 717617887/25000000, 165437331/10000000], ![41441779/4000000, 446822939/50000000, 341391137/50000000]]
def vcS1172CutWeightFloor : ℚ := 57136917/50000000
def vcS1172CutMargins : Fin 3 → ℚ := ![7227607/2500000000, 22068643/10000000000, 7397123/5000000000]

theorem vcS1172Cut_roots_ok : vcS1172CutCell.rootsOK vcS1172CutRoots = true := by decide +kernel

theorem vcS1172Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1172CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1172Cut_margin_le (i : Fin 3) : curvatureLoss vcS1172CutCell vcS1172CutCaps i ≤ vcS1172CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1173CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨29/80, 3/8⟩, ⟨1/40, 1/20⟩⟩
def vcS1173CutRoots : Fin 3 → RatBounds := ![⟨454842940222839/281474976710656, 484836580607401/281474976710656⟩, ⟨190286635056285/140737488355328, 407850206290919/281474976710656⟩, ⟨9886274281979/8796093022208, 345706197441147/281474976710656⟩]
def vcS1173CutCaps : Fin 3 → Fin 3 → ℚ := ![![8123154981/100000000, 2559709507/50000000, 1685699683/50000000], ![3052447559/100000000, 120023447/4000000, 54145889/3125000], ![232049049/25000000, 398794809/50000000, 152387021/25000000]]
def vcS1173CutWeightFloor : ℚ := 29780403/25000000
def vcS1173CutMargins : Fin 3 → ℚ := ![14539441/5000000000, 4418111/2000000000, 14730977/10000000000]

theorem vcS1173Cut_roots_ok : vcS1173CutCell.rootsOK vcS1173CutRoots = true := by decide +kernel

theorem vcS1173Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1173CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1173Cut_margin_le (i : Fin 3) : curvatureLoss vcS1173CutCell vcS1173CutCaps i ≤ vcS1173CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1174CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨29/80, 3/8⟩, ⟨1/20, 3/40⟩⟩
def vcS1174CutRoots : Fin 3 → RatBounds := ![⟨112928693547757/70368744177664, 481238495833711/281474976710656⟩, ⟨375814522317399/281474976710656, 402450376430511/281474976710656⟩, ⟨311524267935399/281474976710656, 340149066917747/281474976710656⟩]
def vcS1174CutCaps : Fin 3 → Fin 3 → ℚ := ![![8498794711/100000000, 1076427537/20000000, 710424103/20000000], ![3191839617/100000000, 3129730903/100000000, 905125613/50000000], ![83579947/10000000, 71575173/10000000, 273571981/50000000]]
def vcS1174CutWeightFloor : ℚ := 61990437/50000000
def vcS1174CutMargins : Fin 3 → ℚ := ![14681477/5000000000, 11108277/5000000000, 2949589/2000000000]

theorem vcS1174Cut_roots_ok : vcS1174CutCell.rootsOK vcS1174CutRoots = true := by decide +kernel

theorem vcS1174Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1174CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1174Cut_margin_le (i : Fin 3) : curvatureLoss vcS1174CutCell vcS1174CutCaps i ≤ vcS1174CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1175CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨29/80, 3/8⟩, ⟨3/40, 1/10⟩⟩
def vcS1175CutRoots : Fin 3 → RatBounds := ![⟨112205710026493/70368744177664, 477928388010715/281474976710656⟩, ⟨92859777144263/70368744177664, 99376239606251/70368744177664⟩, ⟨153543133306111/140737488355328, 335069954318029/281474976710656⟩]
def vcS1175CutCaps : Fin 3 → Fin 3 → ℚ := ![![443656717/5000000, 5642535259/100000000, 3731498403/100000000], ![3330122811/100000000, 3257988953/100000000, 1887185191/100000000], ![756104777/100000000, 32275757/5000000, 246788413/50000000]]
def vcS1175CutWeightFloor : ℚ := 8053103/6250000
def vcS1175CutMargins : Fin 3 → ℚ := ![7435389/2500000000, 5606731/2500000000, 14830061/10000000000]

theorem vcS1175Cut_roots_ok : vcS1175CutCell.rootsOK vcS1175CutRoots = true := by decide +kernel

theorem vcS1175Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1175CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1175Cut_margin_le (i : Fin 3) : curvatureLoss vcS1175CutCell vcS1175CutCaps i ≤ vcS1175CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1176CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨3/8, 31/80⟩, ⟨0, 1/40⟩⟩
def vcS1176CutRoots : Fin 3 → RatBounds := ![⟨456471347024351/281474976710656, 243391505746781/140737488355328⟩, ⟨381119897238941/281474976710656, 204416458210037/140737488355328⟩, ⟨162219610917885/140737488355328, 177232702917391/140737488355328⟩]
def vcS1176CutCaps : Fin 3 → Fin 3 → ℚ := ![![1498035053/20000000, 1160392223/25000000, 1565762757/50000000], ![2775867287/100000000, 2685574299/100000000, 820443901/50000000], ![1031421521/100000000, 437753719/50000000, 346253647/50000000]]
def vcS1176CutWeightFloor : ℚ := 57631983/50000000
def vcS1176CutMargins : Fin 3 → ℚ := ![5621769/2000000000, 21150729/10000000000, 14731333/10000000000]

theorem vcS1176Cut_roots_ok : vcS1176CutCell.rootsOK vcS1176CutRoots = true := by decide +kernel

theorem vcS1176Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1176CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1176Cut_margin_le (i : Fin 3) : curvatureLoss vcS1176CutCell vcS1176CutCaps i ≤ vcS1176CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1177CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨3/8, 31/80⟩, ⟨1/40, 1/20⟩⟩
def vcS1177CutRoots : Fin 3 → RatBounds := ![⟨453101297975405/281474976710656, 120721241336653/70368744177664⟩, ⟨187962102019885/140737488355328, 201455036959375/140737488355328⟩, ⟨319156246299243/281474976710656, 348376629251277/281474976710656⟩]
def vcS1177CutCaps : Fin 3 → Fin 3 → ℚ := ![![7854566437/100000000, 611864011/12500000, 103510977/3125000], ![1454886219/50000000, 2807188021/100000000, 343641743/20000000], ![923912017/100000000, 195320177/25000000, 309087133/50000000]]
def vcS1177CutWeightFloor : ℚ := 60066201/50000000
def vcS1177CutMargins : Fin 3 → ℚ := ![14121081/5000000000, 528673/250000000, 14654799/10000000000]

theorem vcS1177Cut_roots_ok : vcS1177CutCell.rootsOK vcS1177CutRoots = true := by decide +kernel

theorem vcS1177Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1177CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1177Cut_margin_le (i : Fin 3) : curvatureLoss vcS1177CutCell vcS1177CutCaps i ≤ vcS1177CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1178CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨3/8, 31/80⟩, ⟨1/20, 3/40⟩⟩
def vcS1178CutRoots : Fin 3 → RatBounds := ![⟨112499036979901/70368744177664, 239656286204707/140737488355328⟩, ⟨371165957270459/281474976710656, 99377307507505/70368744177664⟩, ⟨39290890466449/35184372088832, 342834982591589/281474976710656⟩]
def vcS1178CutCaps : Fin 3 → Fin 3 → ℚ := ![![8217656143/100000000, 1286440943/25000000, 3491655477/100000000], ![760629453/25000000, 1463965499/50000000, 358968487/20000000], ![831822631/100000000, 70101583/10000000, 554840027/100000000]]
def vcS1178CutWeightFloor : ℚ := 25002571/20000000
def vcS1178CutMargins : Fin 3 → ℚ := ![14245571/5000000000, 10622811/5000000000, 14659879/10000000000]

theorem vcS1178Cut_roots_ok : vcS1178CutCell.rootsOK vcS1178CutRoots = true := by decide +kernel

theorem vcS1178Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1178CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1178Cut_margin_le (i : Fin 3) : curvatureLoss vcS1178CutCell vcS1178CutCaps i ≤ vcS1178CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1179CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨3/8, 31/80⟩, ⟨3/40, 1/10⟩⟩
def vcS1179CutRoots : Fin 3 → RatBounds := ![⟨6986336583203/4398046511104, 238013130122123/140737488355328⟩, ⟨366791675542207/281474976710656, 196281849016637/140737488355328⟩, ⟨309895566988851/281474976710656, 337769602180377/281474976710656⟩]
def vcS1179CutCaps : Fin 3 → Fin 3 → ℚ := ![![8579527187/100000000, 5394400461/100000000, 3669621477/100000000], ![317420583/10000000, 3047846603/100000000, 467712231/25000000], ![752406759/100000000, 63214073/10000000, 500479561/100000000]]
def vcS1179CutWeightFloor : ℚ := 129903261/100000000
def vcS1179CutMargins : Fin 3 → ℚ := ![225271/78125000, 5356841/2500000000, 3682807/2500000000]

theorem vcS1179Cut_roots_ok : vcS1179CutCell.rootsOK vcS1179CutRoots = true := by decide +kernel

theorem vcS1179Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1179CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1179Cut_margin_le (i : Fin 3) : curvatureLoss vcS1179CutCell vcS1179CutCaps i ≤ vcS1179CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1180CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨31/80, 2/5⟩, ⟨0, 1/40⟩⟩
def vcS1180CutRoots : Fin 3 → RatBounds := ![⟨454932239562959/281474976710656, 60634263339869/35184372088832⟩, ⟨376647069076485/281474976710656, 404109161739961/281474976710656⟩, ⟨20455551518697/17592186044416, 357216046215563/281474976710656⟩]
def vcS1180CutCaps : Fin 3 → Fin 3 → ℚ := ![![1454044619/20000000, 891533613/20000000, 772036763/25000000], ![2660204049/100000000, 1260568997/50000000, 204412723/12500000], ![256864917/25000000, 429045417/50000000, 702578889/100000000]]
def vcS1180CutWeightFloor : ℚ := 29069087/25000000
def vcS1180CutMargins : Fin 3 → ℚ := ![5484479/2000000000, 5083579/2500000000, 919649/625000000]

theorem vcS1180Cut_roots_ok : vcS1180CutCell.rootsOK vcS1180CutRoots = true := by decide +kernel

theorem vcS1180Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1180CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1180Cut_margin_le (i : Fin 3) : curvatureLoss vcS1180CutCell vcS1180CutCaps i ≤ vcS1180CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1181CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨31/80, 2/5⟩, ⟨1/40, 1/20⟩⟩
def vcS1181CutRoots : Fin 3 → RatBounds := ![⟨451583870656767/281474976710656, 481200233515223/281474976710656⟩, ⟨185725065457381/140737488355328, 49772846265617/35184372088832⟩, ⟨322014211898075/281474976710656, 175572033344591/140737488355328⟩]
def vcS1181CutCaps : Fin 3 → Fin 3 → ℚ := ![![3811954229/50000000, 4700558943/100000000, 817074367/25000000], ![557679057/20000000, 658812137/25000000, 856007301/50000000], ![92023951/10000000, 765633209/100000000, 627116079/100000000]]
def vcS1181CutWeightFloor : ℚ := 121165939/100000000
def vcS1181CutMargins : Fin 3 → ℚ := ![13762951/5000000000, 20309259/10000000000, 14626517/10000000000]

theorem vcS1181Cut_roots_ok : vcS1181CutCell.rootsOK vcS1181CutRoots = true := by decide +kernel

theorem vcS1181Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1181CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1181Cut_margin_le (i : Fin 3) : curvatureLoss vcS1181CutCell vcS1181CutCaps i ≤ vcS1181CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1182CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨31/80, 2/5⟩, ⟨1/20, 3/40⟩⟩
def vcS1182CutRoots : Fin 3 → RatBounds := ![⟨56062342998671/35184372088832, 477650156877541/281474976710656⟩, ⟨91672872135369/70368744177664, 196389799162373/140737488355328⟩, ⟨317192335476459/281474976710656, 345617202998693/281474976710656⟩]
def vcS1182CutCaps : Fin 3 → Fin 3 → ℚ := ![![3988182937/50000000, 617632777/12500000, 3446924541/100000000], ![1457736989/50000000, 1374256923/50000000, 1788061219/100000000], ![207103219/25000000, 343443929/50000000, 281412341/50000000]]
def vcS1182CutWeightFloor : ℚ := 126068079/100000000
def vcS1182CutMargins : Fin 3 → ℚ := ![27745101/10000000000, 4077003/2000000000, 292433/200000000]

theorem vcS1182Cut_roots_ok : vcS1182CutCell.rootsOK vcS1182CutRoots = true := by decide +kernel

theorem vcS1182Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1182CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1182Cut_margin_le (i : Fin 3) : curvatureLoss vcS1182CutCell vcS1182CutCaps i ≤ vcS1182CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1183CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨31/80, 2/5⟩, ⟨3/40, 1/10⟩⟩
def vcS1183CutRoots : Fin 3 → RatBounds := ![⟨445646691166247/281474976710656, 59298064309683/35184372088832⟩, ⟨181158744465879/140737488355328, 387832717633083/281474976710656⟩, ⟨312767079563099/281474976710656, 85141224013891/70368744177664⟩]
def vcS1183CutCaps : Fin 3 → Fin 3 → ℚ := ![![8327671451/100000000, 5179443351/100000000, 3624212057/100000000], ![760384461/25000000, 2861003837/100000000, 1863498509/100000000], ![749235561/100000000, 123865347/20000000, 4061177/800000]]
def vcS1183CutWeightFloor : ℚ := 32745153/25000000
def vcS1183CutMargins : Fin 3 → ℚ := ![2805889/1000000000, 20542489/10000000000, 7342089/5000000000]

theorem vcS1183Cut_roots_ok : vcS1183CutCell.rootsOK vcS1183CutRoots = true := by decide +kernel

theorem vcS1183Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1183CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1183Cut_margin_le (i : Fin 3) : curvatureLoss vcS1183CutCell vcS1183CutCaps i ≤ vcS1183CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1184CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨2/5, 33/80⟩, ⟨0, 1/40⟩⟩
def vcS1184CutRoots : Fin 3 → RatBounds := ![⟨28350808041861/17592186044416, 30226635943429/17592186044416⟩, ⟨372338238333435/281474976710656, 399585317703801/281474976710656⟩, ⟨165102693196019/140737488355328, 45008476023353/35184372088832⟩]
def vcS1184CutCaps : Fin 3 → Fin 3 → ℚ := ![![442685227/6250000, 2149610779/50000000, 3058178691/100000000], ![2562717667/100000000, 1187059191/50000000, 1637180657/100000000], ![512059997/50000000, 420669879/50000000, 71299943/10000000]]
def vcS1184CutWeightFloor : ℚ := 117312519/100000000
def vcS1184CutMargins : Fin 3 → ℚ := ![26840159/10000000000, 9803417/5000000000, 3685233/2500000000]

theorem vcS1184Cut_roots_ok : vcS1184CutCell.rootsOK vcS1184CutRoots = true := by decide +kernel

theorem vcS1184Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1184CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1184Cut_margin_le (i : Fin 3) : curvatureLoss vcS1184CutCell vcS1184CutCaps i ≤ vcS1184CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1185CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨2/5, 33/80⟩, ⟨1/40, 1/20⟩⟩
def vcS1185CutRoots : Fin 3 → RatBounds := ![⟨450283087457363/281474976710656, 119943231717959/70368744177664⟩, ⟨367139189595375/281474976710656, 24603379682295/17592186044416⟩, ⟨324938965062901/281474976710656, 177005938102545/140737488355328⟩]
def vcS1185CutCaps : Fin 3 → Fin 3 → ℚ := ![![3713850339/50000000, 2266510659/50000000, 3238372203/100000000], ![2686064589/100000000, 496304307/20000000, 1713630237/100000000], ![917143019/100000000, 93824429/12500000, 318187959/50000000]]
def vcS1185CutWeightFloor : ℚ := 122223819/100000000
def vcS1185CutMargins : Fin 3 → ℚ := ![6729657/2500000000, 9782153/5000000000, 14643567/10000000000]

theorem vcS1185Cut_roots_ok : vcS1185CutCell.rootsOK vcS1185CutRoots = true := by decide +kernel

theorem vcS1185Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1185CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1185Cut_margin_le (i : Fin 3) : curvatureLoss vcS1185CutCell vcS1185CutCaps i ≤ vcS1185CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1186CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨2/5, 33/80⟩, ⟨1/20, 3/40⟩⟩
def vcS1186CutRoots : Fin 3 → RatBounds := ![⟨223607535995099/140737488355328, 476241891834741/281474976710656⟩, ⟨90594832595427/70368744177664, 194123676341637/140737488355328⟩, ⟨40015519970581/35184372088832, 43562386446885/35184372088832⟩]
def vcS1186CutCaps : Fin 3 → Fin 3 → ℚ := ![![1554253693/20000000, 2382262063/50000000, 854258371/25000000], ![702084953/25000000, 2588130221/100000000, 894715361/50000000], ![82553743/10000000, 21041257/3125000, 285550149/50000000]]
def vcS1186CutWeightFloor : ℚ := 127148199/100000000
def vcS1186CutMargins : Fin 3 → ℚ := ![27112809/10000000000, 2452621/1250000000, 14630597/10000000000]

theorem vcS1186Cut_roots_ok : vcS1186CutCell.rootsOK vcS1186CutRoots = true := by decide +kernel

theorem vcS1186Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1186CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1186Cut_margin_le (i : Fin 3) : curvatureLoss vcS1186CutCell vcS1186CutCaps i ≤ vcS1186CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1187CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨2/5, 33/80⟩, ⟨3/40, 1/10⟩⟩
def vcS1187CutRoots : Fin 3 → RatBounds := ![⟨111094718480185/70368744177664, 472993886740695/281474976710656⟩, ⟨358004833481135/281474976710656, 383297973852911/281474976710656⟩, ⟨157852514358425/140737488355328, 343459196019635/281474976710656⟩]
def vcS1187CutCaps : Fin 3 → Fin 3 → ℚ := ![![8113738121/100000000, 499398593/10000000, 1797173837/50000000], ![2929636409/100000000, 1347004527/50000000, 466159089/25000000], ![373280479/50000000, 121405843/20000000, 6438523/1250000]]
def vcS1187CutWeightFloor : ℚ := 33020853/25000000
def vcS1187CutMargins : Fin 3 → ℚ := ![27401599/10000000000, 19758031/10000000000, 3671539/2500000000]

theorem vcS1187Cut_roots_ok : vcS1187CutCell.rootsOK vcS1187CutRoots = true := by decide +kernel

theorem vcS1187Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1187CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1187Cut_margin_le (i : Fin 3) : curvatureLoss vcS1187CutCell vcS1187CutCaps i ≤ vcS1187CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1188CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨33/80, 17/40⟩, ⟨0, 1/40⟩⟩
def vcS1188CutRoots : Fin 3 → RatBounds := ![⟨7070421592641/4398046511104, 120607819798799/70368744177664⟩, ⟨368182511533893/281474976710656, 395248483527079/281474976710656⟩, ⟨333193399664731/281474976710656, 363024510436015/281474976710656⟩]
def vcS1188CutCaps : Fin 3 → Fin 3 → ℚ := ![![6925769483/100000000, 832730671/20000000, 608212179/20000000], ![620427217/25000000, 70074489/3125000, 25722541/1562500], ![1021370671/100000000, 41260233/5000000, 723773751/100000000]]
def vcS1188CutWeightFloor : ℚ := 59187037/50000000
def vcS1188CutMargins : Fin 3 → ℚ := ![164709/62500000, 18958703/10000000000, 14809373/10000000000]

theorem vcS1188Cut_roots_ok : vcS1188CutCell.rootsOK vcS1188CutRoots = true := by decide +kernel

theorem vcS1188Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1188CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1188Cut_margin_le (i : Fin 3) : curvatureLoss vcS1188CutCell vcS1188CutCaps i ≤ vcS1188CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1189CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨33/80, 17/40⟩, ⟨1/40, 1/20⟩⟩
def vcS1189CutRoots : Fin 3 → RatBounds := ![⟨449192588847505/281474976710656, 119648799711061/70368744177664⟩, ⟨90745140086029/70368744177664, 194655587234345/140737488355328⟩, ⟨327934960100473/281474976710656, 44622983581783/35184372088832⟩]
def vcS1189CutCaps : Fin 3 → Fin 3 → ℚ := ![![7263177161/100000000, 1097395623/25000000, 1611000509/50000000], ![1300498203/50000000, 2343805931/100000000, 430689893/25000000], ![914593391/100000000, 368060943/50000000, 645958421/100000000]]
def vcS1189CutWeightFloor : ℚ := 24661539/20000000
def vcS1189CutMargins : Fin 3 → ℚ := ![1056449/400000000, 9451051/5000000000, 7352143/5000000000]

theorem vcS1189Cut_roots_ok : vcS1189CutCell.rootsOK vcS1189CutRoots = true := by decide +kernel

theorem vcS1189Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1189CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1189Cut_margin_le (i : Fin 3) : curvatureLoss vcS1189CutCell vcS1189CutCaps i ≤ vcS1189CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1190CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨33/80, 17/40⟩, ⟨1/20, 3/40⟩⟩
def vcS1190CutRoots : Fin 3 → RatBounds := ![⟨223069419951747/140737488355328, 237540007308139/140737488355328⟩, ⟨358218731845845/281474976710656, 47987470037843/35184372088832⟩, ⟨80781754083181/70368744177664, 351484451286657/281474976710656⟩]
def vcS1190CutCaps : Fin 3 → Fin 3 → ℚ := ![![3799730353/50000000, 922658693/20000000, 1700696513/50000000], ![2719246727/100000000, 244447793/10000000, 899320429/50000000], ![102896187/12500000, 660271041/100000000, 579671307/100000000]]
def vcS1190CutWeightFloor : ℚ := 128254923/100000000
def vcS1190CutMargins : Fin 3 → ℚ := ![13292369/5000000000, 9471539/5000000000, 14684999/10000000000]

theorem vcS1190Cut_roots_ok : vcS1190CutCell.rootsOK vcS1190CutRoots = true := by decide +kernel

theorem vcS1190Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1190CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1190Cut_margin_le (i : Fin 3) : curvatureLoss vcS1190CutCell vcS1190CutCaps i ≤ vcS1190CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1191CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨33/80, 17/40⟩, ⟨3/40, 1/10⟩⟩
def vcS1191CutRoots : Fin 3 → RatBounds := ![⟨443315860296943/281474976710656, 471846692122357/281474976710656⟩, ⟨353843022561019/281474976710656, 378946809544563/281474976710656⟩, ⟨159356901008597/140737488355328, 346456297184757/281474976710656⟩]
def vcS1191CutCaps : Fin 3 → Fin 3 → ℚ := ![![3967343919/50000000, 4835034081/100000000, 3579424287/100000000], ![2836548987/100000000, 254445969/10000000, 936969267/50000000], ![744358241/100000000, 595209491/100000000, 6534849/1250000]]
def vcS1191CutWeightFloor : ℚ := 66606711/50000000
def vcS1191CutMargins : Fin 3 → ℚ := ![26852871/10000000000, 4765787/2500000000, 736769/500000000]

theorem vcS1191Cut_roots_ok : vcS1191CutCell.rootsOK vcS1191CutRoots = true := by decide +kernel

theorem vcS1191Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1191CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1191Cut_margin_le (i : Fin 3) : curvatureLoss vcS1191CutCell vcS1191CutCaps i ≤ vcS1191CutMargins i := by
  fin_cases i <;> decide +kernel


end HlawkaSchatten.BelowExponent.Vertex
