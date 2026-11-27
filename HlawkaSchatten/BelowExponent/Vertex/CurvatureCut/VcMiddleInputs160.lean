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

def vcM178CutCell : ParameterCell := ⟨⟨9/40, 1/4⟩, ⟨13/40, 7/20⟩, ⟨0, 1/36⟩⟩
def vcM178CutRoots : Fin 3 → RatBounds := ![⟨5829363956825/4398046511104, 208082668500779/140737488355328⟩, ⟨351763519115173/281474976710656, 393641076774861/281474976710656⟩, ⟨82125403375875/70368744177664, 93860866846625/70368744177664⟩]
def vcM178CutCaps : Fin 3 → Fin 3 → ℚ := ![![21463499693/100000000, 18686423041/100000000, 18473941387/100000000], ![9475624267/100000000, 9482713083/100000000, 4379407369/50000000], ![771294633/50000000, 5724373/390625, 1392682627/100000000]]
def vcM178CutWeightFloor : ℚ := 28984601/25000000
def vcM178CutMargins : Fin 3 → ℚ := ![10263611/400000000, 234205631/10000000000, 113094209/5000000000]

theorem vcM178Cut_roots_ok : vcM178CutCell.rootsOK vcM178CutRoots = true := by decide +kernel

theorem vcM178Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM178CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM178Cut_margin_le (i : Fin 3) : curvatureLoss vcM178CutCell vcM178CutCaps i ≤ vcM178CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM179CutCell : ParameterCell := ⟨⟨9/40, 1/4⟩, ⟨13/40, 7/20⟩, ⟨1/36, 1/18⟩⟩
def vcM179CutRoots : Fin 3 → RatBounds := ![⟨368805755082641/281474976710656, 51389291395857/35184372088832⟩, ⟨347095284556119/281474976710656, 48513171513439/35184372088832⟩, ⟨323647733403165/281474976710656, 92411290869735/70368744177664⟩]
def vcM179CutCaps : Fin 3 → Fin 3 → ℚ := ![![11581754477/50000000, 10043650023/50000000, 1991997571/10000000], ![636761379/6250000, 2556619997/25000000, 2360168053/25000000], ![694345497/50000000, 657921059/50000000, 156212531/12500000]]
def vcM179CutWeightFloor : ℚ := 29969847/25000000
def vcM179CutMargins : Fin 3 → ℚ := ![273954097/10000000000, 49903557/2000000000, 120716749/5000000000]

theorem vcM179Cut_roots_ok : vcM179CutCell.rootsOK vcM179CutRoots = true := by decide +kernel

theorem vcM179Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM179CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM179Cut_margin_le (i : Fin 3) : curvatureLoss vcM179CutCell vcM179CutCaps i ≤ vcM179CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM180CutCell : ParameterCell := ⟨⟨9/40, 1/4⟩, ⟨7/20, 3/8⟩, ⟨0, 1/36⟩⟩
def vcM180CutRoots : Fin 3 → RatBounds := ![⟨186149735445665/140737488355328, 207734047928343/140737488355328⟩, ⟨345426499994993/281474976710656, 387070817700309/281474976710656⟩, ⟨333829161418891/281474976710656, 11905998649929/8796093022208⟩]
def vcM180CutCaps : Fin 3 → Fin 3 → ℚ := ![![1482200873/6250000, 10203468867/50000000, 20811609347/100000000], ![8779824511/100000000, 8596227863/100000000, 4136114379/50000000], ![384945589/25000000, 714135659/50000000, 35728359/2500000]]
def vcM180CutWeightFloor : ℚ := 58850869/50000000
def vcM180CutMargins : Fin 3 → ℚ := ![4198731/156250000, 240362997/10000000000, 9640063/400000000]

theorem vcM180Cut_roots_ok : vcM180CutCell.rootsOK vcM180CutRoots = true := by decide +kernel

theorem vcM180Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM180CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM180Cut_margin_le (i : Fin 3) : curvatureLoss vcM180CutCell vcM180CutCaps i ≤ vcM180CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM181CutCell : ParameterCell := ⟨⟨9/40, 1/4⟩, ⟨7/20, 3/8⟩, ⟨1/36, 1/18⟩⟩
def vcM181CutRoots : Fin 3 → RatBounds := ![⟨368041629434309/281474976710656, 410435340378703/281474976710656⟩, ⟨170352427974705/140737488355328, 381463458751315/281474976710656⟩, ⟨164515984841675/140737488355328, 187636533463379/140737488355328⟩]
def vcM181CutCaps : Fin 3 → Fin 3 → ℚ := ![![5117545617/20000000, 5481040977/25000000, 22445264841/100000000], ![9439694261/100000000, 4634870209/50000000, 356974239/4000000], ![277258131/20000000, 641088291/50000000, 1282792183/100000000]]
def vcM181CutWeightFloor : ℚ := 60821303/50000000
def vcM181CutMargins : Fin 3 → ℚ := ![287022597/10000000000, 5121381/200000000, 257447773/10000000000]

theorem vcM181Cut_roots_ok : vcM181CutCell.rootsOK vcM181CutRoots = true := by decide +kernel

theorem vcM181Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM181CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM181Cut_margin_le (i : Fin 3) : curvatureLoss vcM181CutCell vcM181CutCaps i ≤ vcM181CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM182CutCell : ParameterCell := ⟨⟨9/40, 1/4⟩, ⟨3/8, 2/5⟩, ⟨0, 1/36⟩⟩
def vcM182CutRoots : Fin 3 → RatBounds := ![⟨186020397405175/140737488355328, 415471603744517/281474976710656⟩, ⟨339460378936235/281474976710656, 190515950194457/140737488355328⟩, ⟨339460378936235/281474976710656, 96757951336675/70368744177664⟩]
def vcM182CutCaps : Fin 3 → Fin 3 → ℚ := ![![27353425281/100000000, 4646739799/20000000, 6127702429/25000000], ![1816920609/20000000, 33871671/390625, 4397213623/50000000], ![1546775991/100000000, 1397139713/100000000, 736102141/50000000]]
def vcM182CutWeightFloor : ℚ := 59771997/50000000
def vcM182CutMargins : Fin 3 → ℚ := ![299590847/10000000000, 52546423/2000000000, 54879333/2000000000]

theorem vcM182Cut_roots_ok : vcM182CutCell.rootsOK vcM182CutRoots = true := by decide +kernel

theorem vcM182Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM182CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM182Cut_margin_le (i : Fin 3) : curvatureLoss vcM182CutCell vcM182CutCaps i ≤ vcM182CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM183CutCell : ParameterCell := ⟨⟨9/40, 1/4⟩, ⟨3/8, 2/5⟩, ⟨1/36, 1/18⟩⟩
def vcM183CutRoots : Fin 3 → RatBounds := ![⟨11493309741535/8796093022208, 205221034045577/140737488355328⟩, ⟨167341951729449/140737488355328, 93837387285611/70368744177664⟩, ⟨334718541160477/281474976710656, 47673591737947/35184372088832⟩]
def vcM183CutCaps : Fin 3 → Fin 3 → ℚ := ![![29502651347/100000000, 24943934023/100000000, 1321625491/5000000], ![1953732609/20000000, 4673245509/50000000, 4743967291/50000000], ![1392751441/100000000, 1254027309/100000000, 16524003/1250000]]
def vcM183CutWeightFloor : ℚ := 123462279/100000000
def vcM183CutMargins : Fin 3 → ℚ := ![160120159/5000000000, 279989117/10000000000, 11735139/400000000]

theorem vcM183Cut_roots_ok : vcM183CutCell.rootsOK vcM183CutRoots = true := by decide +kernel

theorem vcM183Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM183CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM183Cut_margin_le (i : Fin 3) : curvatureLoss vcM183CutCell vcM183CutCaps i ≤ vcM183CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM184CutCell : ParameterCell := ⟨⟨1/4, 11/40⟩, ⟨1/4, 11/40⟩, ⟨0, 1/36⟩⟩
def vcM184CutRoots : Fin 3 → RatBounds := ![⟨46347092871403/35184372088832, 413852186928483/281474976710656⟩, ⟨46347092871403/35184372088832, 413852186928483/281474976710656⟩, ⟨318424514863393/281474976710656, 182695218863327/140737488355328⟩]
def vcM184CutCaps : Fin 3 → Fin 3 → ℚ := ![![21386140369/100000000, 3923660441/20000000, 18365212243/100000000], ![336099741/1562500, 5652274041/25000000, 19413798991/100000000], ![402442319/25000000, 1634618101/100000000, 1370323027/100000000]]
def vcM184CutWeightFloor : ℚ := 5618667/5000000
def vcM184CutMargins : Fin 3 → ℚ := ![350655417/10000000000, 345667543/10000000000, 4818209/156250000]

theorem vcM184Cut_roots_ok : vcM184CutCell.rootsOK vcM184CutRoots = true := by decide +kernel

theorem vcM184Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM184CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM184Cut_margin_le (i : Fin 3) : curvatureLoss vcM184CutCell vcM184CutCaps i ≤ vcM184CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM185CutCell : ParameterCell := ⟨⟨1/4, 11/40⟩, ⟨1/4, 11/40⟩, ⟨1/36, 1/18⟩⟩
def vcM185CutRoots : Fin 3 → RatBounds := ![⟨91580837906511/70368744177664, 204293349700303/140737488355328⟩, ⟨91580837906511/70368744177664, 204293349700303/140737488355328⟩, ⟨156730433544393/140737488355328, 359430613578035/281474976710656⟩]
def vcM185CutCaps : Fin 3 → Fin 3 → ℚ := ![![23067775351/100000000, 4223414103/20000000, 19745020379/100000000], ![23117946181/100000000, 24369103979/100000000, 833982791/4000000], ![1448609993/100000000, 58806139/4000000, 614881/50000]]
def vcM185CutWeightFloor : ℚ := 116089961/100000000
def vcM185CutMargins : Fin 3 → ℚ := ![374797883/10000000000, 18477023/500000000, 164503183/5000000000]

theorem vcM185Cut_roots_ok : vcM185CutCell.rootsOK vcM185CutRoots = true := by decide +kernel

theorem vcM185Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM185CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM185Cut_margin_le (i : Fin 3) : curvatureLoss vcM185CutCell vcM185CutCaps i ≤ vcM185CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM186CutCell : ParameterCell := ⟨⟨1/4, 11/40⟩, ⟨11/40, 3/10⟩, ⟨0, 1/36⟩⟩
def vcM186CutRoots : Fin 3 → RatBounds := ![⟨368682669229505/281474976710656, 205694162641271/140737488355328⟩, ⟨1419528225061/1099511627776, 405805520492005/281474976710656⟩, ⟨80748808353071/70368744177664, 184864216130401/140737488355328⟩]
def vcM186CutCaps : Fin 3 → Fin 3 → ℚ := ![![5347810079/25000000, 19482752107/100000000, 18615018303/100000000], ![15896864503/100000000, 2068145077/12500000, 14629650067/100000000], ![787613659/50000000, 196604397/12500000, 695467327/50000000]]
def vcM186CutWeightFloor : ℚ := 113939761/100000000
def vcM186CutMargins : Fin 3 → ℚ := ![76626621/2500000000, 296638161/10000000000, 273139623/10000000000]

theorem vcM186Cut_roots_ok : vcM186CutCell.rootsOK vcM186CutRoots = true := by decide +kernel

theorem vcM186Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM186CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM186Cut_margin_le (i : Fin 3) : curvatureLoss vcM186CutCell vcM186CutCaps i ≤ vcM186CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM187CutCell : ParameterCell := ⟨⟨1/4, 11/40⟩, ⟨11/40, 3/10⟩, ⟨1/36, 1/18⟩⟩
def vcM187CutRoots : Fin 3 → RatBounds := ![⟨364278679840957/281474976710656, 406180913344061/281474976710656⟩, ⟨358890659660129/281474976710656, 200235347546415/140737488355328⟩, ⟨318098549896015/281474976710656, 363864665264677/281474976710656⟩]
def vcM187CutCaps : Fin 3 → Fin 3 → ℚ := ![![5771626537/25000000, 20963419649/100000000, 20049916619/100000000], ![8545802393/50000000, 3568191447/20000000, 15736403367/100000000], ![56715663/4000000, 282851493/20000000, 1248589469/100000000]]
def vcM187CutWeightFloor : ℚ := 14714321/12500000
def vcM187CutMargins : Fin 3 → ℚ := ![40945893/1250000000, 63359959/2000000000, 72905837/2500000000]

theorem vcM187Cut_roots_ok : vcM187CutCell.rootsOK vcM187CutRoots = true := by decide +kernel

theorem vcM187Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM187CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM187Cut_margin_le (i : Fin 3) : curvatureLoss vcM187CutCell vcM187CutCaps i ≤ vcM187CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM188CutCell : ParameterCell := ⟨⟨1/4, 11/40⟩, ⟨3/10, 13/40⟩, ⟨0, 1/36⟩⟩
def vcM188CutRoots : Fin 3 → RatBounds := ![⟨367138975567455/281474976710656, 204830517515797/140737488355328⟩, ⟨356509581016933/281474976710656, 12451065811157/8796093022208⟩, ⟨81953742214711/70368744177664, 374499395106101/281474976710656⟩]
def vcM188CutCaps : Fin 3 → Fin 3 → ℚ := ![![22466629901/100000000, 10142156283/50000000, 19862547011/100000000], ![12587989177/100000000, 6459807131/50000000, 11772810467/100000000], ![24315257/1562500, 152612263/10000000, 1419217359/100000000]]
def vcM188CutWeightFloor : ℚ := 115562093/100000000
def vcM188CutMargins : Fin 3 → ℚ := ![28887363/1000000000, 137062613/5000000000, 26083967/1000000000]

theorem vcM188Cut_roots_ok : vcM188CutCell.rootsOK vcM188CutRoots = true := by decide +kernel

theorem vcM188Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM188CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM188Cut_margin_le (i : Fin 3) : curvatureLoss vcM188CutCell vcM188CutCaps i ≤ vcM188CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM189CutCell : ParameterCell := ⟨⟨1/4, 11/40⟩, ⟨3/10, 13/40⟩, ⟨1/36, 1/18⟩⟩
def vcM189CutRoots : Fin 3 → RatBounds := ![⟨22673167087425/17592186044416, 404495441095021/281474976710656⟩, ⟨10998258325399/8796093022208, 393026678958769/281474976710656⟩, ⟨161491694627763/140737488355328, 368727079339633/281474976710656⟩]
def vcM189CutCaps : Fin 3 → Fin 3 → ℚ := ![![4849744653/20000000, 4363222897/20000000, 21411467207/100000000], ![6768090431/50000000, 13937809863/100000000, 12684566559/100000000], ![280195741/20000000, 54872829/4000000, 1274319521/100000000]]
def vcM189CutWeightFloor : ℚ := 1865123/1562500
def vcM189CutMargins : Fin 3 → ℚ := ![30870709/1000000000, 29255883/1000000000, 55733231/2000000000]

theorem vcM189Cut_roots_ok : vcM189CutCell.rootsOK vcM189CutRoots = true := by decide +kernel

theorem vcM189Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM189CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM189Cut_margin_le (i : Fin 3) : curvatureLoss vcM189CutCell vcM189CutCaps i ≤ vcM189CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM190CutCell : ParameterCell := ⟨⟨1/4, 11/40⟩, ⟨13/40, 7/20⟩, ⟨0, 1/36⟩⟩
def vcM190CutRoots : Fin 3 → RatBounds := ![⟨366122318706395/281474976710656, 408638398448167/281474976710656⟩, ⟨350056207572003/281474976710656, 195835583811055/140737488355328⟩, ⟨166452371941153/140737488355328, 379721282935173/281474976710656⟩]
def vcM190CutCaps : Fin 3 → Fin 3 → ℚ := ![![6181976471/25000000, 2210048019/10000000, 347757167/1562500], ![2143155601/20000000, 2698553967/25000000, 2539297437/25000000], ![1548543063/100000000, 1487608499/100000000, 1453748953/100000000]]
def vcM190CutWeightFloor : ℚ := 117248891/100000000
def vcM190CutMargins : Fin 3 → ℚ := ![145919787/5000000000, 271337889/10000000000, 267253127/10000000000]

theorem vcM190Cut_roots_ok : vcM190CutCell.rootsOK vcM190CutRoots = true := by decide +kernel

theorem vcM190Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM190CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM190Cut_margin_le (i : Fin 3) : curvatureLoss vcM190CutCell vcM190CutCaps i ≤ vcM190CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM191CutCell : ParameterCell := ⟨⟨1/4, 11/40⟩, ⟨13/40, 7/20⟩, ⟨1/36, 1/18⟩⟩
def vcM191CutRoots : Fin 3 → RatBounds := ![⟨45222054024511/35184372088832, 403498964938253/281474976710656⟩, ⟨345432625608313/281474976710656, 386187903524089/281474976710656⟩, ⟨328136583240105/281474976710656, 374036273717733/281474976710656⟩]
def vcM191CutCaps : Fin 3 → Fin 3 → ℚ := ![![1667794097/6250000, 11878452549/50000000, 6000107003/25000000], ![1440286189/12500000, 11649710561/100000000, 5480616679/50000000], ![1394323359/100000000, 133684297/10000000, 1305742873/100000000]]
def vcM191CutWeightFloor : ℚ := 121059971/100000000
def vcM191CutMargins : Fin 3 → ℚ := ![77985121/2500000000, 144754059/5000000000, 285731951/10000000000]

theorem vcM191Cut_roots_ok : vcM191CutCell.rootsOK vcM191CutRoots = true := by decide +kernel

theorem vcM191Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM191CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM191Cut_margin_le (i : Fin 3) : curvatureLoss vcM191CutCell vcM191CutCaps i ≤ vcM191CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM192CutCell : ParameterCell := ⟨⟨1/4, 11/40⟩, ⟨7/20, 3/8⟩, ⟨0, 1/36⟩⟩
def vcM192CutRoots : Fin 3 → RatBounds := ![⟨91404417504567/70368744177664, 408301913949779/281474976710656⟩, ⟨171997581972239/140737488355328, 48182827712819/35184372088832⟩, ⟨338288809821547/281474976710656, 385419892547201/281474976710656⟩]
def vcM192CutCaps : Fin 3 → Fin 3 → ℚ := ![![14234717267/50000000, 25147447399/100000000, 26125770019/100000000], ![1329804149/12500000, 5227308173/50000000, 10332987947/100000000], ![310370941/20000000, 181976701/12500000, 373756553/25000000]]
def vcM192CutWeightFloor : ℚ := 23801611/20000000
def vcM192CutMargins : Fin 3 → ℚ := ![10015561/312500000, 36522817/1250000000, 299253667/10000000000]

theorem vcM192Cut_roots_ok : vcM192CutCell.rootsOK vcM192CutRoots = true := by decide +kernel

theorem vcM192Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM192CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM192Cut_margin_le (i : Fin 3) : curvatureLoss vcM192CutCell vcM192CutCaps i ≤ vcM192CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM193CutCell : ParameterCell := ⟨⟨1/4, 11/40⟩, ⟨7/20, 3/8⟩, ⟨1/36, 1/18⟩⟩
def vcM193CutRoots : Fin 3 → RatBounds := ![⟨180640604308765/140737488355328, 3149791707817/2199023255552⟩, ⟨42413976432763/35184372088832, 189950113627241/140737488355328⟩, ⟨333582511843153/281474976710656, 189909194804763/140737488355328⟩]
def vcM193CutCaps : Fin 3 → Fin 3 → ℚ := ![![959753643/3125000, 6753833869/25000000, 14087021129/50000000], ![1144004167/10000000, 11285518379/100000000, 11163017997/100000000], ![1397513377/100000000, 654004097/50000000, 268664847/20000000]]
def vcM193CutWeightFloor : ℚ := 122798633/100000000
def vcM193CutMargins : Fin 3 → ℚ := ![8569821/250000000, 311841241/10000000000, 320277229/10000000000]

theorem vcM193Cut_roots_ok : vcM193CutCell.rootsOK vcM193CutRoots = true := by decide +kernel

theorem vcM193Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM193CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM193Cut_margin_le (i : Fin 3) : curvatureLoss vcM193CutCell vcM193CutCaps i ≤ vcM193CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM194CutCell : ParameterCell := ⟨⟨11/40, 3/10⟩, ⟨11/40, 3/10⟩, ⟨0, 1/36⟩⟩
def vcM194CutRoots : Fin 3 → RatBounds := ![⟨361626219073745/281474976710656, 100941024852113/70368744177664⟩, ⟨361626219073745/281474976710656, 100941024852113/70368744177664⟩, ⟨327587200897671/281474976710656, 93546644861207/70368744177664⟩]
def vcM194CutCaps : Fin 3 → Fin 3 → ℚ := ![![23060668811/100000000, 5371256777/25000000, 20906371657/100000000], ![17147954591/100000000, 18068776399/100000000, 813263263/5000000], ![1568243303/100000000, 794415601/50000000, 289280491/20000000]]
def vcM194CutWeightFloor : ℚ := 57675507/50000000
def vcM194CutMargins : Fin 3 → ℚ := ![164627837/5000000000, 64867693/2000000000, 60870811/2000000000]

theorem vcM194Cut_roots_ok : vcM194CutCell.rootsOK vcM194CutRoots = true := by decide +kernel

theorem vcM194Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM194CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM194Cut_margin_le (i : Fin 3) : curvatureLoss vcM194CutCell vcM194CutCaps i ≤ vcM194CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM195CutCell : ParameterCell := ⟨⟨11/40, 3/10⟩, ⟨11/40, 3/10⟩, ⟨1/36, 1/18⟩⟩
def vcM195CutRoots : Fin 3 → RatBounds := ![⟨357160759912467/281474976710656, 398479851893485/281474976710656⟩, ⟨357160759912467/281474976710656, 398479851893485/281474976710656⟩, ⟨10086344591455/8796093022208, 368422884195425/281474976710656⟩]
def vcM195CutCaps : Fin 3 → Fin 3 → ℚ := ![![6221983533/25000000, 5780291929/25000000, 22531649201/100000000], ![576061603/3125000, 19496767839/100000000, 68461943/390625], ![1411490269/100000000, 1429370953/100000000, 649614061/50000000]]
def vcM195CutWeightFloor : ℚ := 23805601/20000000
def vcM195CutMargins : Fin 3 → ℚ := ![352066297/10000000000, 346738993/10000000000, 325483531/10000000000]

theorem vcM195Cut_roots_ok : vcM195CutCell.rootsOK vcM195CutRoots = true := by decide +kernel

theorem vcM195Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM195CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM195Cut_margin_le (i : Fin 3) : curvatureLoss vcM195CutCell vcM195CutCaps i ≤ vcM195CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM196CutCell : ParameterCell := ⟨⟨11/40, 3/10⟩, ⟨3/10, 13/40⟩, ⟨0, 1/36⟩⟩
def vcM196CutRoots : Fin 3 → RatBounds := ![⟨11261817177501/8796093022208, 100606125074017/70368744177664⟩, ⟨355032320251847/281474976710656, 396780508768175/281474976710656⟩, ⟨41555735125057/35184372088832, 189545789664863/140737488355328⟩]
def vcM196CutCaps : Fin 3 → Fin 3 → ℚ := ![![12614416053/50000000, 4665628741/20000000, 23254083997/100000000], ![13826737287/100000000, 14346780623/100000000, 13303115513/100000000], ![194277927/12500000, 154518681/10000000, 295507451/20000000]]
def vcM196CutWeightFloor : ℚ := 58483731/50000000
def vcM196CutMargins : Fin 3 → ℚ := ![320112217/10000000000, 309238769/10000000000, 14992703/500000000]

theorem vcM196Cut_roots_ok : vcM196CutCell.rootsOK vcM196CutRoots = true := by decide +kernel

theorem vcM196Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM196CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM196Cut_margin_le (i : Fin 3) : curvatureLoss vcM196CutCell vcM196CutCaps i ≤ vcM196CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM197CutCell : ParameterCell := ⟨⟨11/40, 3/10⟩, ⟨3/10, 13/40⟩, ⟨1/36, 1/18⟩⟩
def vcM197CutRoots : Fin 3 → RatBounds := ![⟨88985531391361/70368744177664, 397174680335223/281474976710656⟩, ⟨87625956960199/70368744177664, 391416232343429/281474976710656⟩, ⟨327692154841763/281474976710656, 373423387555703/281474976710656⟩]
def vcM197CutCaps : Fin 3 → Fin 3 → ℚ := ![![5444992641/20000000, 12545671147/50000000, 25073671221/100000000], ![3716541891/25000000, 7744265403/50000000, 1794857567/12500000], ![1399232971/100000000, 173727991/12500000, 265541961/20000000]]
def vcM197CutWeightFloor : ℚ := 120659021/100000000
def vcM197CutMargins : Fin 3 → ℚ := ![42791581/1250000000, 330435197/10000000000, 160436249/5000000000]

theorem vcM197Cut_roots_ok : vcM197CutCell.rootsOK vcM197CutRoots = true := by decide +kernel

theorem vcM197Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM197CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM197Cut_margin_le (i : Fin 3) : curvatureLoss vcM197CutCell vcM197CutCaps i ≤ vcM197CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM198CutCell : ParameterCell := ⟨⟨11/40, 3/10⟩, ⟨13/40, 7/20⟩, ⟨0, 1/36⟩⟩
def vcM198CutRoots : Fin 3 → RatBounds := ![⟨179818251154763/140737488355328, 401762430996421/281474976710656⟩, ⟨87213572909191/70368744177664, 195189257797741/140737488355328⟩, ⟨42199077705839/35184372088832, 192232067898733/140737488355328⟩]
def vcM198CutCaps : Fin 3 → Fin 3 → ℚ := ![![5788789589/20000000, 26507177123/100000000, 1358268357/5000000], ![313171733/2500000, 254566899/2000000, 6129597407/50000000], ![388246051/25000000, 60489011/4000000, 758288931/50000000]]
def vcM198CutWeightFloor : ℚ := 59325177/50000000
def vcM198CutMargins : Fin 3 → ℚ := ![338969389/10000000000, 321113023/10000000000, 161315939/5000000000]

theorem vcM198Cut_roots_ok : vcM198CutCell.rootsOK vcM198CutRoots = true := by decide +kernel

theorem vcM198Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM198CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM198Cut_margin_le (i : Fin 3) : curvatureLoss vcM198CutCell vcM198CutCaps i ≤ vcM198CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM199CutCell : ParameterCell := ⟨⟨11/40, 3/10⟩, ⟨13/40, 7/20⟩, ⟨1/36, 1/18⟩⟩
def vcM199CutRoots : Fin 3 → RatBounds := ![⟨355216604431461/281474976710656, 396531366384645/281474976710656⟩, ⟨344261196509653/281474976710656, 384930953358101/281474976710656⟩, ⟨83226872320777/70368744177664, 378887333402059/281474976710656⟩]
def vcM199CutCaps : Fin 3 → Fin 3 → ℚ := ![![3903060231/12500000, 14246514637/50000000, 29295017641/100000000], ![6734427547/50000000, 13744710131/100000000, 1324679171/10000000], ![1398407663/100000000, 679937093/50000000, 1363355017/100000000]]
def vcM199CutWeightFloor : ℚ := 122326921/100000000
def vcM199CutMargins : Fin 3 → ℚ := ![45331803/1250000000, 34309841/1000000000, 345507529/10000000000]

theorem vcM199Cut_roots_ok : vcM199CutCell.rootsOK vcM199CutRoots = true := by decide +kernel

theorem vcM199Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM199CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM199Cut_margin_le (i : Fin 3) : curvatureLoss vcM199CutCell vcM199CutCaps i ≤ vcM199CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM200CutCell : ParameterCell := ⟨⟨11/40, 3/10⟩, ⟨7/20, 3/8⟩, ⟨0, 1/36⟩⟩
def vcM200CutRoots : Fin 3 → RatBounds := ![⟨359390470788423/281474976710656, 401766058296083/281474976710656⟩, ⟨343052385469853/281474976710656, 384510629964081/281474976710656⟩, ⟨343052385469853/281474976710656, 390333065932483/281474976710656⟩]
def vcM200CutCaps : Fin 3 → Fin 3 → ℚ := ![![17371248107/50000000, 15721816027/50000000, 16616077361/50000000], ![102665623/781250, 2603616097/20000000, 103219089/781250], ![390881813/25000000, 185789879/12500000, 390914469/25000000]]
def vcM200CutWeightFloor : ℚ := 120406707/100000000
def vcM200CutMargins : Fin 3 → ℚ := ![97292923/2500000000, 361692769/10000000000, 604683/16000000]

theorem vcM200Cut_roots_ok : vcM200CutCell.rootsOK vcM200CutRoots = true := by decide +kernel

theorem vcM200Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM200CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM200Cut_margin_le (i : Fin 3) : curvatureLoss vcM200CutCell vcM200CutCaps i ≤ vcM200CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM201CutCell : ParameterCell := ⟨⟨11/40, 3/10⟩, ⟨7/20, 3/8⟩, ⟨1/36, 1/18⟩⟩
def vcM201CutRoots : Fin 3 → RatBounds := ![⟨177486798306995/140737488355328, 396538318875223/281474976710656⟩, ⟨169196536473755/140737488355328, 378976377596317/281474976710656⟩, ⟨338434151058395/281474976710656, 384843881235077/281474976710656⟩]
def vcM201CutCaps : Fin 3 → Fin 3 → ℚ := ![![37461717061/100000000, 33774810027/100000000, 35832215291/100000000], ![14130045349/100000000, 3513864641/25000000, 14276588697/100000000], ![1408157871/100000000, 10690843/800000, 1406324739/100000000]]
def vcM201CutWeightFloor : ℚ := 31009383/25000000
def vcM201CutMargins : Fin 3 → ℚ := ![208321207/5000000000, 96640801/2500000000, 405039121/10000000000]

theorem vcM201Cut_roots_ok : vcM201CutCell.rootsOK vcM201CutRoots = true := by decide +kernel

theorem vcM201Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM201CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM201Cut_margin_le (i : Fin 3) : curvatureLoss vcM201CutCell vcM201CutCaps i ≤ vcM201CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM202CutCell : ParameterCell := ⟨⟨3/10, 13/40⟩, ⟨3/10, 13/40⟩, ⟨0, 1/36⟩⟩
def vcM202CutRoots : Fin 3 → RatBounds := ![⟨354059292533981/281474976710656, 395801499166787/281474976710656⟩, ⟨354059292533981/281474976710656, 395801499166787/281474976710656⟩, ⟨337361670601189/281474976710656, 48018427519759/35184372088832⟩]
def vcM202CutCaps : Fin 3 → Fin 3 → ℚ := ![![5759299837/20000000, 27259928763/100000000, 13806670679/50000000], ![604332949/4000000, 15891047077/100000000, 7494138553/50000000], ![310117681/20000000, 391750509/25000000, 768801023/50000000]]
def vcM202CutWeightFloor : ℚ := 59233063/50000000
def vcM202CutMargins : Fin 3 → ℚ := ![7159239/200000000, 352230831/10000000000, 347655411/10000000000]

theorem vcM202Cut_roots_ok : vcM202CutCell.rootsOK vcM202CutRoots = true := by decide +kernel

theorem vcM202Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM202CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM202Cut_margin_le (i : Fin 3) : curvatureLoss vcM202CutCell vcM202CutCaps i ≤ vcM202CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM203CutCell : ParameterCell := ⟨⟨3/10, 13/40⟩, ⟨3/10, 13/40⟩, ⟨1/36, 1/18⟩⟩
def vcM203CutRoots : Fin 3 → RatBounds := ![⟨87388481035911/70368744177664, 12202007059669/8796093022208⟩, ⟨87388481035911/70368744177664, 12202007059669/8796093022208⟩, ⟨332683567373233/281474976710656, 189289405880407/140737488355328⟩]
def vcM203CutCaps : Fin 3 → Fin 3 → ℚ := ![![3105993299/10000000, 7329543451/25000000, 1488825533/5000000], ![16239429839/100000000, 17155378099/100000000, 2023266277/12500000], ![55833483/4000000, 176264551/12500000, 1382630183/100000000]]
def vcM203CutWeightFloor : ℚ := 122041171/100000000
def vcM203CutMargins : Fin 3 → ℚ := ![382989207/10000000000, 75335057/2000000000, 186209343/5000000000]

theorem vcM203Cut_roots_ok : vcM203CutCell.rootsOK vcM203CutRoots = true := by decide +kernel

theorem vcM203Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM203CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM203Cut_margin_le (i : Fin 3) : curvatureLoss vcM203CutCell vcM203CutCaps i ≤ vcM203CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM204CutCell : ParameterCell := ⟨⟨3/10, 13/40⟩, ⟨13/40, 7/20⟩, ⟨0, 1/36⟩⟩
def vcM204CutRoots : Fin 3 → RatBounds := ![⟨353576264456175/281474976710656, 98869885555611/70368744177664⟩, ⟨174070017411533/140737488355328, 24358735496487/17592186044416⟩, ⟨342584373648571/281474976710656, 389690614590925/281474976710656⟩]
def vcM204CutCaps : Fin 3 → Fin 3 → ℚ := ![![8628033927/25000000, 809036119/2500000, 33698820307/100000000], ![14934416551/100000000, 1917449573/12500000, 7585769649/50000000], ![1557071561/100000000, 385121401/25000000, 63297831/4000000]]
def vcM204CutWeightFloor : ℚ := 60073363/50000000
def vcM204CutMargins : Fin 3 → ℚ := ![401319241/10000000000, 77504493/2000000000, 49632809/1250000000]

theorem vcM204Cut_roots_ok : vcM204CutCell.rootsOK vcM204CutRoots = true := by decide +kernel

theorem vcM204Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM204CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM204Cut_margin_le (i : Fin 3) : curvatureLoss vcM204CutCell vcM204CutCaps i ≤ vcM204CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM205CutCell : ParameterCell := ⟨⟨3/10, 13/40⟩, ⟨13/40, 7/20⟩, ⟨1/36, 1/18⟩⟩
def vcM205CutRoots : Fin 3 → RatBounds := ![⟨349080608534853/281474976710656, 195076743674283/140737488355328⟩, ⟨343563634355015/281474976710656, 3002434862069/2199023255552⟩, ⟨168989948727113/140737488355328, 384217497951089/281474976710656⟩]
def vcM205CutCaps : Fin 3 → Fin 3 → ℚ := ![![18604366853/50000000, 34780612453/100000000, 1816911759/5000000], ![16053116357/100000000, 16561499669/100000000, 16392179147/100000000], ![1401993641/100000000, 692995033/50000000, 1423653727/100000000]]
def vcM205CutWeightFloor : ℚ := 7730121/6250000
def vcM205CutMargins : Fin 3 → ℚ := ![429630519/10000000000, 414478211/10000000000, 425687591/10000000000]

theorem vcM205Cut_roots_ok : vcM205CutCell.rootsOK vcM205CutRoots = true := by decide +kernel

theorem vcM205Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM205CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM205Cut_margin_le (i : Fin 3) : curvatureLoss vcM205CutCell vcM205CutCaps i ≤ vcM205CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM206CutCell : ParameterCell := ⟨⟨13/40, 7/20⟩, ⟨13/40, 7/20⟩, ⟨0, 1/36⟩⟩
def vcM206CutRoots : Fin 3 → RatBounds := ![⟨347903083926075/281474976710656, 389743548585795/281474976710656⟩, ⟨347903083926075/281474976710656, 389743548585795/281474976710656⟩, ⟨347903083926075/281474976710656, 395427755854527/281474976710656⟩]
def vcM206CutCaps : Fin 3 → Fin 3 → ℚ := ![![42335844459/100000000, 10156658271/25000000, 8597481589/20000000], ![9121025189/50000000, 474200323/2500000, 4813838817/25000000], ![779485023/50000000, 314518677/20000000, 1651824911/100000000]]
def vcM206CutWeightFloor : ℚ := 121741499/100000000
def vcM206CutMargins : Fin 3 → ℚ := ![244150583/5000000000, 480750933/10000000000, 502203541/10000000000]

theorem vcM206Cut_roots_ok : vcM206CutCell.rootsOK vcM206CutRoots = true := by decide +kernel

theorem vcM206Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM206CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM206Cut_margin_le (i : Fin 3) : curvatureLoss vcM206CutCell vcM206CutCaps i ≤ vcM206CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM207CutCell : ParameterCell := ⟨⟨13/40, 7/20⟩, ⟨13/40, 7/20⟩, ⟨1/36, 1/18⟩⟩
def vcM207CutRoots : Fin 3 → RatBounds := ![⟨171664899122715/140737488355328, 384318904326347/281474976710656⟩, ⟨171664899122715/140737488355328, 384318904326347/281474976710656⟩, ⟨85844287295423/70368744177664, 390054249194131/281474976710656⟩]
def vcM207CutCaps : Fin 3 → Fin 3 → ℚ := ![![5700842997/12500000, 43654130523/100000000, 5793204839/12500000], ![3919910761/20000000, 5117380339/25000000, 831836399/4000000], ![280710313/20000000, 1415415609/100000000, 74354619/5000000]]
def vcM207CutWeightFloor : ℚ := 31281139/25000000
def vcM207CutMargins : Fin 3 → ℚ := ![522961543/10000000000, 257308901/5000000000, 538886447/10000000000]

theorem vcM207Cut_roots_ok : vcM207CutCell.rootsOK vcM207CutRoots = true := by decide +kernel

theorem vcM207Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM207CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM207Cut_margin_le (i : Fin 3) : curvatureLoss vcM207CutCell vcM207CutCaps i ≤ vcM207CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM1Child0CutCell : ParameterCell := ⟨⟨1/20, 1/16⟩, ⟨1/8, 11/80⟩, ⟨1/36, 1/24⟩⟩
def vcM1Child0CutRoots : Fin 3 → RatBounds := ![⟨543851821740283/281474976710656, 589294652093481/281474976710656⟩, ⟨524753217766547/281474976710656, 284503258819669/140737488355328⟩, ⟨136384633552877/140737488355328, 304530603803/274877906944⟩]
def vcM1Child0CutCaps : Fin 3 → Fin 3 → ℚ := ![![2486308793/5000000, 43833196379/100000000, 9902736173/50000000], ![909017047/2500000, 38381913323/100000000, 7468270487/50000000], ![540227657/50000000, 144483561/12500000, 447493957/100000000]]
def vcM1Child0CutWeightFloor : ℚ := 25981111/25000000
def vcM1Child0CutMargins : Fin 3 → ℚ := ![170743659/10000000000, 40840873/2500000000, 34467261/5000000000]

theorem vcM1Child0Cut_roots_ok : vcM1Child0CutCell.rootsOK vcM1Child0CutRoots = true := by decide +kernel

theorem vcM1Child0Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM1Child0CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM1Child0Cut_margin_le (i : Fin 3) : curvatureLoss vcM1Child0CutCell vcM1Child0CutCaps i ≤ vcM1Child0CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM1Child1CutCell : ParameterCell := ⟨⟨1/20, 1/16⟩, ⟨1/8, 11/80⟩, ⟨1/24, 1/18⟩⟩
def vcM1Child1CutRoots : Fin 3 → RatBounds := ![⟨541298865035999/281474976710656, 586477387965781/281474976710656⟩, ⟨521852126569779/281474976710656, 565805338461737/281474976710656⟩, ⟨134950671851991/140737488355328, 77123041158819/70368744177664⟩]
def vcM1Child1CutCaps : Fin 3 → Fin 3 → ℚ := ![![51212032077/100000000, 45157234911/100000000, 2028234063/10000000], ![7487730317/20000000, 39498344963/100000000, 15292430423/100000000], ![205434263/20000000, 1096750859/100000000, 423822467/100000000]]
def vcM1Child1CutWeightFloor : ℚ := 106334703/100000000
def vcM1Child1CutMargins : Fin 3 → ℚ := ![3512453/200000000, 167987487/10000000000, 17625981/2500000000]

theorem vcM1Child1Cut_roots_ok : vcM1Child1CutCell.rootsOK vcM1Child1CutRoots = true := by decide +kernel

theorem vcM1Child1Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM1Child1CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM1Child1Cut_margin_le (i : Fin 3) : curvatureLoss vcM1Child1CutCell vcM1Child1CutCaps i ≤ vcM1Child1CutMargins i := by
  fin_cases i <;> decide +kernel


end HlawkaSchatten.BelowExponent.Vertex
