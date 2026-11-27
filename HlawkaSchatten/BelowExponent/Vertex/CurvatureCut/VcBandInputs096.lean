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

def vcS196CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨37/80, 19/40⟩, ⟨0, 1/40⟩⟩
def vcS196CutRoots : Fin 3 → RatBounds := ![⟨228137860698645/140737488355328, 486899136227261/281474976710656⟩, ⟨88948733203491/70368744177664, 382918828887523/281474976710656⟩, ⟨345215637333551/281474976710656, 375689234997151/281474976710656⟩]
def vcS196CutCaps : Fin 3 → Fin 3 → ℚ := ![![411915099/6250000, 3809700219/100000000, 3011744927/100000000], ![468940927/20000000, 7339086/390625, 864252353/50000000], ![516154101/50000000, 770977769/100000000, 95300427/12500000]]
def vcS196CutWeightFloor : ℚ := 122645231/100000000
def vcS196CutMargins : Fin 3 → ℚ := ![6379189/2500000000, 4283407/2500000000, 15214577/10000000000]

theorem vcS196Cut_roots_ok : vcS196CutCell.rootsOK vcS196CutRoots = true := by decide +kernel

theorem vcS196Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS196CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS196Cut_margin_le (i : Fin 3) : curvatureLoss vcS196CutCell vcS196CutCaps i ≤ vcS196CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS197CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨37/80, 19/40⟩, ⟨1/40, 1/20⟩⟩
def vcS197CutRoots : Fin 3 → RatBounds := ![⟨226517880702205/140737488355328, 120785835596383/70368744177664⟩, ⟨175247253263733/140737488355328, 47107098462027/35184372088832⟩, ⟨42487890973871/35184372088832, 369604754847791/281474976710656⟩]
def vcS197CutCaps : Fin 3 → Fin 3 → ℚ := ![![1725952697/25000000, 250494301/6250000, 1594222269/50000000], ![613770291/25000000, 1962244167/100000000, 451498327/25000000], ![923570563/100000000, 687208649/100000000, 340024323/50000000]]
def vcS197CutWeightFloor : ℚ := 15959979/12500000
def vcS197CutMargins : Fin 3 → ℚ := ![25494481/10000000000, 17029273/10000000000, 7533821/5000000000]

theorem vcS197Cut_roots_ok : vcS197CutCell.rootsOK vcS197CutRoots = true := by decide +kernel

theorem vcS197Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS197CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS197Cut_margin_le (i : Fin 3) : curvatureLoss vcS197CutCell vcS197CutCaps i ≤ vcS197CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS198CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨37/80, 19/40⟩, ⟨1/20, 3/40⟩⟩
def vcS198CutRoots : Fin 3 → RatBounds := ![⟨225024642224217/140737488355328, 479700479814973/281474976710656⟩, ⟨86411207967899/70368744177664, 371334217814093/281474976710656⟩, ⟨335044088577907/281474976710656, 364063089036657/281474976710656⟩]
def vcS198CutCaps : Fin 3 → Fin 3 → ℚ := ![![7217828931/100000000, 1051054017/25000000, 336423161/10000000], ![2564509773/100000000, 12781689/625000, 117680891/6250000], ![830560327/100000000, 615942819/100000000, 304968283/50000000]]
def vcS198CutWeightFloor : ℚ := 66365569/50000000
def vcS198CutMargins : Fin 3 → ℚ := ![25594883/10000000000, 17017691/10000000000, 15013423/10000000000]

theorem vcS198Cut_roots_ok : vcS198CutCell.rootsOK vcS198CutRoots = true := by decide +kernel

theorem vcS198Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS198CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS198Cut_margin_le (i : Fin 3) : curvatureLoss vcS198CutCell vcS198CutCaps i ≤ vcS198CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS199CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨37/80, 19/40⟩, ⟨3/40, 1/10⟩⟩
def vcS199CutRoots : Fin 3 → RatBounds := ![⟨447287390177711/281474976710656, 119133159696213/70368744177664⟩, ⟨341190387694669/281474976710656, 366281708920385/281474976710656⟩, ⟨165291258803235/140737488355328, 358994275401731/281474976710656⟩]
def vcS199CutCaps : Fin 3 → Fin 3 → ℚ := ![![470680761/6250000, 175950943/4000000, 176932647/5000000], ![534613697/20000000, 1063664857/50000000, 6122661/312500], ![750455707/100000000, 554862843/100000000, 549804783/100000000]]
def vcS199CutWeightFloor : ℚ := 27559267/20000000
def vcS199CutMargins : Fin 3 → ℚ := ![12896273/5000000000, 8540581/5000000000, 3006689/2000000000]

theorem vcS199Cut_roots_ok : vcS199CutCell.rootsOK vcS199CutRoots = true := by decide +kernel

theorem vcS199Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS199CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS199Cut_margin_le (i : Fin 3) : curvatureLoss vcS199CutCell vcS199CutCaps i ≤ vcS199CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1100CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨19/40, 39/80⟩, ⟨0, 1/40⟩⟩
def vcS1100CutRoots : Fin 3 → RatBounds := ![⟨111345831489/68719476736, 486778560527083/281474976710656⟩, ⟨2751260508223/2199023255552, 189618195281039/140737488355328⟩, ⟨174318574991173/140737488355328, 189616584241077/140737488355328⟩]
def vcS1100CutCaps : Fin 3 → Fin 3 → ℚ := ![![653085643/10000000, 1871998211/50000000, 30425047/1000000], ![581702351/25000000, 224824801/12500000, 889274379/50000000], ![20639027/2000000, 189237439/25000000, 387510931/50000000]]
def vcS1100CutWeightFloor : ℚ := 123860797/100000000
def vcS1100CutMargins : Fin 3 → ℚ := ![25362249/10000000000, 16739051/10000000000, 15470979/10000000000]

theorem vcS1100Cut_roots_ok : vcS1100CutCell.rootsOK vcS1100CutRoots = true := by decide +kernel

theorem vcS1100Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1100CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1100Cut_margin_le (i : Fin 3) : curvatureLoss vcS1100CutCell vcS1100CutCaps i ≤ vcS1100CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1101CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨19/40, 39/80⟩, ⟨1/40, 1/20⟩⟩
def vcS1101CutRoots : Fin 3 → RatBounds := ![⟨452834737845759/281474976710656, 483025081378607/281474976710656⟩, ⟨86714164959463/70368744177664, 373165111028741/281474976710656⟩, ⟨343329835916355/281474976710656, 373158915626013/281474976710656⟩]
def vcS1101CutCaps : Fin 3 → Fin 3 → ℚ := ![![6842451231/100000000, 196909133/5000000, 3222661907/100000000], ![2436241701/100000000, 234831413/12500000, 371601613/20000000], ![923239663/100000000, 674676851/100000000, 86413027/12500000]]
def vcS1101CutWeightFloor : ℚ := 64461099/50000000
def vcS1101CutMargins : Fin 3 → ℚ := ![25335257/10000000000, 16631917/10000000000, 7661999/5000000000]

theorem vcS1101Cut_roots_ok : vcS1101CutCell.rootsOK vcS1101CutRoots = true := by decide +kernel

theorem vcS1101Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1101CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1101Cut_margin_le (i : Fin 3) : curvatureLoss vcS1101CutCell vcS1101CutCaps i ≤ vcS1101CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1102CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨19/40, 39/80⟩, ⟨1/20, 3/40⟩⟩
def vcS1102CutRoots : Fin 3 → RatBounds := ![⟨449850266087115/281474976710656, 119896090463231/70368744177664⟩, ⟨342003670518767/281474976710656, 91908708495075/70368744177664⟩, ⟨169237506626729/140737488355328, 367625884971661/281474976710656⟩]
def vcS1102CutCaps : Fin 3 → Fin 3 → ℚ := ![![7154505423/100000000, 4130490571/100000000, 1700872597/50000000], ![2544735129/100000000, 1958110963/100000000, 1936875283/100000000], ![207563361/25000000, 302343673/50000000, 620031841/100000000]]
def vcS1102CutWeightFloor : ℚ := 67000421/50000000
def vcS1102CutMargins : Fin 3 → ℚ := ![5086037/2000000000, 207699/125000000, 954437/625000000]

theorem vcS1102Cut_roots_ok : vcS1102CutCell.rootsOK vcS1102CutRoots = true := by decide +kernel

theorem vcS1102Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1102CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1102Cut_margin_le (i : Fin 3) : curvatureLoss vcS1102CutCell vcS1102CutCaps i ≤ vcS1102CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1103CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨19/40, 39/80⟩, ⟨3/40, 1/10⟩⟩
def vcS1103CutRoots : Fin 3 → RatBounds := ![⟨223545114504541/140737488355328, 238209255489803/140737488355328⟩, ⟨168773344474007/140737488355328, 90643971998087/70368744177664⟩, ⟨167008423402555/140737488355328, 90641095137341/70368744177664⟩]
def vcS1103CutCaps : Fin 3 → Fin 3 → ℚ := ![![1493120783/20000000, 4321085437/100000000, 3579425601/100000000], ![2652366669/100000000, 2037021227/100000000, 1007597143/50000000], ![750170931/100000000, 544704009/100000000, 558904939/100000000]]
def vcS1103CutWeightFloor : ℚ := 139093821/100000000
def vcS1103CutMargins : Fin 3 → ℚ := ![6405593/2500000000, 8336839/5000000000, 15293437/10000000000]

theorem vcS1103Cut_roots_ok : vcS1103CutCell.rootsOK vcS1103CutRoots = true := by decide +kernel

theorem vcS1103Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1103CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1103Cut_margin_le (i : Fin 3) : curvatureLoss vcS1103CutCell vcS1103CutCaps i ≤ vcS1103CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1104CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨3/20, 13/80⟩, ⟨0, 1/40⟩⟩
def vcS1104CutRoots : Fin 3 → RatBounds := ![⟨540967670457213/281474976710656, 587720616265253/281474976710656⟩, ⟨513542098789139/281474976710656, 17460607149445/8796093022208⟩, ⟨279577655198877/281474976710656, 320882347938615/281474976710656⟩]
def vcS1104CutCaps : Fin 3 → Fin 3 → ℚ := ![![16709995347/50000000, 1745389701/6250000, 612166171/5000000], ![19500105961/100000000, 525977309/2500000, 1743514607/25000000], ![54089249/4000000, 72922891/5000000, 295291093/50000000]]
def vcS1104CutWeightFloor : ℚ := 19865187/20000000
def vcS1104CutMargins : Fin 3 → ℚ := ![113923871/10000000000, 13378701/1250000000, 42147873/10000000000]

theorem vcS1104Cut_roots_ok : vcS1104CutCell.rootsOK vcS1104CutRoots = true := by decide +kernel

theorem vcS1104Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1104CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1104Cut_margin_le (i : Fin 3) : curvatureLoss vcS1104CutCell vcS1104CutCaps i ≤ vcS1104CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1105CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨3/20, 13/80⟩, ⟨1/40, 1/20⟩⟩
def vcS1105CutRoots : Fin 3 → RatBounds := ![⟨134113220993927/70368744177664, 291247097278091/140737488355328⟩, ⟨508056339749117/281474976710656, 34527049386091/17592186044416⟩, ⟨137085576174727/140737488355328, 314324610029721/281474976710656⟩]
def vcS1105CutCaps : Fin 3 → Fin 3 → ℚ := ![![35178718841/100000000, 29446702007/100000000, 12789993933/100000000], ![20498443729/100000000, 2760408403/12500000, 1457584439/20000000], ![610765369/50000000, 1311560733/100000000, 264857341/50000000]]
def vcS1105CutWeightFloor : ℚ := 51899111/50000000
def vcS1105CutMargins : Fin 3 → ℚ := ![29571917/2500000000, 693069/62500000, 10838269/2500000000]

theorem vcS1105Cut_roots_ok : vcS1105CutCell.rootsOK vcS1105CutRoots = true := by decide +kernel

theorem vcS1105Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1105CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1105Cut_margin_le (i : Fin 3) : curvatureLoss vcS1105CutCell vcS1105CutCaps i ≤ vcS1105CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1106CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨3/20, 13/80⟩, ⟨1/20, 3/40⟩⟩
def vcS1106CutRoots : Fin 3 → RatBounds := ![⟨66536235148519/35184372088832, 577695674728811/281474976710656⟩, ⟨503011520638245/281474976710656, 546655838525405/281474976710656⟩, ⟨134616845414219/140737488355328, 77090547672783/70368744177664⟩]
def vcS1106CutCaps : Fin 3 → Fin 3 → ℚ := ![![4615098981/12500000, 30950165879/100000000, 3332921819/25000000], ![21486462307/100000000, 5779408269/25000000, 1519724389/20000000], ![554159379/50000000, 1185217731/100000000, 119391191/25000000]]
def vcS1106CutWeightFloor : ℚ := 27068671/25000000
def vcS1106CutMargins : Fin 3 → ℚ := ![122735409/10000000000, 28715171/2500000000, 8922097/2000000000]

theorem vcS1106Cut_roots_ok : vcS1106CutCell.rootsOK vcS1106CutRoots = true := by decide +kernel

theorem vcS1106Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1106CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1106Cut_margin_le (i : Fin 3) : curvatureLoss vcS1106CutCell vcS1106CutCaps i ≤ vcS1106CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1107CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨3/20, 13/80⟩, ⟨3/40, 1/10⟩⟩
def vcS1107CutRoots : Fin 3 → RatBounds := ![⟨264219269602323/140737488355328, 286636930484159/140737488355328⟩, ⟨249177860228371/140737488355328, 541343489343725/281474976710656⟩, ⟨132353366994255/140737488355328, 151458742630023/140737488355328⟩]
def vcS1107CutCaps : Fin 3 → Fin 3 → ℚ := ![![9662071787/25000000, 16219324609/50000000, 13869014263/100000000], ![11232675153/50000000, 24143294609/100000000, 7906528783/100000000], ![1009680689/100000000, 1075831143/100000000, 432569941/100000000]]
def vcS1107CutWeightFloor : ℚ := 56377323/50000000
def vcS1107CutMargins : Fin 3 → ℚ := ![7953169/625000000, 5945827/500000000, 45909811/10000000000]

theorem vcS1107Cut_roots_ok : vcS1107CutCell.rootsOK vcS1107CutRoots = true := by decide +kernel

theorem vcS1107Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1107CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1107Cut_margin_le (i : Fin 3) : curvatureLoss vcS1107CutCell vcS1107CutCaps i ≤ vcS1107CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1108CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨13/80, 7/40⟩, ⟨0, 1/40⟩⟩
def vcS1108CutRoots : Fin 3 → RatBounds := ![⟨132928434450323/70368744177664, 72024326242133/35184372088832⟩, ⟨62705036105379/35184372088832, 544502246978485/281474976710656⟩, ⟨282032779777375/281474976710656, 80460385061313/70368744177664⟩]
def vcS1108CutCaps : Fin 3 → Fin 3 → ℚ := ![![28375052919/100000000, 5784380001/25000000, 2075611713/20000000], ![15863791679/100000000, 17168318787/100000000, 141818937/2500000], ![162947727/12500000, 279054821/20000000, 589195807/100000000]]
def vcS1108CutWeightFloor : ℚ := 100198171/100000000
def vcS1108CutMargins : Fin 3 → ℚ := ![96588227/10000000000, 89622921/10000000000, 35952343/10000000000]

theorem vcS1108Cut_roots_ok : vcS1108CutCell.rootsOK vcS1108CutRoots = true := by decide +kernel

theorem vcS1108Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1108CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1108Cut_margin_le (i : Fin 3) : curvatureLoss vcS1108CutCell vcS1108CutCaps i ≤ vcS1108CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1109CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨13/80, 7/40⟩, ⟨1/40, 1/20⟩⟩
def vcS1109CutRoots : Fin 3 → RatBounds := ![⟨16478728412941/8796093022208, 571113294370321/281474976710656⟩, ⟨496199990738773/281474976710656, 538259661042507/281474976710656⟩, ⟨17289225983083/17592186044416, 157661719918551/140737488355328⟩]
def vcS1109CutCaps : Fin 3 → Fin 3 → ℚ := ![![5970021931/20000000, 12199498269/50000000, 216979369/2000000], ![833352201/5000000, 4502715727/25000000, 5932401259/100000000], ![588460501/50000000, 9796621/781250, 52830219/10000000]]
def vcS1109CutWeightFloor : ℚ := 104703677/100000000
def vcS1109CutMargins : Fin 3 → ℚ := ![781629/78125000, 46314189/5000000000, 18451737/5000000000]

theorem vcS1109Cut_roots_ok : vcS1109CutCell.rootsOK vcS1109CutRoots = true := by decide +kernel

theorem vcS1109Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1109CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1109Cut_margin_le (i : Fin 3) : curvatureLoss vcS1109CutCell vcS1109CutCaps i ≤ vcS1109CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1110CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨13/80, 7/40⟩, ⟨1/20, 3/40⟩⟩
def vcS1110CutRoots : Fin 3 → RatBounds := ![⟨261633782616571/140737488355328, 566448692252133/281474976710656⟩, ⟨245599276287103/140737488355328, 266271683804501/140737488355328⟩, ⟨135845619473291/140737488355328, 309396884287785/281474976710656⟩]
def vcS1110CutCaps : Fin 3 → Fin 3 → ℚ := ![![3914025877/12500000, 12823276179/50000000, 11315606641/100000000], ![8731163613/50000000, 18845775387/100000000, 6189400529/100000000], ![533640373/50000000, 566260337/50000000, 476145943/100000000]]
def vcS1110CutWeightFloor : ℚ := 4368541/4000000
def vcS1110CutMargins : Fin 3 → ℚ := ![51800447/5000000000, 5984181/625000000, 18954679/5000000000]

theorem vcS1110Cut_roots_ok : vcS1110CutCell.rootsOK vcS1110CutRoots = true := by decide +kernel

theorem vcS1110Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1110CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1110Cut_margin_le (i : Fin 3) : curvatureLoss vcS1110CutCell vcS1110CutCaps i ≤ vcS1110CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1111CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨13/80, 7/40⟩, ⟨3/40, 1/10⟩⟩
def vcS1111CutRoots : Fin 3 → RatBounds := ![⟨519519403080479/281474976710656, 140537720923595/70368744177664⟩, ⟨121646034385355/70368744177664, 32955530480161/17592186044416⟩, ⟨133582577473901/140737488355328, 303984774141211/281474976710656⟩]
def vcS1111CutCaps : Fin 3 → Fin 3 → ℚ := ![![16381452977/50000000, 26881818203/100000000, 11778554557/100000000], ![9125271901/50000000, 9836952121/50000000, 6444061673/100000000], ![971813837/100000000, 1027444263/100000000, 10778977/2500000]]
def vcS1111CutWeightFloor : ℚ := 22745399/20000000
def vcS1111CutMargins : Fin 3 → ℚ := ![5361397/500000000, 49478027/5000000000, 19479739/5000000000]

theorem vcS1111Cut_roots_ok : vcS1111CutCell.rootsOK vcS1111CutRoots = true := by decide +kernel

theorem vcS1111Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1111CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1111Cut_margin_le (i : Fin 3) : curvatureLoss vcS1111CutCell vcS1111CutCaps i ≤ vcS1111CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1112CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨7/40, 3/16⟩, ⟨0, 1/40⟩⟩
def vcS1112CutRoots : Fin 3 → RatBounds := ![⟨523323869442605/281474976710656, 565844193951497/281474976710656⟩, ⟨245315481039737/140737488355328, 531474066158929/281474976710656⟩, ⟨71111998036069/70368744177664, 322947436174715/281474976710656⟩]
def vcS1112CutCaps : Fin 3 → Fin 3 → ℚ := ![![12246885873/50000000, 4876651607/25000000, 1790375949/20000000], ![6589290823/50000000, 7152112621/50000000, 473334747/10000000], ![157773571/12500000, 669513337/50000000, 589143301/100000000]]
def vcS1112CutWeightFloor : ℚ := 101056227/100000000
def vcS1112CutMargins : Fin 3 → ℚ := ![5214979/625000000, 76497927/10000000000, 15665821/5000000000]

theorem vcS1112Cut_roots_ok : vcS1112CutCell.rootsOK vcS1112CutRoots = true := by decide +kernel

theorem vcS1112Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1112CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1112Cut_margin_le (i : Fin 3) : curvatureLoss vcS1112CutCell vcS1112CutCaps i ≤ vcS1112CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1113CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨7/40, 3/16⟩, ⟨1/40, 1/20⟩⟩
def vcS1113CutRoots : Fin 3 → RatBounds := ![⟨32439970233607/17592186044416, 280447169373801/140737488355328⟩, ⟨485230114884081/281474976710656, 262643247743415/140737488355328⟩, ⟨279045587270145/281474976710656, 39558272284409/35184372088832⟩]
def vcS1113CutCaps : Fin 3 → Fin 3 → ℚ := ![![25752555141/100000000, 5142802433/25000000, 1872849671/20000000], ![3459937687/25000000, 7497919209/50000000, 2475559987/50000000], ![227791807/20000000, 1202758021/100000000, 132025583/25000000]]
def vcS1113CutWeightFloor : ℚ := 26397819/25000000
def vcS1113CutMargins : Fin 3 → ℚ := ![2155671/250000000, 39431719/5000000000, 62667/19531250]

theorem vcS1113Cut_roots_ok : vcS1113CutCell.rootsOK vcS1113CutRoots = true := by decide +kernel

theorem vcS1113Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1113CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1113Cut_margin_le (i : Fin 3) : curvatureLoss vcS1113CutCell vcS1113CutCaps i ≤ vcS1113CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1114CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨7/40, 3/16⟩, ⟨1/20, 3/40⟩⟩
def vcS1114CutRoots : Fin 3 → RatBounds := ![⟨515089535431809/281474976710656, 17385970808011/8796093022208⟩, ⟨60033305936875/35184372088832, 8119101056491/4398046511104⟩, ⟨137055790477205/140737488355328, 155286465481227/140737488355328⟩]
def vcS1114CutCaps : Fin 3 → Fin 3 → ℚ := ![![13500664169/50000000, 2162473407/10000000, 9773021091/100000000], ![724728901/5000000, 15681302429/100000000, 2583304379/50000000], ![1032354451/100000000, 1085715963/100000000, 475834429/100000000]]
def vcS1114CutWeightFloor : ℚ := 13766363/12500000
def vcS1114CutMargins : Fin 3 → ℚ := ![44555981/5000000000, 81345509/10000000000, 16448211/5000000000]

theorem vcS1114Cut_roots_ok : vcS1114CutCell.rootsOK vcS1114CutRoots = true := by decide +kernel

theorem vcS1114Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1114CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1114Cut_margin_le (i : Fin 3) : curvatureLoss vcS1114CutCell vcS1114CutCaps i ≤ vcS1114CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1115CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨7/40, 3/16⟩, ⟨3/40, 1/10⟩⟩
def vcS1115CutRoots : Fin 3 → RatBounds := ![⟨511435735689979/281474976710656, 552165609891509/281474976710656⟩, ⟨237844084608477/140737488355328, 514417242682487/281474976710656⟩, ⟨269587538571391/281474976710656, 76297767501909/70368744177664⟩]
def vcS1115CutCaps : Fin 3 → Fin 3 → ℚ := ![![706024441/2500000, 22667961681/100000000, 3257139/32000], ![1892971191/12500000, 16364172669/100000000, 5381760611/100000000], ![469792057/50000000, 984511097/100000000, 53845429/12500000]]
def vcS1115CutWeightFloor : ℚ := 114674341/100000000
def vcS1115CutMargins : Fin 3 → ℚ := ![5754771/625000000, 83926131/10000000000, 3375659/1000000000]

theorem vcS1115Cut_roots_ok : vcS1115CutCell.rootsOK vcS1115CutRoots = true := by decide +kernel

theorem vcS1115Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1115CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1115Cut_margin_le (i : Fin 3) : curvatureLoss vcS1115CutCell vcS1115CutCaps i ≤ vcS1115CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1116CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨3/16, 1/5⟩, ⟨0, 1/40⟩⟩
def vcS1116CutRoots : Fin 3 → RatBounds := ![⟨257847914266913/140737488355328, 556513717094165/281474976710656⟩, ⟨480404161760967/281474976710656, 259745046912145/140737488355328⟩, ⟨286836492379455/281474976710656, 162092211310191/140737488355328⟩]
def vcS1116CutCaps : Fin 3 → Fin 3 → ℚ := ![![21447448663/100000000, 16701835149/100000000, 7839255003/100000000], ![11138102417/100000000, 12119110647/100000000, 4033275723/100000000], ![1226607419/100000000, 644229963/50000000, 295103841/50000000]]
def vcS1116CutWeightFloor : ℚ := 101904793/100000000
def vcS1116CutMargins : Fin 3 → ℚ := ![2929061/400000000, 66357003/10000000000, 5559907/2000000000]

theorem vcS1116Cut_roots_ok : vcS1116CutCell.rootsOK vcS1116CutRoots = true := by decide +kernel

theorem vcS1116Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1116CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1116Cut_margin_le (i : Fin 3) : curvatureLoss vcS1116CutCell vcS1116CutCaps i ≤ vcS1116CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1117CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨3/16, 1/5⟩, ⟨1/40, 1/20⟩⟩
def vcS1117CutRoots : Fin 3 → RatBounds := ![⟨255756202183847/140737488355328, 275841685710579/140737488355328⟩, ⟨237518775673261/140737488355328, 513349805906287/281474976710656⟩, ⟨140719009471389/140737488355328, 317737631036085/281474976710656⟩]
def vcS1117CutCaps : Fin 3 → Fin 3 → ℚ := ![![901516233/4000000, 8806519619/50000000, 820548611/10000000], ![2923165079/25000000, 3174861697/25000000, 4220848411/100000000], ![1106320459/100000000, 289192789/25000000, 528916913/100000000]]
def vcS1117CutWeightFloor : ℚ := 106466601/100000000
def vcS1117CutMargins : Fin 3 → ℚ := ![9437463/1250000000, 68241349/10000000000, 7100587/2500000000]

theorem vcS1117Cut_roots_ok : vcS1117CutCell.rootsOK vcS1117CutRoots = true := by decide +kernel

theorem vcS1117Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1117CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1117Cut_margin_le (i : Fin 3) : curvatureLoss vcS1117CutCell vcS1117CutCaps i ≤ vcS1117CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1118CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨3/16, 1/5⟩, ⟨1/20, 3/40⟩⟩
def vcS1118CutRoots : Fin 3 → RatBounds := ![⟨253827849327907/140737488355328, 547250401869389/281474976710656⟩, ⟨117526696174467/70368744177664, 253865429471635/140737488355328⟩, ⟨138253720977979/140737488355328, 311875516927137/281474976710656⟩]
def vcS1118CutCaps : Fin 3 → Fin 3 → ℚ := ![![1476248829/6250000, 18514342499/100000000, 4284224299/50000000], ![6121021541/50000000, 829672019/6250000, 4406439289/100000000], ![250580267/25000000, 521863583/50000000, 59556061/12500000]]
def vcS1118CutWeightFloor : ℚ := 111033283/100000000
def vcS1118CutMargins : Fin 3 → ℚ := ![1557473/200000000, 14048439/2000000000, 3632979/1250000000]

theorem vcS1118Cut_roots_ok : vcS1118CutCell.rootsOK vcS1118CutRoots = true := by decide +kernel

theorem vcS1118Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1118CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1118Cut_margin_le (i : Fin 3) : curvatureLoss vcS1118CutCell vcS1118CutCaps i ≤ vcS1118CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1119CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨3/16, 1/5⟩, ⟨3/40, 1/10⟩⟩
def vcS1119CutRoots : Fin 3 → RatBounds := ![⟨63011049959105/35184372088832, 135791772862243/70368744177664⟩, ⟨465560084837299/281474976710656, 502568596339769/281474976710656⟩, ⟨271986401724461/281474976710656, 306521906332015/281474976710656⟩]
def vcS1119CutCaps : Fin 3 → Fin 3 → ℚ := ![![12347286921/50000000, 19406880589/100000000, 1785707849/20000000], ![3196704291/25000000, 1384557219/10000000, 4590272869/100000000], ![911866287/100000000, 18920629/2000000, 431215757/100000000]]
def vcS1119CutWeightFloor : ℚ := 11560401/10000000
def vcS1119CutMargins : Fin 3 → ℚ := ![40164899/5000000000, 18084267/2500000000, 7443201/2500000000]

theorem vcS1119Cut_roots_ok : vcS1119CutCell.rootsOK vcS1119CutRoots = true := by decide +kernel

theorem vcS1119Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1119CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1119Cut_margin_le (i : Fin 3) : curvatureLoss vcS1119CutCell vcS1119CutCaps i ≤ vcS1119CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1120CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨1/5, 17/80⟩, ⟨0, 1/40⟩⟩
def vcS1120CutRoots : Fin 3 → RatBounds := ![⟨508744673333623/281474976710656, 274038246255697/140737488355328⟩, ⟨235434073544257/140737488355328, 508415723023541/281474976710656⟩, ⟨144604597492487/140737488355328, 81385126574313/70368744177664⟩]
def vcS1120CutCaps : Fin 3 → Fin 3 → ℚ := ![![19010365283/100000000, 7245052247/50000000, 6959027811/100000000], ![596899609/6250000, 2602584319/25000000, 3497864729/100000000], ![18731131/1562500, 24897411/2000000, 148262367/25000000]]
def vcS1120CutWeightFloor : ℚ := 51373873/50000000
def vcS1120CutMargins : Fin 3 → ℚ := ![32574149/5000000000, 58359227/10000000000, 12528409/5000000000]

theorem vcS1120Cut_roots_ok : vcS1120CutCell.rootsOK vcS1120CutRoots = true := by decide +kernel

theorem vcS1120Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1120CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1120Cut_margin_le (i : Fin 3) : curvatureLoss vcS1120CutCell vcS1120CutCaps i ≤ vcS1120CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1121CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨1/5, 17/80⟩, ⟨1/40, 1/20⟩⟩
def vcS1121CutRoots : Fin 3 → RatBounds := ![⟨63081742232661/35184372088832, 543355089468659/281474976710656⟩, ⟨465531219878349/281474976710656, 31394752808901/17592186044416⟩, ⟨141907812176089/140737488355328, 159563067596947/140737488355328⟩]
def vcS1121CutCaps : Fin 3 → Fin 3 → ℚ := ![![1247999723/6250000, 3056266439/20000000, 3644008191/50000000], ![5011471013/50000000, 10904684869/100000000, 915515431/25000000], ![539237071/50000000, 1115459851/100000000, 265359363/50000000]]
def vcS1121CutWeightFloor : ℚ := 107334191/100000000
def vcS1121CutMargins : Fin 3 → ℚ := ![6700163/1000000000, 11971819/2000000000, 3191639/1250000000]

theorem vcS1121Cut_roots_ok : vcS1121CutCell.rootsOK vcS1121CutRoots = true := by decide +kernel

theorem vcS1121Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1121CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1121Cut_margin_le (i : Fin 3) : curvatureLoss vcS1121CutCell vcS1121CutCaps i ≤ vcS1121CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1122CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨1/5, 17/80⟩, ⟨1/20, 3/40⟩⟩
def vcS1122CutRoots : Fin 3 → RatBounds := ![⟨500882900533331/281474976710656, 269511336682999/140737488355328⟩, ⟨230314549167259/140737488355328, 496735975377623/281474976710656⟩, ⟨278889351809595/281474976710656, 313293279346901/281474976710656⟩]
def vcS1122CutCaps : Fin 3 → Fin 3 → ℚ := ![![5229681163/25000000, 8032097077/50000000, 95179927/1250000], ![10491175949/100000000, 11394838447/100000000, 3824513591/100000000], ![122034123/12500000, 1005733733/100000000, 477849357/100000000]]
def vcS1122CutWeightFloor : ℚ := 2238517/2000000
def vcS1122CutMargins : Fin 3 → ℚ := ![13794919/2000000000, 30744109/5000000000, 5214963/2000000000]

theorem vcS1122Cut_roots_ok : vcS1122CutCell.rootsOK vcS1122CutRoots = true := by decide +kernel

theorem vcS1122Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1122CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1122Cut_margin_le (i : Fin 3) : curvatureLoss vcS1122CutCell vcS1122CutCaps i ≤ vcS1122CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1123CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨1/5, 17/80⟩, ⟨3/40, 1/10⟩⟩
def vcS1123CutRoots : Fin 3 → RatBounds := ![⟨248697518833597/140737488355328, 267516240993699/140737488355328⟩, ⟨456109991488825/281474976710656, 245805446796923/140737488355328⟩, ⟨137186052782391/140737488355328, 19247887129945/17592186044416⟩]
def vcS1123CutCaps : Fin 3 → Fin 3 → ℚ := ![![5465818869/25000000, 16839649319/100000000, 396924169/5000000], ![10955559849/100000000, 475249841/4000000, 1992707743/50000000], ![443911341/50000000, 911243633/100000000, 17295537/4000000]]
def vcS1123CutWeightFloor : ℚ := 116521829/100000000
def vcS1123CutMargins : Fin 3 → ℚ := ![71035403/10000000000, 6321459/1000000000, 266669/100000000]

theorem vcS1123Cut_roots_ok : vcS1123CutCell.rootsOK vcS1123CutRoots = true := by decide +kernel

theorem vcS1123Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1123CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1123Cut_margin_le (i : Fin 3) : curvatureLoss vcS1123CutCell vcS1123CutCaps i ≤ vcS1123CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1124CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨17/80, 9/40⟩, ⟨0, 1/40⟩⟩
def vcS1124CutRoots : Fin 3 → RatBounds := ![⟨502399225082489/281474976710656, 270214146263209/140737488355328⟩, ⟨230972832413537/140737488355328, 249069873915335/140737488355328⟩, ⟨36446911132425/35184372088832, 163503227294689/140737488355328⟩]
def vcS1124CutCaps : Fin 3 → Fin 3 → ℚ := ![![17030555621/100000000, 12725536809/100000000, 6264581027/100000000], ![2072610399/25000000, 9047072667/100000000, 3084342987/100000000], ![234955819/20000000, 241042883/20000000, 298379639/50000000]]
def vcS1124CutWeightFloor : ℚ := 103588351/100000000
def vcS1124CutMargins : Fin 3 → ℚ := ![11726607/2000000000, 25970183/5000000000, 114609/50000000]

theorem vcS1124Cut_roots_ok : vcS1124CutCell.rootsOK vcS1124CutRoots = true := by decide +kernel

theorem vcS1124Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1124CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1124Cut_margin_le (i : Fin 3) : curvatureLoss vcS1124CutCell vcS1124CutCaps i ≤ vcS1124CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1125CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨17/80, 9/40⟩, ⟨1/40, 1/20⟩⟩
def vcS1125CutRoots : Fin 3 → RatBounds := ![⟨498393726171865/281474976710656, 16743950230659/8796093022208⟩, ⟨456634420574225/281474976710656, 492074876800483/281474976710656⟩, ⟨71546856917921/70368744177664, 80155680369843/70368744177664⟩]
def vcS1125CutCaps : Fin 3 → Fin 3 → ℚ := ![![17881263083/100000000, 13420808597/100000000, 656390469/10000000], ![8698689399/100000000, 2368392731/25000000, 40380299/1250000], ![264087199/25000000, 1079407973/100000000, 533887851/100000000]]
def vcS1125CutWeightFloor : ℚ := 108197811/100000000
def vcS1125CutMargins : Fin 3 → ℚ := ![12033339/2000000000, 2657423/500000000, 23300547/10000000000]

theorem vcS1125Cut_roots_ok : vcS1125CutCell.rootsOK vcS1125CutRoots = true := by decide +kernel

theorem vcS1125Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1125CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1125Cut_margin_le (i : Fin 3) : curvatureLoss vcS1125CutCell vcS1125CutCaps i ≤ vcS1125CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1126CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨17/80, 9/40⟩, ⟨1/20, 3/40⟩⟩
def vcS1126CutRoots : Fin 3 → RatBounds := ![⟨247350732629767/140737488355328, 531565848036371/281474976710656⟩, ⟨451757203277263/281474976710656, 243264143512989/140737488355328⟩, ⟨140633091896711/140737488355328, 78704372023845/70368744177664⟩]
def vcS1126CutCaps : Fin 3 → Fin 3 → ℚ := ![![18726227031/100000000, 14108789869/100000000, 3430454197/50000000], ![9103347217/100000000, 4948258269/50000000, 135001791/4000000], ![7456577/781250, 971791187/100000000, 480192861/100000000]]
def vcS1126CutWeightFloor : ℚ := 56406431/50000000
def vcS1126CutMargins : Fin 3 → ℚ := ![12362243/2000000000, 54477483/10000000000, 23743603/10000000000]

theorem vcS1126Cut_roots_ok : vcS1126CutCell.rootsOK vcS1126CutRoots = true := by decide +kernel

theorem vcS1126Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1126CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1126Cut_margin_le (i : Fin 3) : curvatureLoss vcS1126CutCell vcS1126CutCaps i ≤ vcS1126CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1127CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨17/80, 9/40⟩, ⟨3/40, 1/10⟩⟩
def vcS1127CutRoots : Fin 3 → RatBounds := ![⟨491286644155037/281474976710656, 65957590463609/35184372088832⟩, ⟨447262184169771/281474976710656, 30089709570321/17592186044416⟩, ⟨276753384789663/281474976710656, 309515421251499/281474976710656⟩]
def vcS1127CutCaps : Fin 3 → Fin 3 → ℚ := ![![9783017021/50000000, 2958062739/20000000, 3577938763/50000000], ![2376405467/25000000, 10316283607/100000000, 3519781891/100000000], ![173363473/20000000, 879556759/100000000, 86836561/20000000]]
def vcS1127CutWeightFloor : ℚ := 117432541/100000000
def vcS1127CutMargins : Fin 3 → ℚ := ![63552589/10000000000, 55907861/10000000000, 24242951/10000000000]

theorem vcS1127Cut_roots_ok : vcS1127CutCell.rootsOK vcS1127CutRoots = true := by decide +kernel

theorem vcS1127Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1127CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1127Cut_margin_le (i : Fin 3) : curvatureLoss vcS1127CutCell vcS1127CutCaps i ≤ vcS1127CutMargins i := by
  fin_cases i <;> decide +kernel


end HlawkaSchatten.BelowExponent.Vertex
