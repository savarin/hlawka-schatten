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

def vcS1128CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨9/40, 19/80⟩, ⟨0, 1/40⟩⟩
def vcS1128CutRoots : Fin 3 → RatBounds := ![⟨248299693318369/140737488355328, 533482556166265/281474976710656⟩, ⟨453571115649449/281474976710656, 488569360044271/281474976710656⟩, ⟨146971324294419/140737488355328, 82143794856539/70368744177664⟩]
def vcS1128CutCaps : Fin 3 → Fin 3 → ℚ := ![![3080170019/20000000, 5645748503/50000000, 1424520087/25000000], ![7286424451/100000000, 3970517751/50000000, 2779855437/100000000], ![288457241/25000000, 1168817911/100000000, 75150051/12500000]]
def vcS1128CutWeightFloor : ℚ := 52214703/50000000
def vcS1128CutMargins : Fin 3 → ℚ := ![13331343/2500000000, 4669493/1000000000, 21255347/10000000000]

theorem vcS1128Cut_roots_ok : vcS1128CutCell.rootsOK vcS1128CutRoots = true := by decide +kernel

theorem vcS1128Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1128CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1128Cut_margin_le (i : Fin 3) : curvatureLoss vcS1128CutCell vcS1128CutCaps i ≤ vcS1128CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1129CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨9/40, 19/80⟩, ⟨1/40, 1/20⟩⟩
def vcS1129CutRoots : Fin 3 → RatBounds := ![⟨30792020844965/17592186044416, 528951715698157/281474976710656⟩, ⟨112070505382667/70368744177664, 241267107502911/140737488355328⟩, ⟨288561165716131/281474976710656, 322220513572293/281474976710656⟩]
def vcS1129CutCaps : Fin 3 → Fin 3 → ℚ := ![![16164292213/100000000, 1488596507/12500000, 5973212041/100000000], ![3822376391/50000000, 8313042483/100000000, 728412671/25000000], ![64814709/6250000, 1046350119/100000000, 33607497/6250000]]
def vcS1129CutWeightFloor : ℚ := 54530323/50000000
def vcS1129CutMargins : Fin 3 → ℚ := ![1365097/250000000, 23835171/5000000000, 21558091/10000000000]

theorem vcS1129Cut_roots_ok : vcS1129CutCell.rootsOK vcS1129CutRoots = true := by decide +kernel

theorem vcS1129Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1129CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1129Cut_margin_le (i : Fin 3) : curvatureLoss vcS1129CutCell vcS1129CutCaps i ≤ vcS1129CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1130CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨9/40, 19/80⟩, ⟨1/20, 3/40⟩⟩
def vcS1130CutRoots : Fin 3 → RatBounds := ![⟨244526284474437/140737488355328, 524795193907835/281474976710656⟩, ⟨221713201285735/140737488355328, 119254094007563/70368744177664⟩, ⟨141822774585133/140737488355328, 19777591191529/17592186044416⟩]
def vcS1130CutCaps : Fin 3 → Fin 3 → ℚ := ![![1692290337/10000000, 6259810333/50000000, 6246259039/100000000], ![3999940967/50000000, 4340999533/50000000, 3045958241/100000000], ![936591571/100000000, 235410743/25000000, 120879907/25000000]]
def vcS1130CutWeightFloor : ℚ := 28424471/25000000
def vcS1130CutMargins : Fin 3 → ℚ := ![55994437/10000000000, 24383/5000000, 21926359/10000000000]

theorem vcS1130Cut_roots_ok : vcS1130CutCell.rootsOK vcS1130CutRoots = true := by decide +kernel

theorem vcS1130Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1130CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1130Cut_margin_le (i : Fin 3) : curvatureLoss vcS1130CutCell vcS1130CutCaps i ≤ vcS1130CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1131CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨9/40, 19/80⟩, ⟨3/40, 1/10⟩⟩
def vcS1131CutRoots : Fin 3 → RatBounds := ![⟨485704963183595/281474976710656, 260483948325277/140737488355328⟩, ⟨438952371672211/281474976710656, 117987794566105/70368744177664⟩, ⟨279137735314437/281474976710656, 311163078998803/281474976710656⟩]
def vcS1131CutCaps : Fin 3 → Fin 3 → ℚ := ![![3535432717/20000000, 262495503/2000000, 6517477067/100000000], ![1670429129/20000000, 9048221823/100000000, 3176941871/100000000], ![849646753/100000000, 851483199/100000000, 87381303/20000000]]
def vcS1131CutWeightFloor : ℚ := 118340087/100000000
def vcS1131CutMargins : Fin 3 → ℚ := ![1436909/250000000, 780607/156250000, 4469549/2000000000]

theorem vcS1131Cut_roots_ok : vcS1131CutCell.rootsOK vcS1131CutRoots = true := by decide +kernel

theorem vcS1131Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1131CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1131Cut_margin_le (i : Fin 3) : curvatureLoss vcS1131CutCell vcS1131CutCaps i ≤ vcS1131CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1132CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨19/80, 1/4⟩, ⟨0, 1/40⟩⟩
def vcS1132CutRoots : Fin 3 → RatBounds := ![⟨491294079963555/281474976710656, 131791700191835/70368744177664⟩, ⟨111422092872279/70368744177664, 479626398568531/281474976710656⟩, ⟨148159069153711/140737488355328, 330241288472729/281474976710656⟩]
def vcS1132CutCaps : Fin 3 → Fin 3 → ℚ := ![![1404397881/10000000, 10111992657/100000000, 26153429/500000], ![3234238783/50000000, 1757678369/25000000, 2539332599/100000000], ![1135454443/100000000, 45408381/4000000, 121257561/20000000]]
def vcS1132CutWeightFloor : ℚ := 2105467/2000000
def vcS1132CutMargins : Fin 3 → ℚ := ![4893413/1000000000, 42350673/10000000000, 19912441/10000000000]

theorem vcS1132Cut_roots_ok : vcS1132CutCell.rootsOK vcS1132CutRoots = true := by decide +kernel

theorem vcS1132Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1132CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1132Cut_margin_le (i : Fin 3) : curvatureLoss vcS1132CutCell vcS1132CutCaps i ≤ vcS1132CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1133CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨19/80, 1/4⟩, ⟨1/40, 1/20⟩⟩
def vcS1133CutRoots : Fin 3 → RatBounds := ![⟨487439245802593/281474976710656, 261359665474227/140737488355328⟩, ⟨440418292570737/281474976710656, 118404125617149/70368744177664⟩, ⟨290943587694581/281474976710656, 161957145285915/140737488355328⟩]
def vcS1133CutCaps : Fin 3 → Fin 3 → ℚ := ![![7367679341/50000000, 10665084509/100000000, 5485903067/100000000], ![6785491103/100000000, 7358286903/100000000, 53235827/2000000], ![510043623/50000000, 203170447/20000000, 108427561/20000000]]
def vcS1133CutWeightFloor : ℚ := 343517/312500
def vcS1133CutMargins : Fin 3 → ℚ := ![25001171/5000000000, 43138243/10000000000, 10074459/5000000000]

theorem vcS1133Cut_roots_ok : vcS1133CutCell.rootsOK vcS1133CutRoots = true := by decide +kernel

theorem vcS1133Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1133CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1133Cut_margin_le (i : Fin 3) : curvatureLoss vcS1133CutCell vcS1133CutCaps i ≤ vcS1133CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1134CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨19/80, 1/4⟩, ⟨1/20, 3/40⟩⟩
def vcS1134CutRoots : Fin 3 → RatBounds := ![⟨483886219303803/281474976710656, 518639764604113/281474976710656⟩, ⟨108895334091061/70368744177664, 468123245000889/281474976710656⟩, ⟨143017045679977/140737488355328, 159080063445053/140737488355328⟩]
def vcS1134CutCaps : Fin 3 → Fin 3 → ℚ := ![![3084527383/20000000, 11212454099/100000000, 573922813/10000000], ![3549852459/50000000, 1920802633/25000000, 2782902581/100000000], ![115115053/12500000, 913852497/100000000, 487379789/100000000]]
def vcS1134CutWeightFloor : ℚ := 57291981/50000000
def vcS1134CutMargins : Fin 3 → ℚ := ![1279591/250000000, 11011267/2500000000, 10226221/5000000000]

theorem vcS1134Cut_roots_ok : vcS1134CutCell.rootsOK vcS1134CutRoots = true := by decide +kernel

theorem vcS1134Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1134CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1134Cut_margin_le (i : Fin 3) : curvatureLoss vcS1134CutCell vcS1134CutCaps i ≤ vcS1134CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1135CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨19/80, 1/4⟩, ⟨3/40, 1/10⟩⟩
def vcS1135CutRoots : Fin 3 → RatBounds := ![⟨30037530426079/17592186044416, 257441868299117/140737488355328⟩, ⟨107781384917177/70368744177664, 231540945868625/140737488355328⟩, ⟨140765851663061/140737488355328, 156452121854083/140737488355328⟩]
def vcS1135CutCaps : Fin 3 → Fin 3 → ℚ := ![![16106209141/100000000, 11754751961/100000000, 2995446287/50000000], ![185285161/2500000, 8005755243/100000000, 2902812427/100000000], ![417560727/50000000, 826062623/100000000, 440298513/100000000]]
def vcS1135CutWeightFloor : ℚ := 59623903/50000000
def vcS1135CutMargins : Fin 3 → ℚ := ![5245723/1000000000, 9009671/2000000000, 416207/200000000]

theorem vcS1135Cut_roots_ok : vcS1135CutCell.rootsOK vcS1135CutRoots = true := by decide +kernel

theorem vcS1135Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1135CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1135Cut_margin_le (i : Fin 3) : curvatureLoss vcS1135CutCell vcS1135CutCaps i ≤ vcS1135CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1136CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨1/4, 21/80⟩, ⟨0, 1/40⟩⟩
def vcS1136CutRoots : Fin 3 → RatBounds := ![⟨486439640744373/281474976710656, 521419895999027/281474976710656⟩, ⟨109562268454407/70368744177664, 471244496261591/281474976710656⟩, ⟨74676961386239/70368744177664, 83000188461199/70368744177664⟩]
def vcS1136CutCaps : Fin 3 → Fin 3 → ℚ := ![![12903121713/100000000, 1141456041/12500000, 605169373/12500000], ![115857707/2000000, 6272053069/100000000, 2345331289/100000000], ![1119272261/100000000, 1104010203/100000000, 61195463/10000000]]
def vcS1136CutWeightFloor : ℚ := 13265293/12500000
def vcS1136CutMargins : Fin 3 → ℚ := ![22629977/5000000000, 7742087/2000000000, 18817393/10000000000]

theorem vcS1136Cut_roots_ok : vcS1136CutCell.rootsOK vcS1136CutRoots = true := by decide +kernel

theorem vcS1136Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1136CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1136Cut_margin_le (i : Fin 3) : curvatureLoss vcS1136CutCell vcS1136CutCaps i ≤ vcS1136CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1137CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨1/4, 21/80⟩, ⟨1/40, 1/20⟩⟩
def vcS1137CutRoots : Fin 3 → RatBounds := ![⟨60331410286877/35184372088832, 258524399422589/140737488355328⟩, ⟨216497608124983/140737488355328, 465255881601839/281474976710656⟩, ⟨293340682449521/281474976710656, 162850082043991/140737488355328⟩]
def vcS1137CutCaps : Fin 3 → Fin 3 → ℚ := ![![422949641/3125000, 4815676423/50000000, 5080057227/100000000], ![1518994303/25000000, 6562909727/100000000, 1229281683/50000000], ![1005152957/100000000, 246891243/25000000, 273540267/50000000]]
def vcS1137CutWeightFloor : ℚ := 110794601/100000000
def vcS1137CutMargins : Fin 3 → ℚ := ![23077127/5000000000, 39344771/10000000000, 1187371/625000000]

theorem vcS1137Cut_roots_ok : vcS1137CutCell.rootsOK vcS1137CutRoots = true := by decide +kernel

theorem vcS1137Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1137CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1137Cut_margin_le (i : Fin 3) : curvatureLoss vcS1137CutCell vcS1137CutCaps i ≤ vcS1137CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1138CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨1/4, 21/80⟩, ⟨1/20, 3/40⟩⟩
def vcS1138CutRoots : Fin 3 → RatBounds := ![⟨119789920777583/70368744177664, 513039729419581/281474976710656⟩, ⟨107043576183035/70368744177664, 229891754325901/140737488355328⟩, ⟨288437708967719/281474976710656, 319969729659285/281474976710656⟩]
def vcS1138CutCaps : Fin 3 → Fin 3 → ℚ := ![![7081248963/50000000, 10126262713/100000000, 2658670961/50000000], ![1271317891/20000000, 6851441231/100000000, 1285282429/50000000], ![14173513/1562500, 444048427/50000000, 12292941/2500000]]
def vcS1138CutWeightFloor : ℚ := 7217109/6250000
def vcS1138CutMargins : Fin 3 → ℚ := ![471631/100000000, 8019567/2000000000, 4811903/2500000000]

theorem vcS1138Cut_roots_ok : vcS1138CutCell.rootsOK vcS1138CutRoots = true := by decide +kernel

theorem vcS1138Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1138CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1138Cut_margin_le (i : Fin 3) : curvatureLoss vcS1138CutCell vcS1138CutCaps i ≤ vcS1138CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1139CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨1/4, 21/80⟩, ⟨3/40, 1/10⟩⟩
def vcS1139CutRoots : Fin 3 → RatBounds := ![⟨237965448641677/140737488355328, 127337247503037/70368744177664⟩, ⟨423734284549483/281474976710656, 454762547256127/281474976710656⟩, ⟨283941104449315/281474976710656, 157367634332397/140737488355328⟩]
def vcS1139CutCaps : Fin 3 → Fin 3 → ℚ := ![![7395190293/50000000, 5308563733/50000000, 2776878131/50000000], ![1658743167/25000000, 7137881627/100000000, 2681467123/100000000], ![164462177/20000000, 802520559/100000000, 222063557/50000000]]
def vcS1139CutWeightFloor : ℚ := 60079293/50000000
def vcS1139CutMargins : Fin 3 → ℚ := ![48270697/10000000000, 8189489/2000000000, 4888541/2500000000]

theorem vcS1139Cut_roots_ok : vcS1139CutCell.rootsOK vcS1139CutRoots = true := by decide +kernel

theorem vcS1139Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1139CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1139Cut_margin_le (i : Fin 3) : curvatureLoss vcS1139CutCell vcS1139CutCaps i ≤ vcS1139CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1140CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨21/80, 11/40⟩, ⟨0, 1/40⟩⟩
def vcS1140CutRoots : Fin 3 → RatBounds := ![⟨481998555349213/281474976710656, 516189966056519/281474976710656⟩, ⟨26950705757929/17592186044416, 115841720144305/70368744177664⟩, ⟨301117258828347/281474976710656, 166925332458279/140737488355328⟩]
def vcS1140CutCaps : Fin 3 → Fin 3 → ℚ := ![![11935855157/100000000, 519342599/6250000, 4514561073/100000000], ![5229361717/100000000, 1408238729/25000000, 273469947/12500000], ![1104972109/100000000, 1074905043/100000000, 309072751/50000000]]
def vcS1140CutWeightFloor : ℚ := 5348917/5000000
def vcS1140CutMargins : Fin 3 → ℚ := ![42158409/10000000000, 35629017/10000000000, 4479933/2500000000]

theorem vcS1140Cut_roots_ok : vcS1140CutCell.rootsOK vcS1140CutRoots = true := by decide +kernel

theorem vcS1140Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1140CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1140Cut_margin_le (i : Fin 3) : curvatureLoss vcS1140CutCell vcS1140CutCaps i ≤ vcS1140CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1141CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨21/80, 11/40⟩, ⟨1/40, 1/20⟩⟩
def vcS1141CutRoots : Fin 3 → RatBounds := ![⟨239135673047001/140737488355328, 255944409483849/140737488355328⟩, ⟨106492789086241/70368744177664, 114349003211085/70368744177664⟩, ⟨295757853531999/281474976710656, 163787668676057/140737488355328⟩]
def vcS1141CutCaps : Fin 3 → Fin 3 → ℚ := ![![2503431727/20000000, 8764967183/100000000, 4740060829/100000000], ![274215099/5000000, 589312217/10000000, 143339013/6250000], ![991949301/100000000, 961200051/100000000, 552498459/100000000]]
def vcS1141CutWeightFloor : ℚ := 111670279/100000000
def vcS1141CutMargins : Fin 3 → ℚ := ![42908707/10000000000, 36138457/10000000000, 1805367/1000000000]

theorem vcS1141Cut_roots_ok : vcS1141CutCell.rootsOK vcS1141CutRoots = true := by decide +kernel

theorem vcS1141Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1141CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1141Cut_margin_le (i : Fin 3) : curvatureLoss vcS1141CutCell vcS1141CutCaps i ≤ vcS1141CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1142CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨21/80, 11/40⟩, ⟨1/20, 3/40⟩⟩
def vcS1142CutRoots : Fin 3 → RatBounds := ![⟨474836249140927/281474976710656, 507944318722285/281474976710656⟩, ⟨421163945464249/281474976710656, 451941228859467/281474976710656⟩, ⟨290861727637049/281474976710656, 321867573750075/281474976710656⟩]
def vcS1142CutCaps : Fin 3 → Fin 3 → ℚ := ![![1636934549/12500000, 4607915251/50000000, 2481981133/50000000], ![5737022717/100000000, 6151230997/100000000, 1198978411/50000000], ![178977087/20000000, 8641113/1000000, 124122101/25000000]]
def vcS1142CutWeightFloor : ℚ := 116369579/100000000
def vcS1142CutMargins : Fin 3 → ℚ := ![21886759/5000000000, 18382331/5000000000, 4564391/2500000000]

theorem vcS1142Cut_roots_ok : vcS1142CutCell.rootsOK vcS1142CutRoots = true := by decide +kernel

theorem vcS1142Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1142CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1142Cut_margin_le (i : Fin 3) : curvatureLoss vcS1142CutCell vcS1142CutCaps i ≤ vcS1142CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1143CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨21/80, 11/40⟩, ⟨3/40, 1/10⟩⟩
def vcS1143CutRoots : Fin 3 → RatBounds := ![⟨235829920712077/140737488355328, 126078344647399/70368744177664⟩, ⟨208368749931061/140737488355328, 446937579918769/281474976710656⟩, ⟨143185596321523/140737488355328, 316653554123261/281474976710656⟩]
def vcS1143CutCaps : Fin 3 → Fin 3 → ℚ := ![![3419174667/25000000, 1207869957/12500000, 1037463843/20000000], ![5987744779/100000000, 3203742671/50000000, 1250738127/50000000], ![810976689/100000000, 195153289/25000000, 224175891/50000000]]
def vcS1143CutWeightFloor : ℚ := 15134371/12500000
def vcS1143CutMargins : Fin 3 → ℚ := ![5592859/1250000000, 37486129/10000000000, 18519927/10000000000]

theorem vcS1143Cut_roots_ok : vcS1143CutCell.rootsOK vcS1143CutRoots = true := by decide +kernel

theorem vcS1143Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1143CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1143Cut_margin_le (i : Fin 3) : curvatureLoss vcS1143CutCell vcS1143CutCaps i ≤ vcS1143CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1144CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨11/40, 23/80⟩, ⟨0, 1/40⟩⟩
def vcS1144CutRoots : Fin 3 → RatBounds := ![⟨477938457543739/281474976710656, 255716378216725/140737488355328⟩, ⟨212269227804651/140737488355328, 113986164431209/70368744177664⟩, ⟨303551407676775/281474976710656, 335789042353747/281474976710656⟩]
def vcS1144CutCaps : Fin 3 → Fin 3 → ℚ := ![![11110459479/100000000, 1903780707/25000000, 1059776763/25000000], ![4755520083/100000000, 5090174247/100000000, 2059470927/100000000], ![546152267/50000000, 209527089/20000000, 624816551/100000000]]
def vcS1144CutWeightFloor : ℚ := 107843123/100000000
def vcS1144CutMargins : Fin 3 → ℚ := ![39521871/10000000000, 16499843/5000000000, 1718329/1000000000]

theorem vcS1144Cut_roots_ok : vcS1144CutCell.rootsOK vcS1144CutRoots = true := by decide +kernel

theorem vcS1144Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1144CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1144Cut_margin_le (i : Fin 3) : curvatureLoss vcS1144CutCell vcS1144CutCaps i ≤ vcS1144CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1145CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨11/40, 23/80⟩, ⟨1/40, 1/20⟩⟩
def vcS1145CutRoots : Fin 3 → RatBounds := ![⟨237133715775723/140737488355328, 507195629072827/281474976710656⟩, ⟨209654898740243/140737488355328, 449988372725985/281474976710656⟩, ⟨298200056262515/281474976710656, 10298060126459/8796093022208⟩]
def vcS1145CutCaps : Fin 3 → Fin 3 → ℚ := ![![582444421/5000000, 8032654583/100000000, 2226531033/50000000], ![4986909259/100000000, 5324512969/100000000, 1079462147/50000000], ![980247251/100000000, 936519133/100000000, 69793951/12500000]]
def vcS1145CutWeightFloor : ℚ := 11255443/10000000
def vcS1145CutMargins : Fin 3 → ℚ := ![20074987/5000000000, 16702387/5000000000, 8638079/5000000000]

theorem vcS1145Cut_roots_ok : vcS1145CutCell.rootsOK vcS1145CutRoots = true := by decide +kernel

theorem vcS1145Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1145CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1145Cut_margin_le (i : Fin 3) : curvatureLoss vcS1145CutCell vcS1145CutCaps i ≤ vcS1145CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1146CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨11/40, 23/80⟩, ⟨1/20, 3/40⟩⟩
def vcS1146CutRoots : Fin 3 → RatBounds := ![⟨470884245498177/281474976710656, 251655112213143/140737488355328⟩, ⟨414514181071439/281474976710656, 444548225589173/281474976710656⟩, ⟨293311034611759/281474976710656, 323851857021551/281474976710656⟩]
def vcS1146CutCaps : Fin 3 → Fin 3 → ℚ := ![![1523293769/12500000, 8446056541/100000000, 4665793449/100000000], ![1304074323/25000000, 555703059/10000000, 2257334873/100000000], ![442025613/50000000, 210418879/25000000, 250827743/50000000]]
def vcS1146CutWeightFloor : ℚ := 117273583/100000000
def vcS1146CutMargins : Fin 3 → ℚ := ![10224049/2500000000, 3392537/1000000000, 17440919/10000000000]

theorem vcS1146Cut_roots_ok : vcS1146CutCell.rootsOK vcS1146CutRoots = true := by decide +kernel

theorem vcS1146Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1146CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1146Cut_margin_le (i : Fin 3) : curvatureLoss vcS1146CutCell vcS1146CutCaps i ≤ vcS1146CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1147CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨11/40, 23/80⟩, ⟨3/40, 1/10⟩⟩
def vcS1147CutRoots : Fin 3 → RatBounds := ![⟨467755957233091/281474976710656, 499734014680837/281474976710656⟩, ⟨410099330197007/281474976710656, 439559129065515/281474976710656⟩, ⟨288826792470323/281474976710656, 159328687238995/140737488355328⟩]
def vcS1147CutCaps : Fin 3 → Fin 3 → ℚ := ![![1272601689/10000000, 8856009377/100000000, 4877969519/100000000], ![5443880809/100000000, 5787903919/100000000, 2354809983/100000000], ![160184767/20000000, 380068091/50000000, 226469433/50000000]]
def vcS1147CutWeightFloor : ℚ := 12199923/10000000
def vcS1147CutMargins : Fin 3 → ℚ := ![41745299/10000000000, 17269979/5000000000, 4416277/2500000000]

theorem vcS1147Cut_roots_ok : vcS1147CutCell.rootsOK vcS1147CutRoots = true := by decide +kernel

theorem vcS1147Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1147CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1147Cut_margin_le (i : Fin 3) : curvatureLoss vcS1147CutCell vcS1147CutCaps i ≤ vcS1147CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1148CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨23/80, 3/10⟩, ⟨0, 1/40⟩⟩
def vcS1148CutRoots : Fin 3 → RatBounds := ![⟨237115662288741/140737488355328, 507110349114971/281474976710656⟩, ⟨209099247221187/140737488355328, 448935459356365/281474976710656⟩, ⟨76503743450913/70368744177664, 337814697469485/281474976710656⟩]
def vcS1148CutCaps : Fin 3 → Fin 3 → ℚ := ![![10401194499/100000000, 1404814283/20000000, 2002601877/50000000], ![54434209/1250000, 4628218431/100000000, 1955952219/100000000], ![540533137/50000000, 127748237/12500000, 631932689/100000000]]
def vcS1148CutWeightFloor : ℚ := 54359179/50000000
def vcS1148CutMargins : Fin 3 → ℚ := ![37266009/10000000000, 7685661/2500000000, 16579857/10000000000]

theorem vcS1148Cut_roots_ok : vcS1148CutCell.rootsOK vcS1148CutRoots = true := by decide +kernel

theorem vcS1148Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1148CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1148Cut_margin_le (i : Fin 3) : curvatureLoss vcS1148CutCell vcS1148CutCaps i ≤ vcS1148CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1149CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨23/80, 3/10⟩, ⟨1/40, 1/20⟩⟩
def vcS1149CutRoots : Fin 3 → RatBounds := ![⟨470611828971167/281474976710656, 502931734108671/281474976710656⟩, ⟨412979292784343/281474976710656, 442990911485705/281474976710656⟩, ⟨37583988348209/35184372088832, 331586811347955/281474976710656⟩]
def vcS1149CutCaps : Fin 3 → Fin 3 → ℚ := ![![10903049729/100000000, 1852308813/25000000, 841896859/20000000], ![2283157121/50000000, 4840579709/100000000, 410055783/20000000], ![48493031/5000000, 913324213/100000000, 564608267/100000000]]
def vcS1149CutWeightFloor : ℚ := 22689771/20000000
def vcS1149CutMargins : Fin 3 → ℚ := ![18895319/5000000000, 15530383/5000000000, 16637103/10000000000]

theorem vcS1149Cut_roots_ok : vcS1149CutCell.rootsOK vcS1149CutRoots = true := by decide +kernel

theorem vcS1149Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1149CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1149Cut_margin_le (i : Fin 3) : curvatureLoss vcS1149CutCell vcS1149CutCaps i ≤ vcS1149CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1150CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨23/80, 3/10⟩, ⟨1/20, 3/40⟩⟩
def vcS1150CutRoots : Fin 3 → RatBounds := ![⟨467276252270215/281474976710656, 249550170870633/140737488355328⟩, ⟨408193372359825/281474976710656, 27347671539015/17592186044416⟩, ⟨295790185827977/281474976710656, 81480383801829/70368744177664⟩]
def vcS1150CutCaps : Fin 3 → Fin 3 → ℚ := ![![11406259857/100000000, 973838307/12500000, 551624533/12500000], ![4776065737/100000000, 1262826591/25000000, 2143634761/100000000], ![437215527/50000000, 51287939/6250000, 507190073/100000000]]
def vcS1150CutWeightFloor : ℚ := 118187699/100000000
def vcS1150CutMargins : Fin 3 → ℚ := ![19218799/5000000000, 31493049/10000000000, 16768343/10000000000]

theorem vcS1150Cut_roots_ok : vcS1150CutCell.rootsOK vcS1150CutRoots = true := by decide +kernel

theorem vcS1150Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1150CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1150Cut_margin_le (i : Fin 3) : curvatureLoss vcS1150CutCell vcS1150CutCaps i ≤ vcS1150CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1151CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨23/80, 3/10⟩, ⟨3/40, 1/10⟩⟩
def vcS1151CutRoots : Fin 3 → RatBounds := ![⟨464192093890325/281474976710656, 495574154815473/281474976710656⟩, ⟨201894165137083/140737488355328, 432585715389895/281474976710656⟩, ⟨291312404389231/281474976710656, 80186436928883/70368744177664⟩]
def vcS1151CutCaps : Fin 3 → Fin 3 → ℚ := ![![2977397993/25000000, 63819483/781250, 2307837291/50000000], ![4984168079/100000000, 210422177/4000000, 559029459/25000000], ![791994481/100000000, 740920979/100000000, 45786207/10000000]]
def vcS1151CutWeightFloor : ℚ := 122933451/100000000
def vcS1151CutMargins : Fin 3 → ℚ := ![19591541/5000000000, 32017837/10000000000, 3391891/2000000000]

theorem vcS1151Cut_roots_ok : vcS1151CutCell.rootsOK vcS1151CutRoots = true := by decide +kernel

theorem vcS1151Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1151CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1151Cut_margin_le (i : Fin 3) : curvatureLoss vcS1151CutCell vcS1151CutCaps i ≤ vcS1151CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1152CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨3/10, 5/16⟩, ⟨0, 1/40⟩⟩
def vcS1152CutRoots : Fin 3 → RatBounds := ![⟨470852828015835/281474976710656, 503190142458291/281474976710656⟩, ⟨103040785898437/70368744177664, 27643897780611/17592186044416⟩, ⟨154256190532931/140737488355328, 339927125683809/281474976710656⟩]
def vcS1152CutCaps : Fin 3 → Fin 3 → ℚ := ![![978869473/10000000, 1629514269/25000000, 1902983749/50000000], ![4013417313/100000000, 4229358219/100000000, 935898567/50000000], ![1071090227/100000000, 997775081/100000000, 159866479/25000000]]
def vcS1152CutWeightFloor : ℚ := 21921123/20000000
def vcS1152CutMargins : Fin 3 → ℚ := ![35325143/10000000000, 7196541/2500000000, 4021303/2500000000]

theorem vcS1152Cut_roots_ok : vcS1152CutCell.rootsOK vcS1152CutRoots = true := by decide +kernel

theorem vcS1152Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1152CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1152Cut_margin_le (i : Fin 3) : curvatureLoss vcS1152CutCell vcS1152CutCaps i ≤ vcS1152CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1153CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨3/10, 5/16⟩, ⟨1/40, 1/20⟩⟩
def vcS1153CutRoots : Fin 3 → RatBounds := ![⟨467280482405751/281474976710656, 249532448543687/140737488355328⟩, ⟨406951572844227/281474976710656, 218183491836505/140737488355328⟩, ⟨151588885155981/140737488355328, 333721556242671/281474976710656⟩]
def vcS1153CutCaps : Fin 3 → Fin 3 → ℚ := ![![10259195787/100000000, 3437723383/50000000, 4002149697/100000000], ![2104084871/50000000, 276419931/6250000, 1961809431/100000000], ![960636337/100000000, 891448763/100000000, 142810793/25000000]]
def vcS1153CutWeightFloor : ℚ := 114355249/100000000
def vcS1153CutMargins : Fin 3 → ℚ := ![7152309/2000000000, 14515587/5000000000, 3222239/2000000000]

theorem vcS1153Cut_roots_ok : vcS1153CutCell.rootsOK vcS1153CutRoots = true := by decide +kernel

theorem vcS1153Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1153CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1153Cut_margin_le (i : Fin 3) : curvatureLoss vcS1153CutCell vcS1153CutCaps i ≤ vcS1153CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1154CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨3/10, 5/16⟩, ⟨1/20, 3/40⟩⟩
def vcS1154CutRoots : Fin 3 → RatBounds := ![⟨7249819777593/4398046511104, 61910346271869/35184372088832⟩, ⟨201086816087039/140737488355328, 430948396195729/281474976710656⟩, ⟨298303492594987/281474976710656, 82019055207137/70368744177664⟩]
def vcS1154CutCaps : Fin 3 → Fin 3 → ℚ := ![![1341605927/12500000, 903686589/12500000, 4197957911/100000000], ![550155357/12500000, 4614736523/100000000, 205099083/10000000], ![865884207/100000000, 160150479/20000000, 2052277/400000]]
def vcS1154CutWeightFloor : ℚ := 59556869/50000000
def vcS1154CutMargins : Fin 3 → ℚ := ![36323491/10000000000, 29389139/10000000000, 4053333/2500000000]

theorem vcS1154Cut_roots_ok : vcS1154CutCell.rootsOK vcS1154CutRoots = true := by decide +kernel

theorem vcS1154Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1154CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1154Cut_margin_le (i : Fin 3) : curvatureLoss vcS1154CutCell vcS1154CutCaps i ≤ vcS1154CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1155CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨3/10, 5/16⟩, ⟨3/40, 1/10⟩⟩
def vcS1155CutRoots : Fin 3 → RatBounds := ![⟨460944681969007/281474976710656, 122950552518051/70368744177664⟩, ⟨397776783145801/281474976710656, 425981187017783/281474976710656⟩, ⟨73458072500309/70368744177664, 322918336697191/281474976710656⟩]
def vcS1155CutCaps : Fin 3 → Fin 3 → ℚ := ![![1400626179/12500000, 303216607/4000000, 878537217/20000000], ![2296398537/50000000, 192216647/4000000, 1069676667/50000000], ![392029489/50000000, 722825919/100000000, 231550291/50000000]]
def vcS1155CutWeightFloor : ℚ := 30969889/25000000
def vcS1155CutMargins : Fin 3 → ℚ := ![4622569/1250000000, 5967631/2000000000, 16375863/10000000000]

theorem vcS1155Cut_roots_ok : vcS1155CutCell.rootsOK vcS1155CutRoots = true := by decide +kernel

theorem vcS1155Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1155CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1155Cut_margin_le (i : Fin 3) : curvatureLoss vcS1155CutCell vcS1155CutCaps i ≤ vcS1155CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1156CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨5/16, 13/40⟩, ⟨0, 1/40⟩⟩
def vcS1156CutRoots : Fin 3 → RatBounds := ![⟨233890902958409/140737488355328, 499644034571113/281474976710656⟩, ⟨101601843468239/70368744177664, 436013032812211/281474976710656⟩, ⟨311047869518579/281474976710656, 342126426072989/281474976710656⟩]
def vcS1156CutCaps : Fin 3 → Fin 3 → ℚ := ![![1851539291/20000000, 190086729/3125000, 909008993/25000000], ![930371407/25000000, 1941360377/50000000, 450977371/25000000], ![132779793/12500000, 60928099/6250000, 129478853/20000000]]
def vcS1156CutWeightFloor : ℚ := 55253201/50000000
def vcS1156CutMargins : Fin 3 → ℚ := ![33648703/10000000000, 423123/156250000, 7841331/5000000000]

theorem vcS1156Cut_roots_ok : vcS1156CutCell.rootsOK vcS1156CutRoots = true := by decide +kernel

theorem vcS1156Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1156CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1156Cut_margin_le (i : Fin 3) : curvatureLoss vcS1156CutCell vcS1156CutCaps i ≤ vcS1156CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1157CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨5/16, 13/40⟩, ⟨1/40, 1/20⟩⟩
def vcS1157CutRoots : Fin 3 → RatBounds := ![⟨464252467506473/281474976710656, 495567331277817/281474976710656⟩, ⟨200600890479473/140737488355328, 215042244201221/140737488355328⟩, ⟨76430458449467/70368744177664, 167971153653033/140737488355328⟩]
def vcS1157CutCaps : Fin 3 → Fin 3 → ℚ := ![![1940468773/20000000, 3208126073/50000000, 765136721/20000000], ![243867309/6250000, 162389669/4000000, 236306653/12500000], ![476224587/50000000, 435376637/50000000, 578237297/100000000]]
def vcS1157CutWeightFloor : ℚ := 115275221/100000000
def vcS1157CutMargins : Fin 3 → ℚ := ![34011753/10000000000, 13631843/5000000000, 15681809/10000000000]

theorem vcS1157Cut_roots_ok : vcS1157CutCell.rootsOK vcS1157CutRoots = true := by decide +kernel

theorem vcS1157Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1157CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1157Cut_margin_le (i : Fin 3) : curvatureLoss vcS1157CutCell vcS1157CutCaps i ≤ vcS1157CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1158CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨5/16, 13/40⟩, ⟨1/20, 3/40⟩⟩
def vcS1158CutRoots : Fin 3 → RatBounds := ![⟨461000181609503/281474976710656, 15369687932775/8796093022208⟩, ⟨396430264551043/281474976710656, 53084162708565/35184372088832⟩, ⟨37606886627283/35184372088832, 330316106996609/281474976710656⟩]
def vcS1158CutCaps : Fin 3 → Fin 3 → ℚ := ![![5074643059/50000000, 6746577623/100000000, 4014869969/100000000], ![4080712761/100000000, 2117743683/50000000, 1976177377/100000000], ![858296579/100000000, 3127937/400000, 4056847/781250]]
def vcS1158CutWeightFloor : ℚ := 30013353/25000000
def vcS1158CutMargins : Fin 3 → ℚ := ![34498409/10000000000, 13779299/5000000000, 492441/312500000]

theorem vcS1158Cut_roots_ok : vcS1158CutCell.rootsOK vcS1158CutRoots = true := by decide +kernel

theorem vcS1158Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1158CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1158Cut_margin_le (i : Fin 3) : curvatureLoss vcS1158CutCell vcS1158CutCaps i ≤ vcS1158CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1159CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨5/16, 13/40⟩, ⟨3/40, 1/10⟩⟩
def vcS1159CutRoots : Fin 3 → RatBounds := ![⟨114498305348421/70368744177664, 30524434619155/17592186044416⟩, ⟨196020071492889/140737488355328, 104928468040541/70368744177664⟩, ⟨148195271160141/140737488355328, 20323460925563/17592186044416⟩]
def vcS1159CutCaps : Fin 3 → Fin 3 → ℚ := ![![10594608781/100000000, 884247107/12500000, 4202972317/100000000], ![4258139683/100000000, 2205067253/50000000, 515299101/25000000], ![388506273/50000000, 705733823/100000000, 468639601/100000000]]
def vcS1159CutWeightFloor : ℚ := 62419681/50000000
def vcS1159CutMargins : Fin 3 → ℚ := ![7015937/2000000000, 27943451/10000000000, 993497/625000000]

theorem vcS1159Cut_roots_ok : vcS1159CutCell.rootsOK vcS1159CutRoots = true := by decide +kernel

theorem vcS1159Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1159CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1159Cut_margin_le (i : Fin 3) : curvatureLoss vcS1159CutCell vcS1159CutCaps i ≤ vcS1159CutMargins i := by
  fin_cases i <;> decide +kernel


end HlawkaSchatten.BelowExponent.Vertex
