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

def vcM38CutCell : ParameterCell := ⟨⟨3/40, 1/10⟩, ⟨9/40, 1/4⟩, ⟨0, 1/36⟩⟩
def vcM38CutRoots : Fin 3 → RatBounds := ![⟨450061547333213/281474976710656, 508542595440739/281474976710656⟩, ⟨208706542026683/140737488355328, 236652454162667/140737488355328⟩, ⟨287253401578413/281474976710656, 86079822493293/70368744177664⟩]
def vcM38CutCaps : Fin 3 → Fin 3 → ℚ := ![![20971027267/100000000, 3395554277/20000000, 12132411101/100000000], ![713148119/6250000, 1518610859/12500000, 1461716069/20000000], ![434641031/25000000, 868354937/50000000, 255956991/25000000]]
def vcM38CutWeightFloor : ℚ := 25513227/25000000
def vcM38CutMargins : Fin 3 → ℚ := ![263426/9765625, 61075673/2500000000, 16175763/1000000000]

theorem vcM38Cut_roots_ok : vcM38CutCell.rootsOK vcM38CutRoots = true := by decide +kernel

theorem vcM38Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM38CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM38Cut_margin_le (i : Fin 3) : curvatureLoss vcM38CutCell vcM38CutCaps i ≤ vcM38CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM39CutCell : ParameterCell := ⟨⟨3/40, 1/10⟩, ⟨9/40, 1/4⟩, ⟨1/36, 1/18⟩⟩
def vcM39CutRoots : Fin 3 → RatBounds := ![⟨445815122916703/281474976710656, 503496654699765/281474976710656⟩, ⟨412138326473319/281474976710656, 467038019702999/281474976710656⟩, ⟨281720914638111/281474976710656, 168699038565773/140737488355328⟩]
def vcM39CutCaps : Fin 3 → Fin 3 → ℚ := ![![1120683469/5000000, 18157781967/100000000, 2575821417/20000000], ![3045763423/25000000, 6473231987/50000000, 7748800069/100000000], ![390024873/25000000, 310439679/20000000, 913492403/100000000]]
def vcM39CutWeightFloor : ℚ := 53186521/50000000
def vcM39CutMargins : Fin 3 → ℚ := ![57066831/2000000000, 257972971/10000000000, 21245777/1250000000]

theorem vcM39Cut_roots_ok : vcM39CutCell.rootsOK vcM39CutRoots = true := by decide +kernel

theorem vcM39Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM39CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM39Cut_margin_le (i : Fin 3) : curvatureLoss vcM39CutCell vcM39CutCaps i ≤ vcM39CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM40CutCell : ParameterCell := ⟨⟨3/40, 1/10⟩, ⟨1/4, 11/40⟩, ⟨0, 1/36⟩⟩
def vcM40CutRoots : Fin 3 → RatBounds := ![⟨443166446612007/281474976710656, 499307530392143/281474976710656⟩, ⟨101330247147781/70368744177664, 3582794755631/2199023255552⟩, ⟨73043165217683/70368744177664, 173745624713371/140737488355328⟩]
def vcM40CutCaps : Fin 3 → Fin 3 → ℚ := ![![17265144157/100000000, 6804497301/50000000, 2516122607/25000000], ![8459072031/100000000, 4502299921/50000000, 694822043/12500000], ![16687411/1000000, 817849037/50000000, 1032208771/100000000]]
def vcM40CutWeightFloor : ℚ := 5190029/5000000
def vcM40CutMargins : Fin 3 → ℚ := ![4341311/200000000, 48111279/2500000000, 132010927/10000000000]

theorem vcM40Cut_roots_ok : vcM40CutCell.rootsOK vcM40CutRoots = true := by decide +kernel

theorem vcM40Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM40CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM40Cut_margin_le (i : Fin 3) : curvatureLoss vcM40CutCell vcM40CutCaps i ≤ vcM40CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM41CutCell : ParameterCell := ⟨⟨3/40, 1/10⟩, ⟨1/4, 11/40⟩, ⟨1/36, 1/18⟩⟩
def vcM41CutRoots : Fin 3 → RatBounds := ![⟨219519438667079/140737488355328, 247204620053477/140737488355328⟩, ⟨400052467666991/281474976710656, 113086101527185/70368744177664⟩, ⟨286657388674997/281474976710656, 10645295910267/8796093022208⟩]
def vcM41CutCaps : Fin 3 → Fin 3 → ℚ := ![![1844737379/10000000, 1455178589/10000000, 10700446089/100000000], ![2256383887/25000000, 9586686899/100000000, 2949508411/50000000], ![1496470651/100000000, 1460714233/100000000, 57537951/6250000]]
def vcM41CutWeightFloor : ℚ := 21640709/20000000
def vcM41CutMargins : Fin 3 → ℚ := ![229065657/10000000000, 101335249/5000000000, 69281309/5000000000]

theorem vcM41Cut_roots_ok : vcM41CutCell.rootsOK vcM41CutRoots = true := by decide +kernel

theorem vcM41Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM41CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM41Cut_margin_le (i : Fin 3) : curvatureLoss vcM41CutCell vcM41CutCaps i ≤ vcM41CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM42CutCell : ParameterCell := ⟨⟨3/40, 1/10⟩, ⟨11/40, 3/10⟩, ⟨0, 1/36⟩⟩
def vcM42CutRoots : Fin 3 → RatBounds := ![⟨437379290224903/281474976710656, 245847048383057/140737488355328⟩, ⟨197147700632077/140737488355328, 111368360818239/70368744177664⟩, ⟨37144052129083/35184372088832, 175555227311091/140737488355328⟩]
def vcM42CutCaps : Fin 3 → Fin 3 → ℚ := ![![3730898673/25000000, 11414529409/100000000, 8750047103/100000000], ![6620873501/100000000, 3503436589/50000000, 34986589/781250], ![1615087501/100000000, 387270281/25000000, 522584811/50000000]]
def vcM42CutWeightFloor : ℚ := 21113949/20000000
def vcM42CutMargins : Fin 3 → ℚ := ![183893777/10000000000, 158858191/10000000000, 56713529/5000000000]

theorem vcM42Cut_roots_ok : vcM42CutCell.rootsOK vcM42CutRoots = true := by decide +kernel

theorem vcM42Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM42CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM42Cut_margin_le (i : Fin 3) : curvatureLoss vcM42CutCell vcM42CutCaps i ≤ vcM42CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM43CutCell : ParameterCell := ⟨⟨3/40, 1/10⟩, ⟨11/40, 3/10⟩, ⟨1/36, 1/18⟩⟩
def vcM43CutRoots : Fin 3 → RatBounds := ![⟨433352072339381/281474976710656, 486919133194321/281474976710656⟩, ⟨389027287487755/281474976710656, 219611477554699/140737488355328⟩, ⟨291656176034391/281474976710656, 172170625333497/140737488355328⟩]
def vcM43CutCaps : Fin 3 → Fin 3 → ℚ := ![![15940179607/100000000, 12206245031/100000000, 9315706449/100000000], ![882411207/12500000, 7455002501/100000000, 4756453589/100000000], ![361888879/25000000, 691209447/50000000, 931869389/100000000]]
def vcM43CutWeightFloor : ℚ := 55020509/50000000
def vcM43CutMargins : Fin 3 → ℚ := ![48411279/2500000000, 41734253/2500000000, 118926689/10000000000]

theorem vcM43Cut_roots_ok : vcM43CutCell.rootsOK vcM43CutRoots = true := by decide +kernel

theorem vcM43Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM43CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM43Cut_margin_le (i : Fin 3) : curvatureLoss vcM43CutCell vcM43CutCaps i ≤ vcM43CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM44CutCell : ParameterCell := ⟨⟨3/40, 1/10⟩, ⟨3/10, 13/40⟩, ⟨0, 1/36⟩⟩
def vcM44CutRoots : Fin 3 → RatBounds := ![⟨432571652947937/281474976710656, 242742311894359/140737488355328⟩, ⟨384176673753559/281474976710656, 433675315789351/281474976710656⟩, ⟨302230823312201/281474976710656, 355158818281517/281474976710656⟩]
def vcM44CutCaps : Fin 3 → Fin 3 → ℚ := ![![52029647/390625, 9909698561/100000000, 984057287/12500000], ![2701963937/50000000, 1132095177/20000000, 1888962289/50000000], ![786871749/50000000, 1473602931/100000000, 1062051007/100000000]]
def vcM44CutWeightFloor : ℚ := 53686979/50000000
def vcM44CutMargins : Fin 3 → ℚ := ![80728167/5000000000, 6792749/500000000, 25315541/2500000000]

theorem vcM44Cut_roots_ok : vcM44CutCell.rootsOK vcM44CutRoots = true := by decide +kernel

theorem vcM44Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM44CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM44Cut_margin_le (i : Fin 3) : curvatureLoss vcM44CutCell vcM44CutCaps i ≤ vcM44CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM45CutCell : ParameterCell := ⟨⟨3/40, 1/10⟩, ⟨3/10, 13/40⟩, ⟨1/36, 1/18⟩⟩
def vcM45CutRoots : Fin 3 → RatBounds := ![⟨26789254590471/17592186044416, 240405777918425/140737488355328⟩, ⟨189452092250799/140737488355328, 213709379719957/140737488355328⟩, ⟨74188725181103/70368744177664, 348456344288915/281474976710656⟩]
def vcM45CutCaps : Fin 3 → Fin 3 → ℚ := ![![2847378847/20000000, 5298957157/50000000, 8398737117/100000000], ![28791217/500000, 6019252911/100000000, 4014894041/100000000], ![1409846961/100000000, 164289571/12500000, 946680841/100000000]]
def vcM45CutWeightFloor : ℚ := 111903251/100000000
def vcM45CutMargins : Fin 3 → ℚ := ![84905037/5000000000, 35624571/2500000000, 106112289/10000000000]

theorem vcM45Cut_roots_ok : vcM45CutCell.rootsOK vcM45CutRoots = true := by decide +kernel

theorem vcM45Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM45CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM45Cut_margin_le (i : Fin 3) : curvatureLoss vcM45CutCell vcM45CutCaps i ≤ vcM45CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM46CutCell : ParameterCell := ⟨⟨3/40, 1/10⟩, ⟨13/40, 7/20⟩, ⟨0, 1/36⟩⟩
def vcM46CutRoots : Fin 3 → RatBounds := ![⟨428644720391251/281474976710656, 480516766404339/281474976710656⟩, ⟨187417993695561/140737488355328, 423003999830821/281474976710656⟩, ⟨76860625710281/70368744177664, 359631137633503/281474976710656⟩]
def vcM46CutCaps : Fin 3 → Fin 3 → ℚ := ![![6106206991/50000000, 8864220313/100000000, 7301566873/100000000], ![4576987547/100000000, 1180618433/25000000, 3319370739/100000000], ![771060871/50000000, 175872237/12500000, 216487977/20000000]]
def vcM46CutWeightFloor : ℚ := 54612759/50000000
def vcM46CutMargins : Fin 3 → ℚ := ![146041059/10000000000, 29929109/2500000000, 3736651/400000000]

theorem vcM46Cut_roots_ok : vcM46CutCell.rootsOK vcM46CutRoots = true := by decide +kernel

theorem vcM46Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM46CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM46Cut_margin_le (i : Fin 3) : curvatureLoss vcM46CutCell vcM46CutCaps i ≤ vcM46CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM47CutCell : ParameterCell := ⟨⟨3/40, 1/10⟩, ⟨13/40, 7/20⟩, ⟨1/36, 1/18⟩⟩
def vcM47CutRoots : Fin 3 → RatBounds := ![⟨212384724396805/140737488355328, 475926332667041/281474976710656⟩, ⟨369555179253171/281474976710656, 416733854093791/281474976710656⟩, ⟨150993875268737/140737488355328, 352990257971331/281474976710656⟩]
def vcM47CutCaps : Fin 3 → Fin 3 → ℚ := ![![13061725537/100000000, 379176179/4000000, 7815765957/100000000], ![2437304139/50000000, 1254902301/25000000, 882201823/25000000], ![1380994867/100000000, 627153547/50000000, 482334129/50000000]]
def vcM47CutWeightFloor : ℚ := 113805353/100000000
def vcM47CutMargins : Fin 3 → ℚ := ![153447389/10000000000, 62685707/5000000000, 24483441/2500000000]

theorem vcM47Cut_roots_ok : vcM47CutCell.rootsOK vcM47CutRoots = true := by decide +kernel

theorem vcM47Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM47CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM47Cut_margin_le (i : Fin 3) : curvatureLoss vcM47CutCell vcM47CutCaps i ≤ vcM47CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM48CutCell : ParameterCell := ⟨⟨3/40, 1/10⟩, ⟨7/20, 3/8⟩, ⟨0, 1/36⟩⟩
def vcM48CutRoots : Fin 3 → RatBounds := ![⟨212761408409579/140737488355328, 476669893842723/281474976710656⟩, ⟨183083935334147/140737488355328, 206651188538725/140737488355328⟩, ⟨19551271077175/17592186044416, 364532795149435/281474976710656⟩]
def vcM48CutCaps : Fin 3 → Fin 3 → ℚ := ![![5739244837/50000000, 4075141687/50000000, 6975786933/100000000], ![4003984641/100000000, 2022102121/50000000, 3020697583/100000000], ![303692673/20000000, 673779113/50000000, 553050511/50000000]]
def vcM48CutWeightFloor : ℚ := 111136109/100000000
def vcM48CutMargins : Fin 3 → ℚ := ![16950313/1250000000, 108266717/10000000000, 22191487/2500000000]

theorem vcM48Cut_roots_ok : vcM48CutCell.rootsOK vcM48CutRoots = true := by decide +kernel

theorem vcM48Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM48CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM48Cut_margin_le (i : Fin 3) : curvatureLoss vcM48CutCell vcM48CutCaps i ≤ vcM48CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM49CutCell : ParameterCell := ⟨⟨3/40, 1/10⟩, ⟨7/20, 3/8⟩, ⟨1/36, 1/18⟩⟩
def vcM49CutRoots : Fin 3 → RatBounds := ![⟨421701583636901/281474976710656, 472144454487707/281474976710656⟩, ⟨360875484645279/281474976710656, 407012172199943/281474976710656⟩, ⟨38423404366573/35184372088832, 89487215501359/70368744177664⟩]
def vcM49CutCaps : Fin 3 → Fin 3 → ℚ := ![![12276133711/100000000, 8714659483/100000000, 373828351/5000000], ![4262509063/100000000, 1074245719/25000000, 1605791471/50000000], ![339850519/25000000, 600439003/50000000, 6160127/625000]]
def vcM49CutWeightFloor : ℚ := 1157609/1000000
def vcM49CutMargins : Fin 3 → ℚ := ![8894979/625000000, 113235999/10000000000, 93007541/10000000000]

theorem vcM49Cut_roots_ok : vcM49CutCell.rootsOK vcM49CutRoots = true := by decide +kernel

theorem vcM49Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM49CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM49Cut_margin_le (i : Fin 3) : curvatureLoss vcM49CutCell vcM49CutCaps i ≤ vcM49CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM50CutCell : ParameterCell := ⟨⟨3/40, 1/10⟩, ⟨3/8, 2/5⟩, ⟨0, 1/36⟩⟩
def vcM50CutRoots : Fin 3 → RatBounds := ![⟨423148877476157/281474976710656, 473855974754299/281474976710656⟩, ⟨22380299176727/17592186044416, 202222565448393/140737488355328⟩, ⟨318396849722469/281474976710656, 369878522902947/281474976710656⟩]
def vcM50CutCaps : Fin 3 → Fin 3 → ℚ := ![![689806333/6250000, 1922603189/25000000, 6842406579/100000000], ![3609824727/100000000, 886330141/25000000, 2837182813/100000000], ![1501574329/100000000, 647065751/50000000, 226587427/20000000]]
def vcM50CutWeightFloor : ℚ := 28279321/25000000
def vcM50CutMargins : Fin 3 → ℚ := ![5156413/400000000, 20052229/2000000000, 86549041/10000000000]

theorem vcM50Cut_roots_ok : vcM50CutCell.rootsOK vcM50CutRoots = true := by decide +kernel

theorem vcM50Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM50CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM50Cut_margin_le (i : Fin 3) : curvatureLoss vcM50CutCell vcM50CutCaps i ≤ vcM50CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM51CutCell : ParameterCell := ⟨⟨3/40, 1/10⟩, ⟨3/8, 2/5⟩, ⟨1/36, 1/18⟩⟩
def vcM51CutRoots : Fin 3 → RatBounds := ![⟨209684106732611/140737488355328, 469379080906379/281474976710656⟩, ⟨352778131739053/281474976710656, 199064598975759/140737488355328⟩, ⟨312985546031551/281474976710656, 181673601176261/140737488355328⟩]
def vcM51CutCaps : Fin 3 → Fin 3 → ℚ := ![![1475589183/12500000, 4110514247/50000000, 458878769/6250000], ![960375247/25000000, 753142047/20000000, 3016193127/100000000], ![671992317/50000000, 576458703/50000000, 504725671/50000000]]
def vcM51CutWeightFloor : ℚ := 117782727/100000000
def vcM51CutMargins : Fin 3 → ℚ := ![67599433/5000000000, 26191589/2500000000, 22665019/2500000000]

theorem vcM51Cut_roots_ok : vcM51CutCell.rootsOK vcM51CutRoots = true := by decide +kernel

theorem vcM51Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM51CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM51Cut_margin_le (i : Fin 3) : curvatureLoss vcM51CutCell vcM51CutCaps i ≤ vcM51CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM52CutCell : ParameterCell := ⟨⟨3/40, 1/10⟩, ⟨2/5, 17/40⟩, ⟨0, 1/36⟩⟩
def vcM52CutRoots : Fin 3 → RatBounds := ![⟨105370321084969/70368744177664, 472013472373471/281474976710656⟩, ⟨175256567193729/140737488355328, 198165713116319/140737488355328⟩, ⟨324205362332995/281474976710656, 93922982197269/70368744177664⟩]
def vcM52CutCaps : Fin 3 → Fin 3 → ℚ := ![![10850373821/100000000, 3719581479/50000000, 1377199603/20000000], ![671684513/20000000, 3187692123/100000000, 1377268561/50000000], ![186333253/12500000, 124579327/10000000, 1162967403/100000000]]
def vcM52CutWeightFloor : ℚ := 57590441/50000000
def vcM52CutMargins : Fin 3 → ℚ := ![31345947/2500000000, 95038059/10000000000, 43266787/5000000000]

theorem vcM52Cut_roots_ok : vcM52CutCell.rootsOK vcM52CutRoots = true := by decide +kernel

theorem vcM52Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM52CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM52Cut_margin_le (i : Fin 3) : curvatureLoss vcM52CutCell vcM52CutCaps i ≤ vcM52CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM53CutCell : ParameterCell := ⟨⟨3/40, 1/10⟩, ⟨2/5, 17/40⟩, ⟨1/36, 1/18⟩⟩
def vcM53CutRoots : Fin 3 → RatBounds := ![⟨417728302276049/281474976710656, 233784757249709/140737488355328⟩, ⟨345189998597431/281474976710656, 48748087588011/35184372088832⟩, ⟨318815699024351/281474976710656, 184604528946829/140737488355328⟩]
def vcM53CutCaps : Fin 3 → Fin 3 → ℚ := ![![5803694257/50000000, 3974966213/50000000, 1849070851/25000000], ![223326871/6250000, 33858221/1000000, 585639369/20000000], ![1334026909/100000000, 554798171/50000000, 1036181727/100000000]]
def vcM53CutWeightFloor : ℚ := 23976701/20000000
def vcM53CutMargins : Fin 3 → ℚ := ![65732677/5000000000, 24815677/2500000000, 90654039/10000000000]

theorem vcM53Cut_roots_ok : vcM53CutCell.rootsOK vcM53CutRoots = true := by decide +kernel

theorem vcM53Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM53CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM53Cut_margin_le (i : Fin 3) : curvatureLoss vcM53CutCell vcM53CutCaps i ≤ vcM53CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM54CutCell : ParameterCell := ⟨⟨3/40, 1/10⟩, ⟨17/40, 9/20⟩, ⟨0, 1/36⟩⟩
def vcM54CutRoots : Fin 3 → RatBounds := ![⟨420491695683163/281474976710656, 471103354823537/281474976710656⟩, ⟨343390229624649/281474976710656, 97219922860113/70368744177664⟩, ⟨41285131186107/35184372088832, 382005629844395/281474976710656⟩]
def vcM54CutCaps : Fin 3 → Fin 3 → ℚ := ![![10906473713/100000000, 7373461003/100000000, 1777250491/25000000], ![3218996609/100000000, 1833343/62500, 55051509/2000000], ![1485259519/100000000, 37558277/3125000, 598159487/50000000]]
def vcM54CutWeightFloor : ℚ := 586697/500000
def vcM54CutMargins : Fin 3 → ℚ := ![124680657/10000000000, 92114013/10000000000, 86506/9765625]

theorem vcM54Cut_roots_ok : vcM54CutCell.rootsOK vcM54CutRoots = true := by decide +kernel

theorem vcM54Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM54CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM54Cut_margin_le (i : Fin 3) : curvatureLoss vcM54CutCell vcM54CutCaps i ≤ vcM54CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM55CutCell : ParameterCell := ⟨⟨3/40, 1/10⟩, ⟨17/40, 9/20⟩, ⟨1/36, 1/18⟩⟩
def vcM55CutRoots : Fin 3 → RatBounds := ![⟨416753901294321/281474976710656, 466677262996257/281474976710656⟩, ⟨84512203583011/70368744177664, 382497553753687/281474976710656⟩, ⟨40614071531241/35184372088832, 93891773041841/70368744177664⟩]
def vcM55CutCaps : Fin 3 → Fin 3 → ℚ := ![![2334156741/20000000, 3938312469/50000000, 382110929/5000000], ![3424561789/100000000, 623214183/20000000, 731497787/25000000], ![265818921/20000000, 535146513/50000000, 1065930303/100000000]]
def vcM55CutWeightFloor : ℚ := 122076211/100000000
def vcM55CutMargins : Fin 3 → ℚ := ![130751587/10000000000, 96203479/10000000000, 92845103/10000000000]

theorem vcM55Cut_roots_ok : vcM55CutCell.rootsOK vcM55CutRoots = true := by decide +kernel

theorem vcM55Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM55CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM55Cut_margin_le (i : Fin 3) : curvatureLoss vcM55CutCell vcM55CutCaps i ≤ vcM55CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM56CutCell : ParameterCell := ⟨⟨3/40, 1/10⟩, ⟨9/20, 19/40⟩, ⟨0, 1/36⟩⟩
def vcM56CutRoots : Fin 3 → RatBounds := ![⟨52520454372361/35184372088832, 471106684158221/281474976710656⟩, ⟨84165495099337/70368744177664, 47752983462895/35184372088832⟩, ⟨84165495099337/70368744177664, 48607741721095/35184372088832⟩]
def vcM56CutCaps : Fin 3 → Fin 3 → ℚ := ![![11215211203/100000000, 748806837/10000000, 7531663149/100000000], ![1604259901/50000000, 2797835927/100000000, 180052007/6250000], ![742565789/50000000, 1161839799/100000000, 77076819/6250000]]
def vcM56CutWeightFloor : ℚ := 59803181/50000000
def vcM56CutMargins : Fin 3 → ℚ := ![25401917/2000000000, 22891161/2500000000, 93242191/10000000000]

theorem vcM56Cut_roots_ok : vcM56CutCell.rootsOK vcM56CutRoots = true := by decide +kernel

theorem vcM56Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM56CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM56Cut_margin_le (i : Fin 3) : curvatureLoss vcM56CutCell vcM56CutCaps i ≤ vcM56CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM57CutCell : ParameterCell := ⟨⟨3/40, 1/10⟩, ⟨9/20, 19/40⟩, ⟨1/36, 1/18⟩⟩
def vcM57CutRoots : Fin 3 → RatBounds := ![⟨208214378377873/140737488355328, 233341829960303/140737488355328⟩, ⟨331300849866529/281474976710656, 375602008255661/281474976710656⟩, ⟨331313937907381/281474976710656, 382463543748123/281474976710656⟩]
def vcM57CutCaps : Fin 3 → Fin 3 → ℚ := ![![6002814167/50000000, 7995344629/100000000, 4050889933/50000000], ![3414035157/100000000, 594636091/20000000, 153096267/5000000], ![1328985757/100000000, 206908689/20000000, 1098916397/100000000]]
def vcM57CutWeightFloor : ℚ := 124374539/100000000
def vcM57CutMargins : Fin 3 → ℚ := ![133284271/10000000000, 47834919/5000000000, 24453891/2500000000]

theorem vcM57Cut_roots_ok : vcM57CutCell.rootsOK vcM57CutRoots = true := by decide +kernel

theorem vcM57Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM57CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM57Cut_margin_le (i : Fin 3) : curvatureLoss vcM57CutCell vcM57CutCaps i ≤ vcM57CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM64CutCell : ParameterCell := ⟨⟨1/10, 1/8⟩, ⟨7/40, 1/5⟩, ⟨0, 1/36⟩⟩
def vcM64CutRoots : Fin 3 → RatBounds := ![⟨56396905524947/35184372088832, 511406696124573/281474976710656⟩, ⟨434771963545261/281474976710656, 493648100418403/281474976710656⟩, ⟨140631992217211/140737488355328, 339968817714327/281474976710656⟩]
def vcM64CutCaps : Fin 3 → Fin 3 → ℚ := ![![4390417947/20000000, 1840548097/10000000, 2875087787/25000000], ![4034177133/20000000, 5273102837/25000000, 6017196831/50000000], ![66166549/5000000, 676947539/50000000, 714700173/100000000]]
def vcM64CutWeightFloor : ℚ := 51691221/50000000
def vcM64CutMargins : Fin 3 → ℚ := ![68369871/2000000000, 160817843/5000000000, 95379261/5000000000]

theorem vcM64Cut_roots_ok : vcM64CutCell.rootsOK vcM64CutRoots = true := by decide +kernel

theorem vcM64Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM64CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM64Cut_margin_le (i : Fin 3) : curvatureLoss vcM64CutCell vcM64CutCaps i ≤ vcM64CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM65CutCell : ParameterCell := ⟨⟨1/10, 1/8⟩, ⟨7/40, 1/5⟩, ⟨1/36, 1/18⟩⟩
def vcM65CutRoots : Fin 3 → RatBounds := ![⟨446622642475105/281474976710656, 505991667908145/281474976710656⟩, ⟨107420080814493/70368744177664, 487593200458917/281474976710656⟩, ⟨34470730491875/35184372088832, 333019465472059/281474976710656⟩]
def vcM65CutCaps : Fin 3 → Fin 3 → ℚ := ![![2928842037/12500000, 19669568093/100000000, 1526260601/12500000], ![4309599227/20000000, 5633347273/25000000, 3187612451/25000000], ![237228369/20000000, 1209897553/100000000, 636379407/100000000]]
def vcM65CutWeightFloor : ℚ := 108169233/100000000
def vcM65CutMargins : Fin 3 → ℚ := ![362836759/10000000000, 17069007/500000000, 12571381/625000000]

theorem vcM65Cut_roots_ok : vcM65CutCell.rootsOK vcM65CutRoots = true := by decide +kernel

theorem vcM65Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM65CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM65Cut_margin_le (i : Fin 3) : curvatureLoss vcM65CutCell vcM65CutCaps i ≤ vcM65CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM66CutCell : ParameterCell := ⟨⟨1/10, 1/8⟩, ⟨1/5, 9/40⟩, ⟨0, 1/36⟩⟩
def vcM66CutRoots : Fin 3 → RatBounds := ![⟨442799487214195/281474976710656, 499988011722031/281474976710656⟩, ⟨210574448676507/140737488355328, 476650106711123/281474976710656⟩, ⟨285934200392557/281474976710656, 42792593192981/35184372088832⟩]
def vcM66CutCaps : Fin 3 → Fin 3 → ℚ := ![![1720229411/6250000, 4649884699/20000000, 4263261261/25000000], ![10338728041/50000000, 4276492233/20000000, 13930396219/100000000], ![1822392199/100000000, 458131119/25000000, 531034133/50000000]]
def vcM66CutWeightFloor : ℚ := 50792117/50000000
def vcM66CutMargins : Fin 3 → ℚ := ![98537097/2500000000, 366361411/10000000000, 252301849/10000000000]

theorem vcM66Cut_roots_ok : vcM66CutCell.rootsOK vcM66CutRoots = true := by decide +kernel

theorem vcM66Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM66CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM66Cut_margin_le (i : Fin 3) : curvatureLoss vcM66CutCell vcM66CutCaps i ≤ vcM66CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM67CutCell : ParameterCell := ⟨⟨1/10, 1/8⟩, ⟨1/5, 9/40⟩, ⟨1/36, 1/18⟩⟩
def vcM67CutRoots : Fin 3 → RatBounds := ![⟨438397062941265/281474976710656, 247380905518097/140737488355328⟩, ⟨416064211528619/281474976710656, 117653689254623/70368744177664⟩, ⟨35057429373981/35184372088832, 335489123378275/281474976710656⟩]
def vcM67CutCaps : Fin 3 → Fin 3 → ℚ := ![![7379052271/25000000, 24921398003/100000000, 18119324387/100000000], ![4428109467/20000000, 22880047339/100000000, 14772112817/100000000], ![819101371/50000000, 821069691/50000000, 949224933/100000000]]
def vcM67CutWeightFloor : ℚ := 105677959/100000000
def vcM67CutMargins : Fin 3 → ℚ := ![419368977/10000000000, 12165229/312500000, 266119687/10000000000]

theorem vcM67Cut_roots_ok : vcM67CutCell.rootsOK vcM67CutRoots = true := by decide +kernel

theorem vcM67Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM67CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM67Cut_margin_le (i : Fin 3) : curvatureLoss vcM67CutCell vcM67CutCaps i ≤ vcM67CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM68CutCell : ParameterCell := ⟨⟨1/10, 1/8⟩, ⟨9/40, 1/4⟩, ⟨0, 1/36⟩⟩
def vcM68CutRoots : Fin 3 → RatBounds := ![⟨435707590010395/281474976710656, 490497683138751/281474976710656⟩, ⟨204420761867877/140737488355328, 230819546703337/140737488355328⟩, ⟨145312695161135/140737488355328, 345205696898069/281474976710656⟩]
def vcM68CutCaps : Fin 3 → Fin 3 → ℚ := ![![4320591679/20000000, 17763824117/100000000, 6751490827/50000000], ![13655733769/100000000, 14251627773/100000000, 1901053763/20000000], ![1730022773/100000000, 1718062909/100000000, 1064776227/100000000]]
def vcM68CutWeightFloor : ℚ := 103250879/100000000
def vcM68CutMargins : Fin 3 → ℚ := ![292144709/10000000000, 266691541/10000000000, 19002179/1000000000]

theorem vcM68Cut_roots_ok : vcM68CutCell.rootsOK vcM68CutRoots = true := by decide +kernel

theorem vcM68Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM68CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM68Cut_margin_le (i : Fin 3) : curvatureLoss vcM68CutCell vcM68CutCaps i ≤ vcM68CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM69CutCell : ParameterCell := ⟨⟨1/10, 1/8⟩, ⟨9/40, 1/4⟩, ⟨1/36, 1/18⟩⟩
def vcM69CutRoots : Fin 3 → RatBounds := ![⟨431433471730085/281474976710656, 15169706151547/8796093022208⟩, ⟨201878462789519/140737488355328, 455610638528035/281474976710656⟩, ⟨71293929746285/70368744177664, 338442602506703/281474976710656⟩]
def vcM69CutCaps : Fin 3 → Fin 3 → ℚ := ![![23164338907/100000000, 1190054919/6250000, 14367633593/100000000], ![14620021409/100000000, 15242208981/100000000, 10095653129/100000000], ![388525011/25000000, 48061027/3125000, 951182679/100000000]]
def vcM69CutWeightFloor : ℚ := 53731837/50000000
def vcM69CutMargins : Fin 3 → ℚ := ![155089853/5000000000, 282670273/10000000000, 50073411/2500000000]

theorem vcM69Cut_roots_ok : vcM69CutCell.rootsOK vcM69CutRoots = true := by decide +kernel

theorem vcM69Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM69CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM69Cut_margin_le (i : Fin 3) : curvatureLoss vcM69CutCell vcM69CutCaps i ≤ vcM69CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM70CutCell : ParameterCell := ⟨⟨1/10, 1/8⟩, ⟨1/4, 11/40⟩, ⟨0, 1/36⟩⟩
def vcM70CutRoots : Fin 3 → RatBounds := ![⟨429725693576023/281474976710656, 120657757583611/70368744177664⟩, ⟨397639269043765/281474976710656, 14008180124145/8796093022208⟩, ⟨147688983322431/140737488355328, 174260545554135/140737488355328⟩]
def vcM70CutCaps : Fin 3 → Fin 3 → ℚ := ![![2226800617/12500000, 14269342699/100000000, 2803529963/25000000], ![9724884279/100000000, 5095217183/50000000, 6967369997/100000000], ![1659771229/100000000, 324360153/20000000, 536565539/50000000]]
def vcM70CutWeightFloor : ℚ := 52469667/50000000
def vcM70CutMargins : Fin 3 → ℚ := ![231159293/10000000000, 206734377/10000000000, 30478661/2000000000]

theorem vcM70Cut_roots_ok : vcM70CutCell.rootsOK vcM70CutRoots = true := by decide +kernel

theorem vcM70Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM70CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM70Cut_margin_le (i : Fin 3) : curvatureLoss vcM70CutCell vcM70CutCaps i ≤ vcM70CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM71CutCell : ParameterCell := ⟨⟨1/10, 1/8⟩, ⟨1/4, 11/40⟩, ⟨1/36, 1/18⟩⟩
def vcM71CutRoots : Fin 3 → RatBounds := ![⟨106390135657853/70368744177664, 477697572838445/281474976710656⟩, ⟨196274586061433/140737488355328, 442229941835817/281474976710656⟩, ⟨72488657827431/70368744177664, 85459753873867/70368744177664⟩]
def vcM71CutCaps : Fin 3 → Fin 3 → ℚ := ![![19099381063/100000000, 7647549591/50000000, 11951552249/100000000], ![2601920369/25000000, 10893653197/100000000, 3705781001/50000000], ![1490120971/100000000, 290105501/20000000, 119784663/12500000]]
def vcM71CutWeightFloor : ℚ := 109245403/100000000
def vcM71CutMargins : Fin 3 → ℚ := ![48979247/2000000000, 27323757/1250000000, 80258487/5000000000]

theorem vcM71Cut_roots_ok : vcM71CutCell.rootsOK vcM71CutRoots = true := by decide +kernel

theorem vcM71Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM71CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM71Cut_margin_le (i : Fin 3) : curvatureLoss vcM71CutCell vcM71CutCaps i ≤ vcM71CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM72CutCell : ParameterCell := ⟨⟨1/10, 1/8⟩, ⟨11/40, 3/10⟩, ⟨0, 1/36⟩⟩
def vcM72CutRoots : Fin 3 → RatBounds := ![⟨212360135096845/140737488355328, 476162014731335/281474976710656⟩, ⟨387375552468909/281474976710656, 436249629026341/281474976710656⟩, ⟨75056691892823/70368744177664, 176131252179867/140737488355328⟩]
def vcM72CutCaps : Fin 3 → Fin 3 → ℚ := ![![767726013/5000000, 600161709/5000000, 973054557/10000000], ![7396083353/100000000, 3862026523/50000000, 680404913/12500000], ![50187189/3125000, 48101537/3125000, 543095539/50000000]]
def vcM72CutWeightFloor : ℚ := 53330987/50000000
def vcM72CutMargins : Fin 3 → ℚ := ![48307241/2500000000, 33793117/2000000000, 5160863/400000000]

theorem vcM72Cut_roots_ok : vcM72CutCell.rootsOK vcM72CutRoots = true := by decide +kernel

theorem vcM72Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM72CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM72Cut_margin_le (i : Fin 3) : curvatureLoss vcM72CutCell vcM72CutCaps i ≤ vcM72CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM73CutCell : ParameterCell := ⟨⟨1/10, 1/8⟩, ⟨11/40, 3/10⟩, ⟨1/36, 1/18⟩⟩
def vcM73CutRoots : Fin 3 → RatBounds := ![⟨420646702283855/281474976710656, 471339854875359/281474976710656⟩, ⟨382275371255133/281474976710656, 215102976404477/140737488355328⟩, ⟨294830629281317/281474976710656, 345655150532611/281474976710656⟩]
def vcM73CutCaps : Fin 3 → Fin 3 → ℚ := ![![8229301283/50000000, 6432516763/50000000, 10385891573/100000000], ![988837469/12500000, 1650031267/20000000, 1159050883/20000000], ![1441128119/100000000, 1375712551/100000000, 484824111/50000000]]
def vcM73CutWeightFloor : ℚ := 13880393/12500000
def vcM73CutMargins : Fin 3 → ℚ := ![40856989/2000000000, 89115627/5000000000, 848547/62500000]

theorem vcM73Cut_roots_ok : vcM73CutCell.rootsOK vcM73CutRoots = true := by decide +kernel

theorem vcM73Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM73CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM73Cut_margin_le (i : Fin 3) : curvatureLoss vcM73CutCell vcM73CutCaps i ≤ vcM73CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM74CutCell : ParameterCell := ⟨⟨1/10, 1/8⟩, ⟨3/10, 13/40⟩, ⟨0, 1/36⟩⟩
def vcM74CutRoots : Fin 3 → RatBounds := ![⟨420588243179601/281474976710656, 470921452925795/281474976710656⟩, ⟨377916442877741/281474976710656, 13293585791499/8796093022208⟩, ⟨305203338791799/281474976710656, 356419134444883/281474976710656⟩]
def vcM74CutCaps : Fin 3 → Fin 3 → ℚ := ![![3432931369/25000000, 2625148491/25000000, 8775463177/100000000], ![185530787/3125000, 3070603293/50000000, 17968447/400000], ![1564917893/100000000, 1467354169/100000000, 68959307/6250000]]
def vcM74CutWeightFloor : ℚ := 108430007/100000000
def vcM74CutMargins : Fin 3 → ℚ := ![42188883/2500000000, 144166789/10000000000, 57147399/5000000000]

theorem vcM74Cut_roots_ok : vcM74CutCell.rootsOK vcM74CutRoots = true := by decide +kernel

theorem vcM74Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM74CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM74Cut_margin_le (i : Fin 3) : curvatureLoss vcM74CutCell vcM74CutCaps i ≤ vcM74CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM75CutCell : ParameterCell := ⟨⟨1/10, 1/8⟩, ⟨3/10, 13/40⟩, ⟨1/36, 1/18⟩⟩
def vcM75CutRoots : Fin 3 → RatBounds := ![⟨416590388413277/281474976710656, 466190633927599/281474976710656⟩, ⟨372802387779345/281474976710656, 209666031650423/140737488355328⟩, ⟨149917471264803/140737488355328, 43735134659059/35184372088832⟩]
def vcM75CutCaps : Fin 3 → Fin 3 → ℚ := ![![14722519093/100000000, 2250581247/20000000, 9390054983/100000000], ![3172987867/50000000, 204871199/3125000, 4786115853/100000000], ![701851191/50000000, 327671691/25000000, 984741937/100000000]]
def vcM75CutWeightFloor : ℚ := 112873043/100000000
def vcM75CutMargins : Fin 3 → ℚ := ![44534103/2500000000, 30354557/2000000000, 7515577/625000000]

theorem vcM75Cut_roots_ok : vcM75CutCell.rootsOK vcM75CutRoots = true := by decide +kernel

theorem vcM75Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM75CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM75Cut_margin_le (i : Fin 3) : curvatureLoss vcM75CutCell vcM75CutCaps i ≤ vcM75CutMargins i := by
  fin_cases i <;> decide +kernel


end HlawkaSchatten.BelowExponent.Vertex
