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

def vcS1192CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨17/40, 7/16⟩, ⟨0, 1/40⟩⟩
def vcS1192CutRoots : Fin 3 → RatBounds := ![⟨28225568723821/17592186044416, 481482983647571/281474976710656⟩, ⟨364169920333529/281474976710656, 195543505356483/140737488355328⟩, ⟨336257553121911/281474976710656, 366090439048947/281474976710656⟩]
def vcS1192CutCaps : Fin 3 → Fin 3 → ℚ := ![![1359319031/20000000, 404888037/10000000, 759121397/25000000], ![2415985359/100000000, 42490631/2000000, 831318729/50000000], ![1019186173/100000000, 404820923/50000000, 7349091/1000000]]
def vcS1192CutWeightFloor : ℚ := 2986567/2500000
def vcS1192CutMargins : Fin 3 → ℚ := ![12977857/5000000000, 18382773/10000000000, 14919453/10000000000]

theorem vcS1192Cut_roots_ok : vcS1192CutCell.rootsOK vcS1192CutRoots = true := by decide +kernel

theorem vcS1192Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1192CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1192Cut_margin_le (i : Fin 3) : curvatureLoss vcS1192CutCell vcS1192CutCaps i ≤ vcS1192CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1193CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨17/40, 7/16⟩, ⟨1/40, 1/20⟩⟩
def vcS1193CutRoots : Fin 3 → RatBounds := ![⟨448307135042945/281474976710656, 477660687973245/281474976710656⟩, ⟨358964342380457/281474976710656, 48142812166191/35184372088832⟩, ⟨165503424252257/140737488355328, 360064317119871/281474976710656⟩]
def vcS1193CutCaps : Fin 3 → Fin 3 → ℚ := ![![7128186779/100000000, 4268045033/100000000, 3218873779/100000000], ![2531951417/100000000, 138789701/6250000, 1739562297/100000000], ![912567249/100000000, 722172449/100000000, 655870433/100000000]]
def vcS1193CutWeightFloor : ℚ := 15552411/12500000
def vcS1193CutMargins : Fin 3 → ℚ := ![2599689/1000000000, 2289397/1250000000, 7404217/5000000000]

theorem vcS1193Cut_roots_ok : vcS1193CutCell.rootsOK vcS1193CutRoots = true := by decide +kernel

theorem vcS1193Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1193CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1193Cut_margin_le (i : Fin 3) : curvatureLoss vcS1193CutCell vcS1193CutCaps i ≤ vcS1193CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1194CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨17/40, 7/16⟩, ⟨1/20, 3/40⟩⟩
def vcS1194CutRoots : Fin 3 → RatBounds := ![⟨445264863497063/281474976710656, 237079116016053/140737488355328⟩, ⟨177099927593577/140737488355328, 370825509347/274877906944⟩, ⟨326205521823975/281474976710656, 354577542572509/281474976710656⟩]
def vcS1194CutCaps : Fin 3 → Fin 3 → ℚ := ![![1491737349/20000000, 4485059577/100000000, 849922727/25000000], ![1323454321/50000000, 18093957/781250, 907930629/50000000], ![410643797/50000000, 161925839/25000000, 294272079/50000000]]
def vcS1194CutWeightFloor : ℚ := 32347507/25000000
def vcS1194CutMargins : Fin 3 → ℚ := ![26153801/10000000000, 9171777/5000000000, 14784627/10000000000]

theorem vcS1194Cut_roots_ok : vcS1194CutCell.rootsOK vcS1194CutRoots = true := by decide +kernel

theorem vcS1194Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1194CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1194Cut_margin_le (i : Fin 3) : curvatureLoss vcS1194CutCell vcS1194CutCaps i ≤ vcS1194CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1195CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨17/40, 7/16⟩, ⟨3/40, 1/10⟩⟩
def vcS1195CutRoots : Fin 3 → RatBounds := ![⟨221226258838885/140737488355328, 470936700700527/281474976710656⟩, ⟨10931946167439/8796093022208, 374767792220087/281474976710656⟩, ⟨321797983649951/281474976710656, 349560447748551/281474976710656⟩]
def vcS1195CutCaps : Fin 3 → Fin 3 → ℚ := ![![1557632167/20000000, 293760307/6250000, 447390933/12500000], ![34511787/1250000, 2410761587/100000000, 236448079/12500000], ![92825951/12500000, 583833437/100000000, 6634643/1250000]]
def vcS1195CutWeightFloor : ℚ := 16796559/12500000
def vcS1195CutMargins : Fin 3 → ℚ := ![26405341/10000000000, 288277/156250000, 14831637/10000000000]

theorem vcS1195Cut_roots_ok : vcS1195CutCell.rootsOK vcS1195CutRoots = true := by decide +kernel

theorem vcS1195Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1195CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1195Cut_margin_le (i : Fin 3) : curvatureLoss vcS1195CutCell vcS1195CutCaps i ≤ vcS1195CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1196CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨7/16, 9/20⟩, ⟨0, 1/40⟩⟩
def vcS1196CutRoots : Fin 3 → RatBounds := ![⟨225457520099997/140737488355328, 240388127042257/140737488355328⟩, ⟨180145657276665/140737488355328, 387090362472299/281474976710656⟩, ⟨169701384367227/140737488355328, 184635185884833/140737488355328⟩]
def vcS1196CutCaps : Fin 3 → Fin 3 → ℚ := ![![836738489/12500000, 3953238503/100000000, 1522190471/50000000], ![472887587/20000000, 126181621/6250000, 843108233/50000000], ![1017546673/100000000, 198653183/25000000, 746415137/100000000]]
def vcS1196CutWeightFloor : ℚ := 24116017/20000000
def vcS1196CutMargins : Fin 3 → ℚ := ![12820833/5000000000, 17872257/10000000000, 15070817/10000000000]

theorem vcS1196Cut_roots_ok : vcS1196CutCell.rootsOK vcS1196CutRoots = true := by decide +kernel

theorem vcS1196Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1196CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1196Cut_margin_le (i : Fin 3) : curvatureLoss vcS1196CutCell vcS1196CutCaps i ≤ vcS1196CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1197CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨7/16, 9/20⟩, ⟨1/40, 1/20⟩⟩
def vcS1197CutRoots : Fin 3 → RatBounds := ![⟨447622532489023/281474976710656, 476964417973085/281474976710656⟩, ⟨44385180963049/35184372088832, 381137574887811/281474976710656⟩, ⟨334159514094017/281474976710656, 363257981217731/281474976710656⟩]
def vcS1197CutCaps : Fin 3 → Fin 3 → ℚ := ![![1755280059/25000000, 4166652799/100000000, 3228929057/100000000], ![2477758181/100000000, 422054429/20000000, 1763880289/100000000], ![455523221/50000000, 354355839/50000000, 166530251/25000000]]
def vcS1197CutWeightFloor : ℚ := 125560401/100000000
def vcS1197CutMargins : Fin 3 → ℚ := ![802189/312500000, 1779643/1000000000, 3738913/2500000000]

theorem vcS1197Cut_roots_ok : vcS1197CutCell.rootsOK vcS1197CutRoots = true := by decide +kernel

theorem vcS1197Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1197CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1197Cut_margin_le (i : Fin 3) : curvatureLoss vcS1197CutCell vcS1197CutCaps i ≤ vcS1197CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1198CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨7/16, 9/20⟩, ⟨1/20, 3/40⟩⟩
def vcS1198CutRoots : Fin 3 → RatBounds := ![⟨222294496777689/140737488355328, 14795988170313/8796093022208⟩, ⟨350313670415161/281474976710656, 93928407876007/70368744177664⟩, ⟨164682262291129/140737488355328, 22361444230331/17592186044416⟩]
def vcS1198CutCaps : Fin 3 → Fin 3 → ℚ := ![![3673630653/50000000, 437797517/10000000, 53310561/1562500], ![1295046257/50000000, 88038333/4000000, 3681849/200000], ![819875049/100000000, 635584523/100000000, 18678979/3125000]]
def vcS1198CutWeightFloor : ℚ := 130555369/100000000
def vcS1198CutMargins : Fin 3 → ℚ := ![3226771/1250000000, 2226873/1250000000, 14929121/10000000000]

theorem vcS1198Cut_roots_ok : vcS1198CutCell.rootsOK vcS1198CutRoots = true := by decide +kernel

theorem vcS1198Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1198CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1198Cut_margin_le (i : Fin 3) : curvatureLoss vcS1198CutCell vcS1198CutCaps i ≤ vcS1198CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1199CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨7/16, 9/20⟩, ⟨3/40, 1/10⟩⟩
def vcS1199CutRoots : Fin 3 → RatBounds := ![⟨110446184510739/70368744177664, 470259039572257/281474976710656⟩, ⟨345933622116677/281474976710656, 92687644097435/70368744177664⟩, ⟨324962388894811/281474976710656, 352776373362625/281474976710656⟩]
def vcS1199CutCaps : Fin 3 → Fin 3 → ℚ := ![![3836198193/50000000, 458744077/10000000, 718683201/20000000], ![2701524261/100000000, 1145508729/50000000, 479349511/25000000], ![74129369/10000000, 286435449/50000000, 26952017/5000000]]
def vcS1199CutWeightFloor : ℚ := 135562473/100000000
def vcS1199CutMargins : Fin 3 → ℚ := ![26052921/10000000000, 17910043/10000000000, 7487281/5000000000]

theorem vcS1199Cut_roots_ok : vcS1199CutCell.rootsOK vcS1199CutRoots = true := by decide +kernel

theorem vcS1199Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1199CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1199Cut_margin_le (i : Fin 3) : curvatureLoss vcS1199CutCell vcS1199CutCaps i ≤ vcS1199CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1200CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨9/20, 37/80⟩, ⟨0, 1/40⟩⟩
def vcS1200CutRoots : Fin 3 → RatBounds := ![⟨450421562469099/281474976710656, 480307379783587/281474976710656⟩, ⟨356538268939225/281474976710656, 95812248416439/70368744177664⟩, ⟨42829279829575/35184372088832, 186284804517703/140737488355328⟩]
def vcS1200CutCaps : Fin 3 → Fin 3 → ℚ := ![![3308319707/50000000, 3875426903/100000000, 1532452911/50000000], ![2326195111/100000000, 962028577/50000000, 6706661/390625], ![508218791/50000000, 39004161/5000000, 758303991/100000000]]
def vcS1200CutWeightFloor : ℚ := 60864067/50000000
def vcS1200CutMargins : Fin 3 → ℚ := ![25407393/10000000000, 8710759/5000000000, 610549/400000000]

theorem vcS1200Cut_roots_ok : vcS1200CutCell.rootsOK vcS1200CutRoots = true := by decide +kernel

theorem vcS1200Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1200CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1200Cut_margin_le (i : Fin 3) : curvatureLoss vcS1200CutCell vcS1200CutCaps i ≤ vcS1200CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1201CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨9/20, 37/80⟩, ⟨1/40, 1/20⟩⟩
def vcS1201CutRoots : Fin 3 → RatBounds := ![⟨447135576268201/281474976710656, 59562840152891/35184372088832⟩, ⟨351323508549145/281474976710656, 377286922189949/281474976710656⟩, ⟨337398109843735/281474976710656, 366570138089231/281474976710656⟩]
def vcS1201CutCaps : Fin 3 → Fin 3 → ℚ := ![![1735214767/25000000, 4084032129/100000000, 130093947/4000000], ![243749319/10000000, 2011195703/100000000, 448908019/25000000], ![910017621/100000000, 347854121/50000000, 4229509/625000]]
def vcS1201CutWeightFloor : ℚ := 31683233/25000000
def vcS1201CutMargins : Fin 3 → ℚ := ![25426607/10000000000, 17339963/10000000000, 946639/625000000]

theorem vcS1201Cut_roots_ok : vcS1201CutCell.rootsOK vcS1201CutRoots = true := by decide +kernel

theorem vcS1201Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1201CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1201Cut_margin_le (i : Fin 3) : curvatureLoss vcS1201CutCell vcS1201CutCaps i ≤ vcS1201CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1202CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨9/20, 37/80⟩, ⟨1/20, 3/40⟩⟩
def vcS1202CutRoots : Fin 3 → RatBounds := ![⟨222054029435445/140737488355328, 473016555072439/281474976710656⟩, ⟨346551863392493/281474976710656, 371855261373369/281474976710656⟩, ⟨332609141143881/281474976710656, 180553200820083/140737488355328⟩]
def vcS1202CutCaps : Fin 3 → Fin 3 → ℚ := ![![7264016101/100000000, 858118893/20000000, 3438152447/100000000], ![2547823389/100000000, 524420437/25000000, 234217781/12500000], ![163783921/20000000, 623885673/100000000, 948799/156250]]
def vcS1202CutWeightFloor : ℚ := 65876449/50000000
def vcS1202CutMargins : Fin 3 → ℚ := ![25561559/10000000000, 17351209/10000000000, 1511879/1000000000]

theorem vcS1202Cut_roots_ok : vcS1202CutCell.rootsOK vcS1202CutRoots = true := by decide +kernel

theorem vcS1202Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1202CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1202Cut_margin_le (i : Fin 3) : curvatureLoss vcS1202CutCell vcS1202CutCaps i ≤ vcS1202CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1203CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨9/20, 37/80⟩, ⟨3/40, 1/10⟩⟩
def vcS1203CutRoots : Fin 3 → RatBounds := ![⟨220654690750955/140737488355328, 469810117856809/281474976710656⟩, ⟨171084396418123/140737488355328, 366885785948989/281474976710656⟩, ⟨328212100303559/281474976710656, 356109308036349/281474976710656⟩]
def vcS1203CutCaps : Fin 3 → Fin 3 → ℚ := ![![7586176647/100000000, 224767219/5000000, 3622516653/100000000], ![2657267007/100000000, 2183565601/100000000, 78051349/4000000], ![1851013/250000, 140573801/25000000, 273802231/50000000]]
def vcS1203CutWeightFloor : ℚ := 34196357/25000000
def vcS1203CutMargins : Fin 3 → ℚ := ![12895571/5000000000, 8718839/5000000000, 15164489/10000000000]

theorem vcS1203Cut_roots_ok : vcS1203CutCell.rootsOK vcS1203CutRoots = true := by decide +kernel

theorem vcS1203Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1203CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1203Cut_margin_le (i : Fin 3) : curvatureLoss vcS1203CutCell vcS1203CutCaps i ≤ vcS1203CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1204CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨37/80, 19/40⟩, ⟨0, 1/40⟩⟩
def vcS1204CutRoots : Fin 3 → RatBounds := ![⟨450126381443183/281474976710656, 480073917600021/281474976710656⟩, ⟨352903001446617/281474976710656, 189777124044795/140737488355328⟩, ⟨345957464701059/281474976710656, 46999251523175/35184372088832⟩]
def vcS1204CutCaps : Fin 3 → Fin 3 → ℚ := ![![820519401/12500000, 953616761/25000000, 3098453347/100000000], ![92029201/4000000, 1838958337/100000000, 1754954307/100000000], ![1015849223/100000000, 191505797/25000000, 770590347/100000000]]
def vcS1204CutWeightFloor : ℚ := 122908781/100000000
def vcS1204CutMargins : Fin 3 → ℚ := ![3156319/1250000000, 17026403/10000000000, 15499549/10000000000]

theorem vcS1204Cut_roots_ok : vcS1204CutCell.rootsOK vcS1204CutRoots = true := by decide +kernel

theorem vcS1204Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1204CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1204Cut_margin_le (i : Fin 3) : curvatureLoss vcS1204CutCell vcS1204CutCaps i ≤ vcS1204CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1205CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨37/80, 19/40⟩, ⟨1/40, 1/20⟩⟩
def vcS1205CutRoots : Fin 3 → RatBounds := ![⟨446844006834677/281474976710656, 476273183320167/281474976710656⟩, ⟨347682796278871/281474976710656, 373581935955997/281474976710656⟩, ⟨170364048545627/140737488355328, 185003310241963/140737488355328⟩]
def vcS1205CutCaps : Fin 3 → Fin 3 → ℚ := ![![6886743569/100000000, 502393579/12500000, 3289561823/100000000], ![301326533/12500000, 384466621/20000000, 1835105709/100000000], ![113683993/12500000, 13662689/2000000, 687685387/100000000]]
def vcS1205CutWeightFloor : ℚ := 127938889/100000000
def vcS1205CutMargins : Fin 3 → ℚ := ![6316037/2500000000, 3388289/2000000000, 15381659/10000000000]

theorem vcS1205Cut_roots_ok : vcS1205CutCell.rootsOK vcS1205CutRoots = true := by decide +kernel

theorem vcS1205Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1205CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1205Cut_margin_le (i : Fin 3) : curvatureLoss vcS1205CutCell vcS1205CutCaps i ≤ vcS1205CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1206CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨37/80, 19/40⟩, ⟨1/20, 3/40⟩⟩
def vcS1206CutRoots : Fin 3 → RatBounds := ![⟨221909911707993/140737488355328, 29549415316261/17592186044416⟩, ⟨342906755302327/281474976710656, 184070828701659/140737488355328⟩, ⟨83986198776109/70368744177664, 182276615088033/140737488355328⟩]
def vcS1206CutCaps : Fin 3 → Fin 3 → ℚ := ![![7208266179/100000000, 168873109/4000000, 1739492649/50000000], ![251954057/10000000, 2005079213/100000000, 59832499/3125000], ![25575411/3125000, 612581281/100000000, 77133619/12500000]]
def vcS1206CutWeightFloor : ℚ := 66492339/50000000
def vcS1206CutMargins : Fin 3 → ℚ := ![6348369/2500000000, 16947719/10000000000, 3838819/2500000000]

theorem vcS1206Cut_roots_ok : vcS1206CutCell.rootsOK vcS1206CutRoots = true := by decide +kernel

theorem vcS1206Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1206CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1206Cut_margin_le (i : Fin 3) : curvatureLoss vcS1206CutCell vcS1206CutCaps i ≤ vcS1206CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1207CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨37/80, 19/40⟩, ⟨3/40, 1/10⟩⟩
def vcS1207CutRoots : Fin 3 → RatBounds := ![⟨441024233871353/281474976710656, 117396893087027/70368744177664⟩, ⟨338520157269213/281474976710656, 90791228375981/70368744177664⟩, ⟨331552506251371/281474976710656, 179782515990907/140737488355328⟩]
def vcS1207CutCaps : Fin 3 → Fin 3 → ℚ := ![![7528791453/100000000, 55284139/1250000, 1833464653/50000000], ![2627594647/100000000, 521811183/25000000, 1993604537/100000000], ![739934677/100000000, 34505173/6250000, 111295127/20000000]]
def vcS1207CutWeightFloor : ℚ := 138043453/100000000
def vcS1207CutMargins : Fin 3 → ℚ := ![3202179/1250000000, 2128493/1250000000, 15403197/10000000000]

theorem vcS1207Cut_roots_ok : vcS1207CutCell.rootsOK vcS1207CutRoots = true := by decide +kernel

theorem vcS1207Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1207CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1207Cut_margin_le (i : Fin 3) : curvatureLoss vcS1207CutCell vcS1207CutCaps i ≤ vcS1207CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1208CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨19/40, 39/80⟩, ⟨0, 1/40⟩⟩
def vcS1208CutRoots : Fin 3 → RatBounds := ![⟨450028138110215/281474976710656, 480074655493295/281474976710656⟩, ⟨349378301216275/281474976710656, 375998270533193/281474976710656⟩, ⟨349378301216275/281474976710656, 379550049445817/281474976710656⟩]
def vcS1208CutCaps : Fin 3 → Fin 3 → ℚ := ![![6536240369/100000000, 3769674257/100000000, 1572831813/50000000], ![286983291/12500000, 1771825481/100000000, 453857669/25000000], ![1015776619/100000000, 752406063/100000000, 391645799/50000000]]
def vcS1208CutWeightFloor : ℚ := 62062053/50000000
def vcS1208CutMargins : Fin 3 → ℚ := ![6296491/2500000000, 3340283/2000000000, 15809103/10000000000]

theorem vcS1208Cut_roots_ok : vcS1208CutCell.rootsOK vcS1208CutRoots = true := by decide +kernel

theorem vcS1208Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1208CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1208Cut_margin_le (i : Fin 3) : curvatureLoss vcS1208CutCell vcS1208CutCaps i ≤ vcS1208CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1209CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨19/40, 39/80⟩, ⟨1/40, 1/20⟩⟩
def vcS1209CutRoots : Fin 3 → RatBounds := ![⟨111686619975917/70368744177664, 238137303505613/140737488355328⟩, ⟨86038037477991/70368744177664, 370014807240879/281474976710656⟩, ⟨344155287837069/281474976710656, 373573862534013/281474976710656⟩]
def vcS1209CutCaps : Fin 3 → Fin 3 → ℚ := ![![3429278897/50000000, 1985638541/50000000, 3341258851/100000000], ![2405541381/100000000, 926224547/50000000, 949052211/50000000], ![7275239/800000, 335482931/50000000, 699028971/100000000]]
def vcS1209CutWeightFloor : ℚ := 129180409/100000000
def vcS1209CutMargins : Fin 3 → ℚ := ![2519867/1000000000, 8308193/5000000000, 1961787/1250000000]

theorem vcS1209Cut_roots_ok : vcS1209CutCell.rootsOK vcS1209CutRoots = true := by decide +kernel

theorem vcS1209Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1209CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1209Cut_margin_le (i : Fin 3) : curvatureLoss vcS1209CutCell vcS1209CutCaps i ≤ vcS1209CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1210CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨19/40, 39/80⟩, ⟨1/20, 3/40⟩⟩
def vcS1210CutRoots : Fin 3 → RatBounds := ![⟨221861478267423/140737488355328, 472792707839835/281474976710656⟩, ⟨339371231680167/281474976710656, 45570631748975/35184372088832⟩, ⟨339377259069755/281474976710656, 368129995331481/281474976710656⟩]
def vcS1210CutCaps : Fin 3 → Fin 3 → ℚ := ![![7179794317/100000000, 4170909529/100000000, 1767557193/50000000], ![628566127/25000000, 241557043/12500000, 1980151929/100000000], ![204587887/25000000, 150412203/25000000, 627255077/100000000]]
def vcS1210CutWeightFloor : ℚ := 134252897/100000000
def vcS1210CutMargins : Fin 3 → ℚ := ![25327081/10000000000, 8310509/5000000000, 3134487/2000000000]

theorem vcS1210Cut_roots_ok : vcS1210CutCell.rootsOK vcS1210CutRoots = true := by decide +kernel

theorem vcS1210Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1210CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1210Cut_margin_le (i : Fin 3) : curvatureLoss vcS1210CutCell vcS1210CutCaps i ≤ vcS1210CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS1211CutCell : ParameterCell := ⟨⟨3/80, 1/20⟩, ⟨19/40, 39/80⟩, ⟨3/40, 1/10⟩⟩
def vcS1211CutRoots : Fin 3 → RatBounds := ![⟨440927977147817/281474976710656, 234795116084447/140737488355328⟩, ⟨83745161106631/70368744177664, 2809220579039/2199023255552⟩, ⟨334989342563675/281474976710656, 181574958500879/140737488355328⟩]
def vcS1211CutCaps : Fin 3 → Fin 3 → ℚ := ![![7500022079/100000000, 4368795701/100000000, 372744289/10000000], ![1311057591/50000000, 402378883/20000000, 2061621103/100000000], ![369939161/50000000, 542212759/100000000, 113133557/20000000]]
def vcS1211CutWeightFloor : ℚ := 139338789/100000000
def vcS1211CutMargins : Fin 3 → ℚ := ![25550099/10000000000, 16698323/10000000000, 7863023/5000000000]

theorem vcS1211Cut_roots_ok : vcS1211CutCell.rootsOK vcS1211CutRoots = true := by decide +kernel

theorem vcS1211Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS1211CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS1211Cut_margin_le (i : Fin 3) : curvatureLoss vcS1211CutCell vcS1211CutCaps i ≤ vcS1211CutMargins i := by
  fin_cases i <;> decide +kernel


end HlawkaSchatten.BelowExponent.Vertex
