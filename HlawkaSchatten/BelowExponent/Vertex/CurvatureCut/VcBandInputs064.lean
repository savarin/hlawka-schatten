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

def vcS164CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨29/80, 3/8⟩, ⟨0, 1/40⟩⟩
def vcS164CutRoots : Fin 3 → RatBounds := ![⟨7274108240105/4398046511104, 496958623130053/281474976710656⟩, ⟨389804797756967/281474976710656, 418492580463051/281474976710656⟩, ⟨320857964693325/281474976710656, 87901698248353/70368744177664⟩]
def vcS164CutCaps : Fin 3 → Fin 3 → ℚ := ![![2003233043/25000000, 12546421/250000, 317793813/10000000], ![121132479/4000000, 2988619951/100000000, 814392329/50000000], ![105439511/10000000, 11280607/1250000, 134971233/20000000]]
def vcS164CutWeightFloor : ℚ := 3562239/3125000
def vcS164CutMargins : Fin 3 → ℚ := ![3725299/1250000000, 1134471/500000000, 2932089/2000000000]

theorem vcS164Cut_roots_ok : vcS164CutCell.rootsOK vcS164CutRoots = true := by decide +kernel

theorem vcS164Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS164CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS164Cut_margin_le (i : Fin 3) : curvatureLoss vcS164CutCell vcS164CutCaps i ≤ vcS164CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS165CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨29/80, 3/8⟩, ⟨1/40, 1/20⟩⟩
def vcS165CutRoots : Fin 3 → RatBounds := ![⟨462177609543533/281474976710656, 493063009303737/281474976710656⟩, ⟨384512873574059/281474976710656, 412463037934067/281474976710656⟩, ⟨157746386523683/140737488355328, 172705024727115/140737488355328⟩]
def vcS165CutCaps : Fin 3 → Fin 3 → ℚ := ![![2097278127/25000000, 5283808073/100000000, 670016357/20000000], ![1586058091/50000000, 3121246291/100000000, 1704415067/100000000], ![472025337/50000000, 161012267/20000000, 150557741/25000000]]
def vcS165CutWeightFloor : ℚ := 118840901/100000000
def vcS165CutMargins : Fin 3 → ℚ := ![29955921/10000000000, 44347/19531250, 7288497/5000000000]

theorem vcS165Cut_roots_ok : vcS165CutCell.rootsOK vcS165CutRoots = true := by decide +kernel

theorem vcS165Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS165CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS165Cut_margin_le (i : Fin 3) : curvatureLoss vcS165CutCell vcS165CutCaps i ≤ vcS165CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS166CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨29/80, 3/8⟩, ⟨1/20, 3/40⟩⟩
def vcS166CutRoots : Fin 3 → RatBounds := ![⟨459075320892769/281474976710656, 1912074266673/1099511627776⟩, ⟨379665384330213/281474976710656, 406963251230333/281474976710656⟩, ⟨310589120547251/281474976710656, 339770699148579/281474976710656⟩]
def vcS166CutCaps : Fin 3 → Fin 3 → ℚ := ![![8764128653/100000000, 554643951/10000000, 1760412977/50000000], ![828675427/25000000, 813227971/25000000, 1779361411/100000000], ![169915757/20000000, 722131149/100000000, 108074291/20000000]]
def vcS166CutWeightFloor : ℚ := 123702387/100000000
def vcS166CutMargins : Fin 3 → ℚ := ![18893/6250000, 22827883/10000000000, 14573581/10000000000]

theorem vcS166Cut_roots_ok : vcS166CutCell.rootsOK vcS166CutRoots = true := by decide +kernel

theorem vcS166Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS166CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS166Cut_margin_le (i : Fin 3) : curvatureLoss vcS166CutCell vcS166CutCaps i ≤ vcS166CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS167CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨29/80, 3/8⟩, ⟨3/40, 1/10⟩⟩
def vcS167CutRoots : Fin 3 → RatBounds := ![⟨456206087119501/281474976710656, 486203519800919/281474976710656⟩, ⟨23450505287439/17592186044416, 200962845408931/140737488355328⟩, ⟨38261213520507/35184372088832, 334616500262311/281474976710656⟩]
def vcS167CutCaps : Fin 3 → Fin 3 → ℚ := ![![9141436513/100000000, 5806926877/100000000, 3691259889/100000000], ![3456175907/100000000, 1691848967/50000000, 1853683843/100000000], ![768145307/100000000, 65099063/10000000, 243646247/50000000]]
def vcS167CutWeightFloor : ℚ := 32143513/25000000
def vcS167CutMargins : Fin 3 → ℚ := ![30605847/10000000000, 1439769/625000000, 14636941/10000000000]

theorem vcS167Cut_roots_ok : vcS167CutCell.rootsOK vcS167CutRoots = true := by decide +kernel

theorem vcS167Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS167CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS167Cut_margin_le (i : Fin 3) : curvatureLoss vcS167CutCell vcS167CutCaps i ≤ vcS167CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS168CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨3/8, 31/80⟩, ⟨0, 1/40⟩⟩
def vcS168CutRoots : Fin 3 → RatBounds := ![⟨463593674726529/281474976710656, 494758930470133/281474976710656⟩, ⟨192489533699121/140737488355328, 413341603069657/281474976710656⟩, ⟨40457086888977/35184372088832, 354246207332659/281474976710656⟩]
def vcS168CutCaps : Fin 3 → Fin 3 → ℚ := ![![1544881179/20000000, 2391101999/50000000, 389352311/12500000], ![720181347/25000000, 2791418087/100000000, 808472361/50000000], ![1049561039/100000000, 441875039/50000000, 342288453/50000000]]
def vcS168CutWeightFloor : ℚ := 28746489/25000000
def vcS168CutMargins : Fin 3 → ℚ := ![28912843/10000000000, 21696529/10000000000, 14589983/10000000000]

theorem vcS168Cut_roots_ok : vcS168CutCell.rootsOK vcS168CutRoots = true := by decide +kernel

theorem vcS168Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS168CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS168Cut_margin_le (i : Fin 3) : curvatureLoss vcS168CutCell vcS168CutCaps i ≤ vcS168CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS169CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨3/8, 31/80⟩, ⟨1/40, 1/20⟩⟩
def vcS169CutRoots : Fin 3 → RatBounds := ![⟨115063762635765/70368744177664, 122723308870063/70368744177664⟩, ⟨379689235868081/281474976710656, 407312780549235/281474976710656⟩, ⟨318298774554463/281474976710656, 348066284619507/281474976710656⟩]
def vcS169CutCaps : Fin 3 → Fin 3 → ℚ := ![![8086880337/100000000, 5034678919/100000000, 1642649057/50000000], ![1508737317/50000000, 583044629/20000000, 1691728093/100000000], ![939570599/100000000, 3153033/400000, 305422317/50000000]]
def vcS169CutWeightFloor : ℚ := 1498201/1250000
def vcS169CutMargins : Fin 3 → ℚ := ![29028589/10000000000, 21685421/10000000000, 14492979/10000000000]

theorem vcS169Cut_roots_ok : vcS169CutCell.rootsOK vcS169CutRoots = true := by decide +kernel

theorem vcS169Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS169CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS169Cut_margin_le (i : Fin 3) : curvatureLoss vcS169CutCell vcS169CutCaps i ≤ vcS169CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS170CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨3/8, 31/80⟩, ⟨1/20, 3/40⟩⟩
def vcS170CutRoots : Fin 3 → RatBounds := ![⟨28573589079271/17592186044416, 30459304180635/17592186044416⟩, ⟨374844462977029/281474976710656, 200907315076783/140737488355328⟩, ⟨156700694919863/140737488355328, 342441761041315/281474976710656⟩]
def vcS170CutCaps : Fin 3 → Fin 3 → ℚ := ![![8449098911/100000000, 5284714717/100000000, 3454618041/100000000], ![3153060941/100000000, 607626791/20000000, 1765851349/100000000], ![845419941/100000000, 353478271/50000000, 274024487/50000000]]
def vcS170CutWeightFloor : ℚ := 62369503/50000000
def vcS170CutMargins : Fin 3 → ℚ := ![914541/312500000, 10889331/5000000000, 7238931/5000000000]

theorem vcS170Cut_roots_ok : vcS170CutCell.rootsOK vcS170CutRoots = true := by decide +kernel

theorem vcS170Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS170CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS170Cut_margin_le (i : Fin 3) : curvatureLoss vcS170CutCell vcS170CutCaps i ≤ vcS170CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS171CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨3/8, 31/80⟩, ⟨3/40, 1/10⟩⟩
def vcS171CutRoots : Fin 3 → RatBounds := ![⟨227165526416407/140737488355328, 242043485351777/140737488355328⟩, ⟨92597588527925/70368744177664, 396779412460849/281474976710656⟩, ⟨154453698713941/140737488355328, 168650347142363/140737488355328⟩]
def vcS171CutCaps : Fin 3 → Fin 3 → ℚ := ![![881274767/10000000, 69158223/1250000, 3623408971/100000000], ![3287585683/100000000, 197514041/6250000, 183937121/10000000], ![382138973/50000000, 19913269/3125000, 98834459/20000000]]
def vcS171CutWeightFloor : ℚ := 25926517/20000000
def vcS171CutMargins : Fin 3 → ℚ := ![14802193/5000000000, 5489151/2500000000, 7265107/5000000000]

theorem vcS171Cut_roots_ok : vcS171CutCell.rootsOK vcS171CutRoots = true := by decide +kernel

theorem vcS171Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS171CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS171Cut_margin_le (i : Fin 3) : curvatureLoss vcS171CutCell vcS171CutCaps i ≤ vcS171CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS172CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨31/80, 2/5⟩, ⟨0, 1/40⟩⟩
def vcS172CutRoots : Fin 3 → RatBounds := ![⟨115471190080479/70368744177664, 492846376575781/281474976710656⟩, ⟨380340894754255/281474976710656, 204209907316835/140737488355328⟩, ⟨326516382142037/281474976710656, 89245975345237/70368744177664⟩]
def vcS172CutCaps : Fin 3 → Fin 3 → ℚ := ![![934182247/12500000, 4575792853/100000000, 3065013163/100000000], ![2754456891/100000000, 653830459/25000000, 806219997/50000000], ![522691233/50000000, 432901123/50000000, 138927621/20000000]]
def vcS172CutWeightFloor : ℚ := 116001921/100000000
def vcS172CutMargins : Fin 3 → ℚ := ![28143447/10000000000, 10404613/5000000000, 14562511/10000000000]

theorem vcS172Cut_roots_ok : vcS172CutCell.rootsOK vcS172CutRoots = true := by decide +kernel

theorem vcS172Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS172CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS172Cut_margin_le (i : Fin 3) : curvatureLoss vcS172CutCell vcS172CutCaps i ≤ vcS172CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS173CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨31/80, 2/5⟩, ⟨1/40, 1/20⟩⟩
def vcS173CutRoots : Fin 3 → RatBounds := ![⟨458569521852049/281474976710656, 489006846750043/281474976710656⟩, ⟨375052088514601/281474976710656, 402390147197531/281474976710656⟩, ⟨80291405042961/70368744177664, 350820020584857/281474976710656⟩]
def vcS173CutCaps : Fin 3 → Fin 3 → ℚ := ![![7824145093/100000000, 4817047949/100000000, 1617243459/50000000], ![2885143187/100000000, 54625439/2000000, 84335197/5000000], ![467848487/50000000, 96517741/12500000, 309883957/50000000]]
def vcS173CutWeightFloor : ℚ := 120893459/100000000
def vcS173CutMargins : Fin 3 → ℚ := ![3528339/1250000000, 5193793/2500000000, 7226819/5000000000]

theorem vcS173Cut_roots_ok : vcS173CutCell.rootsOK vcS173CutRoots = true := by decide +kernel

theorem vcS173Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS173CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS173Cut_margin_le (i : Fin 3) : curvatureLoss vcS173CutCell vcS173CutCaps i ≤ vcS173CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS174CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨31/80, 2/5⟩, ⟨1/20, 3/40⟩⟩
def vcS174CutRoots : Fin 3 → RatBounds := ![⟨455513502807387/281474976710656, 60685830110661/35184372088832⟩, ⟨370209023295309/281474976710656, 198446083584971/140737488355328⟩, ⟨316274383112059/281474976710656, 86302398465431/70368744177664⟩]
def vcS174CutCaps : Fin 3 → Fin 3 → ℚ := ![![4087671463/50000000, 2528002799/50000000, 212688361/6250000], ![1507357321/50000000, 2846386251/100000000, 880163991/50000000], ![841823299/100000000, 692412309/100000000, 69501151/12500000]]
def vcS174CutWeightFloor : ℚ := 62899183/50000000
def vcS174CutMargins : Fin 3 → ℚ := ![14216163/5000000000, 20843831/10000000000, 7214237/5000000000]

theorem vcS174Cut_roots_ok : vcS174CutCell.rootsOK vcS174CutRoots = true := by decide +kernel

theorem vcS174Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS174CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS174Cut_margin_le (i : Fin 3) : curvatureLoss vcS174CutCell vcS174CutCaps i ≤ vcS174CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS175CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨31/80, 2/5⟩, ⟨3/40, 1/10⟩⟩
def vcS175CutRoots : Fin 3 → RatBounds := ![⟨452687157216591/281474976710656, 482247130653983/281474976710656⟩, ⟨182878575631271/140737488355328, 391857916677129/281474976710656⟩, ⟨155892842723517/140737488355328, 170040487037201/140737488355328⟩]
def vcS175CutCaps : Fin 3 → Fin 3 → ℚ := ![![1705446889/20000000, 2646460693/50000000, 3570807731/100000000], ![628653493/20000000, 740183181/25000000, 366673171/20000000], ![190233207/25000000, 124807797/20000000, 250655613/50000000]]
def vcS175CutWeightFloor : ℚ := 130714399/100000000
def vcS175CutMargins : Fin 3 → ℚ := ![28738737/10000000000, 20995723/10000000000, 14471521/10000000000]

theorem vcS175Cut_roots_ok : vcS175CutCell.rootsOK vcS175CutRoots = true := by decide +kernel

theorem vcS175Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS175CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS175Cut_margin_le (i : Fin 3) : curvatureLoss vcS175CutCell vcS175CutCaps i ≤ vcS175CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS176CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨2/5, 33/80⟩, ⟨0, 1/40⟩⟩
def vcS176CutRoots : Fin 3 → RatBounds := ![⟨460407397828413/281474976710656, 491209865574247/281474976710656⟩, ⟨46984654230795/35184372088832, 403711407425043/281474976710656⟩, ⟨329441470429503/281474976710656, 359823123520121/281474976710656⟩]
def vcS176CutCaps : Fin 3 → Fin 3 → ℚ := ![![7256334481/100000000, 175834597/4000000, 3027629489/100000000], ![661809723/25000000, 1228820139/50000000, 403726633/25000000], ![1041819969/100000000, 848545203/100000000, 352520613/50000000]]
def vcS176CutWeightFloor : ℚ := 117041121/100000000
def vcS176CutMargins : Fin 3 → ℚ := ![3435267/1250000000, 5003753/2500000000, 3643897/2500000000]

theorem vcS176Cut_roots_ok : vcS176CutCell.rootsOK vcS176CutRoots = true := by decide +kernel

theorem vcS176Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS176CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS176Cut_margin_le (i : Fin 3) : curvatureLoss vcS176CutCell vcS176CutCaps i ≤ vcS176CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS177CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨2/5, 33/80⟩, ⟨1/40, 1/20⟩⟩
def vcS177CutRoots : Fin 3 → RatBounds := ![⟨114278083471041/70368744177664, 243696435042337/140737488355328⟩, ⟨370588477786749/281474976710656, 198839722130925/140737488355328⟩, ⟨162048856301465/140737488355328, 353674503852239/281474976710656⟩]
def vcS177CutCaps : Fin 3 → Fin 3 → ℚ := ![![759696293/10000000, 2313631917/50000000, 3196724479/100000000], ![110909813/4000000, 641644281/25000000, 1688961389/100000000], ![233098419/25000000, 47291097/6250000, 4914081/781250]]
def vcS177CutWeightFloor : ℚ := 121954673/100000000
def vcS177CutMargins : Fin 3 → ℚ := ![27537663/10000000000, 9980929/5000000000, 14456437/10000000000]

theorem vcS177Cut_roots_ok : vcS177CutCell.rootsOK vcS177CutRoots = true := by decide +kernel

theorem vcS177Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS177CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS177Cut_margin_le (i : Fin 3) : curvatureLoss vcS177CutCell vcS177CutCaps i ≤ vcS177CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS178CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨2/5, 33/80⟩, ⟨1/20, 3/40⟩⟩
def vcS178CutRoots : Fin 3 → RatBounds := ![⟨454074953545845/281474976710656, 483893474688307/281474976710656⟩, ⟨182873098764183/140737488355328, 392180274772911/281474976710656⟩, ⟨159606232123327/140737488355328, 87019360420819/70368744177664⟩]
def vcS178CutCaps : Fin 3 → Fin 3 → ℚ := ![![992344129/12500000, 4856483999/100000000, 1682530921/50000000], ![90536821/3125000, 167170593/6250000, 352478611/20000000], ![838755647/100000000, 84806011/12500000, 564253767/100000000]]
def vcS178CutWeightFloor : ℚ := 126882161/100000000
def vcS178CutMargins : Fin 3 → ℚ := ![27716707/10000000000, 10004889/5000000000, 14422793/10000000000]

theorem vcS178Cut_roots_ok : vcS178CutCell.rootsOK vcS178CutRoots = true := by decide +kernel

theorem vcS178Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS178CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS178Cut_margin_le (i : Fin 3) : curvatureLoss vcS178CutCell vcS178CutCaps i ≤ vcS178CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS179CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨2/5, 33/80⟩, ⟨3/40, 1/10⟩⟩
def vcS179CutRoots : Fin 3 → RatBounds := ![⟨451265883592903/281474976710656, 240336622617741/140737488355328⟩, ⟨361295688595151/281474976710656, 387145714867957/281474976710656⟩, ⟨314728900071233/281474976710656, 342960580879155/281474976710656⟩]
def vcS179CutCaps : Fin 3 → Fin 3 → ℚ := ![![4140300619/50000000, 1016742327/20000000, 3532474443/100000000], ![604125899/20000000, 695540001/25000000, 367050539/20000000], ![758079321/100000000, 611387349/100000000, 508710909/100000000]]
def vcS179CutWeightFloor : ℚ := 32955311/25000000
def vcS179CutMargins : Fin 3 → ℚ := ![27995211/10000000000, 4027899/2000000000, 14458147/10000000000]

theorem vcS179Cut_roots_ok : vcS179CutCell.rootsOK vcS179CutRoots = true := by decide +kernel

theorem vcS179Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS179CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS179Cut_margin_le (i : Fin 3) : curvatureLoss vcS179CutCell vcS179CutCaps i ≤ vcS179CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS180CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨33/80, 17/40⟩, ⟨0, 1/40⟩⟩
def vcS180CutRoots : Fin 3 → RatBounds := ![⟨459154158243993/281474976710656, 244920060746715/140737488355328⟩, ⟨185788107506969/140737488355328, 49900271705073/35184372088832⟩, ⟨20777284267661/17592186044416, 181383792108535/140737488355328⟩]
def vcS180CutCaps : Fin 3 → Fin 3 → ℚ := ![![441874079/6250000, 2119781647/50000000, 3002020973/100000000], ![639322889/25000000, 579073439/25000000, 20303019/1250000], ![1038840959/100000000, 207981561/25000000, 715790149/100000000]]
def vcS180CutWeightFloor : ℚ := 118105187/100000000
def vcS180CutMargins : Fin 3 → ℚ := ![26919221/10000000000, 19303833/10000000000, 731389/500000000]

theorem vcS180Cut_roots_ok : vcS180CutCell.rootsOK vcS180CutRoots = true := by decide +kernel

theorem vcS180Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS180CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS180Cut_margin_le (i : Fin 3) : curvatureLoss vcS180CutCell vcS180CutCaps i ≤ vcS180CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS181CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨33/80, 17/40⟩, ⟨1/40, 1/20⟩⟩
def vcS181CutRoots : Fin 3 → RatBounds := ![⟨455876139430735/281474976710656, 243021066244151/140737488355328⟩, ⟨366286617991439/281474976710656, 393166565056781/281474976710656⟩, ⟨327099598748327/281474976710656, 356633437356781/281474976710656⟩]
def vcS181CutCaps : Fin 3 → Fin 3 → ℚ := ![![7402131133/100000000, 4462320057/100000000, 3171344763/100000000], ![2678422149/100000000, 30237057/1250000, 1698393671/100000000], ![232407711/25000000, 741756849/100000000, 319275879/50000000]]
def vcS181CutWeightFloor : ℚ := 12304141/10000000
def vcS181CutMargins : Fin 3 → ℚ := ![13475661/5000000000, 3846997/2000000000, 7249947/5000000000]

theorem vcS181Cut_roots_ok : vcS181CutCell.rootsOK vcS181CutRoots = true := by decide +kernel

theorem vcS181Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS181CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS181Cut_margin_le (i : Fin 3) : curvatureLoss vcS181CutCell vcS181CutCaps i ≤ vcS181CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS182CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨33/80, 17/40⟩, ⟨1/20, 3/40⟩⟩
def vcS182CutRoots : Fin 3 → RatBounds := ![⟨452854506053699/281474976710656, 241280145212053/140737488355328⟩, ⟨90361069559447/70368744177664, 193832470177949/140737488355328⟩, ⟨161110070888917/140737488355328, 351048999825199/281474976710656⟩]
def vcS182CutCaps : Fin 3 → Fin 3 → ℚ := ![![7735994703/100000000, 4682997379/100000000, 3340079521/100000000], ![2798514429/100000000, 2520895713/100000000, 354387197/20000000], ![836189533/100000000, 665019521/100000000, 17899571/3125000]]
def vcS182CutWeightFloor : ℚ := 31998033/25000000
def vcS182CutMargins : Fin 3 → ℚ := ![3388493/1250000000, 19265569/10000000000, 14459299/10000000000]

theorem vcS182Cut_roots_ok : vcS182CutCell.rootsOK vcS182CutRoots = true := by decide +kernel

theorem vcS182Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS182CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS182Cut_margin_le (i : Fin 3) : curvatureLoss vcS182CutCell vcS182CutCaps i ≤ vcS182CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS183CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨33/80, 17/40⟩, ⟨3/40, 1/10⟩⟩
def vcS183CutRoots : Fin 3 → RatBounds := ![⟨450060030954547/281474976710656, 479356324730733/281474976710656⟩, ⟨178497165883987/140737488355328, 191314441081087/140737488355328⟩, ⟨158870757095185/140737488355328, 345943202413985/281474976710656⟩]
def vcS183CutCaps : Fin 3 → Fin 3 → ℚ := ![![126083787/1562500, 2450864671/50000000, 3507707229/100000000], ![1458828181/50000000, 2622145241/100000000, 1844917451/100000000], ![151138421/20000000, 599228817/100000000, 51637481/10000000]]
def vcS183CutWeightFloor : ℚ := 132954917/100000000
def vcS183CutMargins : Fin 3 → ℚ := ![13681433/5000000000, 19376543/10000000000, 3622131/2500000000]

theorem vcS183Cut_roots_ok : vcS183CutCell.rootsOK vcS183CutRoots = true := by decide +kernel

theorem vcS183Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS183CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS183Cut_margin_le (i : Fin 3) : curvatureLoss vcS183CutCell vcS183CutCaps i ≤ vcS183CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS184CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨17/40, 7/16⟩, ⟨0, 1/40⟩⟩
def vcS184CutRoots : Fin 3 → RatBounds := ![⟨229059429538353/140737488355328, 122182383192055/70368744177664⟩, ⟨183713501735535/140737488355328, 394879313242103/281474976710656⟩, ⟨335506384583597/281474976710656, 365821471088575/281474976710656⟩]
def vcS184CutCaps : Fin 3 → Fin 3 → ℚ := ![![3455978383/50000000, 4104539521/100000000, 2987760013/100000000], ![2483110021/100000000, 547317787/25000000, 1640257999/100000000], ![518209451/50000000, 407949427/50000000, 726891097/100000000]]
def vcS184CutWeightFloor : ℚ := 29798953/25000000
def vcS184CutMargins : Fin 3 → ℚ := ![26446763/10000000000, 18666809/10000000000, 2943587/2000000000]

theorem vcS184Cut_roots_ok : vcS184CutCell.rootsOK vcS184CutRoots = true := by decide +kernel

theorem vcS184Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS184CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS184Cut_margin_le (i : Fin 3) : curvatureLoss vcS184CutCell vcS184CutCaps i ≤ vcS184CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS185CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨17/40, 7/16⟩, ⟨1/40, 1/20⟩⟩
def vcS185CutRoots : Fin 3 → RatBounds := ![⟨454854824017675/281474976710656, 242473553578779/140737488355328⟩, ⟨90533937776275/70368744177664, 388838799185461/281474976710656⟩, ⟨330176006154923/281474976710656, 359700995709349/281474976710656⟩]
def vcS185CutCaps : Fin 3 → Fin 3 → ℚ := ![![7237075279/100000000, 5399681/125000, 3157911163/100000000], ![2600592337/100000000, 1143164887/50000000, 428700873/25000000], ![231846043/25000000, 181849301/25000000, 324210991/50000000]]
def vcS185CutWeightFloor : ℚ := 124155419/100000000
def vcS185CutMargins : Fin 3 → ℚ := ![3307423/1250000000, 18585281/10000000000, 7291409/5000000000]

theorem vcS185Cut_roots_ok : vcS185CutCell.rootsOK vcS185CutRoots = true := by decide +kernel

theorem vcS185Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS185CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS185Cut_margin_le (i : Fin 3) : curvatureLoss vcS185CutCell vcS185CutCaps i ≤ vcS185CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS186CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨17/40, 7/16⟩, ⟨1/20, 3/40⟩⟩
def vcS186CutRoots : Fin 3 → RatBounds := ![⟨451846108873399/281474976710656, 60184954949069/35184372088832⟩, ⟨357292578941553/281474976710656, 383333536975799/281474976710656⟩, ⟨162651052458023/140737488355328, 354128430252035/281474976710656⟩]
def vcS186CutCaps : Fin 3 → Fin 3 → ℚ := ![![945548657/12500000, 2266476701/50000000, 3327623557/100000000], ![1358533009/50000000, 2382687851/100000000, 1788749289/100000000], ![834102613/100000000, 8151093/1250000, 290806149/50000000]]
def vcS186CutWeightFloor : ℚ := 25826017/20000000
def vcS186CutMargins : Fin 3 → ℚ := ![13298697/5000000000, 3720309/2000000000, 7268381/5000000000]

theorem vcS186Cut_roots_ok : vcS186CutCell.rootsOK vcS186CutRoots = true := by decide +kernel

theorem vcS186Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS186CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS186Cut_margin_le (i : Fin 3) : curvatureLoss vcS186CutCell vcS186CutCaps i ≤ vcS186CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS187CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨17/40, 7/16⟩, ⟨3/40, 1/10⟩⟩
def vcS187CutRoots : Fin 3 → RatBounds := ![⟨449063606406929/281474976710656, 478288993217539/281474976710656⟩, ⟨176421230563051/140737488355328, 47286858685791/35184372088832⟩, ⟨160414090683311/140737488355328, 349032988400061/281474976710656⟩]
def vcS187CutCaps : Fin 3 → Fin 3 → ℚ := ![![7890719229/100000000, 593032643/12500000, 109251687/3125000], ![2832615809/100000000, 1239199723/50000000, 372428517/20000000], ![753750579/100000000, 7344091/1250000, 524308193/100000000]]
def vcS187CutWeightFloor : ℚ := 67058639/50000000
def vcS187CutMargins : Fin 3 → ℚ := ![26832691/10000000000, 1168551/625000000, 7280693/5000000000]

theorem vcS187Cut_roots_ok : vcS187CutCell.rootsOK vcS187CutRoots = true := by decide +kernel

theorem vcS187Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS187CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS187Cut_margin_le (i : Fin 3) : curvatureLoss vcS187CutCell vcS187CutCaps i ≤ vcS187CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS188CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨7/16, 9/20⟩, ⟨0, 1/40⟩⟩
def vcS188CutRoots : Fin 3 → RatBounds := ![⟨228648237342205/140737488355328, 487872028328767/281474976710656⟩, ⟨363419677159077/281474976710656, 24420704427923/17592186044416⟩, ⟨20669919813/17179869184, 368989470945647/281474976710656⟩]
def vcS188CutCaps : Fin 3 → Fin 3 → ℚ := ![![3390155311/50000000, 3988872541/100000000, 298461983/10000000], ![1211752803/50000000, 518720813/25000000, 1662889213/100000000], ![258633179/25000000, 8004219/1000000, 738352621/100000000]]
def vcS188CutWeightFloor : ℚ := 7519673/6250000
def vcS188CutMargins : Fin 3 → ℚ := ![26058491/10000000000, 1809657/1000000000, 7422773/5000000000]

theorem vcS188Cut_roots_ok : vcS188CutCell.rootsOK vcS188CutRoots = true := by decide +kernel

theorem vcS188Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS188CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS188Cut_margin_le (i : Fin 3) : curvatureLoss vcS188CutCell vcS188CutCaps i ≤ vcS188CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS189CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨7/16, 9/20⟩, ⟨1/40, 1/20⟩⟩
def vcS189CutRoots : Fin 3 → RatBounds := ![⟨227021708595623/140737488355328, 242050895445029/140737488355328⟩, ⟨89531506390525/70368744177664, 192342335351665/140737488355328⟩, ⟨166665940003987/140737488355328, 181440923658023/140737488355328⟩]
def vcS189CutCaps : Fin 3 → Fin 3 → ℚ := ![![7100202027/100000000, 16396607/390625, 1578170047/50000000], ![2538006517/100000000, 2166905323/100000000, 1738119003/100000000], ![18512687/2000000, 356770459/50000000, 32931053/5000000]]
def vcS189CutWeightFloor : ℚ := 125298529/100000000
def vcS189CutMargins : Fin 3 → ℚ := ![5211229/2000000000, 18005079/10000000000, 1838121/1250000000]

theorem vcS189Cut_roots_ok : vcS189CutCell.rootsOK vcS189CutRoots = true := by decide +kernel

theorem vcS189Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS189CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS189Cut_margin_le (i : Fin 3) : curvatureLoss vcS189CutCell vcS189CutCaps i ≤ vcS189CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS190CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨7/16, 9/20⟩, ⟨1/20, 3/40⟩⟩
def vcS190CutRoots : Fin 3 → RatBounds := ![⟨112761210670159/70368744177664, 240322790847269/140737488355328⟩, ⟨176640656885891/140737488355328, 189587331348299/140737488355328⟩, ⟨41057907517401/35184372088832, 178660191878175/140737488355328⟩]
def vcS190CutCaps : Fin 3 → Fin 3 → ℚ := ![![7421824893/100000000, 220211523/5000000, 3327471057/100000000], ![106060941/4000000, 2258260851/100000000, 1812756137/100000000], ![166495429/20000000, 639617187/100000000, 147684841/25000000]]
def vcS190CutWeightFloor : ℚ := 130297903/100000000
def vcS190CutMargins : Fin 3 → ℚ := ![26178237/10000000000, 2251211/1250000000, 7327329/5000000000]

theorem vcS190Cut_roots_ok : vcS190CutCell.rootsOK vcS190CutRoots = true := by decide +kernel

theorem vcS190Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS190CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS190Cut_margin_le (i : Fin 3) : curvatureLoss vcS190CutCell vcS190CutCaps i ≤ vcS190CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS191CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨7/16, 9/20⟩, ⟨3/40, 1/10⟩⟩
def vcS191CutRoots : Fin 3 → RatBounds := ![⟨224135869070383/140737488355328, 477465368321563/281474976710656⟩, ⟨87207588042177/70368744177664, 374132344004645/281474976710656⟩, ⟨161996886027783/140737488355328, 176117286400361/140737488355328⟩]
def vcS191CutCaps : Fin 3 → Fin 3 → ℚ := ![![7742467161/100000000, 4609085913/100000000, 3497292719/100000000], ![2764138669/100000000, 93960021/4000000, 471711597/25000000], ![150447677/20000000, 115250157/20000000, 66564763/12500000]]
def vcS191CutWeightFloor : ℚ := 135310263/100000000
def vcS191CutMargins : Fin 3 → ℚ := ![26397577/10000000000, 4522993/2500000000, 2935239/2000000000]

theorem vcS191Cut_roots_ok : vcS191CutCell.rootsOK vcS191CutRoots = true := by decide +kernel

theorem vcS191Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS191CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS191Cut_margin_le (i : Fin 3) : curvatureLoss vcS191CutCell vcS191CutCaps i ≤ vcS191CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS192CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨9/20, 37/80⟩, ⟨0, 1/40⟩⟩
def vcS192CutRoots : Fin 3 → RatBounds := ![⟨456683065113775/281474976710656, 60907872644903/35184372088832⟩, ⟨89886280174659/70368744177664, 193373798423775/140737488355328⟩, ⟨170945268388923/140737488355328, 93069199730141/70368744177664⟩]
def vcS192CutCaps : Fin 3 → Fin 3 → ℚ := ![![6673563067/100000000, 121593937/3125000, 2992564297/100000000], ![2377587383/100000000, 1971777057/100000000, 1692236769/100000000], ![1033166303/100000000, 9818237/1250000, 750185621/100000000]]
def vcS192CutWeightFloor : ℚ := 60731959/50000000
def vcS192CutMargins : Fin 3 → ℚ := ![643741/250000000, 17587147/10000000000, 3752707/2500000000]

theorem vcS192Cut_roots_ok : vcS192CutCell.rootsOK vcS192CutRoots = true := by decide +kernel

theorem vcS192Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS192CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS192Cut_margin_le (i : Fin 3) : curvatureLoss vcS192CutCell vcS192CutCaps i ≤ vcS192CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS193CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨9/20, 37/80⟩, ⟨1/40, 1/20⟩⟩
def vcS193CutRoots : Fin 3 → RatBounds := ![⟨226719011053689/140737488355328, 120875402168283/70368744177664⟩, ⟨88562097756165/70368744177664, 380693800305995/281474976710656⟩, ⟨336572421424091/281474976710656, 366181183485397/281474976710656⟩]
def vcS193CutCaps : Fin 3 → Fin 3 → ℚ := ![![3494745849/50000000, 51175269/1250000, 3166462429/100000000], ![2489730409/100000000, 2059276371/100000000, 1768445023/100000000], ![462183321/50000000, 350077299/50000000, 669159157/100000000]]
def vcS193CutWeightFloor : ℚ := 63236329/50000000
def vcS193CutMargins : Fin 3 → ℚ := ![25735721/10000000000, 8744059/5000000000, 7433149/5000000000]

theorem vcS193Cut_roots_ok : vcS193CutCell.rootsOK vcS193CutRoots = true := by decide +kernel

theorem vcS193Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS193CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS193Cut_margin_le (i : Fin 3) : curvatureLoss vcS193CutCell vcS193CutCaps i ≤ vcS193CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS194CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨9/20, 37/80⟩, ⟨1/20, 3/40⟩⟩
def vcS194CutRoots : Fin 3 → RatBounds := ![⟨450446850567645/281474976710656, 480053589770623/281474976710656⟩, ⟨21837593312761/17592186044416, 375178003766731/281474976710656⟩, ⟨331708769098883/281474976710656, 180315014521035/140737488355328⟩]
def vcS194CutCaps : Fin 3 → Fin 3 → ℚ := ![![913336323/12500000, 2147554251/50000000, 667921801/20000000], ![2600909679/100000000, 536534627/25000000, 922032311/50000000], ![831299591/100000000, 125515611/20000000, 12003539/2000000]]
def vcS194CutWeightFloor : ℚ := 3287439/2500000
def vcS194CutMargins : Fin 3 → ℚ := ![2584531/1000000000, 3496703/2000000000, 2962649/2000000000]

theorem vcS194Cut_roots_ok : vcS194CutCell.rootsOK vcS194CutRoots = true := by decide +kernel

theorem vcS194Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS194CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS194Cut_margin_le (i : Fin 3) : curvatureLoss vcS194CutCell vcS194CutCaps i ≤ vcS194CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS195CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨9/20, 37/80⟩, ⟨3/40, 1/10⟩⟩
def vcS195CutRoots : Fin 3 → RatBounds := ![⟨447680606359319/281474976710656, 119220241908509/70368744177664⟩, ⟨172474535892899/140737488355328, 370131053216257/281474976710656⟩, ⟨327243411154547/281474976710656, 22222068929881/17592186044416⟩]
def vcS195CutCaps : Fin 3 → Fin 3 → ℚ := ![![119108223/1562500, 2247201179/50000000, 1755710449/50000000], ![2711205001/100000000, 2232411307/100000000, 959570141/50000000], ![751143047/100000000, 141342753/25000000, 108202679/20000000]]
def vcS195CutWeightFloor : ℚ := 136535903/100000000
def vcS195CutMargins : Fin 3 → ℚ := ![6513039/2500000000, 17555269/10000000000, 927077/625000000]

theorem vcS195Cut_roots_ok : vcS195CutCell.rootsOK vcS195CutRoots = true := by decide +kernel

theorem vcS195Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS195CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS195Cut_margin_le (i : Fin 3) : curvatureLoss vcS195CutCell vcS195CutCaps i ≤ vcS195CutMargins i := by
  fin_cases i <;> decide +kernel


end HlawkaSchatten.BelowExponent.Vertex
