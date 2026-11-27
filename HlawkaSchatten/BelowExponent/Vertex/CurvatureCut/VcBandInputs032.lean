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

def vcS132CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨21/80, 11/40⟩, ⟨0, 1/40⟩⟩
def vcS132CutRoots : Fin 3 → RatBounds := ![⟨491430474304559/281474976710656, 527026696710391/281474976710656⟩, ⟨218639180337315/140737488355328, 29412785544709/17592186044416⟩, ⟨37518138389885/35184372088832, 333793591234299/281474976710656⟩]
def vcS132CutCaps : Fin 3 → Fin 3 → ℚ := ![![3145880871/25000000, 4382231041/50000000, 2252862799/50000000], ![5498703963/100000000, 2964333709/50000000, 105340711/5000000], ![562367529/50000000, 34058039/3125000, 305069931/50000000]]
def vcS132CutWeightFloor : ℚ := 53316481/50000000
def vcS132CutMargins : Fin 3 → ℚ := ![11025961/2500000000, 37212029/10000000000, 3536367/2000000000]

theorem vcS132Cut_roots_ok : vcS132CutCell.rootsOK vcS132CutRoots = true := by decide +kernel

theorem vcS132Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS132CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS132Cut_margin_le (i : Fin 3) : curvatureLoss vcS132CutCell vcS132CutCaps i ≤ vcS132CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS133CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨21/80, 11/40⟩, ⟨1/40, 1/20⟩⟩
def vcS133CutRoots : Fin 3 → RatBounds := ![⟨487714517115857/281474976710656, 522733169039551/281474976710656⟩, ⟨215958117513131/140737488355328, 29030818988549/17592186044416⟩, ⟨147361685808575/140737488355328, 327432226178117/281474976710656⟩]
def vcS133CutCaps : Fin 3 → Fin 3 → ℚ := ![![13181179711/100000000, 4613957749/50000000, 188892429/4000000], ![180004057/3125000, 1548566857/25000000, 1103080641/50000000], ![504558463/50000000, 974092077/100000000, 272580121/50000000]]
def vcS133CutWeightFloor : ℚ := 55663409/50000000
def vcS133CutMargins : Fin 3 → ℚ := ![5609809/1250000000, 18865773/5000000000, 17791237/10000000000]

theorem vcS133Cut_roots_ok : vcS133CutCell.rootsOK vcS133CutRoots = true := by decide +kernel

theorem vcS133Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS133CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS133Cut_margin_le (i : Fin 3) : curvatureLoss vcS133CutCell vcS133CutCaps i ≤ vcS133CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS134CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨21/80, 11/40⟩, ⟨1/20, 3/40⟩⟩
def vcS134CutRoots : Fin 3 → RatBounds := ![⟨242144093304559/140737488355328, 129698435760677/70368744177664⟩, ⟨53374587021267/35184372088832, 57363630392339/35184372088832⟩, ⟨72442621933805/70368744177664, 628215290005/549755813888⟩]
def vcS134CutCaps : Fin 3 → Fin 3 → ℚ := ![![13775759641/100000000, 9686705763/100000000, 4937303989/100000000], ![3009691253/50000000, 6457865303/100000000, 576111133/25000000], ![909886321/100000000, 437648791/50000000, 489738959/100000000]]
def vcS134CutWeightFloor : ℚ := 58014223/50000000
def vcS134CutMargins : Fin 3 → ℚ := ![22885437/5000000000, 9592657/2500000000, 8985063/5000000000]

theorem vcS134Cut_roots_ok : vcS134CutCell.rootsOK vcS134CutRoots = true := by decide +kernel

theorem vcS134Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS134CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS134Cut_margin_le (i : Fin 3) : curvatureLoss vcS134CutCell vcS134CutCaps i ≤ vcS134CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS135CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨21/80, 11/40⟩, ⟨3/40, 1/10⟩⟩
def vcS135CutRoots : Fin 3 → RatBounds := ![⟨240559262174393/140737488355328, 515165863909119/281474976710656⟩, ⟨422466445795225/281474976710656, 113446520678215/70368744177664⟩, ⟨285228052674231/281474976710656, 316360763017051/281474976710656⟩]
def vcS135CutCaps : Fin 3 → Fin 3 → ℚ := ![![14367547287/100000000, 5070680797/50000000, 5150896939/100000000], ![1255334633/20000000, 6719656211/100000000, 480354903/20000000], ![412077281/50000000, 395187611/50000000, 442123889/100000000]]
def vcS135CutWeightFloor : ℚ := 6036827/5000000
def vcS135CutMargins : Fin 3 → ℚ := ![46759451/10000000000, 19553241/5000000000, 3641081/2000000000]

theorem vcS135Cut_roots_ok : vcS135CutCell.rootsOK vcS135CutRoots = true := by decide +kernel

theorem vcS135Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS135CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS135Cut_margin_le (i : Fin 3) : curvatureLoss vcS135CutCell vcS135CutCaps i ≤ vcS135CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS136CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨11/40, 23/80⟩, ⟨0, 1/40⟩⟩
def vcS136CutRoots : Fin 3 → RatBounds := ![⟨487018214453611/281474976710656, 521823169909503/281474976710656⟩, ⟨107567675611315/70368744177664, 462758875372985/281474976710656⟩, ⟨302612336758795/281474976710656, 335706971966093/281474976710656⟩]
def vcS136CutCaps : Fin 3 → Fin 3 → ℚ := ![![5845038729/50000000, 62644101/781250, 2117381367/50000000], ![249908289/5000000, 5353310899/100000000, 79713437/4000000], ![222387209/20000000, 1061587489/100000000, 308411141/50000000]]
def vcS136CutWeightFloor : ℚ := 53754749/50000000
def vcS136CutMargins : Fin 3 → ℚ := ![20640613/5000000000, 34410363/10000000000, 16982203/10000000000]

theorem vcS136Cut_roots_ok : vcS136CutCell.rootsOK vcS136CutRoots = true := by decide +kernel

theorem vcS136Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS136CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS136Cut_margin_le (i : Fin 3) : curvatureLoss vcS136CutCell vcS136CutCaps i ≤ vcS136CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS137CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨11/40, 23/80⟩, ⟨1/40, 1/20⟩⟩
def vcS137CutRoots : Fin 3 → RatBounds := ![⟨483361333596989/281474976710656, 517597337649161/281474976710656⟩, ⟨53115507589065/35184372088832, 114166781689175/70368744177664⟩, ⟨297196996971907/281474976710656, 329369439944477/281474976710656⟩]
def vcS137CutCaps : Fin 3 → Fin 3 → ℚ := ![![12243040433/100000000, 1688539697/20000000, 2220250863/50000000], ![26178333/500000, 87386097/1562500, 2086850657/100000000], ![24932299/2500000, 948530697/100000000, 551019403/100000000]]
def vcS137CutWeightFloor : ℚ := 14027799/12500000
def vcS137CutMargins : Fin 3 → ℚ := ![10482361/2500000000, 4352913/1250000000, 682143/400000000]

theorem vcS137Cut_roots_ok : vcS137CutCell.rootsOK vcS137CutRoots = true := by decide +kernel

theorem vcS137Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS137CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS137Cut_margin_le (i : Fin 3) : curvatureLoss vcS137CutCell vcS137CutCaps i ≤ vcS137CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS138CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨11/40, 23/80⟩, ⟨1/20, 3/40⟩⟩
def vcS138CutRoots : Fin 3 → RatBounds := ![⟨239994803135227/140737488355328, 513720418927931/281474976710656⟩, ⟨420019827471819/281474976710656, 451102442815881/281474976710656⟩, ⟨73062426286771/70368744177664, 161802398377425/140737488355328⟩]
def vcS138CutCaps : Fin 3 → Fin 3 → ℚ := ![![12793316231/100000000, 2215674103/25000000, 1161187093/25000000], ![1094238507/20000000, 5830313831/100000000, 1089937437/50000000], ![449468653/50000000, 85208191/10000000, 247453979/50000000]]
def vcS138CutWeightFloor : ℚ := 116943593/100000000
def vcS138CutMargins : Fin 3 → ℚ := ![42695817/10000000000, 552409/156250000, 17195811/10000000000]

theorem vcS138Cut_roots_ok : vcS138CutCell.rootsOK vcS138CutRoots = true := by decide +kernel

theorem vcS138Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS138CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS138Cut_margin_le (i : Fin 3) : curvatureLoss vcS138CutCell vcS138CutCaps i ≤ vcS138CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS139CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨11/40, 23/80⟩, ⟨3/40, 1/10⟩⟩
def vcS139CutRoots : Fin 3 → RatBounds := ![⟨7451102738437/4398046511104, 63768805674785/35184372088832⟩, ⟨415504620274333/281474976710656, 445998426048351/281474976710656⟩, ⟨35964022266313/35184372088832, 19896159736077/17592186044416⟩]
def vcS139CutCaps : Fin 3 → Fin 3 → ℚ := ![![13341152141/100000000, 1855784899/20000000, 4847682131/100000000], ![5704932819/100000000, 379143383/6250000, 454401941/20000000], ![813994531/100000000, 153840713/20000000, 446709757/100000000]]
def vcS139CutWeightFloor : ℚ := 15208963/12500000
def vcS139CutMargins : Fin 3 → ℚ := ![43558717/10000000000, 35980533/10000000000, 17395569/10000000000]

theorem vcS139Cut_roots_ok : vcS139CutCell.rootsOK vcS139CutRoots = true := by decide +kernel

theorem vcS139Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS139CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS139Cut_margin_le (i : Fin 3) : curvatureLoss vcS139CutCell vcS139CutCaps i ≤ vcS139CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS140CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨23/80, 3/10⟩, ⟨0, 1/40⟩⟩
def vcS140CutRoots : Fin 3 → RatBounds := ![⟨482989507883577/281474976710656, 129274066602307/70368744177664⟩, ⟨211812429706397/140737488355328, 455365732286913/281474976710656⟩, ⟨305105111466999/281474976710656, 337710160333981/281474976710656⟩]
def vcS140CutCaps : Fin 3 → Fin 3 → ℚ := ![![10920704447/100000000, 3690846183/50000000, 4003140399/100000000], ![2286414223/50000000, 4859927109/100000000, 118716009/6250000], ![275136679/25000000, 258755853/25000000, 623951949/100000000]]
def vcS140CutWeightFloor : ℚ := 10839511/10000000
def vcS140CutMargins : Fin 3 → ℚ := ![9714707/2500000000, 15997767/5000000000, 8201567/5000000000]

theorem vcS140Cut_roots_ok : vcS140CutCell.rootsOK vcS140CutRoots = true := by decide +kernel

theorem vcS140Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS140CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS140Cut_margin_le (i : Fin 3) : curvatureLoss vcS140CutCell vcS140CutCaps i ≤ vcS140CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS141CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨23/80, 3/10⟩, ⟨1/40, 1/20⟩⟩
def vcS141CutRoots : Fin 3 → RatBounds := ![⟨479386830386611/281474976710656, 128233076413905/70368744177664⟩, ⟨209145694267841/140737488355328, 449290435734689/281474976710656⟩, ⟨149848243637099/140737488355328, 82848855936307/70368744177664⟩]
def vcS141CutCaps : Fin 3 → Fin 3 → ℚ := ![![11435410883/100000000, 971553553/12500000, 2099858459/50000000], ![2395027807/50000000, 5077006461/100000000, 15539573/781250], ![246691133/25000000, 57783143/6250000, 557283349/100000000]]
def vcS141CutWeightFloor : ℚ := 56563483/50000000
def vcS141CutMargins : Fin 3 → ℚ := ![39399463/10000000000, 16159723/5000000000, 8220621/5000000000]

theorem vcS141Cut_roots_ok : vcS141CutCell.rootsOK vcS141CutRoots = true := by decide +kernel

theorem vcS141Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS141CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS141Cut_margin_le (i : Fin 3) : curvatureLoss vcS141CutCell vcS141CutCaps i ≤ vcS141CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS142CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨23/80, 3/10⟩, ⟨1/20, 3/40⟩⟩
def vcS142CutRoots : Fin 3 → RatBounds := ![⟨14877037488689/8796093022208, 254556258626629/140737488355328⟩, ⟨206700146071657/140737488355328, 443742085748945/281474976710656⟩, ⟨147377532729665/140737488355328, 325651174401331/281474976710656⟩]
def vcS142CutCaps : Fin 3 → Fin 3 → ℚ := ![![2986939221/25000000, 8159256409/100000000, 4394886569/100000000], ![5005478409/100000000, 264624003/5000000, 519438193/25000000], ![889185951/100000000, 103787449/12500000, 250222529/50000000]]
def vcS142CutWeightFloor : ℚ := 117867673/100000000
def vcS142CutMargins : Fin 3 → ℚ := ![40058553/10000000000, 32759639/10000000000, 16551601/10000000000]

theorem vcS142Cut_roots_ok : vcS142CutCell.rootsOK vcS142CutRoots = true := by decide +kernel

theorem vcS142Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS142CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS142Cut_margin_le (i : Fin 3) : curvatureLoss vcS142CutCell vcS142CutCaps i ≤ vcS142CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS143CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨23/80, 3/10⟩, ⟨3/40, 1/10⟩⟩
def vcS143CutRoots : Fin 3 → RatBounds := ![⟨236496309401515/140737488355328, 252797734301663/140737488355328⟩, ⟨204449045568337/140737488355328, 438654169996131/281474976710656⟩, ⟨36277836120465/35184372088832, 320403265727855/281474976710656⟩]
def vcS143CutCaps : Fin 3 → Fin 3 → ℚ := ![![12457945919/100000000, 8542617803/100000000, 2294409203/50000000], ![2609633927/50000000, 5506498847/100000000, 433122109/20000000], ![402471463/50000000, 29974089/4000000, 451631811/100000000]]
def vcS143CutWeightFloor : ℚ := 1915871/1562500
def vcS143CutMargins : Fin 3 → ℚ := ![1632577/400000000, 8323499/2500000000, 8360309/5000000000]

theorem vcS143Cut_roots_ok : vcS143CutCell.rootsOK vcS143CutRoots = true := by decide +kernel

theorem vcS143Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS143CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS143Cut_margin_le (i : Fin 3) : curvatureLoss vcS143CutCell vcS143CutCaps i ≤ vcS143CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS144CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨3/10, 5/16⟩, ⟨0, 1/40⟩⟩
def vcS144CutRoots : Fin 3 → RatBounds := ![⟨479316490583761/281474976710656, 64101023979817/35184372088832⟩, ⟨52163637452601/35184372088832, 448383150906165/281474976710656⟩, ⟨38453540977689/35184372088832, 339802223632721/281474976710656⟩]
def vcS144CutCaps : Fin 3 → Fin 3 → ℚ := ![![5127348537/50000000, 3417492961/50000000, 3804443779/100000000], ![526217501/12500000, 277262879/6250000, 1824253201/100000000], ![1090404823/100000000, 1009972009/100000000, 315749709/50000000]]
def vcS144CutWeightFloor : ℚ := 6830721/6250000
def vcS144CutMargins : Fin 3 → ℚ := ![18384821/5000000000, 14952227/5000000000, 7963569/5000000000]

theorem vcS144Cut_roots_ok : vcS144CutCell.rootsOK vcS144CutRoots = true := by decide +kernel

theorem vcS144Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS144CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS144Cut_margin_le (i : Fin 3) : curvatureLoss vcS144CutCell vcS144CutCaps i ≤ vcS144CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS145CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨3/10, 5/16⟩, ⟨1/40, 1/20⟩⟩
def vcS145CutRoots : Fin 3 → RatBounds := ![⟨29735215384503/17592186044416, 508700688680613/281474976710656⟩, ⟨411986715636703/281474976710656, 442321369192987/281474976710656⟩, ⟨75556666783743/70368744177664, 166754656917063/140737488355328⟩]
def vcS145CutCaps : Fin 3 → Fin 3 → ℚ := ![![10736481889/100000000, 1799220393/25000000, 3993281219/100000000], ![4409715031/100000000, 463404191/10000000, 1910230673/100000000], ![488692989/50000000, 901914159/100000000, 563925573/100000000]]
def vcS145CutWeightFloor : ℚ := 7127649/6250000
def vcS145CutMargins : Fin 3 → ℚ := ![9304561/2500000000, 30153477/10000000000, 7967983/5000000000]

theorem vcS145Cut_roots_ok : vcS145CutCell.rootsOK vcS145CutRoots = true := by decide +kernel

theorem vcS145Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS145CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS145Cut_margin_le (i : Fin 3) : curvatureLoss vcS145CutCell vcS145CutCaps i ≤ vcS145CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS146CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨3/10, 5/16⟩, ⟨1/20, 3/40⟩⟩
def vcS146CutRoots : Fin 3 → RatBounds := ![⟨236243842819713/140737488355328, 504933032047519/281474976710656⟩, ⟨407106800573915/281474976710656, 218393306764797/140737488355328⟩, ⟨297291327230969/281474976710656, 81946139981465/70368744177664⟩]
def vcS146CutCaps : Fin 3 → Fin 3 → ℚ := ![![1121617681/10000000, 1888791147/25000000, 167231383/4000000], ![921604849/20000000, 2415219143/50000000, 1995348877/100000000], ![220123891/25000000, 404894153/50000000, 506326261/100000000]]
def vcS146CutWeightFloor : ℚ := 118802637/100000000
def vcS146CutMargins : Fin 3 → ℚ := ![7557103/2000000000, 15258551/5000000000, 3203687/2000000000]

theorem vcS146Cut_roots_ok : vcS146CutCell.rootsOK vcS146CutRoots = true := by decide +kernel

theorem vcS146Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS146CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS146Cut_margin_le (i : Fin 3) : curvatureLoss vcS146CutCell vcS146CutCaps i ≤ vcS146CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS147CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨3/10, 5/16⟩, ⟨3/40, 1/10⟩⟩
def vcS147CutRoots : Fin 3 → RatBounds := ![⟨469457634220069/281474976710656, 501464277989847/281474976710656⟩, ⟨402615767757235/281474976710656, 53964029746785/35184372088832⟩, ⟨292764282896405/281474976710656, 322554147840589/281474976710656⟩]
def vcS147CutCaps : Fin 3 → Fin 3 → ℚ := ![![5846978581/50000000, 7910243519/100000000, 4367114267/100000000], ![2402411773/50000000, 2512756343/50000000, 2079682951/100000000], ![796874109/100000000, 365336061/50000000, 456868481/100000000]]
def vcS147CutWeightFloor : ℚ := 15446339/12500000
def vcS147CutMargins : Fin 3 → ℚ := ![38449761/10000000000, 1238941/400000000, 8080343/5000000000]

theorem vcS147Cut_roots_ok : vcS147CutCell.rootsOK vcS147CutRoots = true := by decide +kernel

theorem vcS147Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS147CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS147Cut_margin_le (i : Fin 3) : curvatureLoss vcS147CutCell vcS147CutCaps i ≤ vcS147CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS148CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨5/16, 13/40⟩, ⟨0, 1/40⟩⟩
def vcS148CutRoots : Fin 3 → RatBounds := ![⟨237987493630373/140737488355328, 508926473482281/281474976710656⟩, ⟨411295442626077/281474976710656, 441774530438257/281474976710656⟩, ⟨155093309378173/140737488355328, 170991453926763/140737488355328⟩]
def vcS148CutCaps : Fin 3 → Fin 3 → ℚ := ![![2418918639/25000000, 6363221321/100000000, 908410133/25000000], ![389826179/10000000, 4067574253/100000000, 55108569/3125000], ![540688121/50000000, 24656763/2500000, 127888347/20000000]]
def vcS148CutWeightFloor : ℚ := 13775053/12500000
def vcS148CutMargins : Fin 3 → ℚ := ![34959847/10000000000, 28077887/10000000000, 15536879/10000000000]

theorem vcS148Cut_roots_ok : vcS148CutCell.rootsOK vcS148CutRoots = true := by decide +kernel

theorem vcS148Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS148CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS148Cut_margin_le (i : Fin 3) : curvatureLoss vcS148CutCell vcS148CutCaps i ≤ vcS148CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS149CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨5/16, 13/40⟩, ⟨1/40, 1/20⟩⟩
def vcS149CutRoots : Fin 3 → RatBounds := ![⟨59058408609495/35184372088832, 504870367231149/281474976710656⟩, ⟨202991131383523/140737488355328, 435723609296323/281474976710656⟩, ⟨152396052537243/140737488355328, 335710911504151/281474976710656⟩]
def vcS149CutCaps : Fin 3 → Fin 3 → ℚ := ![![10129006509/100000000, 1675041193/25000000, 3815957547/100000000], ![2041721927/50000000, 2124277293/50000000, 1846321619/100000000], ![484517103/50000000, 880534227/100000000, 114185187/20000000]]
def vcS149CutWeightFloor : ℚ := 114970389/100000000
def vcS149CutMargins : Fin 3 → ℚ := ![4416159/1250000000, 883231/312500000, 7759749/5000000000]

theorem vcS149Cut_roots_ok : vcS149CutCell.rootsOK vcS149CutRoots = true := by decide +kernel

theorem vcS149Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS149CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS149Cut_margin_le (i : Fin 3) : curvatureLoss vcS149CutCell vcS149CutCaps i ≤ vcS149CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS150CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨5/16, 13/40⟩, ⟨1/20, 3/40⟩⟩
def vcS150CutRoots : Fin 3 → RatBounds := ![⟨469233396055743/281474976710656, 125287542464977/70368744177664⟩, ⟨401111760825701/281474976710656, 215099985362017/140737488355328⟩, ⟨299862999810323/281474976710656, 20625300276817/17592186044416⟩]
def vcS150CutCaps : Fin 3 → Fin 3 → ℚ := ![![52902397/500000, 879218923/12500000, 3997003187/100000000], ![4267078179/100000000, 55354371/1250000, 482107809/25000000], ![872754549/100000000, 39520639/5000000, 512533779/100000000]]
def vcS150CutWeightFloor : ℚ := 119750317/100000000
def vcS150CutMargins : Fin 3 → ℚ := ![35817531/10000000000, 892563/312500000, 3115457/2000000000]

theorem vcS150Cut_roots_ok : vcS150CutCell.rootsOK vcS150CutRoots = true := by decide +kernel

theorem vcS150Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS150CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS150Cut_margin_le (i : Fin 3) : curvatureLoss vcS150CutCell vcS150CutCaps i ≤ vcS150CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS151CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨5/16, 13/40⟩, ⟨3/40, 1/10⟩⟩
def vcS151CutRoots : Fin 3 → RatBounds := ![⟨466242179758991/281474976710656, 497725382077529/281474976710656⟩, ⟨396630233009077/281474976710656, 106284204639169/70368744177664⟩, ⟨295341414732969/281474976710656, 324791098300531/281474976710656⟩]
def vcS151CutCaps : Fin 3 → Fin 3 → ℚ := ![![11030243739/100000000, 184109017/2500000, 2088465209/50000000], ![4449307943/100000000, 2303484899/50000000, 502454329/25000000], ![789684329/100000000, 713037669/100000000, 231201589/50000000]]
def vcS151CutWeightFloor : ℚ := 124538533/100000000
def vcS151CutMargins : Fin 3 → ℚ := ![36402909/10000000000, 1809507/625000000, 15696017/10000000000]

theorem vcS151Cut_roots_ok : vcS151CutCell.rootsOK vcS151CutRoots = true := by decide +kernel

theorem vcS151Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS151CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS151Cut_margin_le (i : Fin 3) : curvatureLoss vcS151CutCell vcS151CutCaps i ≤ vcS151CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS152CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨13/40, 27/80⟩, ⟨0, 1/40⟩⟩
def vcS152CutRoots : Fin 3 → RatBounds := ![⟨29558999250905/17592186044416, 252711573963055/140737488355328⟩, ⟨202779549889223/140737488355328, 217753901370035/140737488355328⟩, ⟨312784430786701/281474976710656, 344252561648051/281474976710656⟩]
def vcS152CutCaps : Fin 3 → Fin 3 → ℚ := ![![9170561447/100000000, 595441033/10000000, 3486753373/100000000], ![726052917/20000000, 58514237/1562500, 1714881121/100000000], ![214669871/20000000, 240945129/25000000, 129552261/20000000]]
def vcS152CutWeightFloor : ℚ := 13890419/12500000
def vcS152CutMargins : Fin 3 → ℚ := ![8346789/2500000000, 26473523/10000000000, 7610039/5000000000]

theorem vcS152Cut_roots_ok : vcS152CutCell.rootsOK vcS152CutRoots = true := by decide +kernel

theorem vcS152Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS152CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS152Cut_margin_le (i : Fin 3) : curvatureLoss vcS152CutCell vcS152CutCaps i ≤ vcS152CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS153CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨13/40, 27/80⟩, ⟨1/40, 1/20⟩⟩
def vcS153CutRoots : Fin 3 → RatBounds := ![⟨469477518001215/281474976710656, 501413682870821/281474976710656⟩, ⟨400253418848069/281474976710656, 107366333477705/70368744177664⟩, ⟨153698594620967/140737488355328, 5281259517649/4398046511104⟩]
def vcS153CutCaps : Fin 3 → Fin 3 → ℚ := ![![9599225211/100000000, 313483297/5000000, 5724387/156250], ![30421737/800000, 977834941/25000000, 1795246281/100000000], ![961605237/100000000, 430130937/50000000, 289133849/50000000]]
def vcS153CutWeightFloor : ℚ := 57956321/50000000
def vcS153CutMargins : Fin 3 → ℚ := ![3368821/1000000000, 26605573/10000000000, 15179541/10000000000]

theorem vcS153Cut_roots_ok : vcS153CutCell.rootsOK vcS153CutRoots = true := by decide +kernel

theorem vcS153Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS153CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS153Cut_margin_le (i : Fin 3) : curvatureLoss vcS153CutCell vcS153CutCaps i ≤ vcS153CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS154CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨13/40, 27/80⟩, ⟨1/20, 3/40⟩⟩
def vcS154CutRoots : Fin 3 → RatBounds := ![⟨29142610170239/17592186044416, 497736553791379/281474976710656⟩, ⟨395390727167177/281474976710656, 211975281703279/140737488355328⟩, ⟨302474417678513/281474976710656, 41539042442221/35184372088832⟩]
def vcS154CutCaps : Fin 3 → Fin 3 → ℚ := ![![10026226859/100000000, 3290893381/50000000, 3839244641/100000000], ![794744623/20000000, 2038278737/50000000, 468708823/25000000], ![432932947/50000000, 7720533/1000000, 519051703/100000000]]
def vcS154CutWeightFloor : ℚ := 120712459/100000000
def vcS154CutMargins : Fin 3 → ℚ := ![3410823/1000000000, 5369749/2000000000, 3803851/2500000000]

theorem vcS154Cut_roots_ok : vcS154CutCell.rootsOK vcS154CutRoots = true := by decide +kernel

theorem vcS154Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS154CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS154Cut_margin_le (i : Fin 3) : curvatureLoss vcS154CutCell vcS154CutCaps i ≤ vcS154CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS155CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨13/40, 27/80⟩, ⟨3/40, 1/10⟩⟩
def vcS155CutRoots : Fin 3 → RatBounds := ![⟨463325884567133/281474976710656, 494351664742509/281474976710656⟩, ⟨390917195497819/281474976710656, 209448265043323/140737488355328⟩, ⟨148979184720145/140737488355328, 163557292078641/140737488355328⟩]
def vcS155CutCaps : Fin 3 → Fin 3 → ℚ := ![![5226419749/50000000, 6891201747/100000000, 4014071813/100000000], ![4143414751/100000000, 4240742557/100000000, 1953762119/100000000], ![783284291/100000000, 696338791/100000000, 234110783/50000000]]
def vcS155CutWeightFloor : ℚ := 62760517/50000000
def vcS155CutMargins : Fin 3 → ℚ := ![17313859/5000000000, 13591113/5000000000, 15313907/10000000000]

theorem vcS155Cut_roots_ok : vcS155CutCell.rootsOK vcS155CutRoots = true := by decide +kernel

theorem vcS155Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS155CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS155Cut_margin_le (i : Fin 3) : curvatureLoss vcS155CutCell vcS155CutCaps i ≤ vcS155CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS156CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨27/80, 7/20⟩, ⟨0, 1/40⟩⟩
def vcS156CutRoots : Fin 3 → RatBounds := ![⟨470205220316385/281474976710656, 502274106190019/281474976710656⟩, ⟨400078013103853/281474976710656, 429554738764005/281474976710656⟩, ⟨78856522242237/70368744177664, 21663255004649/17592186044416⟩]
def vcS156CutCaps : Fin 3 → Fin 3 → ℚ := ![![872883763/10000000, 5598953667/100000000, 420077639/12500000], ![3399254759/100000000, 3461088119/100000000, 1676952727/100000000], ![1066227707/100000000, 23559501/2500000, 656443079/100000000]]
def vcS156CutWeightFloor : ℚ := 56030929/50000000
def vcS156CutMargins : Fin 3 → ℚ := ![6403517/2000000000, 25057739/10000000000, 14967473/10000000000]

theorem vcS156Cut_roots_ok : vcS156CutCell.rootsOK vcS156CutRoots = true := by decide +kernel

theorem vcS156Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS156CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS156Cut_margin_le (i : Fin 3) : curvatureLoss vcS156CutCell vcS156CutCaps i ≤ vcS156CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS157CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨27/80, 7/20⟩, ⟨1/40, 1/20⟩⟩
def vcS157CutRoots : Fin 3 → RatBounds := ![⟨466776120889539/281474976710656, 249153395119091/140737488355328⟩, ⟨394778283372449/281474976710656, 211759264388753/140737488355328⟩, ⟨310046191146841/281474976710656, 170189667767101/140737488355328⟩]
def vcS157CutCaps : Fin 3 → Fin 3 → ℚ := ![![9136069243/100000000, 5895285759/100000000, 3532943073/100000000], ![3560726233/100000000, 722951153/20000000, 70212497/4000000], ![955011577/100000000, 420493247/50000000, 457764/78125]]
def vcS157CutWeightFloor : ℚ := 58435379/50000000
def vcS157CutMargins : Fin 3 → ℚ := ![32259457/10000000000, 25144507/10000000000, 2981253/2000000000]

theorem vcS157Cut_roots_ok : vcS157CutCell.rootsOK vcS157CutRoots = true := by decide +kernel

theorem vcS157Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS157CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS157Cut_margin_le (i : Fin 3) : curvatureLoss vcS157CutCell vcS157CutCaps i ≤ vcS157CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS158CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨27/80, 7/20⟩, ⟨1/20, 3/40⟩⟩
def vcS158CutRoots : Fin 3 → RatBounds := ![⟨28975931133643/17592186044416, 123667145465043/70368744177664⟩, ⟨24370121608899/17592186044416, 418010576630155/281474976710656⟩, ⟨305129803057377/281474976710656, 334708124246249/281474976710656⟩]
def vcS158CutCaps : Fin 3 → Fin 3 → ℚ := ![![9541807469/100000000, 1547169173/25000000, 3704094219/100000000], ![186041911/5000000, 3767310309/100000000, 91646643/5000000], ![429874943/50000000, 377304561/50000000, 262934411/50000000]]
def vcS158CutWeightFloor : ℚ := 950709/781250
def vcS158CutMargins : Fin 3 → ℚ := ![32620401/10000000000, 25340671/10000000000, 14922857/10000000000]

theorem vcS158Cut_roots_ok : vcS158CutCell.rootsOK vcS158CutRoots = true := by decide +kernel

theorem vcS158Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS158CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS158Cut_margin_le (i : Fin 3) : curvatureLoss vcS158CutCell vcS158CutCaps i ≤ vcS158CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS159CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨27/80, 7/20⟩, ⟨3/40, 1/10⟩⟩
def vcS159CutRoots : Fin 3 → RatBounds := ![⟨230345516568705/140737488355328, 491319749454503/281474976710656⟩, ⟨192727519136939/140737488355328, 206481871530855/140737488355328⟩, ⟨300619323724299/281474976710656, 20595349469335/17592186044416⟩]
def vcS159CutCaps : Fin 3 → Fin 3 → ℚ := ![![9950585229/100000000, 3239800651/50000000, 1939154539/50000000], ![193985669/5000000, 1959424677/50000000, 1909881973/100000000], ![388800313/50000000, 13609657/2000000, 47431361/10000000]]
def vcS159CutWeightFloor : ℚ := 126519977/100000000
def vcS159CutMargins : Fin 3 → ℚ := ![33087307/10000000000, 25625747/10000000000, 3752659/2500000000]

theorem vcS159Cut_roots_ok : vcS159CutCell.rootsOK vcS159CutRoots = true := by decide +kernel

theorem vcS159Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS159CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS159Cut_margin_le (i : Fin 3) : curvatureLoss vcS159CutCell vcS159CutCaps i ≤ vcS159CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS160CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨7/20, 29/80⟩, ⟨0, 1/40⟩⟩
def vcS160CutRoots : Fin 3 → RatBounds := ![⟨467742797252403/281474976710656, 31216160172557/17592186044416⟩, ⟨197416236391435/140737488355328, 52986297713817/35184372088832⟩, ⟨318115852694243/281474976710656, 21816429006717/17592186044416⟩]
def vcS160CutCaps : Fin 3 → Fin 3 → ℚ := ![![260738579/3125000, 1057820871/20000000, 1627774709/50000000], ![3200008817/100000000, 40128963/1250000, 1648506169/100000000], ![105993191/10000000, 92196589/10000000, 665476957/100000000]]
def vcS160CutWeightFloor : ℚ := 56508727/50000000
def vcS160CutMargins : Fin 3 → ℚ := ![30826897/10000000000, 23803291/10000000000, 14777273/10000000000]

theorem vcS160Cut_roots_ok : vcS160CutCell.rootsOK vcS160CutRoots = true := by decide +kernel

theorem vcS160Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS160CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS160Cut_margin_le (i : Fin 3) : curvatureLoss vcS160CutCell vcS160CutCaps i ≤ vcS160CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS161CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨7/20, 29/80⟩, ⟨1/40, 1/20⟩⟩
def vcS161CutRoots : Fin 3 → RatBounds := ![⟨464347364752771/281474976710656, 495529131670707/281474976710656⟩, ⟨389537286796191/281474976710656, 208929212663455/140737488355328⟩, ⟨312743320436393/281474976710656, 171424258384697/140737488355328⟩]
def vcS161CutCaps : Fin 3 → Fin 3 → ℚ := ![![2183918503/25000000, 2784436879/50000000, 686011857/20000000], ![3351995097/100000000, 1676397019/50000000, 431326969/25000000], ![474590239/50000000, 102826703/12500000, 148481913/25000000]]
def vcS161CutWeightFloor : ℚ := 1473079/1250000
def vcS161CutMargins : Fin 3 → ℚ := ![15512101/5000000000, 11925901/5000000000, 14709137/10000000000]

theorem vcS161Cut_roots_ok : vcS161CutCell.rootsOK vcS161CutRoots = true := by decide +kernel

theorem vcS161Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS161CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS161Cut_margin_le (i : Fin 3) : curvatureLoss vcS161CutCell vcS161CutCaps i ≤ vcS161CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS162CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨7/20, 29/80⟩, ⟨1/20, 3/40⟩⟩
def vcS162CutRoots : Fin 3 → RatBounds := ![⟨230608625396815/140737488355328, 245962953390371/140737488355328⟩, ⟨192342988834505/140737488355328, 103088854138383/70368744177664⟩, ⟨307833319757053/281474976710656, 168596803421833/140737488355328⟩]
def vcS162CutCaps : Fin 3 → Fin 3 → ℚ := ![![4563076817/50000000, 5845871471/100000000, 3603076817/100000000], ![3502697017/100000000, 139771987/4000000, 1801428247/100000000], ![213584907/25000000, 737993487/100000000, 10659543/2000000]]
def vcS162CutWeightFloor : ℚ := 122686849/100000000
def vcS162CutMargins : Fin 3 → ℚ := ![31340253/10000000000, 750253/312500000, 7359779/5000000000]

theorem vcS162Cut_roots_ok : vcS162CutCell.rootsOK vcS162CutRoots = true := by decide +kernel

theorem vcS162Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS162CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS162Cut_margin_le (i : Fin 3) : curvatureLoss vcS162CutCell vcS162CutCaps i ≤ vcS162CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS163CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨7/20, 29/80⟩, ⟨3/40, 1/10⟩⟩
def vcS163CutRoots : Fin 3 → RatBounds := ![⟨229161111907421/140737488355328, 244304741912331/140737488355328⟩, ⟨380224444450865/281474976710656, 407314026261761/281474976710656⟩, ⟨303328399023719/281474976710656, 166012794239655/140737488355328⟩]
def vcS163CutCaps : Fin 3 → Fin 3 → ℚ := ![![2379641763/25000000, 1530149239/25000000, 3775664773/100000000], ![1826114511/50000000, 1817429303/50000000, 938450729/50000000], ![772571621/100000000, 665389907/100000000, 480672137/100000000]]
def vcS163CutWeightFloor : ℚ := 127537083/100000000
def vcS163CutMargins : Fin 3 → ℚ := ![31759927/10000000000, 24251983/10000000000, 739771/500000000]

theorem vcS163Cut_roots_ok : vcS163CutCell.rootsOK vcS163CutRoots = true := by decide +kernel

theorem vcS163Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS163CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS163Cut_margin_le (i : Fin 3) : curvatureLoss vcS163CutCell vcS163CutCaps i ≤ vcS163CutMargins i := by
  fin_cases i <;> decide +kernel


end HlawkaSchatten.BelowExponent.Vertex
