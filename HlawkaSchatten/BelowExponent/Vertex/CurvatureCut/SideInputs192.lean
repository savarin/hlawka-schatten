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

def scS192CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨37/80, 19/40⟩, ⟨0, 1/40⟩⟩
def scS192CutRoots : Fin 3 → RatBounds := ![⟨462767124167303/281474976710656, 494142896141439/281474976710656⟩, ⟨44866867397411/35184372088832, 386588288574825/281474976710656⟩, ⟨86150046950155/70368744177664, 46945347342065/35184372088832⟩]
def scS192CutCaps : Fin 3 → Fin 3 → ℚ := ![![6709352101/100000000, 773248721/20000000, 2977531459/100000000], ![2412136657/100000000, 19360247/1000000, 1713189891/100000000], ![1052000003/100000000, 19438937/2500000, 2951331/390625]]
def scS192CutWeightFloor : ℚ := 6121329/5000000
def scS192CutMargins : Fin 3 → ℚ := ![13017079/5000000000, 2175903/1250000000, 3766057/2500000000]

theorem scS192Cut_roots_ok : scS192CutCell.rootsOK scS192CutRoots = true := by decide +kernel

theorem scS192Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS192CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS192Cut_margin_le (i : Fin 3) : curvatureLoss scS192CutCell scS192CutCaps i ≤ scS192CutMargins i := by
  fin_cases i <;> decide +kernel

def scS193CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨37/80, 19/40⟩, ⟨1/40, 1/20⟩⟩
def scS193CutRoots : Fin 3 → RatBounds := ![⟨459569167363597/281474976710656, 1915747426287/1099511627776⟩, ⟨22096741012931/17592186044416, 380428981959991/281474976710656⟩, ⟨339200974752275/281474976710656, 369376662276507/281474976710656⟩]
def scS193CutCaps : Fin 3 → Fin 3 → ℚ := ![![175474421/2500000, 1015203011/25000000, 628631691/20000000], ![2524277749/100000000, 1010275381/50000000, 447216079/25000000], ![940587071/100000000, 692766899/100000000, 673643557/100000000]]
def scS193CutWeightFloor : ℚ := 25492711/20000000
def scS193CutMargins : Fin 3 → ℚ := ![12993753/5000000000, 1080619/625000000, 7447849/5000000000]

theorem scS193Cut_roots_ok : scS193CutCell.rootsOK scS193CutRoots = true := by decide +kernel

theorem scS193Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS193CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS193Cut_margin_le (i : Fin 3) : curvatureLoss scS193CutCell scS193CutCaps i ≤ scS193CutMargins i := by
  fin_cases i <;> decide +kernel

def scS194CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨37/80, 19/40⟩, ⟨1/20, 3/40⟩⟩
def scS194CutRoots : Fin 3 → RatBounds := ![⟨456619970745783/281474976710656, 243513725430651/140737488355328⟩, ⟨348618630311305/281474976710656, 374817203538075/281474976710656⟩, ⟨83565732098797/70368744177664, 363742552053375/281474976710656⟩]
def scS194CutCaps : Fin 3 → Fin 3 → ℚ := ![![3663775089/50000000, 1063367703/25000000, 330733669/10000000], ![2635469689/100000000, 1052237077/50000000, 116498357/6250000], ![211338581/25000000, 12413299/2000000, 150987973/25000000]]
def scS194CutWeightFloor : ℚ := 13251837/10000000
def scS194CutMargins : Fin 3 → ℚ := ![13031677/5000000000, 17266807/10000000000, 1481859/1000000000]

theorem scS194Cut_roots_ok : scS194CutCell.rootsOK scS194CutRoots = true := by decide +kernel

theorem scS194Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS194CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS194Cut_margin_le (i : Fin 3) : curvatureLoss scS194CutCell scS194CutCaps i ≤ scS194CutMargins i := by
  fin_cases i <;> decide +kernel

def scS195CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨37/80, 19/40⟩, ⟨3/40, 1/10⟩⟩
def scS195CutRoots : Fin 3 → RatBounds := ![⟨453891338313969/281474976710656, 483894144301097/281474976710656⟩, ⟨344090878222817/281474976710656, 184841277887487/140737488355328⟩, ⟨329729061649095/281474976710656, 358589286551627/281474976710656⟩]
def scS195CutCaps : Fin 3 → Fin 3 → ℚ := ![![7636308361/100000000, 4444496131/100000000, 433833827/12500000], ![85805923/3125000, 43756773/2000000, 1938559351/100000000], ![381694269/50000000, 139723709/25000000, 544205453/100000000]]
def scS195CutWeightFloor : ℚ := 68794039/50000000
def scS195CutMargins : Fin 3 → ℚ := ![6560377/2500000000, 3464029/2000000000, 3704127/2500000000]

theorem scS195Cut_roots_ok : scS195CutCell.rootsOK scS195CutRoots = true := by decide +kernel

theorem scS195Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS195CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS195Cut_margin_le (i : Fin 3) : curvatureLoss scS195CutCell scS195CutCaps i ≤ scS195CutMargins i := by
  fin_cases i <;> decide +kernel

def scS196CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨19/40, 39/80⟩, ⟨0, 1/40⟩⟩
def scS196CutRoots : Fin 3 → RatBounds := ![⟨462451260074119/281474976710656, 61736431093483/35184372088832⟩, ⟨355184969286645/281474976710656, 382770067639053/281474976710656⟩, ⟨348024569746213/281474976710656, 189548005584001/140737488355328⟩]
def scS196CutCaps : Fin 3 → Fin 3 → ℚ := ![![6620538237/100000000, 3780310809/100000000, 2995796243/100000000], ![1192153511/50000000, 230536481/12500000, 175491753/10000000], ![525685229/50000000, 763102187/100000000, 384051501/50000000]]
def scS196CutWeightFloor : ℚ := 30910791/25000000
def scS196CutMargins : Fin 3 → ℚ := ![25801421/10000000000, 2118411/1250000000, 15279543/10000000000]

theorem scS196Cut_roots_ok : scS196CutCell.rootsOK scS196CutRoots = true := by decide +kernel

theorem scS196Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS196CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS196Cut_margin_le (i : Fin 3) : curvatureLoss scS196CutCell scS196CutCaps i ≤ scS196CutMargins i := by
  fin_cases i <;> decide +kernel

def scS197CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨19/40, 39/80⟩, ⟨1/40, 1/20⟩⟩
def scS197CutRoots : Fin 3 → RatBounds := ![⟨229628473023191/140737488355328, 490183862969731/281474976710656⟩, ⟨174897692193023/140737488355328, 94150882883441/70368744177664⟩, ⟨171314702261507/140737488355328, 372919178833009/281474976710656⟩]
def scS197CutCaps : Fin 3 → Fin 3 → ℚ := ![![6926777299/100000000, 3969996807/100000000, 1581937041/50000000], ![2494914573/100000000, 1924868839/100000000, 1832103307/100000000], ![235000811/25000000, 679856737/100000000, 85604553/12500000]]
def scS197CutWeightFloor : ℚ := 1608843/1250000
def scS197CutMargins : Fin 3 → ℚ := ![12872759/5000000000, 16824791/10000000000, 15108053/10000000000]

theorem scS197Cut_roots_ok : scS197CutCell.rootsOK scS197CutRoots = true := by decide +kernel

theorem scS197Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS197CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS197Cut_margin_le (i : Fin 3) : curvatureLoss scS197CutCell scS197CutCaps i ≤ scS197CutMargins i := by
  fin_cases i <;> decide +kernel

def scS198CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨19/40, 39/80⟩, ⟨1/20, 3/40⟩⟩
def scS198CutRoots : Fin 3 → RatBounds := ![⟨228155557319029/140737488355328, 121695911100363/70368744177664⟩, ⟨172432235839169/140737488355328, 185492951287217/140737488355328⟩, ⟨84423631895815/70368744177664, 367292846476561/281474976710656⟩]
def scS198CutCaps : Fin 3 → Fin 3 → ℚ := ![![1807993483/25000000, 259863901/6250000, 666094547/20000000], ![65114689/2500000, 1002433647/50000000, 1908723237/100000000], ![16896249/2000000, 304536217/50000000, 38373771/6250000]]
def scS198CutWeightFloor : ℚ := 133790129/100000000
def scS198CutMargins : Fin 3 → ℚ := ![6453033/2500000000, 8397441/5000000000, 15029527/10000000000]

theorem scS198Cut_roots_ok : scS198CutCell.rootsOK scS198CutRoots = true := by decide +kernel

theorem scS198Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS198CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS198Cut_margin_le (i : Fin 3) : curvatureLoss scS198CutCell scS198CutCaps i ≤ scS198CutMargins i := by
  fin_cases i <;> decide +kernel

def scS199CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨19/40, 39/80⟩, ⟨3/40, 1/10⟩⟩
def scS199CutRoots : Fin 3 → RatBounds := ![⟨226792800505453/140737488355328, 241826872419795/140737488355328⟩, ⟨170167847597991/140737488355328, 182923269765969/140737488355328⟩, ⟨166581552878323/140737488355328, 362146107048649/281474976710656⟩]
def scS199CutCaps : Fin 3 → Fin 3 → ℚ := ![![7537730723/100000000, 2172035757/50000000, 3496350413/100000000], ![2713401381/100000000, 1042164367/50000000, 1984818089/100000000], ![190721263/25000000, 109686829/20000000, 110647277/20000000]]
def scS199CutWeightFloor : ℚ := 17361023/12500000
def scS199CutMargins : Fin 3 → ℚ := ![12990891/5000000000, 16840111/10000000000, 15027567/10000000000]

theorem scS199Cut_roots_ok : scS199CutCell.rootsOK scS199CutRoots = true := by decide +kernel

theorem scS199Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS199CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS199Cut_margin_le (i : Fin 3) : curvatureLoss scS199CutCell scS199CutCaps i ≤ scS199CutMargins i := by
  fin_cases i <;> decide +kernel

def scS200CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨39/80, 1/2⟩, ⟨0, 1/40⟩⟩
def scS200CutRoots : Fin 3 → RatBounds := ![⟨462346139594371/281474976710656, 246946094275627/140737488355328⟩, ⟨351550586156063/281474976710656, 47387276424919/35184372088832⟩, ⟨351550586156063/281474976710656, 382767898991617/281474976710656⟩]
def scS200CutCaps : Fin 3 → Fin 3 → ℚ := ![![1310718853/20000000, 1854534723/50000000, 120980573/4000000], ![594563187/25000000, 110686969/6250000, 227480909/12500000], ![525616803/50000000, 749087201/100000000, 390536561/50000000]]
def scS200CutWeightFloor : ℚ := 124895857/100000000
def scS200CutMargins : Fin 3 → ℚ := ![25657777/10000000000, 517359/312500000, 7781889/5000000000]

theorem scS200Cut_roots_ok : scS200CutCell.rootsOK scS200CutRoots = true := by decide +kernel

theorem scS200Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS200CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS200Cut_margin_le (i : Fin 3) : curvatureLoss scS200CutCell scS200CutCaps i ≤ scS200CutMargins i := by
  fin_cases i <;> decide +kernel

def scS201CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨39/80, 1/2⟩, ⟨1/40, 1/20⟩⟩
def scS201CutRoots : Fin 3 → RatBounds := ![⟨459152551670879/281474976710656, 245092645368301/140737488355328⟩, ⟨21634870219113/17592186044416, 372923409309579/281474976710656⟩, ⟨346159002474271/281474976710656, 188299680516421/140737488355328⟩]
def scS201CutCaps : Fin 3 → Fin 3 → ℚ := ![![3428781991/50000000, 3894583509/100000000, 1597807843/50000000], ![1244288991/50000000, 184862319/10000000, 1899651597/100000000], ![37595061/4000000, 83418561/12500000, 696401679/100000000]]
def scS201CutWeightFloor : ℚ := 129988479/100000000
def scS201CutMargins : Fin 3 → ℚ := ![25596969/10000000000, 16430861/10000000000, 15392333/10000000000]

theorem scS201Cut_roots_ok : scS201CutCell.rootsOK scS201CutRoots = true := by decide +kernel

theorem scS201Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS201CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS201Cut_margin_le (i : Fin 3) : curvatureLoss scS201CutCell scS201CutCaps i ≤ scS201CutMargins i := by
  fin_cases i <;> decide +kernel

def scS202CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨39/80, 1/2⟩, ⟨1/20, 3/40⟩⟩
def scS202CutRoots : Fin 3 → RatBounds := ![⟨456207389883849/281474976710656, 486785713595331/281474976710656⟩, ⟨341224773650723/281474976710656, 367298957092019/281474976710656⟩, ⟨341226846484997/281474976710656, 370979877579679/281474976710656⟩]
def scS202CutCaps : Fin 3 → Fin 3 → ℚ := ![![716049091/10000000, 2039139751/50000000, 3365201433/100000000], ![81186603/3125000, 1925689467/100000000, 1978880877/100000000], ![168939069/20000000, 597848071/100000000, 124869999/20000000]]
def scS202CutWeightFloor : ℚ := 135100079/100000000
def scS202CutMargins : Fin 3 → ℚ := ![25658679/10000000000, 1639719/1000000000, 3828849/2500000000]

theorem scS202Cut_roots_ok : scS202CutCell.rootsOK scS202CutRoots = true := by decide +kernel

theorem scS202Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS202CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS202Cut_margin_le (i : Fin 3) : curvatureLoss scS202CutCell scS202CutCaps i ≤ scS202CutMargins i := by
  fin_cases i <;> decide +kernel

def scS203CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨39/80, 1/2⟩, ⟨3/40, 1/10⟩⟩
def scS203CutRoots : Fin 3 → RatBounds := ![⟨226741247898615/140737488355328, 483656413523869/281474976710656⟩, ⟨168347223531237/140737488355328, 362153964492971/281474976710656⟩, ⟨84174359708273/70368744177664, 365838790974491/281474976710656⟩]
def scS203CutCaps : Fin 3 → Fin 3 → ℚ := ![![1866076663/25000000, 4260445841/100000000, 883543801/25000000], ![2706507781/100000000, 1001115437/50000000, 102878817/5000000], ![95347119/12500000, 134577947/25000000, 281290501/50000000]]
def scS203CutWeightFloor : ℚ := 28045503/20000000
def scS203CutMargins : Fin 3 → ℚ := ![25824067/10000000000, 2054669/1250000000, 7658277/5000000000]

theorem scS203Cut_roots_ok : scS203CutCell.rootsOK scS203CutRoots = true := by decide +kernel

theorem scS203Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS203CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS203Cut_margin_le (i : Fin 3) : curvatureLoss scS203CutCell scS203CutCaps i ≤ scS203CutMargins i := by
  fin_cases i <;> decide +kernel

def scD0CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨3/16, 1/5⟩, ⟨1/10, 9/80⟩⟩
def scD0CutRoots : Fin 3 → RatBounds := ![⟨135880753197589/70368744177664, 294034990466331/140737488355328⟩, ⟨491745621226455/281474976710656, 133231448478461/70368744177664⟩, ⟨132830691771803/140737488355328, 302053982345919/281474976710656⟩]
def scD0CutCaps : Fin 3 → Fin 3 → ℚ := ![![31142817363/100000000, 24443806647/100000000, 8603206909/100000000], ![161735129/1000000, 538431631/3125000, 1940901569/50000000], ![340095933/50000000, 711098581/100000000, 60823609/20000000]]
def scD0CutWeightFloor : ℚ := 119851789/100000000
def scD0CutMargins : Fin 3 → ℚ := ![11717901/1250000000, 20695663/2500000000, 12489383/5000000000]

theorem scD0Cut_roots_ok : scD0CutCell.rootsOK scD0CutRoots = true := by decide +kernel

theorem scD0Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD0CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD0Cut_margin_le (i : Fin 3) : curvatureLoss scD0CutCell scD0CutCaps i ≤ scD0CutMargins i := by
  fin_cases i <;> decide +kernel

def scD1CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨3/16, 1/5⟩, ⟨9/80, 1/8⟩⟩
def scD1CutRoots : Fin 3 → RatBounds := ![⟨541858601281397/281474976710656, 146563401029137/70368744177664⟩, ⟨489483639376759/281474976710656, 530452948881353/281474976710656⟩, ⟨263563617820333/281474976710656, 149824079705217/140737488355328⟩]
def scD1CutCaps : Fin 3 → Fin 3 → ℚ := ![![7939385783/25000000, 3117329513/12500000, 8757852479/100000000], ![8242105473/50000000, 3509394101/20000000, 3953566429/100000000], ![162946371/25000000, 340258599/50000000, 290953341/100000000]]
def scD1CutWeightFloor : ℚ := 122133459/100000000
def scD1CutMargins : Fin 3 → ℚ := ![19099039/2000000000, 21077209/2500000000, 25395259/10000000000]

theorem scD1Cut_roots_ok : scD1CutCell.rootsOK scD1CutRoots = true := by decide +kernel

theorem scD1Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD1CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD1Cut_margin_le (i : Fin 3) : curvatureLoss scD1CutCell scD1CutCaps i ≤ scD1CutMargins i := by
  fin_cases i <;> decide +kernel

def scD2CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨1/5, 17/80⟩, ⟨1/10, 9/80⟩⟩
def scD2CutRoots : Fin 3 → RatBounds := ![⟨33414217489427/17592186044416, 576933100828683/281474976710656⟩, ⟨240096743552133/140737488355328, 259558680762265/140737488355328⟩, ⟨268274510639725/281474976710656, 303300481837871/281474976710656⟩]
def scD2CutCaps : Fin 3 → Fin 3 → ℚ := ![![27385095359/100000000, 10556882679/50000000, 192999137/2500000], ![2770727221/20000000, 3687063497/25000000, 865383781/25000000], ![165393033/25000000, 680571651/100000000, 75809657/25000000]]
def scD2CutWeightFloor : ℚ := 120876283/100000000
def scD2CutMargins : Fin 3 → ℚ := ![81836531/10000000000, 71372249/10000000000, 5607783/2500000000]

theorem scD2Cut_roots_ok : scD2CutCell.rootsOK scD2CutRoots = true := by decide +kernel

theorem scD2Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD2CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD2Cut_margin_le (i : Fin 3) : curvatureLoss scD2CutCell scD2CutCaps i ≤ scD2CutMargins i := by
  fin_cases i <;> decide +kernel

def scD3CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨1/5, 17/80⟩, ⟨9/80, 1/8⟩⟩
def scD3CutRoots : Fin 3 → RatBounds := ![⟨533006135072143/281474976710656, 287583833814951/140737488355328⟩, ⟨7468034177213/4398046511104, 64584311201869/35184372088832⟩, ⟨33271906618219/35184372088832, 150453446012817/140737488355328⟩]
def scD3CutCaps : Fin 3 → Fin 3 → ℚ := ![![2792422473/10000000, 21542174607/100000000, 245648841/3125000], ![14119900139/100000000, 15019564029/100000000, 3525972781/100000000], ![633798489/100000000, 130238699/20000000, 145041737/50000000]]
def scD3CutWeightFloor : ℚ := 123169741/100000000
def scD3CutMargins : Fin 3 → ℚ := ![2083883/250000000, 72681509/10000000000, 1425393/625000000]

theorem scD3Cut_roots_ok : scD3CutCell.rootsOK scD3CutRoots = true := by decide +kernel

theorem scD3Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD3CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD3Cut_margin_le (i : Fin 3) : curvatureLoss scD3CutCell scD3CutCaps i ≤ scD3CutMargins i := by
  fin_cases i <;> decide +kernel

def scD4CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨17/80, 9/40⟩, ⟨1/10, 9/80⟩⟩
def scD4CutRoots : Fin 3 → RatBounds := ![⟨263286400709341/140737488355328, 283472922013401/140737488355328⟩, ⟨234745218574457/140737488355328, 126615471921747/70368744177664⟩, ⟨270850057024163/281474976710656, 304683792875053/281474976710656⟩]
def scD4CutCaps : Fin 3 → Fin 3 → ℚ := ![![6083511999/25000000, 18441898007/100000000, 1402345847/20000000], ![5995754797/50000000, 199252109/1562500, 97411689/3125000], ![25815499/4000000, 326612383/50000000, 37880391/12500000]]
def scD4CutWeightFloor : ℚ := 121881767/100000000
def scD4CutMargins : Fin 3 → ℚ := ![36104439/5000000000, 15550419/2500000000, 1273431/625000000]

theorem scD4Cut_roots_ok : scD4CutCell.rootsOK scD4CutRoots = true := by decide +kernel

theorem scD4Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD4CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD4Cut_margin_le (i : Fin 3) : curvatureLoss scD4CutCell scD4CutCaps i ≤ scD4CutMargins i := by
  fin_cases i <;> decide +kernel

def scD5CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨17/80, 9/40⟩, ⟨9/80, 1/8⟩⟩
def scD5CutRoots : Fin 3 → RatBounds := ![⟨524990788013685/281474976710656, 141306632536563/70368744177664⟩, ⟨233635600193181/140737488355328, 252022614810867/140737488355328⟩, ⟨67187480726519/70368744177664, 302301493003667/281474976710656⟩]
def scD5CutCaps : Fin 3 → Fin 3 → ℚ := ![![24811920013/100000000, 588029679/3125000, 7141030303/100000000], ![2444425631/20000000, 6493295947/50000000, 317556319/10000000], ![123632057/20000000, 312464151/50000000, 57973757/20000000]]
def scD5CutWeightFloor : ℚ := 24837319/20000000
def scD5CutMargins : Fin 3 → ℚ := ![7353947/1000000000, 7917107/1250000000, 20715747/10000000000]

theorem scD5Cut_roots_ok : scD5CutCell.rootsOK scD5CutRoots = true := by decide +kernel

theorem scD5Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD5CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD5Cut_margin_le (i : Fin 3) : curvatureLoss scD5CutCell scD5CutCaps i ≤ scD5CutMargins i := by
  fin_cases i <;> decide +kernel

def scD6CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨9/40, 19/80⟩, ⟨1/10, 9/80⟩⟩
def scD6CutRoots : Fin 3 → RatBounds := ![⟨519260701767389/281474976710656, 139489369395243/70368744177664⟩, ⟨459532895932893/281474976710656, 494803487257985/281474976710656⟩, ⟨68350366065019/70368744177664, 153095412870887/140737488355328⟩]
def scD6CutCaps : Fin 3 → Fin 3 → ℚ := ![![2182382269/10000000, 406793107/2500000, 257354607/4000000], ![2095461981/20000000, 2781272151/25000000, 2831764099/100000000], ![631234031/100000000, 314270067/50000000, 151715921/50000000]]
def scD6CutWeightFloor : ℚ := 122874329/100000000
def scD6CutMargins : Fin 3 → ℚ := ![64321029/10000000000, 27368509/5000000000, 18689573/10000000000]

theorem scD6Cut_roots_ok : scD6CutCell.rootsOK scD6CutRoots = true := by decide +kernel

theorem scD6Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD6CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD6Cut_margin_le (i : Fin 3) : curvatureLoss scD6CutCell scD6CutCaps i ≤ scD6CutMargins i := by
  fin_cases i <;> decide +kernel

def scD7CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨9/40, 19/80⟩, ⟨9/80, 1/8⟩⟩
def scD7CutRoots : Fin 3 → RatBounds := ![⟨517714682336419/281474976710656, 278140023254309/140737488355328⟩, ⟨114332860485049/70368744177664, 492409815343585/281474976710656⟩, ⟨271300956765721/281474976710656, 151909502064649/140737488355328⟩]
def scD7CutCaps : Fin 3 → Fin 3 → ℚ := ![![11125736039/50000000, 4150834767/25000000, 26214887/400000], ![1334869453/12500000, 1132953057/10000000, 2885106867/100000000], ![302240823/50000000, 60122373/10000000, 145106897/50000000]]
def scD7CutWeightFloor : ℚ := 125190221/100000000
def scD7CutMargins : Fin 3 → ℚ := ![6549787/1000000000, 13932663/2500000000, 4750509/2500000000]

theorem scD7Cut_roots_ok : scD7CutCell.rootsOK scD7CutRoots = true := by decide +kernel

theorem scD7Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD7CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD7Cut_margin_le (i : Fin 3) : curvatureLoss scD7CutCell scD7CutCaps i ≤ scD7CutMargins i := by
  fin_cases i <;> decide +kernel

def scD8CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨19/80, 1/4⟩, ⟨1/10, 9/80⟩⟩
def scD8CutRoots : Fin 3 → RatBounds := ![⟨512609456676825/281474976710656, 137461309773611/70368744177664⟩, ⟨56279285835809/35184372088832, 121003660434259/70368744177664⟩, ⟨68984974930985/70368744177664, 2404778427857/2199023255552⟩]
def scD8CutCaps : Fin 3 → Fin 3 → ℚ := ![![9868290053/50000000, 14483758777/100000000, 2974222991/50000000], ![2307982249/25000000, 9783231139/100000000, 2592888341/100000000], ![154698211/25000000, 2367602/390625, 152162947/50000000]]
def scD8CutWeightFloor : ℚ := 1935297/1562500
def scD8CutMargins : Fin 3 → ℚ := ![577877/100000000, 24290133/5000000000, 17276681/10000000000]

theorem scD8Cut_roots_ok : scD8CutCell.rootsOK scD8CutRoots = true := by decide +kernel

theorem scD8Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD8CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD8Cut_margin_le (i : Fin 3) : curvatureLoss scD8CutCell scD8CutCaps i ≤ scD8CutMargins i := by
  fin_cases i <;> decide +kernel

def scD9CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨19/80, 1/4⟩, ⟨9/80, 1/8⟩⟩
def scD9CutRoots : Fin 3 → RatBounds := ![⟨63887053260941/35184372088832, 548205934829361/281474976710656⟩, ⟨112012154320805/70368744177664, 481641161022987/281474976710656⟩, ⟨273839430567579/281474976710656, 305449586997393/281474976710656⟩]
def scD9CutCaps : Fin 3 → Fin 3 → ℚ := ![![10061341501/50000000, 230932051/1562500, 6060481737/100000000], ![588109513/6250000, 9962937343/100000000, 2641981109/100000000], ![118491019/20000000, 72460483/12500000, 58208587/20000000]]
def scD9CutWeightFloor : ℚ := 504743/400000
def scD9CutMargins : Fin 3 → ℚ := ![58837677/10000000000, 12364391/2500000000, 17565441/10000000000]

theorem scD9Cut_roots_ok : scD9CutCell.rootsOK scD9CutRoots = true := by decide +kernel

theorem scD9Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD9CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD9Cut_margin_le (i : Fin 3) : curvatureLoss scD9CutCell scD9CutCaps i ≤ scD9CutMargins i := by
  fin_cases i <;> decide +kernel

def scD10CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨1/4, 21/80⟩, ⟨1/10, 9/80⟩⟩
def scD10CutRoots : Fin 3 → RatBounds := ![⟨63318817896287/35184372088832, 135627023540647/70368744177664⟩, ⟨110380395237691/70368744177664, 473989862339657/281474976710656⟩, ⟨278474815342145/281474976710656, 309538703414075/281474976710656⟩]
def scD10CutCaps : Fin 3 → Fin 3 → ℚ := ![![17982612259/100000000, 2598868331/20000000, 1384078723/25000000], ![4104339663/50000000, 4332499039/50000000, 2410847713/100000000], ![607810903/100000000, 292796919/50000000, 152831659/50000000]]
def scD10CutWeightFloor : ℚ := 62420027/50000000
def scD10CutMargins : Fin 3 → ℚ := ![26170999/5000000000, 1357723/312500000, 16118801/10000000000]

theorem scD10Cut_roots_ok : scD10CutCell.rootsOK scD10CutRoots = true := by decide +kernel

theorem scD10Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD10CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD10Cut_margin_le (i : Fin 3) : curvatureLoss scD10CutCell scD10CutCaps i ≤ scD10CutMargins i := by
  fin_cases i <;> decide +kernel

def scD11CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨1/4, 21/80⟩, ⟨9/80, 1/8⟩⟩
def scD11CutRoots : Fin 3 → RatBounds := ![⟨126266943977467/70368744177664, 270451778815051/140737488355328⟩, ⟨439349934881615/281474976710656, 58954266761447/35184372088832⟩, ⟨69093680257131/70368744177664, 307185794890977/281474976710656⟩]
def scD11CutCaps : Fin 3 → Fin 3 → ℚ := ![![2291709793/12500000, 13260237643/100000000, 1410393099/25000000], ![2091789611/25000000, 8824105021/100000000, 98283763/4000000], ![581836771/100000000, 111998503/20000000, 292296831/100000000]]
def scD11CutWeightFloor : ℚ := 12717751/10000000
def scD11CutMargins : Fin 3 → ℚ := ![6660809/1250000000, 22113609/5000000000, 16388601/10000000000]

theorem scD11Cut_roots_ok : scD11CutCell.rootsOK scD11CutRoots = true := by decide +kernel

theorem scD11Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD11CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD11Cut_margin_le (i : Fin 3) : curvatureLoss scD11CutCell scD11CutCaps i ≤ scD11CutMargins i := by
  fin_cases i <;> decide +kernel

def scD12CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨21/80, 11/40⟩, ⟨1/10, 9/80⟩⟩
def scD12CutRoots : Fin 3 → RatBounds := ![⟨250513045303351/140737488355328, 535862129587273/281474976710656⟩, ⟨27083291851453/17592186044416, 464641007460423/281474976710656⟩, ⟨140507178969485/140737488355328, 38920797166735/35184372088832⟩]
def scD12CutCaps : Fin 3 → Fin 3 → ℚ := ![![16495648343/100000000, 5871050507/50000000, 323988243/6250000], ![7359396541/100000000, 1544866871/20000000, 1135152059/50000000], ![598083619/100000000, 566735729/100000000, 307394049/100000000]]
def scD12CutWeightFloor : ℚ := 125821111/100000000
def scD12CutMargins : Fin 3 → ℚ := ![47760017/10000000000, 4890911/1250000000, 18949/12500000]

theorem scD12Cut_roots_ok : scD12CutCell.rootsOK scD12CutRoots = true := by decide +kernel

theorem scD12Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD12CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD12Cut_margin_le (i : Fin 3) : curvatureLoss scD12CutCell scD12CutCaps i ≤ scD12CutMargins i := by
  fin_cases i <;> decide +kernel

def scD13CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨21/80, 11/40⟩, ⟨9/80, 1/8⟩⟩
def scD13CutRoots : Fin 3 → RatBounds := ![⟨249785549086769/140737488355328, 534289332579091/281474976710656⟩, ⟨53896685789171/35184372088832, 462300889081223/281474976710656⟩, ⟨278914912197339/281474976710656, 309022050701933/281474976710656⟩]
def scD13CutCaps : Fin 3 → Fin 3 → ℚ := ![![4204266219/25000000, 2995680927/25000000, 5283295851/100000000], ![7501561051/100000000, 1966530527/25000000, 2313929147/100000000], ![286214827/50000000, 13547313/2500000, 293927723/100000000]]
def scD13CutWeightFloor : ℚ := 16021151/12500000
def scD13CutMargins : Fin 3 → ℚ := ![48615343/10000000000, 39825661/10000000000, 1926551/1250000000]

theorem scD13Cut_roots_ok : scD13CutCell.rootsOK scD13CutRoots = true := by decide +kernel

theorem scD13Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD13CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD13Cut_margin_le (i : Fin 3) : curvatureLoss scD13CutCell scD13CutCaps i ≤ scD13CutMargins i := by
  fin_cases i <;> decide +kernel

def scD14CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨11/40, 23/80⟩, ⟨1/10, 9/80⟩⟩
def scD14CutRoots : Fin 3 → RatBounds := ![⟨495986916424283/281474976710656, 264918549542209/140737488355328⟩, ⟨212807166669453/140737488355328, 227946883114091/140737488355328⟩, ⟨283565676051637/281474976710656, 156645260460913/140737488355328⟩]
def scD14CutCaps : Fin 3 → Fin 3 → ℚ := ![![15225329989/100000000, 5340348039/50000000, 976106899/20000000], ![6644057509/100000000, 173157453/2500000, 1076735099/50000000], ![589444141/100000000, 137328037/25000000, 309477437/100000000]]
def scD14CutWeightFloor : ℚ := 126805361/100000000
def scD14CutMargins : Fin 3 → ℚ := ![21932453/5000000000, 1108173/312500000, 14342739/10000000000]

theorem scD14Cut_roots_ok : scD14CutCell.rootsOK scD14CutRoots = true := by decide +kernel

theorem scD14Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD14CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD14Cut_margin_le (i : Fin 3) : curvatureLoss scD14CutCell scD14CutCaps i ≤ scD14CutMargins i := by
  fin_cases i <;> decide +kernel

def scD15CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨11/40, 23/80⟩, ⟨9/80, 1/8⟩⟩
def scD15CutRoots : Fin 3 → RatBounds := ![⟨494557412457283/281474976710656, 528293291364533/281474976710656⟩, ⟨423466223489215/281474976710656, 14173980109371/8796093022208⟩, ⟨281467099523681/281474976710656, 155477133535517/140737488355328⟩]
def scD15CutCaps : Fin 3 → Fin 3 → ℚ := ![![485045761/3125000, 5449924561/50000000, 4975080101/100000000], ![211639751/3125000, 7053401717/100000000, 219489319/10000000], ![282036397/50000000, 525172561/100000000, 295896603/100000000]]
def scD15CutWeightFloor : ℚ := 32291021/25000000
def scD15CutMargins : Fin 3 → ℚ := ![892891/200000000, 36090671/10000000000, 7290889/5000000000]

theorem scD15Cut_roots_ok : scD15CutCell.rootsOK scD15CutRoots = true := by decide +kernel

theorem scD15Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD15CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD15Cut_margin_le (i : Fin 3) : curvatureLoss scD15CutCell scD15CutCaps i ≤ scD15CutMargins i := by
  fin_cases i <;> decide +kernel

def scD16CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨23/80, 3/10⟩, ⟨1/10, 9/80⟩⟩
def scD16CutRoots : Fin 3 → RatBounds := ![⟨245695497408397/140737488355328, 262186898052991/140737488355328⟩, ⟨209160328365283/140737488355328, 447684979180737/281474976710656⟩, ⟨286135153298005/281474976710656, 157654107497641/140737488355328⟩]
def scD16CutCaps : Fin 3 → Fin 3 → ℚ := ![![353318713/2500000, 4887266931/50000000, 4618356681/100000000], ![6037642319/100000000, 3122031407/50000000, 64264149/3125000], ![72719487/12500000, 533141707/100000000, 77970251/25000000]]
def scD16CutWeightFloor : ℚ := 12779563/10000000
def scD16CutMargins : Fin 3 → ℚ := ![40531537/10000000000, 6465523/2000000000, 341147/250000000]

theorem scD16Cut_roots_ok : scD16CutCell.rootsOK scD16CutRoots = true := by decide +kernel

theorem scD16Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD16CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD16Cut_margin_le (i : Fin 3) : curvatureLoss scD16CutCell scD16CutCaps i ≤ scD16CutMargins i := by
  fin_cases i <;> decide +kernel

def scD17CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨23/80, 3/10⟩, ⟨9/80, 1/8⟩⟩
def scD17CutRoots : Fin 3 → RatBounds := ![⟨489984866269609/281474976710656, 130714115637519/70368744177664⟩, ⟨416182378244755/281474976710656, 13917831495925/8796093022208⟩, ⟨71009405287679/70368744177664, 78244891676883/70368744177664⟩]
def scD17CutCaps : Fin 3 → Fin 3 → ℚ := ![![7203590439/50000000, 1995062807/20000000, 941733269/20000000], ![6154390853/100000000, 6358620597/100000000, 262003221/12500000], ![278317271/50000000, 50965821/10000000, 59634479/20000000]]
def scD17CutWeightFloor : ℚ := 130165013/100000000
def scD17CutMargins : Fin 3 → ℚ := ![41246497/10000000000, 32897643/10000000000, 13872783/10000000000]

theorem scD17Cut_roots_ok : scD17CutCell.rootsOK scD17CutRoots = true := by decide +kernel

theorem scD17Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD17CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD17Cut_margin_le (i : Fin 3) : curvatureLoss scD17CutCell scD17CutCaps i ≤ scD17CutMargins i := by
  fin_cases i <;> decide +kernel

def scD18CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨3/10, 5/16⟩, ⟨1/10, 9/80⟩⟩
def scD18CutRoots : Fin 3 → RatBounds := ![⟨121800562612969/70368744177664, 259711015117945/140737488355328⟩, ⟨411411775917945/281474976710656, 439960569888031/281474976710656⟩, ⟨144364294441217/140737488355328, 158708775520115/140737488355328⟩]
def scD18CutCaps : Fin 3 → Fin 3 → ℚ := ![![13187477297/100000000, 112449229/1250000, 4390861521/100000000], ![2760471231/50000000, 5659106021/100000000, 988536423/50000000], ![449154/78125, 518081093/100000000, 78646059/25000000]]
def scD18CutWeightFloor : ℚ := 128794471/100000000
def scD18CutMargins : Fin 3 → ℚ := ![2353923/625000000, 29635011/10000000000, 2610359/2000000000]

theorem scD18Cut_roots_ok : scD18CutCell.rootsOK scD18CutRoots = true := by decide +kernel

theorem scD18Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD18CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD18Cut_margin_le (i : Fin 3) : curvatureLoss scD18CutCell scD18CutCaps i ≤ scD18CutMargins i := by
  fin_cases i <;> decide +kernel

def scD19CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨3/10, 5/16⟩, ⟨9/80, 1/8⟩⟩
def scD19CutRoots : Fin 3 → RatBounds := ![⟨485817533538887/281474976710656, 258964427857329/140737488355328⟩, ⟨409282214031479/281474976710656, 437656724559093/281474976710656⟩, ⟨143316118415205/140737488355328, 157548037313239/140737488355328⟩]
def scD19CutCaps : Fin 3 → Fin 3 → ℚ := ![![13443172821/100000000, 9180892289/100000000, 4477532607/100000000], ![2813880461/50000000, 1440741373/25000000, 2015129449/100000000], ![275009167/50000000, 123803193/25000000, 18796019/6250000]]
def scD19CutWeightFloor : ℚ := 32793647/25000000
def scD19CutMargins : Fin 3 → ℚ := ![38322173/10000000000, 6030887/2000000000, 13268357/10000000000]

theorem scD19Cut_roots_ok : scD19CutCell.rootsOK scD19CutRoots = true := by decide +kernel

theorem scD19Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD19CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD19Cut_margin_le (i : Fin 3) : curvatureLoss scD19CutCell scD19CutCaps i ≤ scD19CutMargins i := by
  fin_cases i <;> decide +kernel


end HlawkaSchatten.BelowExponent.Vertex
