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

def vcM2CutCell : ParameterCell := ⟨⟨1/20, 3/40⟩, ⟨3/20, 7/40⟩, ⟨0, 1/36⟩⟩
def vcM2CutRoots : Fin 3 → RatBounds := ![⟨500374504577961/281474976710656, 72310175998999/35184372088832⟩, ⟨59654344896007/35184372088832, 552863011606435/281474976710656⟩, ⟨33506641696321/35184372088832, 338800007517183/281474976710656⟩]
def vcM2CutCaps : Fin 3 → Fin 3 → ℚ := ![![7947412759/25000000, 5413284153/20000000, 3359903243/25000000], ![1378498721/6250000, 23500370401/100000000, 2025633321/20000000], ![44295189/4000000, 1185085657/100000000, 511619163/100000000]]
def vcM2CutWeightFloor : ℚ := 50388947/50000000
def vcM2CutMargins : Fin 3 → ℚ := ![86269947/2000000000, 406483281/10000000000, 189057877/10000000000]

theorem vcM2Cut_roots_ok : vcM2CutCell.rootsOK vcM2CutRoots = true := by decide +kernel

theorem vcM2Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM2CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM2Cut_margin_le (i : Fin 3) : curvatureLoss vcM2CutCell vcM2CutCaps i ≤ vcM2CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM4CutCell : ParameterCell := ⟨⟨1/20, 3/40⟩, ⟨7/40, 1/5⟩, ⟨0, 1/36⟩⟩
def vcM4CutRoots : Fin 3 → RatBounds := ![⟨486944852130079/281474976710656, 139678139363193/70368744177664⟩, ⟨458562785553245/281474976710656, 65942906628107/35184372088832⟩, ⟨136776525604983/140737488355328, 339888884411633/281474976710656⟩]
def vcM4CutCaps : Fin 3 → Fin 3 → ℚ := ![![35218212779/100000000, 15005601531/50000000, 18150869003/100000000], ![1038028403/5000000, 2778273679/12500000, 2780468931/25000000], ![491000959/25000000, 511554339/25000000, 989767097/100000000]]
def vcM4CutWeightFloor : ℚ := 48592783/50000000
def vcM4CutMargins : Fin 3 → ℚ := ![114069291/2500000000, 213920261/5000000000, 238239683/10000000000]

theorem vcM4Cut_roots_ok : vcM4CutCell.rootsOK vcM4CutRoots = true := by decide +kernel

theorem vcM4Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM4CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM4Cut_margin_le (i : Fin 3) : curvatureLoss vcM4CutCell vcM4CutCaps i ≤ vcM4CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM5CutCell : ParameterCell := ⟨⟨1/20, 3/40⟩, ⟨7/40, 1/5⟩, ⟨1/36, 1/18⟩⟩
def vcM5CutRoots : Fin 3 → RatBounds := ![⟨120597019542775/70368744177664, 138311321023603/70368744177664⟩, ⟨452996770236823/281474976710656, 260434258187853/140737488355328⟩, ⟨267930366251617/281474976710656, 166299664831571/140737488355328⟩]
def vcM5CutCaps : Fin 3 → Fin 3 → ℚ := ![![25194755227/100000000, 20483769783/100000000, 10308967629/100000000], ![15060760251/100000000, 8083278209/50000000, 3450266047/50000000], ![242223243/20000000, 1269579713/100000000, 293160689/50000000]]
def vcM5CutWeightFloor : ℚ := 3314709/3125000
def vcM5CutMargins : Fin 3 → ℚ := ![163088753/5000000000, 298575849/10000000000, 140104323/10000000000]

theorem vcM5Cut_roots_ok : vcM5CutCell.rootsOK vcM5CutRoots = true := by decide +kernel

theorem vcM5Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM5CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM5Cut_margin_le (i : Fin 3) : curvatureLoss vcM5CutCell vcM5CutCaps i ≤ vcM5CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM6CutCell : ParameterCell := ⟨⟨1/20, 3/40⟩, ⟨1/5, 9/40⟩, ⟨0, 1/36⟩⟩
def vcM6CutRoots : Fin 3 → RatBounds := ![⟨475677422612177/281474976710656, 542588640233203/281474976710656⟩, ⟨442123761997567/281474976710656, 505974037996415/281474976710656⟩, ⟨278838194290583/281474976710656, 42715606128267/35184372088832⟩]
def vcM6CutCaps : Fin 3 → Fin 3 → ℚ := ![![1653410137/6250000, 4361964091/20000000, 3444010637/25000000], ![13964302099/100000000, 3021619953/20000000, 1913191641/25000000], ![1844357243/100000000, 118217261/6250000, 985545461/100000000]]
def vcM6CutWeightFloor : ℚ := 49531613/50000000
def vcM6CutMargins : Fin 3 → ℚ := ![333561317/10000000000, 306664657/10000000000, 88459109/5000000000]

theorem vcM6Cut_roots_ok : vcM6CutCell.rootsOK vcM6CutRoots = true := by decide +kernel

theorem vcM6Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM6CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM6Cut_margin_le (i : Fin 3) : curvatureLoss vcM6CutCell vcM6CutCaps i ≤ vcM6CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM7CutCell : ParameterCell := ⟨⟨1/20, 3/40⟩, ⟨1/5, 9/40⟩, ⟨1/36, 1/18⟩⟩
def vcM7CutRoots : Fin 3 → RatBounds := ![⟨235649942736783/140737488355328, 67169500914797/35184372088832⟩, ⟨109149717163499/70368744177664, 499373361073777/281474976710656⟩, ⟨68303298106755/70368744177664, 167268076092777/140737488355328⟩]
def vcM7CutCaps : Fin 3 → Fin 3 → ℚ := ![![28207266887/100000000, 5813792771/25000000, 2912756929/20000000], ![1857694193/12500000, 16037155037/100000000, 4043028323/50000000], ![827214703/50000000, 422363321/25000000, 878706371/100000000]]
def vcM7CutWeightFloor : ℚ := 51694983/50000000
def vcM7CutMargins : Fin 3 → ℚ := ![176216117/5000000000, 16163309/500000000, 185427063/10000000000]

theorem vcM7Cut_roots_ok : vcM7CutCell.rootsOK vcM7CutRoots = true := by decide +kernel

theorem vcM7Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM7CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM7Cut_margin_le (i : Fin 3) : curvatureLoss vcM7CutCell vcM7CutCaps i ≤ vcM7CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM8CutCell : ParameterCell := ⟨⟨1/20, 3/40⟩, ⟨9/40, 1/4⟩, ⟨0, 1/36⟩⟩
def vcM8CutRoots : Fin 3 → RatBounds := ![⟨233092964529401/140737488355328, 529325749755747/281474976710656⟩, ⟨106871474621013/70368744177664, 243654645948721/140737488355328⟩, ⟨284008137028197/281474976710656, 344175894173889/281474976710656⟩]
def vcM8CutCaps : Fin 3 → Fin 3 → ℚ := ![![4243923273/20000000, 3363119677/20000000, 2778536401/25000000], ![10158657573/100000000, 11010140331/100000000, 5707490421/100000000], ![1755047183/100000000, 55152743/3125000, 988529259/100000000]]
def vcM8CutWeightFloor : ℚ := 100899959/100000000
def vcM8CutMargins : Fin 3 → ℚ := ![8189697/312500000, 58602759/2500000000, 70476729/5000000000]

theorem vcM8Cut_roots_ok : vcM8CutCell.rootsOK vcM8CutRoots = true := by decide +kernel

theorem vcM8Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM8CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM8Cut_margin_le (i : Fin 3) : curvatureLoss vcM8CutCell vcM8CutCaps i ≤ vcM8CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM9CutCell : ParameterCell := ⟨⟨1/20, 3/40⟩, ⟨9/40, 1/4⟩, ⟨1/36, 1/18⟩⟩
def vcM9CutRoots : Fin 3 → RatBounds := ![⟨461961161950911/281474976710656, 524289123508707/281474976710656⟩, ⟨105497617247421/70368744177664, 60095062793463/35184372088832⟩, ⟨278386341625363/281474976710656, 337075961738957/281474976710656⟩]
def vcM9CutCaps : Fin 3 → Fin 3 → ℚ := ![![5652707479/25000000, 17934862849/100000000, 1470732407/12500000], ![1350417013/12500000, 11679404831/100000000, 6039115889/100000000], ![393262009/25000000, 787475001/50000000, 880964029/100000000]]
def vcM9CutWeightFloor : ℚ := 52657077/50000000
def vcM9CutMargins : Fin 3 → ℚ := ![138110159/5000000000, 246551957/10000000000, 147598321/10000000000]

theorem vcM9Cut_roots_ok : vcM9CutCell.rootsOK vcM9CutRoots = true := by decide +kernel

theorem vcM9Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM9CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM9Cut_margin_le (i : Fin 3) : curvatureLoss vcM9CutCell vcM9CutCaps i ≤ vcM9CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM10CutCell : ParameterCell := ⟨⟨1/20, 3/40⟩, ⟨1/4, 11/40⟩, ⟨0, 1/36⟩⟩
def vcM10CutRoots : Fin 3 → RatBounds := ![⟨229092756095091/140737488355328, 518377170729747/281474976710656⟩, ⟨207162938176759/140737488355328, 58869016716723/35184372088832⟩, ⟨289136624709417/281474976710656, 347159419680931/281474976710656⟩]
def vcM10CutCaps : Fin 3 → Fin 3 → ℚ := ![![8843840999/50000000, 6763803117/50000000, 9337443057/100000000], ![7806266921/100000000, 8437376339/100000000, 226353031/5000000], ![1686842293/100000000, 331719161/20000000, 498518131/50000000]]
def vcM10CutWeightFloor : ℚ := 25680491/25000000
def vcM10CutMargins : Fin 3 → ℚ := ![107720587/5000000000, 93799343/5000000000, 7370807/625000000]

theorem vcM10Cut_roots_ok : vcM10CutCell.rootsOK vcM10CutRoots = true := by decide +kernel

theorem vcM10Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM10CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM10Cut_margin_le (i : Fin 3) : curvatureLoss vcM10CutCell vcM10CutCaps i ≤ vcM10CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM11CutCell : ParameterCell := ⟨⟨1/20, 3/40⟩, ⟨1/4, 11/40⟩, ⟨1/36, 1/18⟩⟩
def vcM11CutRoots : Fin 3 → RatBounds := ![⟨454090767692845/281474976710656, 513504695418789/281474976710656⟩, ⟨408850609587663/281474976710656, 464437895847335/281474976710656⟩, ⟨141761055756995/140737488355328, 170069375601891/140737488355328⟩]
def vcM11CutCaps : Fin 3 → Fin 3 → ℚ := ![![9418257331/50000000, 14428070899/100000000, 1237199271/12500000], ![1659287211/20000000, 8942134037/100000000, 47931133/1000000], ![377715997/25000000, 295794633/20000000, 222050811/25000000]]
def vcM11CutWeightFloor : ℚ := 26801951/25000000
def vcM11CutMargins : Fin 3 → ℚ := ![113274277/5000000000, 98422257/5000000000, 15417241/1250000000]

theorem vcM11Cut_roots_ok : vcM11CutCell.rootsOK vcM11CutRoots = true := by decide +kernel

theorem vcM11Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM11CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM11Cut_margin_le (i : Fin 3) : curvatureLoss vcM11CutCell vcM11CutCaps i ≤ vcM11CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM12CutCell : ParameterCell := ⟨⟨1/20, 3/40⟩, ⟨11/40, 3/10⟩, ⟨0, 1/36⟩⟩
def vcM12CutRoots : Fin 3 → RatBounds := ![⟨451462299106527/281474976710656, 254675504028735/140737488355328⟩, ⟨201197913507243/140737488355328, 456467774653899/281474976710656⟩, ⟨147140653556525/140737488355328, 350624756538787/281474976710656⟩]
def vcM12CutCaps : Fin 3 → Fin 3 → ℚ := ![![1521976421/10000000, 11279694633/100000000, 811660579/10000000], ![6251372167/100000000, 6709265307/100000000, 941455543/25000000], ![4085037/250000, 195936791/12500000, 504999373/50000000]]
def vcM12CutWeightFloor : ℚ := 52274861/50000000
def vcM12CutMargins : Fin 3 → ℚ := ![183503427/10000000000, 15565733/1000000000, 102572969/10000000000]

theorem vcM12Cut_roots_ok : vcM12CutCell.rootsOK vcM12CutRoots = true := by decide +kernel

theorem vcM12Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM12CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM12Cut_margin_le (i : Fin 3) : curvatureLoss vcM12CutCell vcM12CutCaps i ≤ vcM12CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM13CutCell : ParameterCell := ⟨⟨1/20, 3/40⟩, ⟨11/40, 3/10⟩, ⟨1/36, 1/18⟩⟩
def vcM13CutRoots : Fin 3 → RatBounds := ![⟨447477637990883/281474976710656, 126153929003893/70368744177664⟩, ⟨198466606662697/140737488355328, 28123388735599/17592186044416⟩, ⟨288677084578925/281474976710656, 343675625409351/281474976710656⟩]
def vcM13CutCaps : Fin 3 → Fin 3 → ℚ := ![![8101145809/50000000, 2406348763/20000000, 8614697509/100000000], ![3320288251/50000000, 1421467447/20000000, 1994969643/50000000], ![146267371/10000000, 698423101/50000000, 449729819/50000000]]
def vcM13CutWeightFloor : ℚ := 109096513/100000000
def vcM13CutMargins : Fin 3 → ℚ := ![96283743/5000000000, 162996739/10000000000, 107149069/10000000000]

theorem vcM13Cut_roots_ok : vcM13CutCell.rootsOK vcM13CutRoots = true := by decide +kernel

theorem vcM13Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM13CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM13Cut_margin_le (i : Fin 3) : curvatureLoss vcM13CutCell vcM13CutCaps i ≤ vcM13CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM14CutCell : ParameterCell := ⟨⟨1/20, 3/40⟩, ⟨3/10, 13/40⟩, ⟨0, 1/36⟩⟩
def vcM14CutRoots : Fin 3 → RatBounds := ![⟨445853690745027/281474976710656, 501960826614323/281474976710656⟩, ⟨391501819705521/281474976710656, 110882776390849/70368744177664⟩, ⟨299489706836055/281474976710656, 177271589750983/140737488355328⟩]
def vcM14CutCaps : Fin 3 → Fin 3 → ℚ := ![![13453713557/100000000, 9696207857/100000000, 3632432201/50000000], ![1295469509/25000000, 5492985711/100000000, 407322057/12500000], ![1592854747/100000000, 186014621/12500000, 1026729949/100000000]]
def vcM14CutWeightFloor : ℚ := 106400117/100000000
def vcM14CutMargins : Fin 3 → ℚ := ![80476871/5000000000, 26603711/2000000000, 11514657/1250000000]

theorem vcM14Cut_roots_ok : vcM14CutCell.rootsOK vcM14CutRoots = true := by decide +kernel

theorem vcM14Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM14CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM14Cut_margin_le (i : Fin 3) : curvatureLoss vcM14CutCell vcM14CutCaps i ≤ vcM14CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM15CutCell : ParameterCell := ⟨⟨1/20, 3/40⟩, ⟨3/10, 13/40⟩, ⟨1/36, 1/18⟩⟩
def vcM15CutRoots : Fin 3 → RatBounds := ![⟨220980659623349/140737488355328, 497339343897023/281474976710656⟩, ⟨24127858812207/17592186044416, 109261727643009/70368744177664⟩, ⟨73474491772733/70368744177664, 347659089499929/281474976710656⟩]
def vcM15CutCaps : Fin 3 → Fin 3 → ℚ := ![![7161140787/50000000, 10343035009/100000000, 1931610797/25000000], ![22009071/400000, 5817041441/100000000, 3454156901/100000000], ![142510749/10000000, 331349751/25000000, 914114273/100000000]]
def vcM15CutWeightFloor : ℚ := 55500229/50000000
def vcM15CutMargins : Fin 3 → ℚ := ![84312271/5000000000, 139034153/10000000000, 96165127/10000000000]

theorem vcM15Cut_roots_ok : vcM15CutCell.rootsOK vcM15CutRoots = true := by decide +kernel

theorem vcM15Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM15CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM15Cut_margin_le (i : Fin 3) : curvatureLoss vcM15CutCell vcM15CutCaps i ≤ vcM15CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM16CutCell : ParameterCell := ⟨⟨1/20, 3/40⟩, ⟨13/40, 7/20⟩, ⟨0, 1/36⟩⟩
def vcM16CutRoots : Fin 3 → RatBounds := ![⟨220617610688501/140737488355328, 495994818472809/281474976710656⟩, ⟨190744691861831/140737488355328, 431893737931893/281474976710656⟩, ⟨76200770424989/70368744177664, 89725509102385/70368744177664⟩]
def vcM16CutCaps : Fin 3 → Fin 3 → ℚ := ![![1523154857/12500000, 2140815027/25000000, 6686943597/100000000], ![110674373/2500000, 230614107/5000000, 2918418037/100000000], ![156088113/10000000, 709013341/50000000, 261698563/25000000]]
def vcM16CutWeightFloor : ℚ := 108287807/100000000
def vcM16CutMargins : Fin 3 → ℚ := ![28967543/2000000000, 116610879/10000000000, 85138283/10000000000]

theorem vcM16Cut_roots_ok : vcM16CutCell.rootsOK vcM16CutRoots = true := by decide +kernel

theorem vcM16Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM16CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM16Cut_margin_le (i : Fin 3) : curvatureLoss vcM16CutCell vcM16CutCaps i ≤ vcM16CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM17CutCell : ParameterCell := ⟨⟨1/20, 3/40⟩, ⟨13/40, 7/20⟩, ⟨1/36, 1/18⟩⟩
def vcM17CutRoots : Fin 3 → RatBounds := ![⟨13669343583761/8796093022208, 491466443876691/281474976710656⟩, ⟨94008706126751/70368744177664, 212704741628733/140737488355328⟩, ⟨149612684660147/140737488355328, 352077344952705/281474976710656⟩]
def vcM17CutCaps : Fin 3 → Fin 3 → ℚ := ![![12976793251/100000000, 4567091887/50000000, 3565767843/50000000], ![117480287/2500000, 4883378553/100000000, 154720641/5000000], ![279182433/20000000, 25248109/2000000, 931775727/100000000]]
def vcM17CutWeightFloor : ℚ := 112936509/100000000
def vcM17CutMargins : Fin 3 → ℚ := ![75778723/5000000000, 24337637/2000000000, 44438629/5000000000]

theorem vcM17Cut_roots_ok : vcM17CutCell.rootsOK vcM17CutRoots = true := by decide +kernel

theorem vcM17Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM17CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM17Cut_margin_le (i : Fin 3) : curvatureLoss vcM17CutCell vcM17CutCaps i ≤ vcM17CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM18CutCell : ParameterCell := ⟨⟨1/20, 3/40⟩, ⟨7/20, 3/8⟩, ⟨0, 1/36⟩⟩
def vcM18CutRoots : Fin 3 → RatBounds := ![⟨109377900222795/70368744177664, 491295919214879/281474976710656⟩, ⟨372233485046527/281474976710656, 105340627138043/70368744177664⟩, ⟨77564767110071/70368744177664, 363701286397989/281474976710656⟩]
def vcM18CutCaps : Fin 3 → Fin 3 → ℚ := ![![11282835133/100000000, 1550139099/20000000, 6315201917/100000000], ![3886609739/100000000, 49491169/1250000, 2694320343/100000000], ![1536399687/100000000, 67773063/5000000, 1069932231/100000000]]
def vcM18CutWeightFloor : ℚ := 110226163/100000000
def vcM18CutMargins : Fin 3 → ℚ := ![66664979/5000000000, 104557797/10000000000, 10088307/1250000000]

theorem vcM18Cut_roots_ok : vcM18CutCell.rootsOK vcM18CutRoots = true := by decide +kernel

theorem vcM18Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM18CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM18Cut_margin_le (i : Fin 3) : curvatureLoss vcM18CutCell vcM18CutCaps i ≤ vcM18CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM19CutCell : ParameterCell := ⟨⟨1/20, 3/40⟩, ⟨7/20, 3/8⟩, ⟨1/36, 1/18⟩⟩
def vcM19CutRoots : Fin 3 → RatBounds := ![⟨433756640283565/281474976710656, 121710486226861/70368744177664⟩, ⟨366776320109603/281474976710656, 207435108303493/140737488355328⟩, ⟨152348197395057/140737488355328, 44616366444401/35184372088832⟩]
def vcM19CutCaps : Fin 3 → Fin 3 → ℚ := ![![12016147913/100000000, 8266566619/100000000, 674358809/10000000], ![8249187/200000, 2095644737/50000000, 2856906301/100000000], ![343387309/25000000, 603128649/50000000, 95221211/10000000]]
def vcM19CutWeightFloor : ℚ := 7182473/6250000
def vcM19CutMargins : Fin 3 → ℚ := ![13934751/1000000000, 108961427/10000000000, 10523501/1250000000]

theorem vcM19Cut_roots_ok : vcM19CutCell.rootsOK vcM19CutRoots = true := by decide +kernel

theorem vcM19Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM19CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM19Cut_margin_le (i : Fin 3) : curvatureLoss vcM19CutCell vcM19CutCaps i ≤ vcM19CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM20CutCell : ParameterCell := ⟨⟨1/20, 3/40⟩, ⟨3/8, 2/5⟩, ⟨0, 1/36⟩⟩
def vcM20CutRoots : Fin 3 → RatBounds := ![⟨434610514807797/281474976710656, 121937174686735/70368744177664⟩, ⟨363631409715105/281474976710656, 411785030479133/281474976710656⟩, ⟨157946804632519/140737488355328, 184475771405731/140737488355328⟩]
def vcM20CutCaps : Fin 3 → Fin 3 → ℚ := ![![10659941947/100000000, 7177334547/100000000, 244042321/4000000], ![1749798293/50000000, 3462307429/100000000, 510823919/20000000], ![303648861/20000000, 1299117787/100000000, 1096016803/100000000]]
def vcM20CutWeightFloor : ℚ := 56113977/50000000
def vcM20CutMargins : Fin 3 → ℚ := ![25052991/2000000000, 3826091/400000000, 3127589/400000000]

theorem vcM20Cut_roots_ok : vcM20CutCell.rootsOK vcM20CutRoots = true := by decide +kernel

theorem vcM20Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM20CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM20Cut_margin_le (i : Fin 3) : curvatureLoss vcM20CutCell vcM20CutCaps i ≤ vcM20CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM21CutCell : ParameterCell := ⟨⟨1/20, 3/40⟩, ⟨3/8, 2/5⟩, ⟨1/36, 1/18⟩⟩
def vcM21CutRoots : Fin 3 → RatBounds := ![⟨430902903722149/281474976710656, 241675945373403/140737488355328⟩, ⟨358168246125271/281474976710656, 202638911937039/140737488355328⟩, ⟨310346529245403/281474976710656, 90557708979461/70368744177664⟩]
def vcM21CutCaps : Fin 3 → Fin 3 → ℚ := ![![5677180247/50000000, 765369037/10000000, 52181679/800000], ![1856527547/50000000, 3664487661/100000000, 2707706561/100000000], ![54278397/4000000, 1155766253/100000000, 975311353/100000000]]
def vcM21CutWeightFloor : ℚ := 58481743/50000000
def vcM21CutMargins : Fin 3 → ℚ := ![130802147/10000000000, 99570703/10000000000, 81519567/10000000000]

theorem vcM21Cut_roots_ok : vcM21CutCell.rootsOK vcM21CutRoots = true := by decide +kernel

theorem vcM21Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM21CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM21Cut_margin_le (i : Fin 3) : curvatureLoss vcM21CutCell vcM21CutCaps i ≤ vcM21CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM22CutCell : ParameterCell := ⟨⟨1/20, 3/40⟩, ⟨2/5, 17/40⟩, ⟨0, 1/36⟩⟩
def vcM22CutRoots : Fin 3 → RatBounds := ![⟨216239153309225/140737488355328, 485270631782855/281474976710656⟩, ⟨355597592924447/281474976710656, 403039736639081/281474976710656⟩, ⟨321742461314667/281474976710656, 46834141434723/35184372088832⟩]
def vcM22CutCaps : Fin 3 → Fin 3 → ℚ := ![![1283475133/12500000, 849043201/12500000, 6024118583/100000000], ![1616323173/50000000, 1542744219/50000000, 497106923/20000000], ![301124263/20000000, 1248016649/100000000, 45001133/4000000]]
def vcM22CutWeightFloor : ℚ := 28576471/25000000
def vcM22CutMargins : Fin 3 → ℚ := ![14999257/1250000000, 89207777/10000000000, 38666317/5000000000]

theorem vcM22Cut_roots_ok : vcM22CutCell.rootsOK vcM22CutRoots = true := by decide +kernel

theorem vcM22Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM22CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM22Cut_margin_le (i : Fin 3) : curvatureLoss vcM22CutCell vcM22CutCaps i ≤ vcM22CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM23CutCell : ParameterCell := ⟨⟨1/20, 3/40⟩, ⟨2/5, 17/40⟩, ⟨1/36, 1/18⟩⟩
def vcM23CutRoots : Fin 3 → RatBounds := ![⟨214402420858817/140737488355328, 480914817275945/281474976710656⟩, ⟨175062825829133/140737488355328, 396511577403003/281474976710656⟩, ⟨316211122952013/281474976710656, 183998795506573/140737488355328⟩]
def vcM23CutCaps : Fin 3 → Fin 3 → ℚ := ![![2187875511/20000000, 11586183/160000, 6447645199/100000000], ![685859133/20000000, 3265910461/100000000, 2634569199/100000000], ![1345423759/100000000, 1110039259/100000000, 100105871/10000000]]
def vcM23CutWeightFloor : ℚ := 29770433/25000000
def vcM23CutMargins : Fin 3 → ℚ := ![25046391/2000000000, 46397241/5000000000, 40305037/5000000000]

theorem vcM23Cut_roots_ok : vcM23CutCell.rootsOK vcM23CutRoots = true := by decide +kernel

theorem vcM23Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM23CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM23Cut_margin_le (i : Fin 3) : curvatureLoss vcM23CutCell vcM23CutCaps i ≤ vcM23CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM24CutCell : ParameterCell := ⟨⟨1/20, 3/40⟩, ⟨17/40, 9/20⟩, ⟨0, 1/36⟩⟩
def vcM24CutRoots : Fin 3 → RatBounds := ![⟨215538496693071/140737488355328, 241903167082077/140737488355328⟩, ⟨348059778098459/281474976710656, 197514442359763/140737488355328⟩, ⟨327842480600061/281474976710656, 190447952335117/140737488355328⟩]
def vcM24CutCaps : Fin 3 → Fin 3 → ℚ := ![![10079812669/100000000, 3282507827/50000000, 3038586263/50000000], ![611935259/20000000, 1397859557/50000000, 1236866069/50000000], ![749007339/50000000, 1201413217/100000000, 1157042289/100000000]]
def vcM24CutWeightFloor : ℚ := 58236523/50000000
def vcM24CutMargins : Fin 3 → ℚ := ![58550351/5000000000, 42359223/5000000000, 77963687/10000000000]

theorem vcM24Cut_roots_ok : vcM24CutCell.rootsOK vcM24CutRoots = true := by decide +kernel

theorem vcM24Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM24CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM24Cut_margin_le (i : Fin 3) : curvatureLoss vcM24CutCell vcM24CutCaps i ≤ vcM24CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM25CutCell : ParameterCell := ⟨⟨1/20, 3/40⟩, ⟨17/40, 9/20⟩, ⟨1/36, 1/18⟩⟩
def vcM25CutRoots : Fin 3 → RatBounds := ![⟨427424973714303/281474976710656, 479476059655905/281474976710656⟩, ⟨5352762584045/4398046511104, 48559296102619/35184372088832⟩, ⟨80581663486929/70368744177664, 187130557478455/140737488355328⟩]
def vcM25CutCaps : Fin 3 → Fin 3 → ℚ := ![![429721241/4000000, 1399363537/20000000, 6511085629/100000000], ![1622654643/50000000, 184980839/6250000, 1310725873/50000000], ![669236237/50000000, 1068397613/100000000, 16086339/1562500]]
def vcM25CutWeightFloor : ℚ := 121287927/100000000
def vcM25CutMargins : Fin 3 → ℚ := ![122193559/10000000000, 22022501/2500000000, 20319447/2500000000]

theorem vcM25Cut_roots_ok : vcM25CutCell.rootsOK vcM25CutRoots = true := by decide +kernel

theorem vcM25Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM25CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM25Cut_margin_le (i : Fin 3) : curvatureLoss vcM25CutCell vcM25CutCaps i ≤ vcM25CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM26CutCell : ParameterCell := ⟨⟨1/20, 3/40⟩, ⟨9/20, 19/40⟩, ⟨0, 1/36⟩⟩
def vcM26CutRoots : Fin 3 → RatBounds := ![⟨107595566846287/70368744177664, 241661960364147/140737488355328⟩, ⟨340956099691479/281474976710656, 387673577208817/281474976710656⟩, ⟨167116406772493/140737488355328, 387659690021015/281474976710656⟩]
def vcM26CutCaps : Fin 3 → Fin 3 → ℚ := ![![10086929263/100000000, 3239607497/50000000, 3132277573/50000000], ![1488587353/50000000, 2590180431/100000000, 317513233/12500000], ![1495129579/100000000, 579369673/50000000, 1192226461/100000000]]
def vcM26CutWeightFloor : ℚ := 29685837/25000000
def vcM26CutMargins : Fin 3 → ℚ := ![11648393/1000000000, 16406153/2000000000, 10035689/1250000000]

theorem vcM26Cut_roots_ok : vcM26CutCell.rootsOK vcM26CutRoots = true := by decide +kernel

theorem vcM26Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM26CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM26Cut_margin_le (i : Fin 3) : curvatureLoss vcM26CutCell vcM26CutCaps i ≤ vcM26CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM27CutCell : ParameterCell := ⟨⟨1/20, 3/40⟩, ⟨9/20, 19/40⟩, ⟨1/36, 1/18⟩⟩
def vcM27CutRoots : Fin 3 → RatBounds := ![⟨426739308961807/281474976710656, 239502077610753/140737488355328⟩, ⟨335460301330399/281474976710656, 381087766582045/281474976710656⟩, ⟨328731902805747/281474976710656, 381061172789273/281474976710656⟩]
def vcM27CutCaps : Fin 3 → Fin 3 → ℚ := ![![1075815537/10000000, 3451435427/50000000, 839828569/12500000], ![24670661/781250, 548612951/20000000, 1345603323/50000000], ![333959703/25000000, 515161723/50000000, 265216903/25000000]]
def vcM27CutWeightFloor : ℚ := 24719261/20000000
def vcM27CutMargins : Fin 3 → ℚ := ![60801499/5000000000, 42648203/5000000000, 10468309/1250000000]

theorem vcM27Cut_roots_ok : vcM27CutCell.rootsOK vcM27CutRoots = true := by decide +kernel

theorem vcM27Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM27CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM27Cut_margin_le (i : Fin 3) : curvatureLoss vcM27CutCell vcM27CutCaps i ≤ vcM27CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM30CutCell : ParameterCell := ⟨⟨3/40, 1/10⟩, ⟨1/8, 3/20⟩, ⟨0, 1/36⟩⟩
def vcM30CutRoots : Fin 3 → RatBounds := ![⟨492994450610813/281474976710656, 569535052150979/281474976710656⟩, ⟨481469301267993/281474976710656, 556791247280649/281474976710656⟩, ⟨133557803327407/140737488355328, 84306643646153/70368744177664⟩]
def vcM30CutCaps : Fin 3 → Fin 3 → ℚ := ![![21497658231/100000000, 9020365201/50000000, 2928475533/50000000], ![5127879423/25000000, 10808895821/50000000, 7914859729/100000000], ![578467819/100000000, 605528623/100000000, 256231457/100000000]]
def vcM30CutWeightFloor : ℚ := 52096891/50000000
def vcM30CutMargins : Fin 3 → ℚ := ![66755209/2000000000, 63134513/2000000000, 110063641/10000000000]

theorem vcM30Cut_roots_ok : vcM30CutCell.rootsOK vcM30CutRoots = true := by decide +kernel

theorem vcM30Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM30CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM30Cut_margin_le (i : Fin 3) : curvatureLoss vcM30CutCell vcM30CutCaps i ≤ vcM30CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM32CutCell : ParameterCell := ⟨⟨3/40, 1/10⟩, ⟨3/20, 7/40⟩, ⟨0, 1/36⟩⟩
def vcM32CutRoots : Fin 3 → RatBounds := ![⟨479352350461079/281474976710656, 549505179973665/281474976710656⟩, ⟨115601450019495/70368744177664, 530921105222155/281474976710656⟩, ⟨272363033500273/281474976710656, 168981770902899/140737488355328⟩]
def vcM32CutCaps : Fin 3 → Fin 3 → ℚ := ![![31637859247/100000000, 13562418781/50000000, 303567297/2000000], ![443640351/1562500, 29698209169/100000000, 1882786617/12500000], ![11223373/781250, 1498390463/100000000, 343565459/50000000]]
def vcM32CutWeightFloor : ℚ := 3147103/3125000
def vcM32CutMargins : Fin 3 → ℚ := ![482846967/10000000000, 229191061/5000000000, 47438/1953125]

theorem vcM32Cut_roots_ok : vcM32CutCell.rootsOK vcM32CutRoots = true := by decide +kernel

theorem vcM32Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM32CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM32Cut_margin_le (i : Fin 3) : curvatureLoss vcM32CutCell vcM32CutCaps i ≤ vcM32CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM33CutCell : ParameterCell := ⟨⟨3/40, 1/10⟩, ⟨3/20, 7/40⟩, ⟨1/36, 1/18⟩⟩
def vcM33CutRoots : Fin 3 → RatBounds := ![⟨118652812188907/70368744177664, 543823916482763/281474976710656⟩, ⟨228530967522377/140737488355328, 524519636847493/281474976710656⟩, ⟨266797612824401/281474976710656, 41343156388207/35184372088832⟩]
def vcM33CutCaps : Fin 3 → Fin 3 → ℚ := ![![21847211461/100000000, 9026534507/50000000, 7941306679/100000000], ![9324862121/50000000, 19590852809/100000000, 2108649461/25000000], ![129796037/20000000, 677299363/100000000, 307445871/100000000]]
def vcM33CutWeightFloor : ℚ := 109511701/100000000
def vcM33CutMargins : Fin 3 → ℚ := ![64528353/2000000000, 150312867/5000000000, 130902089/10000000000]

theorem vcM33Cut_roots_ok : vcM33CutCell.rootsOK vcM33CutRoots = true := by decide +kernel

theorem vcM33Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM33CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM33Cut_margin_le (i : Fin 3) : curvatureLoss vcM33CutCell vcM33CutCaps i ≤ vcM33CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM34CutCell : ParameterCell := ⟨⟨3/40, 1/10⟩, ⟨7/40, 1/5⟩, ⟨0, 1/36⟩⟩
def vcM34CutRoots : Fin 3 → RatBounds := ![⟨467897775970289/281474976710656, 533160087059573/281474976710656⟩, ⟨222828907076327/140737488355328, 63616222244567/35184372088832⟩, ⟨69352517327365/70368744177664, 42434999619763/35184372088832⟩]
def vcM34CutCaps : Fin 3 → Fin 3 → ℚ := ![![36418314483/100000000, 6221047503/20000000, 10300648337/50000000], ![26315616087/100000000, 27380783957/100000000, 15910125571/100000000], ![244223783/12500000, 500919841/25000000, 64092059/6250000]]
def vcM34CutWeightFloor : ℚ := 49277927/50000000
def vcM34CutMargins : Fin 3 → ℚ := ![508953261/10000000000, 238123827/5000000000, 295136237/10000000000]

theorem vcM34Cut_roots_ok : vcM34CutCell.rootsOK vcM34CutRoots = true := by decide +kernel

theorem vcM34Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM34CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM34Cut_margin_le (i : Fin 3) : curvatureLoss vcM34CutCell vcM34CutCaps i ≤ vcM34CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM35CutCell : ParameterCell := ⟨⟨3/40, 1/10⟩, ⟨7/40, 1/5⟩, ⟨1/36, 1/18⟩⟩
def vcM35CutRoots : Fin 3 → RatBounds := ![⟨115837029873481/70368744177664, 527728960013983/281474976710656⟩, ⟨220173692156833/140737488355328, 502592845077089/281474976710656⟩, ⟨135925739393771/140737488355328, 332373028725521/281474976710656⟩]
def vcM35CutCaps : Fin 3 → Fin 3 → ℚ := ![![2982846607/12500000, 9871801343/50000000, 5669298067/50000000], ![17608707377/100000000, 18678009273/100000000, 9453330907/100000000], ![1197652259/100000000, 618502597/50000000, 305365879/50000000]]
def vcM35CutWeightFloor : ℚ := 10709493/10000000
def vcM35CutMargins : Fin 3 → ℚ := ![33554737/1000000000, 62419967/2000000000, 42081869/2500000000]

theorem vcM35Cut_roots_ok : vcM35CutCell.rootsOK vcM35CutRoots = true := by decide +kernel

theorem vcM35Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM35CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM35Cut_margin_le (i : Fin 3) : curvatureLoss vcM35CutCell vcM35CutCaps i ≤ vcM35CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM36CutCell : ParameterCell := ⟨⟨3/40, 1/10⟩, ⟨1/5, 9/40⟩, ⟨0, 1/36⟩⟩
def vcM36CutRoots : Fin 3 → RatBounds := ![⟨57278996408463/35184372088832, 259846456249383/140737488355328⟩, ⟨430772749379447/281474976710656, 122482932653023/70368744177664⟩, ⟨282350477209251/281474976710656, 42703682876703/35184372088832⟩]
def vcM36CutCaps : Fin 3 → Fin 3 → ℚ := ![![13392518933/50000000, 445736839/2000000, 1919592857/12500000], ![16558242053/100000000, 17479920447/100000000, 10324295733/100000000], ![366092313/20000000, 1856913681/100000000, 1021050883/100000000]]
def vcM36CutWeightFloor : ℚ := 78368/78125
def vcM36CutMargins : Fin 3 → ℚ := ![35627429/1000000000, 328587879/10000000000, 210481213/10000000000]

theorem vcM36Cut_roots_ok : vcM36CutCell.rootsOK vcM36CutRoots = true := by decide +kernel

theorem vcM36Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM36CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM36Cut_margin_le (i : Fin 3) : curvatureLoss vcM36CutCell vcM36CutCaps i ≤ vcM36CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM37CutCell : ParameterCell := ⟨⟨3/40, 1/10⟩, ⟨1/5, 9/40⟩, ⟨1/36, 1/18⟩⟩
def vcM37CutRoots : Fin 3 → RatBounds := ![⟨226922932122543/140737488355328, 32154444870845/17592186044416⟩, ⟨425484596047475/281474976710656, 241819045181859/140737488355328⟩, ⟨138401629835485/140737488355328, 41827566662335/35184372088832⟩]
def vcM37CutCaps : Fin 3 → Fin 3 → ℚ := ![![5726721701/20000000, 11918823941/50000000, 4068906133/25000000], ![17689370499/100000000, 3728310217/20000000, 10928464221/100000000], ![164380989/10000000, 1661291763/100000000, 455727791/50000000]]
def vcM37CutWeightFloor : ℚ := 104527221/100000000
def vcM37CutMargins : Fin 3 → ℚ := ![188876461/5000000000, 86973001/2500000000, 221322989/10000000000]

theorem vcM37Cut_roots_ok : vcM37CutCell.rootsOK vcM37CutRoots = true := by decide +kernel

theorem vcM37Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM37CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM37Cut_margin_le (i : Fin 3) : curvatureLoss vcM37CutCell vcM37CutCaps i ≤ vcM37CutMargins i := by
  fin_cases i <;> decide +kernel


end HlawkaSchatten.BelowExponent.Vertex
