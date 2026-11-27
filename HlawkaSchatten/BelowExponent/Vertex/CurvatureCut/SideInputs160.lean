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

def scS160CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨29/80, 3/8⟩, ⟨0, 1/40⟩⟩
def scS160CutRoots : Fin 3 → RatBounds := ![⟨236645947691755/140737488355328, 505704501908723/281474976710656⟩, ⟨394182512536465/281474976710656, 105909884355193/70368744177664⟩, ⟨80043877449567/70368744177664, 21973740466143/17592186044416⟩]
def scS160CutCaps : Fin 3 → Fin 3 → ℚ := ![![8379775053/100000000, 2631254333/50000000, 320581761/10000000], ![1593051329/50000000, 3140435621/100000000, 809068943/50000000], ![538144031/50000000, 228294549/25000000, 133637189/20000000]]
def scS160CutWeightFloor : ℚ := 113749191/100000000
def scS160CutMargins : Fin 3 → ℚ := ![15499053/5000000000, 11773103/5000000000, 14641991/10000000000]

theorem scS160Cut_roots_ok : scS160CutCell.rootsOK scS160CutRoots = true := by decide +kernel

theorem scS160Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS160CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS160Cut_margin_le (i : Fin 3) : curvatureLoss scS160CutCell scS160CutCaps i ≤ scS160CutMargins i := by
  fin_cases i <;> decide +kernel

def scS161CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨29/80, 3/8⟩, ⟨1/40, 1/20⟩⟩
def scS161CutRoots : Fin 3 → RatBounds := ![⟨469955454364257/281474976710656, 250918951416701/140737488355328⟩, ⟨194393282674837/140737488355328, 26093259840155/17592186044416⟩, ⟨157366439632993/140737488355328, 43160951352041/35184372088832⟩]
def scS161CutCaps : Fin 3 → Fin 3 → ℚ := ![![4382180893/50000000, 2765442913/50000000, 33709869/1000000], ![3335179661/100000000, 655472227/20000000, 338412677/20000000], ![963099459/100000000, 814296091/100000000, 74509687/12500000]]
def scS161CutWeightFloor : ℚ := 29649553/25000000
def scS161CutMargins : Fin 3 → ℚ := ![7789033/2500000000, 1472831/625000000, 7272813/5000000000]

theorem scS161Cut_roots_ok : scS161CutCell.rootsOK scS161CutRoots = true := by decide +kernel

theorem scS161Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS161CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS161Cut_margin_le (i : Fin 3) : curvatureLoss scS161CutCell scS161CutCaps i ≤ scS161CutMargins i := by
  fin_cases i <;> decide +kernel

def scS162CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨29/80, 3/8⟩, ⟨1/20, 3/40⟩⟩
def scS162CutRoots : Fin 3 → RatBounds := ![⟨466878272090137/281474976710656, 249145387642525/140737488355328⟩, ⟨191921717493377/140737488355328, 12871379866585/8796093022208⟩, ⟨309758672818079/281474976710656, 339561400415819/281474976710656⟩]
def scS162CutCaps : Fin 3 → Fin 3 → ℚ := ![![1829489341/20000000, 724577537/12500000, 441845357/12500000], ![3483023003/100000000, 682664167/20000000, 1765326081/100000000], ![216563313/25000000, 2852069/390625, 534679793/100000000]]
def scS162CutWeightFloor : ℚ := 61730147/50000000
def scS162CutMargins : Fin 3 → ℚ := ![3143649/1000000000, 4738461/2000000000, 14528923/10000000000]

theorem scS162Cut_roots_ok : scS162CutCell.rootsOK scS162CutRoots = true := by decide +kernel

theorem scS162Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS162CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS162Cut_margin_le (i : Fin 3) : curvatureLoss scS162CutCell scS162CutCaps i ≤ scS162CutMargins i := by
  fin_cases i <;> decide +kernel

def scS163CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨29/80, 3/8⟩, ⟨3/40, 1/10⟩⟩
def scS163CutRoots : Fin 3 → RatBounds := ![⟨116007744269359/70368744177664, 15469522349529/8796093022208⟩, ⟨379297872986257/281474976710656, 406746836375249/281474976710656⟩, ⟨305194710794769/281474976710656, 334327851425581/281474976710656⟩]
def scS163CutCaps : Fin 3 → Fin 3 → ℚ := ![![9529154281/100000000, 6060011909/100000000, 3697310157/100000000], ![1814870033/50000000, 3548396333/100000000, 1837984741/100000000], ![195705479/25000000, 657958123/100000000, 9640289/2000000]]
def scS163CutWeightFloor : ℚ := 128333289/100000000
def scS163CutMargins : Fin 3 → ℚ := ![15908381/5000000000, 23906721/10000000000, 14576861/10000000000]

theorem scS163Cut_roots_ok : scS163CutCell.rootsOK scS163CutRoots = true := by decide +kernel

theorem scS163Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS163CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS163Cut_margin_le (i : Fin 3) : curvatureLoss scS163CutCell scS163CutCaps i ≤ scS163CutMargins i := by
  fin_cases i <;> decide +kernel

def scS164CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨3/8, 31/80⟩, ⟨0, 1/40⟩⟩
def scS164CutRoots : Fin 3 → RatBounds := ![⟨471142220523509/281474976710656, 503261276724369/281474976710656⟩, ⟨389163837628197/281474976710656, 418254581469875/281474976710656⟩, ⟨322987678005047/281474976710656, 177102254176171/140737488355328⟩]
def scS164CutCaps : Fin 3 → Fin 3 → ℚ := ![![4027348393/50000000, 499734267/10000000, 156876659/5000000], ![1511323791/50000000, 731673851/25000000, 64270419/4000000], ![535580731/50000000, 893861657/100000000, 338948629/50000000]]
def scS164CutWeightFloor : ℚ := 57374137/50000000
def scS164CutMargins : Fin 3 → ℚ := ![1875243/625000000, 5614983/2500000000, 14562271/10000000000]

theorem scS164Cut_roots_ok : scS164CutCell.rootsOK scS164CutRoots = true := by decide +kernel

theorem scS164Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS164CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS164Cut_margin_le (i : Fin 3) : curvatureLoss scS164CutCell scS164CutCaps i ≤ scS164CutMargins i := by
  fin_cases i <;> decide +kernel

def scS165CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨3/8, 31/80⟩, ⟨1/40, 1/20⟩⟩
def scS165CutRoots : Fin 3 → RatBounds := ![⟨233917161471267/140737488355328, 62428349609355/35184372088832⟩, ⟨383772566262609/281474976710656, 103027763852035/70368744177664⟩, ⟨317551117151811/281474976710656, 347928463023985/281474976710656⟩]
def scS165CutCaps : Fin 3 → Fin 3 → ℚ := ![![8424172837/100000000, 1050404777/20000000, 16504209/500000], ![3164104409/100000000, 1527138789/50000000, 209988127/12500000], ![958350311/100000000, 159389037/20000000, 302337241/50000000]]
def scS165CutWeightFloor : ℚ := 119618367/100000000
def scS165CutMargins : Fin 3 → ℚ := ![15060233/5000000000, 1122469/500000000, 14452041/10000000000]

theorem scS165Cut_roots_ok : scS165CutCell.rootsOK scS165CutRoots = true := by decide +kernel

theorem scS165Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS165CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS165Cut_margin_le (i : Fin 3) : curvatureLoss scS165CutCell scS165CutCaps i ≤ scS165CutMargins i := by
  fin_cases i <;> decide +kernel

def scS166CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨3/8, 31/80⟩, ⟨1/20, 3/40⟩⟩
def scS166CutRoots : Fin 3 → RatBounds := ![⟨232391761400023/140737488355328, 495909339107207/281474976710656⟩, ⟨189417272704153/140737488355328, 406507584663421/281474976710656⟩, ⟨156291041158811/140737488355328, 342216507051979/281474976710656⟩]
def scS166CutCaps : Fin 3 → Fin 3 → ℚ := ![![4396124153/50000000, 1376049389/25000000, 692553619/20000000], ![826096097/25000000, 795240397/25000000, 13690701/781250], ![861846267/100000000, 714466627/100000000, 542335371/100000000]]
def scS166CutWeightFloor : ℚ := 12450213/10000000
def scS166CutMargins : Fin 3 → ℚ := ![3035941/1000000000, 5636243/2500000000, 1442289/1000000000]

theorem scS166Cut_roots_ok : scS166CutCell.rootsOK scS166CutRoots = true := by decide +kernel

theorem scS166Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS166CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS166Cut_margin_le (i : Fin 3) : curvatureLoss scS166CutCell scS166CutCaps i ≤ scS166CutMargins i := by
  fin_cases i <;> decide +kernel

def scS167CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨3/8, 31/80⟩, ⟨3/40, 1/10⟩⟩
def scS167CutRoots : Fin 3 → RatBounds := ![⟨115490172603563/70368744177664, 492670774273497/281474976710656⟩, ⟨187147199184781/140737488355328, 401375290836853/281474976710656⟩, ⟨308022535847695/281474976710656, 336995567282805/281474976710656⟩]
def scS167CutCaps : Fin 3 → Fin 3 → ℚ := ![![9159037607/100000000, 5754148343/100000000, 362347573/10000000], ![3443588917/100000000, 82670529/2500000, 912164437/50000000], ![778725147/100000000, 643754291/100000000, 24443427/5000000]]
def scS167CutWeightFloor : ℚ := 25879463/20000000
def scS167CutMargins : Fin 3 → ℚ := ![3837287/1250000000, 22726537/10000000000, 14459529/10000000000]

theorem scS167Cut_roots_ok : scS167CutCell.rootsOK scS167CutRoots = true := by decide +kernel

theorem scS167Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS167CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS167Cut_margin_le (i : Fin 3) : curvatureLoss scS167CutCell scS167CutCaps i ≤ scS167CutMargins i := by
  fin_cases i <;> decide +kernel

def scS168CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨31/80, 2/5⟩, ⟨0, 1/40⟩⟩
def scS168CutRoots : Fin 3 → RatBounds := ![⟨14663984247835/8796093022208, 501124195721249/281474976710656⟩, ⟨384345847352961/281474976710656, 206557940334887/140737488355328⟩, ⟨325859131590721/281474976710656, 356928358672005/281474976710656⟩]
def scS168CutCaps : Fin 3 → Fin 3 → ℚ := ![![7769721973/100000000, 4764388609/100000000, 1540982803/50000000], ![2882288331/100000000, 547187367/20000000, 801204241/50000000], ![106669841/10000000, 175066301/20000000, 687946967/100000000]]
def scS168CutWeightFloor : ℚ := 115768419/100000000
def scS168CutMargins : Fin 3 → ℚ := ![29138289/10000000000, 21487601/10000000000, 7261877/5000000000]

theorem scS168Cut_roots_ok : scS168CutCell.rootsOK scS168CutRoots = true := by decide +kernel

theorem scS168Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS168CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS168Cut_margin_le (i : Fin 3) : curvatureLoss scS168CutCell scS168CutCaps i ≤ scS168CutMargins i := by
  fin_cases i <;> decide +kernel

def scS169CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨31/80, 2/5⟩, ⟨1/40, 1/20⟩⟩
def scS169CutRoots : Fin 3 → RatBounds := ![⟨465964754626109/281474976710656, 31082373097717/17592186044416⟩, ⟨189479021669521/140737488355328, 101743612561859/70368744177664⟩, ⟨320428548933991/281474976710656, 350667684457439/281474976710656⟩]
def scS169CutCaps : Fin 3 → Fin 3 → ℚ := ![![8126059819/100000000, 5006966609/100000000, 3244003251/100000000], ![603434081/20000000, 571038471/20000000, 52346131/3125000], ![95421473/10000000, 390156403/50000000, 613578797/100000000]]
def scS169CutWeightFloor : ℚ := 120660163/100000000
def scS169CutMargins : Fin 3 → ℚ := ![1168757/400000000, 10725987/5000000000, 7200581/5000000000]

theorem scS169Cut_roots_ok : scS169CutCell.rootsOK scS169CutRoots = true := by decide +kernel

theorem scS169Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS169CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS169Cut_margin_le (i : Fin 3) : curvatureLoss scS169CutCell scS169CutCaps i ≤ scS169CutMargins i := by
  fin_cases i <;> decide +kernel

def scS170CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨31/80, 2/5⟩, ⟨1/20, 3/40⟩⟩
def scS170CutRoots : Fin 3 → RatBounds := ![⟨115734301263779/70368744177664, 246913305701185/140737488355328⟩, ⟨374023992653985/281474976710656, 401373866169437/281474976710656⟩, ⟨78866146188405/70368744177664, 344969215524959/281474976710656⟩]
def scS170CutCaps : Fin 3 → Fin 3 → ℚ := ![![4240541389/50000000, 5247156703/100000000, 3404664221/100000000], ![126036999/4000000, 2973609599/100000000, 436780963/25000000], ![858007811/100000000, 699462359/100000000, 110054249/20000000]]
def scS170CutWeightFloor : ℚ := 15695773/12500000
def scS170CutMargins : Fin 3 → ℚ := ![229859/78125000, 10760367/5000000000, 14361081/10000000000]

theorem scS170Cut_roots_ok : scS170CutCell.rootsOK scS170CutRoots = true := by decide +kernel

theorem scS170Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS170CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS170Cut_margin_le (i : Fin 3) : curvatureLoss scS170CutCell scS170CutCaps i ≤ scS170CutMargins i := by
  fin_cases i <;> decide +kernel

def scS171CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨31/80, 2/5⟩, ⟨3/40, 1/10⟩⟩
def scS171CutRoots : Fin 3 → RatBounds := ![⟨460135930810943/281474976710656, 61326529221885/35184372088832⟩, ⟨184744092593279/140737488355328, 396245057260407/281474976710656⟩, ⟨77727336539177/70368744177664, 339760165562907/281474976710656⟩]
def scS171CutCaps : Fin 3 → Fin 3 → ℚ := ![![552181059/6250000, 1097046033/20000000, 1782055907/50000000], ![410456029/12500000, 61825121/2000000, 1818602799/100000000], ![775156273/100000000, 78769547/12500000, 123994817/25000000]]
def scS171CutWeightFloor : ℚ := 130484133/100000000
def scS171CutMargins : Fin 3 → ℚ := ![14862471/5000000000, 21674047/10000000000, 14387953/10000000000]

theorem scS171Cut_roots_ok : scS171CutCell.rootsOK scS171CutRoots = true := by decide +kernel

theorem scS171Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS171CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS171Cut_margin_le (i : Fin 3) : curvatureLoss scS171CutCell scS171CutCaps i ≤ scS171CutMargins i := by
  fin_cases i <;> decide +kernel

def scS172CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨2/5, 33/80⟩, ⟨0, 1/40⟩⟩
def scS172CutRoots : Fin 3 → RatBounds := ![⟨58449703455609/35184372088832, 499280370890245/281474976710656⟩, ⟨189857112277379/140737488355328, 408205892031341/281474976710656⟩, ⟨164397225878627/140737488355328, 11242328238815/8796093022208⟩]
def scS172CutCaps : Fin 3 → Fin 3 → ℚ := ![![940071641/12500000, 569970471/12500000, 1519089119/50000000], ![2762483193/100000000, 641291479/25000000, 802373829/50000000], ![1062858003/100000000, 42876181/5000000, 174583869/25000000]]
def scS172CutWeightFloor : ℚ := 58405627/50000000
def scS172CutMargins : Fin 3 → ℚ := ![28387673/10000000000, 10307641/5000000000, 14523961/10000000000]

theorem scS172Cut_roots_ok : scS172CutCell.rootsOK scS172CutRoots = true := by decide +kernel

theorem scS172Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS172CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS172Cut_margin_le (i : Fin 3) : curvatureLoss scS172CutCell scS172CutCaps i ≤ scS172CutMargins i := by
  fin_cases i <;> decide +kernel

def scS173CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨2/5, 33/80⟩, ⟨1/40, 1/20⟩⟩
def scS173CutRoots : Fin 3 → RatBounds := ![⟨464336763290631/281474976710656, 123874667795741/70368744177664⟩, ⟨374328784962449/281474976710656, 402064931942327/281474976710656⟩, ⟨80842427265457/70368744177664, 353508379867189/281474976710656⟩]
def scS173CutCaps : Fin 3 → Fin 3 → ℚ := ![![7865536763/100000000, 4791637761/100000000, 319950229/10000000], ![2891718007/100000000, 10456947/390625, 209653409/12500000], ![950655239/100000000, 5971409/781250, 311395519/50000000]]
def scS173CutWeightFloor : ℚ := 30431321/25000000
def scS173CutMargins : Fin 3 → ℚ := ![14218629/5000000000, 20558551/10000000000, 7195209/5000000000]

theorem scS173Cut_roots_ok : scS173CutCell.rootsOK scS173CutRoots = true := by decide +kernel

theorem scS173Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS173CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS173Cut_margin_le (i : Fin 3) : curvatureLoss scS173CutCell scS173CutCaps i ≤ scS173CutMargins i := by
  fin_cases i <;> decide +kernel

def scS174CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨2/5, 33/80⟩, ⟨1/20, 3/40⟩⟩
def scS174CutRoots : Fin 3 → RatBounds := ![⟨461329432657913/281474976710656, 246014985106447/140737488355328⟩, ⟨369397663369711/281474976710656, 198232856864379/140737488355328⟩, ⟨318410671366547/281474976710656, 347822629433545/281474976710656⟩]
def scS174CutCaps : Fin 3 → Fin 3 → ℚ := ![![4104628711/50000000, 1255307467/25000000, 335945019/10000000], ![301986807/10000000, 1394002787/50000000, 1749103377/100000000], ![85470343/10000000, 137012623/20000000, 558488147/100000000]]
def scS174CutWeightFloor : ℚ := 25330839/20000000
def scS174CutMargins : Fin 3 → ℚ := ![28609257/10000000000, 20604469/10000000000, 14340833/10000000000]

theorem scS174Cut_roots_ok : scS174CutCell.rootsOK scS174CutRoots = true := by decide +kernel

theorem scS174Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS174CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS174Cut_margin_le (i : Fin 3) : curvatureLoss scS174CutCell scS174CutCaps i ≤ scS174CutMargins i := by
  fin_cases i <;> decide +kernel

def scS175CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨2/5, 33/80⟩, ⟨3/40, 1/10⟩⟩
def scS175CutRoots : Fin 3 → RatBounds := ![⟨458546904951255/281474976710656, 122209147537467/70368744177664⟩, ⟨364865211790679/281474976710656, 391338964120127/281474976710656⟩, ⟨78464898227725/70368744177664, 342624748203455/281474976710656⟩]
def scS175CutCaps : Fin 3 → Fin 3 → ℚ := ![![8551834427/100000000, 5248799547/100000000, 3518185487/100000000], ![1573512527/50000000, 2898309353/100000000, 1820424769/100000000], ![193020879/25000000, 24684597/4000000, 10066949/2000000]]
def scS175CutWeightFloor : ℚ := 131595539/100000000
def scS175CutMargins : Fin 3 → ℚ := ![14440619/5000000000, 20733533/10000000000, 897461/625000000]

theorem scS175Cut_roots_ok : scS175CutCell.rootsOK scS175CutRoots = true := by decide +kernel

theorem scS175Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS175CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS175Cut_margin_le (i : Fin 3) : curvatureLoss scS175CutCell scS175CutCaps i ≤ scS175CutMargins i := by
  fin_cases i <;> decide +kernel

def scS176CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨33/80, 17/40⟩, ⟨0, 1/40⟩⟩
def scS176CutRoots : Fin 3 → RatBounds := ![⟨29136502307695/17592186044416, 497718964133201/281474976710656⟩, ⟨375255979977889/281474976710656, 201754446003797/140737488355328⟩, ⟨331798341934833/281474976710656, 181343264075575/140737488355328⟩]
def scS176CutCaps : Fin 3 → Fin 3 → ℚ := ![![292149181/4000000, 1095062129/25000000, 187841179/6250000], ![332645753/12500000, 150742687/6250000, 806785637/50000000], ![1059606129/100000000, 6565481/781250, 709065627/100000000]]
def scS176CutWeightFloor : ℚ := 2357569/2000000
def scS176CutMargins : Fin 3 → ℚ := ![1387043/500000000, 19831363/10000000000, 14561119/10000000000]

theorem scS176Cut_roots_ok : scS176CutCell.rootsOK scS176CutRoots = true := by decide +kernel

theorem scS176Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS176CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS176Cut_margin_le (i : Fin 3) : curvatureLoss scS176CutCell scS176CutCaps i ≤ scS176CutMargins i := by
  fin_cases i <;> decide +kernel

def scS177CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨33/80, 17/40⟩, ⟨1/40, 1/20⟩⟩
def scS177CutRoots : Fin 3 → RatBounds := ![⟨462941861871421/281474976710656, 493958180237217/281474976710656⟩, ⟨369871897659103/281474976710656, 397366894650827/281474976710656⟩, ⟨326379255202055/281474976710656, 178227063775175/140737488355328⟩]
def scS177CutCaps : Fin 3 → Fin 3 → ℚ := ![![7638912677/100000000, 2301328459/50000000, 791651051/25000000], ![2785585433/100000000, 62925633/2500000, 1686141593/100000000], ![189528117/20000000, 93622029/12500000, 31615701/5000000]]
def scS177CutWeightFloor : ℚ := 122815457/100000000
def scS177CutMargins : Fin 3 → ℚ := ![2776379/1000000000, 19757007/10000000000, 14417973/10000000000]

theorem scS177Cut_roots_ok : scS177CutCell.rootsOK scS177CutRoots = true := by decide +kernel

theorem scS177Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS177CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS177Cut_margin_le (i : Fin 3) : curvatureLoss scS177CutCell scS177CutCaps i ≤ scS177CutMargins i := by
  fin_cases i <;> decide +kernel

def scS178CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨33/80, 17/40⟩, ⟨1/20, 3/40⟩⟩
def scS178CutRoots : Fin 3 → RatBounds := ![⟨14373493859397/8796093022208, 122627200443023/70368744177664⟩, ⟨91235688316203/70368744177664, 391767630871497/281474976710656⟩, ⟨321424957484217/281474976710656, 175390160156509/140737488355328⟩]
def scS178CutCaps : Fin 3 → Fin 3 → ℚ := ![![1993228093/25000000, 2411438701/50000000, 3326368923/100000000], ![363619621/12500000, 16383931/625000, 175812187/10000000], ![425952197/50000000, 671221569/100000000, 283494413/50000000]]
def scS178CutWeightFloor : ℚ := 127767947/100000000
def scS178CutMargins : Fin 3 → ℚ := ![5581831/2000000000, 989179/500000000, 14360247/10000000000]

theorem scS178Cut_roots_ok : scS178CutCell.rootsOK scS178CutRoots = true := by decide +kernel

theorem scS178Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS178CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS178Cut_margin_le (i : Fin 3) : curvatureLoss scS178CutCell scS178CutCaps i ≤ scS178CutMargins i := by
  fin_cases i <;> decide +kernel

def scS179CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨33/80, 17/40⟩, ⟨3/40, 1/10⟩⟩
def scS179CutRoots : Fin 3 → RatBounds := ![⟨457185289696471/281474976710656, 487333329492179/281474976710656⟩, ⟨90103189282209/70368744177664, 193320808415067/140737488355328⟩, ⟨39609731519425/35184372088832, 172796439957089/140737488355328⟩]
def scS179CutCaps : Fin 3 → Fin 3 → ℚ := ![![8305822549/100000000, 2520579501/50000000, 1742458713/50000000], ![1515684193/50000000, 2725151143/100000000, 1829558721/100000000], ![384740193/50000000, 120917277/20000000, 510975751/100000000]]
def scS179CutWeightFloor : ℚ := 33183343/25000000
def scS179CutMargins : Fin 3 → ℚ := ![28154517/10000000000, 9945953/5000000000, 2874367/2000000000]

theorem scS179Cut_roots_ok : scS179CutCell.rootsOK scS179CutRoots = true := by decide +kernel

theorem scS179Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS179CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS179Cut_margin_le (i : Fin 3) : curvatureLoss scS179CutCell scS179CutCaps i ≤ scS179CutMargins i := by
  fin_cases i <;> decide +kernel

def scS180CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨17/40, 7/16⟩, ⟨0, 1/40⟩⟩
def scS180CutRoots : Fin 3 → RatBounds := ![⟨58124940894519/35184372088832, 248215498836823/140737488355328⟩, ⟨370959288921893/281474976710656, 99752687745631/70368744177664⟩, ⟨334875667662047/281474976710656, 365728508532829/281474976710656⟩]
def scS180CutCaps : Fin 3 → Fin 3 → ℚ := ![![7116304757/100000000, 4223169869/100000000, 2983291923/100000000], ![2576666013/100000000, 1136990387/50000000, 407194921/25000000], ![105691469/10000000, 823855539/100000000, 720142599/100000000]]
def scS180CutWeightFloor : ℚ := 14871467/12500000
def scS180CutMargins : Fin 3 → ℚ := ![2718873/1000000000, 19126119/10000000000, 14634067/10000000000]

theorem scS180Cut_roots_ok : scS180CutCell.rootsOK scS180CutRoots = true := by decide +kernel

theorem scS180Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS180CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS180Cut_margin_le (i : Fin 3) : curvatureLoss scS180CutCell scS180CutCaps i ≤ scS180CutMargins i := by
  fin_cases i <;> decide +kernel

def scS181CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨17/40, 7/16⟩, ⟨1/40, 1/20⟩⟩
def scS181CutRoots : Fin 3 → RatBounds := ![⟨28860808165161/17592186044416, 492687615816691/281474976710656⟩, ⟨365575644044331/281474976710656, 49108289131921/35184372088832⟩, ⟨82365501893393/70368744177664, 179754495683883/140737488355328⟩]
def scS181CutCaps : Fin 3 → Fin 3 → ℚ := ![![930395371/12500000, 2218608621/50000000, 1572389883/50000000], ![168564017/6250000, 1186566213/50000000, 1701714081/100000000], ![945145029/100000000, 7341749/1000000, 321076341/50000000]]
def scS181CutWeightFloor : ℚ := 123932469/100000000
def scS181CutMargins : Fin 3 → ℚ := ![27188999/10000000000, 9518603/5000000000, 14482627/10000000000]

theorem scS181Cut_roots_ok : scS181CutCell.rootsOK scS181CutRoots = true := by decide +kernel

theorem scS181Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS181CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS181Cut_margin_le (i : Fin 3) : curvatureLoss scS181CutCell scS181CutCaps i ≤ scS181CutMargins i := by
  fin_cases i <;> decide +kernel

def scS182CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨17/40, 7/16⟩, ⟨1/20, 3/40⟩⟩
def scS182CutRoots : Fin 3 → RatBounds := ![⟨114699317276399/70368744177664, 122313578668615/70368744177664⟩, ⟨360647606257093/281474976710656, 387265689247123/281474976710656⟩, ⟨324512221355521/281474976710656, 88461584965521/70368744177664⟩]
def scS182CutCaps : Fin 3 → Fin 3 → ℚ := ![![7768885933/100000000, 581144989/12500000, 3304877571/100000000], ![704091559/25000000, 494317301/20000000, 110879309/6250000], ![169917409/20000000, 657895929/100000000, 71972247/12500000]]
def scS182CutWeightFloor : ℚ := 64454641/50000000
def scS182CutMargins : Fin 3 → ℚ := ![682793/250000000, 119047/62500000, 14418083/10000000000]

theorem scS182Cut_roots_ok : scS182CutCell.rootsOK scS182CutRoots = true := by decide +kernel

theorem scS182Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS182CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS182Cut_margin_le (i : Fin 3) : curvatureLoss scS182CutCell scS182CutCaps i ≤ scS182CutMargins i := by
  fin_cases i <;> decide +kernel

def scS183CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨17/40, 7/16⟩, ⟨3/40, 1/10⟩⟩
def scS183CutRoots : Fin 3 → RatBounds := ![⟨228022051397987/140737488355328, 486093743370331/281474976710656⟩, ⟨356119241002503/281474976710656, 191069588705519/140737488355328⟩, ⟨159984431581655/140737488355328, 174334300295775/140737488355328⟩]
def scS183CutCaps : Fin 3 → Fin 3 → ℚ := ![![202339087/2500000, 2429618867/50000000, 3463751203/100000000], ![586955257/20000000, 32117451/1250000, 1845889069/100000000], ![153465013/20000000, 9258317/1562500, 25943431/5000000]]
def scS183CutWeightFloor : ℚ := 133899527/100000000
def scS183CutMargins : Fin 3 → ℚ := ![13767227/5000000000, 19138209/10000000000, 14424053/10000000000]

theorem scS183Cut_roots_ok : scS183CutCell.rootsOK scS183CutRoots = true := by decide +kernel

theorem scS183Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS183CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS183Cut_margin_le (i : Fin 3) : curvatureLoss scS183CutCell scS183CutCaps i ≤ scS183CutMargins i := by
  fin_cases i <;> decide +kernel

def scS184CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨7/16, 9/20⟩, ⟨0, 1/40⟩⟩
def scS184CutRoots : Fin 3 → RatBounds := ![⟨464038175619169/281474976710656, 495409202013773/281474976710656⟩, ⟨366813350807463/281474976710656, 197349371311059/140737488355328⟩, ⟨169015748200575/140737488355328, 368885031895445/281474976710656⟩]
def scS184CutCaps : Fin 3 → Fin 3 → ℚ := ![![6955951913/100000000, 4086310373/100000000, 74283469/2500000], ![1253824089/50000000, 429935143/20000000, 330074561/20000000], ![527380487/50000000, 32316059/4000000, 182893467/25000000]]
def scS184CutWeightFloor : ℚ := 7505807/6250000
def scS184CutMargins : Fin 3 → ℚ := ![5344783/2000000000, 18491391/10000000000, 7371101/5000000000]

theorem scS184Cut_roots_ok : scS184CutCell.rootsOK scS184CutRoots = true := by decide +kernel

theorem scS184Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS184CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS184Cut_margin_le (i : Fin 3) : curvatureLoss scS184CutCell scS184CutCaps i ≤ scS184CutMargins i := by
  fin_cases i <;> decide +kernel

def scS185CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨7/16, 9/20⟩, ⟨1/40, 1/20⟩⟩
def scS185CutRoots : Fin 3 → RatBounds := ![⟨460824110076841/281474976710656, 122919946781639/70368744177664⟩, ⟨90357325875713/70368744177664, 194275276635031/140737488355328⟩, ⟨332622988257335/281474976710656, 11333673131041/8796093022208⟩]
def scS185CutCaps : Fin 3 → Fin 3 → ℚ := ![![909478739/12500000, 214649491/5000000, 626736969/20000000], ![328079651/12500000, 2243437341/100000000, 861971701/50000000], ![943147769/100000000, 14397921/2000000, 326157027/50000000]]
def scS185CutWeightFloor : ℚ := 3908693/3125000
def scS185CutMargins : Fin 3 → ℚ := ![3338149/1250000000, 2298831/1250000000, 14583759/10000000000]

theorem scS185Cut_roots_ok : scS185CutCell.rootsOK scS185CutRoots = true := by decide +kernel

theorem scS185Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS185CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS185Cut_margin_le (i : Fin 3) : curvatureLoss scS185CutCell scS185CutCaps i ≤ scS185CutMargins i := by
  fin_cases i <;> decide +kernel

def scS186CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨7/16, 9/20⟩, ⟨1/20, 3/40⟩⟩
def scS186CutRoots : Fin 3 → RatBounds := ![⟨457860028510389/281474976710656, 244129695426597/140737488355328⟩, ⟨356501576187699/281474976710656, 191473670486191/140737488355328⟩, ⟨327677442995607/281474976710656, 357025239495801/281474976710656⟩]
def scS186CutCaps : Fin 3 → Fin 3 → ℚ := ![![3797305193/50000000, 4497638109/100000000, 329462649/10000000], ![548127337/20000000, 2336537477/100000000, 179694211/10000000], ![423866133/50000000, 322524601/50000000, 584862199/100000000]]
def scS186CutWeightFloor : ℚ := 130080113/100000000
def scS186CutMargins : Fin 3 → ℚ := ![13404469/5000000000, 18387447/10000000000, 7256853/5000000000]

theorem scS186Cut_roots_ok : scS186CutCell.rootsOK scS186CutRoots = true := by decide +kernel

theorem scS186Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS186CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS186Cut_margin_le (i : Fin 3) : curvatureLoss scS186CutCell scS186CutCaps i ≤ scS186CutMargins i := by
  fin_cases i <;> decide +kernel

def scS187CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨7/16, 9/20⟩, ⟨3/40, 1/10⟩⟩
def scS187CutRoots : Fin 3 → RatBounds := ![⟨227558798862677/140737488355328, 242555390572849/140737488355328⟩, ⟨87993521686397/70368744177664, 377819178175481/281474976710656⟩, ⟨5049024482063/4398046511104, 351856444961893/281474976710656⟩]
def scS187CutCaps : Fin 3 → Fin 3 → ℚ := ![![247270437/3125000, 940100559/20000000, 1727214561/50000000], ![2855728109/100000000, 1214512797/50000000, 934706111/50000000], ![765599931/100000000, 290459287/50000000, 8234879/1562500]]
def scS187CutWeightFloor : ℚ := 135095973/100000000
def scS187CutMargins : Fin 3 → ℚ := ![13506623/5000000000, 18463287/10000000000, 907223/625000000]

theorem scS187Cut_roots_ok : scS187CutCell.rootsOK scS187CutRoots = true := by decide +kernel

theorem scS187Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS187CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS187Cut_margin_le (i : Fin 3) : curvatureLoss scS187CutCell scS187CutCaps i ≤ scS187CutMargins i := by
  fin_cases i <;> decide +kernel

def scS188CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨9/20, 37/80⟩, ⟨0, 1/40⟩⟩
def scS188CutRoots : Fin 3 → RatBounds := ![⟨115823811680257/70368744177664, 247323948082375/140737488355328⟩, ⟨22675516736197/17592186044416, 390561382121323/281474976710656⟩, ⟨341271138165875/281474976710656, 372161222975661/281474976710656⟩]
def scS188CutCaps : Fin 3 → Fin 3 → ℚ := ![![6820790669/100000000, 991959167/25000000, 1484712307/50000000], ![1226533941/50000000, 2037453373/100000000, 13427569/800000], ![105312717/10000000, 792480333/100000000, 92921151/12500000]]
def scS188CutWeightFloor : ℚ := 15155483/12500000
def scS188CutMargins : Fin 3 → ℚ := ![26340561/10000000000, 3584067/2000000000, 2977089/2000000000]

theorem scS188Cut_roots_ok : scS188CutCell.rootsOK scS188CutRoots = true := by decide +kernel

theorem scS188Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS188CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS188Cut_margin_le (i : Fin 3) : curvatureLoss scS188CutCell scS188CutCaps i ≤ scS188CutMargins i := by
  fin_cases i <;> decide +kernel

def scS189CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨9/20, 37/80⟩, ⟨1/40, 1/20⟩⟩
def scS189CutRoots : Fin 3 → RatBounds := ![⟨28755669686447/17592186044416, 490929074957275/281474976710656⟩, ⟨357423051760405/281474976710656, 384408212391341/281474976710656⟩, ⟨167933730672455/140737488355328, 365964874781027/281474976710656⟩]
def scS189CutCaps : Fin 3 → Fin 3 → ℚ := ![![142698923/2000000, 4168048669/100000000, 1566573521/50000000], ![1283665203/50000000, 2126358749/100000000, 1752927811/100000000], ![376653/40000, 44131497/6250000, 33140363/5000000]]
def scS189CutWeightFloor : ℚ := 63127261/50000000
def scS189CutMargins : Fin 3 → ℚ := ![26306263/10000000000, 8905101/5000000000, 14721297/10000000000]

theorem scS189Cut_roots_ok : scS189CutCell.rootsOK scS189CutRoots = true := by decide +kernel

theorem scS189Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS189CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS189Cut_margin_le (i : Fin 3) : curvatureLoss scS189CutCell scS189CutCaps i ≤ scS189CutMargins i := by
  fin_cases i <;> decide +kernel

def scS190CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨9/20, 37/80⟩, ⟨1/20, 3/40⟩⟩
def scS190CutRoots : Fin 3 → RatBounds := ![⟨228567721614037/140737488355328, 487518468194951/281474976710656⟩, ⟨352494907292093/281474976710656, 189400629694627/140737488355328⟩, ⟨330925843893161/281474976710656, 180161048609599/140737488355328⟩]
def scS190CutCaps : Fin 3 → Fin 3 → ℚ := ![![931003991/12500000, 2183147139/50000000, 131817821/4000000], ![2680625659/100000000, 110731707/5000000, 1826842429/100000000], ![846325077/100000000, 79081073/12500000, 297125007/50000000]]
def scS190CutWeightFloor : ℚ := 131282441/100000000
def scS190CutMargins : Fin 3 → ℚ := ![527889/200000000, 17795943/10000000000, 14647047/10000000000]

theorem scS190Cut_roots_ok : scS190CutCell.rootsOK scS190CutRoots = true := by decide +kernel

theorem scS190Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS190CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS190Cut_margin_le (i : Fin 3) : curvatureLoss scS190CutCell scS190CutCaps i ≤ scS190CutMargins i := by
  fin_cases i <;> decide +kernel

def scS191CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨9/20, 37/80⟩, ⟨3/40, 1/10⟩⟩
def scS191CutRoots : Fin 3 → RatBounds := ![⟨113600294852203/70368744177664, 484378933646577/281474976710656⟩, ⟨21747975158281/17592186044416, 373670363607457/281474976710656⟩, ⟨163194572541445/140737488355328, 177580734727987/140737488355328⟩]
def scS191CutCaps : Fin 3 → Fin 3 → ℚ := ![![1940218301/25000000, 570354749/12500000, 864190211/25000000], ![349129089/12500000, 575581483/25000000, 1900232099/100000000], ![764291181/100000000, 569715033/100000000, 66934327/12500000]]
def scS191CutWeightFloor : ℚ := 136324769/100000000
def scS191CutMargins : Fin 3 → ℚ := ![26584123/10000000000, 8929711/5000000000, 14646273/10000000000]

theorem scS191Cut_roots_ok : scS191CutCell.rootsOK scS191CutRoots = true := by decide +kernel

theorem scS191Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS191CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS191Cut_margin_le (i : Fin 3) : curvatureLoss scS191CutCell scS191CutCaps i ≤ scS191CutMargins i := by
  fin_cases i <;> decide +kernel


end HlawkaSchatten.BelowExponent.Vertex
