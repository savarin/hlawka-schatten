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

def scE14CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨9/40, 19/80⟩, ⟨3/20, 13/80⟩⟩
def scE14CutRoots : Fin 3 → RatBounds := ![⟨256695513014691/140737488355328, 275798189311965/140737488355328⟩, ⟨225598196878919/140737488355328, 485748208631843/281474976710656⟩, ⟨4148020762705/4398046511104, 148624362007457/140737488355328⟩]
def scE14CutCaps : Fin 3 → Fin 3 → ℚ := ![![11765236121/50000000, 3518545769/20000000, 6911980609/100000000], ![2256191871/20000000, 11940365781/100000000, 761073441/25000000], ![533597513/100000000, 105813809/20000000, 25530163/10000000]]
def scE14CutWeightFloor : ℚ := 66072677/50000000
def scE14CutMargins : Fin 3 → ℚ := ![3451663/500000000, 14678791/2500000000, 3988897/2000000000]

theorem scE14Cut_roots_ok : scE14CutCell.rootsOK scE14CutRoots = true := by decide +kernel

theorem scE14Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE14CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE14Cut_margin_le (i : Fin 3) : curvatureLoss scE14CutCell scE14CutCaps i ≤ scE14CutMargins i := by
  fin_cases i <;> decide +kernel

def scE15CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨9/40, 19/80⟩, ⟨13/80, 1/6⟩⟩
def scE15CutRoots : Fin 3 → RatBounds := ![⟨256562910438117/140737488355328, 68741655245947/35184372088832⟩, ⟨450554804910223/281474976710656, 483672484675101/281474976710656⟩, ⟨66216534100245/70368744177664, 295215869194597/281474976710656⟩]
def scE15CutCaps : Fin 3 → Fin 3 → ℚ := ![![23364925113/100000000, 4366419367/25000000, 6797127991/100000000], ![2806937749/25000000, 11828139431/100000000, 738608447/25000000], ![206087539/50000000, 410909817/100000000, 101801811/50000000]]
def scE15CutWeightFloor : ℚ := 135083551/100000000
def scE15CutMargins : Fin 3 → ℚ := ![67653269/10000000000, 2865183/500000000, 4772551/2500000000]

theorem scE15Cut_roots_ok : scE15CutCell.rootsOK scE15CutRoots = true := by decide +kernel

theorem scE15Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE15CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE15Cut_margin_le (i : Fin 3) : curvatureLoss scE15CutCell scE15CutCaps i ≤ scE15CutMargins i := by
  fin_cases i <;> decide +kernel

def scE16CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨19/80, 1/4⟩, ⟨1/8, 11/80⟩⟩
def scE16CutRoots : Fin 3 → RatBounds := ![⟨509636541137763/281474976710656, 546625544789905/281474976710656⟩, ⟨222971865272889/140737488355328, 479357041257345/281474976710656⟩, ⟨271820996173337/281474976710656, 18948849414475/17592186044416⟩]
def scE16CutCaps : Fin 3 → Fin 3 → ℚ := ![![20508103041/100000000, 1884325457/12500000, 1234443993/20000000], ![9587126937/100000000, 2535567549/25000000, 2690942103/100000000], ![567745689/100000000, 11098673/2000000, 55720043/20000000]]
def scE16CutWeightFloor : ℚ := 25702771/20000000
def scE16CutMargins : Fin 3 → ℚ := ![479109/80000000, 25167781/5000000000, 3571001/2000000000]

theorem scE16Cut_roots_ok : scE16CutCell.rootsOK scE16CutRoots = true := by decide +kernel

theorem scE16Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE16CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE16Cut_margin_le (i : Fin 3) : curvatureLoss scE16CutCell scE16CutCaps i ≤ scE16CutMargins i := by
  fin_cases i <;> decide +kernel

def scE17CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨19/80, 1/4⟩, ⟨11/80, 3/20⟩⟩
def scE17CutRoots : Fin 3 → RatBounds := ![⟨254113510327729/140737488355328, 68137614588555/35184372088832⟩, ⟨221957583771589/140737488355328, 477157259098229/281474976710656⟩, ⟨269879875538817/281474976710656, 301002132134575/281474976710656⟩]
def scE17CutCaps : Fin 3 → Fin 3 → ℚ := ![![20892874727/100000000, 3842166731/25000000, 98182459/1562500], ![2441018607/25000000, 10321246977/100000000, 2739777641/100000000], ![272267197/50000000, 132929643/25000000, 133464493/50000000]]
def scE17CutWeightFloor : ℚ := 26168647/20000000
def scE17CutMargins : Fin 3 → ℚ := ![30470199/5000000000, 25607063/5000000000, 9072641/5000000000]

theorem scE17Cut_roots_ok : scE17CutCell.rootsOK scE17CutRoots = true := by decide +kernel

theorem scE17Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE17CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE17Cut_margin_le (i : Fin 3) : curvatureLoss scE17CutCell scE17CutCaps i ≤ scE17CutMargins i := by
  fin_cases i <;> decide +kernel

def scE18CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨19/80, 1/4⟩, ⟨3/20, 13/80⟩⟩
def scE18CutRoots : Fin 3 → RatBounds := ![⟨506865275944689/281474976710656, 543629121237647/281474976710656⟩, ⟨441958794879383/281474976710656, 475037164628071/281474976710656⟩, ⟨134005851709913/140737488355328, 74726529423375/70368744177664⟩]
def scE18CutCaps : Fin 3 → Fin 3 → ℚ := ![![21277030223/100000000, 15661888327/100000000, 6394869433/100000000], ![9940614577/100000000, 10499883903/100000000, 2788493641/100000000], ![522703573/100000000, 509915277/100000000, 255967313/100000000]]
def scE18CutWeightFloor : ℚ := 133173811/100000000
def scE18CutMargins : Fin 3 → ℚ := ![15498217/2500000000, 2604657/500000000, 18436193/10000000000]

theorem scE18Cut_roots_ok : scE18CutCell.rootsOK scE18CutRoots = true := by decide +kernel

theorem scE18Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE18CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE18Cut_margin_le (i : Fin 3) : curvatureLoss scE18CutCell scE18CutCaps i ≤ scE18CutMargins i := by
  fin_cases i <;> decide +kernel

def scE19CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨19/80, 1/4⟩, ⟨13/80, 1/6⟩⟩
def scE19CutRoots : Fin 3 → RatBounds := ![⟨126653572857449/70368744177664, 541995186567789/281474976710656⟩, ⟨441322041715017/281474976710656, 59122498799549/35184372088832⟩, ⟨133702241378137/140737488355328, 296881390157255/281474976710656⟩]
def scE19CutCaps : Fin 3 → Fin 3 → ℚ := ![![10559605319/50000000, 15544145807/100000000, 3142207283/50000000], ![9889043973/100000000, 10393644711/100000000, 1351130259/50000000], ![20140011/5000000, 394659179/100000000, 101636757/50000000]]
def scE19CutWeightFloor : ℚ := 68062887/50000000
def scE19CutMargins : Fin 3 → ℚ := ![60650411/10000000000, 25372697/5000000000, 17596213/10000000000]

theorem scE19Cut_roots_ok : scE19CutCell.rootsOK scE19CutRoots = true := by decide +kernel

theorem scE19Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE19CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE19Cut_margin_le (i : Fin 3) : curvatureLoss scE19CutCell scE19CutCaps i ≤ scE19CutMargins i := by
  fin_cases i <;> decide +kernel

def scE20CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨1/4, 21/80⟩, ⟨1/8, 11/80⟩⟩
def scE20CutRoots : Fin 3 → RatBounds := ![⟨251818566016261/140737488355328, 539356751880299/281474976710656⟩, ⟨218629382524345/140737488355328, 234683670585795/140737488355328⟩, ⟨274356607979055/281474976710656, 18611238407/17179869184⟩]
def scE20CutCaps : Fin 3 → Fin 3 → ℚ := ![![18684152127/100000000, 13525286223/100000000, 2873276111/50000000], ![4262615249/50000000, 4491442221/50000000, 625802819/25000000], ![111494853/20000000, 536015319/100000000, 139888647/50000000]]
def scE20CutWeightFloor : ℚ := 32379099/25000000
def scE20CutMargins : Fin 3 → ℚ := ![54232143/10000000000, 2813011/625000000, 832963/500000000]

theorem scE20Cut_roots_ok : scE20CutCell.rootsOK scE20CutRoots = true := by decide +kernel

theorem scE20Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE20CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE20Cut_margin_le (i : Fin 3) : curvatureLoss scE20CutCell scE20CutCaps i ≤ scE20CutMargins i := by
  fin_cases i <;> decide +kernel

def scE21CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨1/4, 21/80⟩, ⟨11/80, 3/20⟩⟩
def scE21CutRoots : Fin 3 → RatBounds := ![⟨122621065017/68719476736, 268932292549587/140737488355328⟩, ⟨108810904900753/70368744177664, 233592236315453/140737488355328⟩, ⟨136207879846103/140737488355328, 302755417332349/281474976710656⟩]
def scE21CutCaps : Fin 3 → Fin 3 → ℚ := ![![3806812679/20000000, 13789533379/100000000, 1462817497/25000000], ![8682914773/100000000, 457067567/5000000, 254920557/10000000], ![534594033/100000000, 256764467/50000000, 26803529/10000000]]
def scE21CutWeightFloor : ℚ := 6592831/5000000
def scE21CutMargins : Fin 3 → ℚ := ![13794713/2500000000, 45789871/10000000000, 8465343/5000000000]

theorem scE21Cut_roots_ok : scE21CutCell.rootsOK scE21CutRoots = true := by decide +kernel

theorem scE21Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE21CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE21Cut_margin_le (i : Fin 3) : curvatureLoss scE21CutCell scE21CutCaps i ≤ scE21CutMargins i := by
  fin_cases i <;> decide +kernel

def scE22CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨1/4, 21/80⟩, ⟨3/20, 13/80⟩⟩
def scE22CutRoots : Fin 3 → RatBounds := ![⟨500921486469225/281474976710656, 536424184282663/281474976710656⟩, ⟨27081273269435/17592186044416, 465080890740911/281474976710656⟩, ⟨270547815016865/281474976710656, 150333693378589/140737488355328⟩]
def scE22CutCaps : Fin 3 → Fin 3 → ℚ := ![![19383439919/100000000, 3513255437/25000000, 119114803/2000000], ![1105028667/12500000, 4649759899/50000000, 324385351/12500000], ![102615867/20000000, 492413353/100000000, 803151/312500]]
def scE22CutWeightFloor : ℚ := 134198097/100000000
def scE22CutMargins : Fin 3 → ℚ := ![56126463/10000000000, 23286089/5000000000, 4300699/2500000000]

theorem scE22Cut_roots_ok : scE22CutCell.rootsOK scE22CutRoots = true := by decide +kernel

theorem scE22Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE22CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE22Cut_margin_le (i : Fin 3) : curvatureLoss scE22CutCell scE22CutCaps i ≤ scE22CutMargins i := by
  fin_cases i <;> decide +kernel

def scE23CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨1/4, 21/80⟩, ⟨13/80, 1/6⟩⟩
def scE23CutRoots : Fin 3 → RatBounds := ![⟨125170906892225/70368744177664, 534816763940435/281474976710656⟩, ⟨432667930583373/281474976710656, 463040101781565/281474976710656⟩, ⟨33742582605399/35184372088832, 298650241799153/281474976710656⟩]
def scE23CutCaps : Fin 3 → Fin 3 → ℚ := ![![961624423/5000000, 13943444063/100000000, 23396697/400000], ![549370973/6250000, 9198539149/100000000, 2511449701/100000000], ![49319261/12500000, 23744127/6250000, 101650227/50000000]]
def scE23CutWeightFloor : ℚ := 137163607/100000000
def scE23CutMargins : Fin 3 → ℚ := ![54816921/10000000000, 45281631/10000000000, 16373463/10000000000]

theorem scE23Cut_roots_ok : scE23CutCell.rootsOK scE23CutRoots = true := by decide +kernel

theorem scE23Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE23CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE23Cut_margin_le (i : Fin 3) : curvatureLoss scE23CutCell scE23CutCaps i ≤ scE23CutMargins i := by
  fin_cases i <;> decide +kernel

def scE24CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨21/80, 11/40⟩, ⟨1/8, 11/80⟩⟩
def scE24CutRoots : Fin 3 → RatBounds := ![⟨498167290481383/281474976710656, 266386592987341/140737488355328⟩, ⟨53636815109277/35184372088832, 230024674717681/140737488355328⟩, ⟨69224345282963/70368744177664, 306770975878005/281474976710656⟩]
def scE24CutCaps : Fin 3 → Fin 3 → ℚ := ![![4284491119/25000000, 3055644257/25000000, 5382519337/100000000], ![3821678923/50000000, 1601524203/20000000, 1178717889/50000000], ![548372757/100000000, 103725801/20000000, 281316053/100000000]]
def scE24CutWeightFloor : ℚ := 26103761/20000000
def scE24CutMargins : Fin 3 → ℚ := ![49472061/10000000000, 40525053/10000000000, 7833273/5000000000]

theorem scE24Cut_roots_ok : scE24CutCell.rootsOK scE24CutRoots = true := by decide +kernel

theorem scE24Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE24CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE24Cut_margin_le (i : Fin 3) : curvatureLoss scE24CutCell scE24CutCaps i ≤ scE24CutMargins i := by
  fin_cases i <;> decide +kernel

def scE25CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨21/80, 11/40⟩, ⟨11/80, 3/20⟩⟩
def scE25CutRoots : Fin 3 → RatBounds := ![⟨496811986009885/281474976710656, 265655326568813/140737488355328⟩, ⟨427091326364095/281474976710656, 457881386677773/281474976710656⟩, ⟨137478526795913/140737488355328, 38075960769949/35184372088832⟩]
def scE25CutCaps : Fin 3 → Fin 3 → ℚ := ![![17458373017/100000000, 12461702767/100000000, 2740748513/50000000], ![1556960853/20000000, 8148844147/100000000, 1200414821/50000000], ![525784353/100000000, 124203813/25000000, 33686111/12500000]]
def scE25CutWeightFloor : ℚ := 33217451/25000000
def scE25CutMargins : Fin 3 → ℚ := ![12582501/2500000000, 41225317/10000000000, 3184303/2000000000]

theorem scE25Cut_roots_ok : scE25CutCell.rootsOK scE25CutRoots = true := by decide +kernel

theorem scE25Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE25CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE25Cut_margin_le (i : Fin 3) : curvatureLoss scE25CutCell scE25CutCaps i ≤ scE25CutMargins i := by
  fin_cases i <;> decide +kernel

def scE26CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨21/80, 11/40⟩, ⟨3/20, 13/80⟩⟩
def scE26CutRoots : Fin 3 → RatBounds := ![⟨247751344481147/140737488355328, 264949456245543/140737488355328⟩, ⟨425159781664767/281474976710656, 227896186092399/140737488355328⟩, ⟨273089573300055/281474976710656, 151263567238985/140737488355328⟩]
def scE26CutCaps : Fin 3 → Fin 3 → ℚ := ![![4444578657/25000000, 2540027933/20000000, 2790121249/50000000], ![7925916559/100000000, 4144901897/50000000, 1222058007/50000000], ![504548443/100000000, 476334319/100000000, 258383081/100000000]]
def scE26CutWeightFloor : ℚ := 27044423/20000000
def scE26CutMargins : Fin 3 → ℚ := ![51189023/10000000000, 10481581/2500000000, 1617723/1000000000]

theorem scE26Cut_roots_ok : scE26CutCell.rootsOK scE26CutRoots = true := by decide +kernel

theorem scE26Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE26CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE26Cut_margin_le (i : Fin 3) : curvatureLoss scE26CutCell scE26CutCaps i ≤ scE26CutMargins i := by
  fin_cases i <;> decide +kernel

def scE27CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨21/80, 11/40⟩, ⟨13/80, 1/6⟩⟩
def scE27CutRoots : Fin 3 → RatBounds := ![⟨495276943860657/281474976710656, 528315597898829/281474976710656⟩, ⟨424531186520475/281474976710656, 453766065536267/281474976710656⟩, ⟨68120640543897/70368744177664, 75129270704225/70368744177664⟩]
def scE27CutCaps : Fin 3 → Fin 3 → ℚ := ![![17633485369/100000000, 3149440283/25000000, 5477128553/100000000], ![3938638783/50000000, 8193468997/100000000, 23634481/1000000], ![193637421/50000000, 91609557/25000000, 101821637/50000000]]
def scE27CutWeightFloor : ℚ := 27640207/20000000
def scE27CutMargins : Fin 3 → ℚ := ![49909753/10000000000, 20343697/5000000000, 767891/500000000]

theorem scE27Cut_roots_ok : scE27CutCell.rootsOK scE27CutRoots = true := by decide +kernel

theorem scE27Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE27CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE27Cut_margin_le (i : Fin 3) : curvatureLoss scE27CutCell scE27CutCaps i ≤ scE27CutMargins i := by
  fin_cases i <;> decide +kernel

def scE28CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨11/40, 23/80⟩, ⟨1/8, 11/80⟩⟩
def scE28CutRoots : Fin 3 → RatBounds := ![⟨493178231441799/281474976710656, 131701286811921/70368744177664⟩, ⟨421398115634835/281474976710656, 225664621804807/140737488355328⟩, ⟨139725180015011/140737488355328, 308710890822949/281474976710656⟩]
def scE28CutCaps : Fin 3 → Fin 3 → ℚ := ![![15817145099/100000000, 11118299071/100000000, 2534690141/50000000], ![276022081/4000000, 1795062339/25000000, 2236207233/100000000], ![540285803/100000000, 100514249/20000000, 11327161/4000000]]
def scE28CutWeightFloor : ℚ := 65762189/50000000
def scE28CutMargins : Fin 3 → ℚ := ![11356437/2500000000, 36720937/10000000000, 1482181/1000000000]

theorem scE28Cut_roots_ok : scE28CutCell.rootsOK scE28CutRoots = true := by decide +kernel

theorem scE28Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE28CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE28Cut_margin_le (i : Fin 3) : curvatureLoss scE28CutCell scE28CutCaps i ≤ scE28CutMargins i := by
  fin_cases i <;> decide +kernel

def scE29CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨11/40, 23/80⟩, ⟨11/80, 3/20⟩⟩
def scE29CutRoots : Fin 3 → RatBounds := ![⟨245923367836251/140737488355328, 525369680487067/281474976710656⟩, ⟨419405565836825/281474976710656, 449174410943109/281474976710656⟩, ⟨277510752505979/281474976710656, 306554949434801/281474976710656⟩]
def scE29CutCaps : Fin 3 → Fin 3 → ℚ := ![![2014049351/12500000, 1417010519/12500000, 5163448867/100000000], ![7028313191/100000000, 3653426237/50000000, 1138708703/50000000], ![25897763/5000000, 240690717/50000000, 271253749/100000000]]
def scE29CutWeightFloor : ℚ := 66943069/50000000
def scE29CutMargins : Fin 3 → ℚ := ![46208327/10000000000, 4669023/1250000000, 3012547/2000000000]

theorem scE29Cut_roots_ok : scE29CutCell.rootsOK scE29CutRoots = true := by decide +kernel

theorem scE29Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE29CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE29Cut_margin_le (i : Fin 3) : curvatureLoss scE29CutCell scE29CutCaps i ≤ scE29CutMargins i := by
  fin_cases i <;> decide +kernel

def scE30CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨11/40, 23/80⟩, ⟨3/20, 13/80⟩⟩
def scE30CutRoots : Fin 3 → RatBounds := ![⟨245280235098965/140737488355328, 523984116471603/281474976710656⟩, ⟨417484456298209/281474976710656, 223549121643249/140737488355328⟩, ⟨137821963111367/140737488355328, 304481417856865/281474976710656⟩]
def scE30CutCaps : Fin 3 → Fin 3 → ℚ := ![![16407234559/100000000, 5776619899/50000000, 210291947/4000000], ![894471281/12500000, 929152729/12500000, 579632119/25000000], ![2484829/500000, 23074453/5000000, 16253557/6250000]]
def scE30CutWeightFloor : ℚ := 13624927/10000000
def scE30CutMargins : Fin 3 → ℚ := ![46992131/10000000000, 37984279/10000000000, 7652231/5000000000]

theorem scE30Cut_roots_ok : scE30CutCell.rootsOK scE30CutRoots = true := by decide +kernel

theorem scE30Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE30CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE30Cut_margin_le (i : Fin 3) : curvatureLoss scE30CutCell scE30CutCaps i ≤ scE30CutMargins i := by
  fin_cases i <;> decide +kernel

def scE31CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨11/40, 23/80⟩, ⟨13/80, 1/6⟩⟩
def scE31CutRoots : Fin 3 → RatBounds := ![⟨490345898399993/281474976710656, 522422733052673/281474976710656⟩, ⟨416859293585029/281474976710656, 445084735378925/281474976710656⟩, ⟨137518559660613/140737488355328, 75619503632497/70368744177664⟩]
def scE31CutCaps : Fin 3 → Fin 3 → ℚ := ![![4066969387/25000000, 572862003/5000000, 41258069/800000], ![7108664841/100000000, 1835258257/25000000, 1120235657/50000000], ![15233239/4000000, 35408213/10000000, 51067173/25000000]]
def scE31CutWeightFloor : ℚ := 139241533/100000000
def scE31CutMargins : Fin 3 → ℚ := ![9147991/2000000000, 18396109/5000000000, 14493021/10000000000]

theorem scE31Cut_roots_ok : scE31CutCell.rootsOK scE31CutRoots = true := by decide +kernel

theorem scE31Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE31CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE31Cut_margin_le (i : Fin 3) : curvatureLoss scE31CutCell scE31CutCaps i ≤ scE31CutMargins i := by
  fin_cases i <;> decide +kernel

def scE32CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨23/80, 3/10⟩, ⟨1/8, 11/80⟩⟩
def scE32CutRoots : Fin 3 → RatBounds := ![⟨122157067486503/70368744177664, 521393891360645/281474976710656⟩, ⟨207061961793545/140737488355328, 443144277177437/281474976710656⟩, ⟨282021839077097/281474976710656, 310743437760341/281474976710656⟩]
def scE32CutCaps : Fin 3 → Fin 3 → ℚ := ![![7340606583/50000000, 10175447839/100000000, 479874371/10000000], ![1567708263/25000000, 32364753/500000, 1067749071/50000000], ![266543211/50000000, 243837089/50000000, 2229191/781250]]
def scE32CutWeightFloor : ℚ := 33134009/25000000
def scE32CutMargins : Fin 3 → ℚ := ![839263/200000000, 8367223/2500000000, 14100739/10000000000]

theorem scE32Cut_roots_ok : scE32CutCell.rootsOK scE32CutRoots = true := by decide +kernel

theorem scE32Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE32CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE32Cut_margin_le (i : Fin 3) : curvatureLoss scE32CutCell scE32CutCaps i ≤ scE32CutMargins i := by
  fin_cases i <;> decide +kernel

def scE33CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨23/80, 3/10⟩, ⟨11/80, 3/20⟩⟩
def scE33CutRoots : Fin 3 → RatBounds := ![⟨487318608354997/281474976710656, 519983142304505/281474976710656⟩, ⟨412140850148077/281474976710656, 441000995197995/281474976710656⟩, ⟨280083108736267/281474976710656, 308594408548755/281474976710656⟩]
def scE33CutCaps : Fin 3 → Fin 3 → ℚ := ![![7477432611/50000000, 10374970451/100000000, 4888601921/100000000], ![6386983229/100000000, 6587062859/100000000, 2174874481/100000000], ![2554921/500000, 116766457/25000000, 13665067/5000000]]
def scE33CutWeightFloor : ℚ := 8431787/6250000
def scE33CutMargins : Fin 3 → ℚ := ![21340657/5000000000, 3404121/1000000000, 2865929/2000000000]

theorem scE33Cut_roots_ok : scE33CutCell.rootsOK scE33CutRoots = true := by decide +kernel

theorem scE33Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE33CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE33Cut_margin_le (i : Fin 3) : curvatureLoss scE33CutCell scE33CutCaps i ≤ scE33CutMargins i := by
  fin_cases i <;> decide +kernel

def scE34CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨23/80, 3/10⟩, ⟨3/20, 13/80⟩⟩
def scE34CutRoots : Fin 3 → RatBounds := ![⟨486053464033245/281474976710656, 518621483658575/281474976710656⟩, ⟨410229041874355/281474976710656, 438936143759233/281474976710656⟩, ⟨278217085532095/281474976710656, 153263737638465/140737488355328⟩]
def scE34CutCaps : Fin 3 → Fin 3 → ℚ := ![![15228155551/100000000, 10573914473/100000000, 311140821/6250000], ![3251427401/50000000, 1675241707/25000000, 1107079549/50000000], ![122553263/25000000, 44772179/10000000, 262002437/100000000]]
def scE34CutWeightFloor : ℚ := 137282581/100000000
def scE34CutMargins : Fin 3 → ℚ := ![43400827/10000000000, 1730723/500000000, 3639851/2500000000]

theorem scE34Cut_roots_ok : scE34CutCell.rootsOK scE34CutRoots = true := by decide +kernel

theorem scE34Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE34CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE34Cut_margin_le (i : Fin 3) : curvatureLoss scE34CutCell scE34CutCaps i ≤ scE34CutMargins i := by
  fin_cases i <;> decide +kernel

def scE35CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨23/80, 3/10⟩, ⟨13/80, 1/6⟩⟩
def scE35CutRoots : Fin 3 → RatBounds := ![⟨485849186487483/281474976710656, 517080054372589/281474976710656⟩, ⟨102401735256117/70368744177664, 27308371035155/17592186044416⟩, ⟨138805265419209/140737488355328, 152265155396405/140737488355328⟩]
def scE35CutCaps : Fin 3 → Fin 3 → ℚ := ![![15093701067/100000000, 1310449047/12500000, 4880956077/100000000], ![3228643113/50000000, 6613491927/100000000, 1069374909/50000000], ![375114683/100000000, 342694289/100000000, 205149683/100000000]]
def scE35CutWeightFloor : ℚ := 140288181/100000000
def scE35CutMargins : Fin 3 → ℚ := ![21086589/5000000000, 33467113/10000000000, 3438721/2500000000]

theorem scE35Cut_roots_ok : scE35CutCell.rootsOK scE35CutRoots = true := by decide +kernel

theorem scE35Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE35CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE35Cut_margin_le (i : Fin 3) : curvatureLoss scE35CutCell scE35CutCaps i ≤ scE35CutMargins i := by
  fin_cases i <;> decide +kernel

def scE36CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨3/10, 5/16⟩, ⟨1/8, 11/80⟩⟩
def scE36CutRoots : Fin 3 → RatBounds := ![⟨242240812100653/140737488355328, 258244810539135/140737488355328⟩, ⟨407232331385315/281474976710656, 435440725339895/281474976710656⟩, ⟨35577192508591/35184372088832, 312866773829285/281474976710656⟩]
def scE36CutCaps : Fin 3 → Fin 3 → ℚ := ![![6849256969/50000000, 9365248779/100000000, 2281991493/50000000], ![1146859569/20000000, 5866621643/100000000, 128318301/6250000], ![263341457/50000000, 29612957/6250000, 287771107/100000000]]
def scE36CutWeightFloor : ℚ := 66778209/50000000
def scE36CutMargins : Fin 3 → ℚ := ![38983389/10000000000, 1917197/625000000, 1348603/1000000000]

theorem scE36Cut_roots_ok : scE36CutCell.rootsOK scE36CutRoots = true := by decide +kernel

theorem scE36Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE36CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE36Cut_margin_le (i : Fin 3) : curvatureLoss scE36CutCell scE36CutCaps i ≤ scE36CutMargins i := by
  fin_cases i <;> decide +kernel

def scE37CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨3/10, 5/16⟩, ⟨11/80, 3/20⟩⟩
def scE37CutRoots : Fin 3 → RatBounds := ![⟨483191961813193/281474976710656, 515101428080901/281474976710656⟩, ⟨101314421306311/70368744177664, 108326895451541/70368744177664⟩, ⟨282679807534685/281474976710656, 77681062861447/70368744177664⟩]
def scE37CutCaps : Fin 3 → Fin 3 → ℚ := ![![1744189767/12500000, 596815021/6250000, 2325112589/50000000], ![1460141581/25000000, 1194016659/20000000, 2090967101/100000000], ![504784021/100000000, 226871879/50000000, 275615907/100000000]]
def scE37CutWeightFloor : ℚ := 135939847/100000000
def scE37CutMargins : Fin 3 → ℚ := ![9911557/2500000000, 31197007/10000000000, 26767/19531250]

theorem scE37Cut_roots_ok : scE37CutCell.rootsOK scE37CutRoots = true := by decide +kernel

theorem scE37Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE37CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE37Cut_margin_le (i : Fin 3) : curvatureLoss scE37CutCell scE37CutCaps i ≤ scE37CutMargins i := by
  fin_cases i <;> decide +kernel

def scE38CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨3/10, 5/16⟩, ⟨3/20, 13/80⟩⟩
def scE38CutRoots : Fin 3 → RatBounds := ![⟨481946163276689/281474976710656, 513761584135445/281474976710656⟩, ⟨403354159850363/281474976710656, 431252677736883/281474976710656⟩, ⟨280814701271791/281474976710656, 38582940531029/35184372088832⟩]
def scE38CutCaps : Fin 3 → Fin 3 → ℚ := ![![7104100869/50000000, 9732297121/100000000, 4736270757/100000000], ![74332233/1250000, 3036679383/50000000, 532189053/25000000], ![30262957/6250000, 54364163/12500000, 1056821/400000]]
def scE38CutWeightFloor : ℚ := 138324771/100000000
def scE38CutMargins : Fin 3 → ℚ := ![40310523/10000000000, 15859931/5000000000, 6962141/5000000000]

theorem scE38Cut_roots_ok : scE38CutCell.rootsOK scE38CutRoots = true := by decide +kernel

theorem scE38Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE38CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE38Cut_margin_le (i : Fin 3) : curvatureLoss scE38CutCell scE38CutCaps i ≤ scE38CutMargins i := by
  fin_cases i <;> decide +kernel

def scE39CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨3/10, 5/16⟩, ⟨13/80, 1/6⟩⟩
def scE39CutRoots : Fin 3 → RatBounds := ![⟨30109459630553/17592186044416, 512238299655393/281474976710656⟩, ⟨402734788004567/281474976710656, 429260431259813/281474976710656⟩, ⟨70052108829721/70368744177664, 306672217435797/281474976710656⟩]
def scE39CutCaps : Fin 3 → Fin 3 → ℚ := ![![879884287/6250000, 9647049911/100000000, 232071301/5000000], ![1475630407/25000000, 1198159019/20000000, 1027933429/50000000], ![370036919/100000000, 20759699/6250000, 41252851/20000000]]
def scE39CutWeightFloor : ℚ := 35335939/25000000
def scE39CutMargins : Fin 3 → ℚ := ![782101/200000000, 30614749/10000000000, 13125413/10000000000]

theorem scE39Cut_roots_ok : scE39CutCell.rootsOK scE39CutRoots = true := by decide +kernel

theorem scE39Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE39CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE39Cut_margin_le (i : Fin 3) : curvatureLoss scE39CutCell scE39CutCaps i ≤ scE39CutMargins i := by
  fin_cases i <;> decide +kernel

def scE40CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨5/16, 13/40⟩, ⟨1/8, 11/80⟩⟩
def scE40CutRoots : Fin 3 → RatBounds := ![⟨480707463935853/281474976710656, 128012480432069/70368744177664⟩, ⟨400688745421975/281474976710656, 428172280269731/281474976710656⟩, ⟨71810687939985/70368744177664, 78769974175575/70368744177664⟩]
def scE40CutCaps : Fin 3 → Fin 3 → ℚ := ![![2568805263/20000000, 8665076517/100000000, 1089954621/25000000], ![5275060017/100000000, 5343487821/100000000, 496548069/25000000], ![520988749/100000000, 230426687/50000000, 290464723/100000000]]
def scE40CutWeightFloor : ℚ := 16823493/12500000
def scE40CutMargins : Fin 3 → ℚ := ![36406397/10000000000, 14130291/5000000000, 12961867/10000000000]

theorem scE40Cut_roots_ok : scE40CutCell.rootsOK scE40CutRoots = true := by decide +kernel

theorem scE40Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE40CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE40Cut_margin_le (i : Fin 3) : curvatureLoss scE40CutCell scE40CutCaps i ≤ scE40CutMargins i := by
  fin_cases i <;> decide +kernel

def scE41CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨5/16, 13/40⟩, ⟨11/80, 3/20⟩⟩
def scE41CutRoots : Fin 3 → RatBounds := ![⟨239718043199051/140737488355328, 255341141369759/140737488355328⟩, ⟨199360790632807/140737488355328, 106512001555317/70368744177664⟩, ⟨285306105528639/281474976710656, 156471750137623/140737488355328⟩]
def scE41CutCaps : Fin 3 → Fin 3 → ℚ := ![![6541424821/50000000, 8835238129/100000000, 2221477893/50000000], ![5372867557/100000000, 217508171/4000000, 505701113/25000000], ![499268539/100000000, 441300377/100000000, 34772329/12500000]]
def scE41CutWeightFloor : ℚ := 68491181/50000000
def scE41CutMargins : Fin 3 → ℚ := ![37021457/10000000000, 7184689/2500000000, 3292939/2500000000]

theorem scE41Cut_roots_ok : scE41CutCell.rootsOK scE41CutRoots = true := by decide +kernel

theorem scE41Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE41CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE41Cut_margin_le (i : Fin 3) : curvatureLoss scE41CutCell scE41CutCaps i ≤ scE41CutMargins i := by
  fin_cases i <;> decide +kernel

def scE42CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨5/16, 13/40⟩, ⟨3/20, 13/80⟩⟩
def scE42CutRoots : Fin 3 → RatBounds := ![⟨478207975019979/281474976710656, 254681158592135/140737488355328⟩, ⟨198412710487867/140737488355328, 53000227417785/35184372088832⟩, ⟨4428781236057/4398046511104, 38861076299679/35184372088832⟩]
def scE42CutCaps : Fin 3 → Fin 3 → ℚ := ![![2664277533/20000000, 4502451483/50000000, 4525905663/100000000], ![2735218767/50000000, 5531770853/100000000, 2059345153/100000000], ![478862833/100000000, 84590223/20000000, 53329213/20000000]]
def scE42CutWeightFloor : ℚ := 4355573/3125000
def scE42CutMargins : Fin 3 → ℚ := ![37638063/10000000000, 14609009/5000000000, 3345653/2500000000]

theorem scE42Cut_roots_ok : scE42CutCell.rootsOK scE42CutRoots = true := by decide +kernel

theorem scE42Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE42CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE42Cut_margin_le (i : Fin 3) : curvatureLoss scE42CutCell scE42CutCaps i ≤ scE42CutMargins i := by
  fin_cases i <;> decide +kernel

def scE43CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨5/16, 13/40⟩, ⟨13/80, 1/6⟩⟩
def scE43CutRoots : Fin 3 → RatBounds := ![⟨478021854438615/281474976710656, 507855511252249/281474976710656⟩, ⟨396208478095895/281474976710656, 26376145567557/17592186044416⟩, ⟨282836048356149/281474976710656, 154451401270899/140737488355328⟩]
def scE43CutCaps : Fin 3 → Fin 3 → ℚ := ![![3298823123/25000000, 8924209619/100000000, 44332557/1000000], ![1085510323/20000000, 340738457/6250000, 497016029/25000000], ![365523753/100000000, 80591151/25000000, 207594589/100000000]]
def scE43CutWeightFloor : ℚ := 35602701/25000000
def scE43CutMargins : Fin 3 → ℚ := ![36452067/10000000000, 7037033/2500000000, 3146673/2500000000]

theorem scE43Cut_roots_ok : scE43CutCell.rootsOK scE43CutRoots = true := by decide +kernel

theorem scE43Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE43CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE43Cut_margin_le (i : Fin 3) : curvatureLoss scE43CutCell scE43CutCaps i ≤ scE43CutMargins i := by
  fin_cases i <;> decide +kernel

def scE44CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨13/40, 27/80⟩, ⟨1/8, 11/80⟩⟩
def scE44CutRoots : Fin 3 → RatBounds := ![⟨119319786856335/70368744177664, 254019265054597/140737488355328⟩, ⟨394462792566327/281474976710656, 421298783878013/281474976710656⟩, ⟨289902441605405/281474976710656, 317382529627265/281474976710656⟩]
def scE44CutCaps : Fin 3 → Fin 3 → ℚ := ![![3024444901/25000000, 4028480181/50000000, 4182010649/100000000], ![2440184147/50000000, 2444000747/50000000, 241531871/12500000], ![515914107/100000000, 448700363/100000000, 293393097/100000000]]
def scE44CutWeightFloor : ℚ := 135632869/100000000
def scE44CutMargins : Fin 3 → ℚ := ![3416809/1000000000, 26159497/10000000000, 12514959/10000000000]

theorem scE44Cut_roots_ok : scE44CutCell.rootsOK scE44CutRoots = true := by decide +kernel

theorem scE44Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE44CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE44Cut_margin_le (i : Fin 3) : curvatureLoss scE44CutCell scE44CutCaps i ≤ scE44CutMargins i := by
  fin_cases i <;> decide +kernel

def scE45CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨13/40, 27/80⟩, ⟨11/80, 3/20⟩⟩
def scE45CutRoots : Fin 3 → RatBounds := ![⟨59503055616921/35184372088832, 126672394997425/70368744177664⟩, ⟨392502255989449/281474976710656, 104795558470717/70368744177664⟩, ⟨287966941561669/281474976710656, 157625948749173/140737488355328⟩]
def scE45CutCaps : Fin 3 → Fin 3 → ℚ := ![![12322504089/100000000, 8215251057/100000000, 170499497/4000000], ![994178707/20000000, 4974176641/100000000, 983917191/50000000], ![494352211/100000000, 429628573/100000000, 70241691/25000000]]
def scE45CutWeightFloor : ℚ := 69019213/50000000
def scE45CutMargins : Fin 3 → ℚ := ![34741699/10000000000, 664993/250000000, 12717361/10000000000]

theorem scE45Cut_roots_ok : scE45CutCell.rootsOK scE45CutRoots = true := by decide +kernel

theorem scE45Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE45CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE45Cut_margin_le (i : Fin 3) : curvatureLoss scE45CutCell scE45CutCaps i ≤ scE45CutMargins i := by
  fin_cases i <;> decide +kernel


end HlawkaSchatten.BelowExponent.Vertex
