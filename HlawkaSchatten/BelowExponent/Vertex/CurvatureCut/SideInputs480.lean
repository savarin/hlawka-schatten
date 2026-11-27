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

def scE174CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨2/5, 33/80⟩, ⟨3/20, 13/80⟩⟩
def scE174CutRoots : Fin 3 → RatBounds := ![⟨452770460172609/281474976710656, 120063289662355/70368744177664⟩, ⟨177501226928833/140737488355328, 23639343855529/17592186044416⟩, ⟨303978670935189/281474976710656, 82343838008939/70368744177664⟩]
def scE174CutCaps : Fin 3 → Fin 3 → ℚ := ![![4582028031/50000000, 5664340573/100000000, 936491647/25000000], ![675316277/20000000, 3044255471/100000000, 188487607/10000000], ![445106233/100000000, 352069717/100000000, 58298119/20000000]]
def scE174CutWeightFloor : ℚ := 147433943/100000000
def scE174CutMargins : Fin 3 → ℚ := ![25362781/10000000000, 17696613/10000000000, 5783529/5000000000]

theorem scE174Cut_roots_ok : scE174CutCell.rootsOK scE174CutRoots = true := by decide +kernel

theorem scE174Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE174CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE174Cut_margin_le (i : Fin 3) : curvatureLoss scE174CutCell scE174CutCaps i ≤ scE174CutMargins i := by
  fin_cases i <;> decide +kernel

def scE175CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨2/5, 33/80⟩, ⟨13/80, 1/6⟩⟩
def scE175CutRoots : Fin 3 → RatBounds := ![⟨452617366826925/281474976710656, 478821490815141/281474976710656⟩, ⟨354416995240987/281474976710656, 376310633859861/281474976710656⟩, ⟨303392119242131/281474976710656, 163721530990547/140737488355328⟩]
def scE175CutCaps : Fin 3 → Fin 3 → ℚ := ![![9056163959/100000000, 5604371293/100000000, 3660955001/100000000], ![26098359/781250, 1488317941/50000000, 1821125837/100000000], ![10548121/3125000, 26555297/10000000, 223327133/100000000]]
def scE175CutWeightFloor : ℚ := 150565821/100000000
def scE175CutMargins : Fin 3 → ℚ := ![24285661/10000000000, 16817409/10000000000, 2151131/2000000000]

theorem scE175Cut_roots_ok : scE175CutCell.rootsOK scE175CutRoots = true := by decide +kernel

theorem scE175Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE175CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE175Cut_margin_le (i : Fin 3) : curvatureLoss scE175CutCell scE175CutCaps i ≤ scE175CutMargins i := by
  fin_cases i <;> decide +kernel

def scE176CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨33/80, 17/40⟩, ⟨1/8, 11/80⟩⟩
def scE176CutRoots : Fin 3 → RatBounds := ![⟨453779167686393/281474976710656, 481294696166929/281474976710656⟩, ⟨177140435965085/140737488355328, 377555450813953/281474976710656⟩, ⟨310730578238729/281474976710656, 336419122170449/281474976710656⟩]
def scE176CutCaps : Fin 3 → Fin 3 → ℚ := ![![8572685821/100000000, 2614237731/50000000, 3561075041/100000000], ![3134121119/100000000, 344958529/12500000, 182817853/10000000], ![48268369/10000000, 93928453/25000000, 322024829/100000000]]
def scE176CutWeightFloor : ℚ := 35917359/25000000
def scE176CutMargins : Fin 3 → ℚ := ![23807599/10000000000, 816783/500000000, 11154841/10000000000]

theorem scE176Cut_roots_ok : scE176CutCell.rootsOK scE176CutRoots = true := by decide +kernel

theorem scE176Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE176CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE176Cut_margin_le (i : Fin 3) : curvatureLoss scE176CutCell scE176CutCaps i ≤ scE176CutMargins i := by
  fin_cases i <;> decide +kernel

def scE177CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨33/80, 17/40⟩, ⟨11/80, 3/20⟩⟩
def scE177CutRoots : Fin 3 → RatBounds := ![⟨452592230868271/281474976710656, 60002791022189/35184372088832⟩, ⟨88096087149615/70368744177664, 187754224495963/140737488355328⟩, ⟨308832165070697/281474976710656, 167177120086679/140737488355328⟩]
def scE177CutCaps : Fin 3 → Fin 3 → ℚ := ![![8736097981/100000000, 1333498319/25000000, 3637587241/100000000], ![798164857/25000000, 1404376467/50000000, 930760183/50000000], ![462413171/100000000, 359673703/100000000, 30834799/10000000]]
def scE177CutWeightFloor : ℚ := 146158623/100000000
def scE177CutMargins : Fin 3 → ℚ := ![12100753/5000000000, 16606289/10000000000, 11342687/10000000000]

theorem scE177Cut_roots_ok : scE177CutCell.rootsOK scE177CutRoots = true := by decide +kernel

theorem scE177Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE177CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE177Cut_margin_le (i : Fin 3) : curvatureLoss scE177CutCell scE177CutCaps i ≤ scE177CutMargins i := by
  fin_cases i <;> decide +kernel

def scE178CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨33/80, 17/40⟩, ⟨3/20, 13/80⟩⟩
def scE178CutRoots : Fin 3 → RatBounds := ![⟨110216311215/68719476736, 119698685138047/70368744177664⟩, ⟨175278678173501/140737488355328, 373537928116277/281474976710656⟩, ⟨307004391038349/281474976710656, 166183798880797/140737488355328⟩]
def scE178CutCaps : Fin 3 → Fin 3 → ℚ := ![![1112422807/12500000, 5439187937/100000000, 464240869/12500000], ![325104559/10000000, 285776109/10000000, 473701779/25000000], ![443378067/100000000, 344626693/100000000, 295513863/100000000]]
def scE178CutWeightFloor : ℚ := 148649669/100000000
def scE178CutMargins : Fin 3 → ℚ := ![12298639/5000000000, 8439039/5000000000, 2306347/2000000000]

theorem scE178Cut_roots_ok : scE178CutCell.rootsOK scE178CutRoots = true := by decide +kernel

theorem scE178Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE178CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE178Cut_margin_le (i : Fin 3) : curvatureLoss scE178CutCell scE178CutCaps i ≤ scE178CutMargins i := by
  fin_cases i <;> decide +kernel

def scE179CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨33/80, 17/40⟩, ⟨13/80, 1/6⟩⟩
def scE179CutRoots : Fin 3 → RatBounds := ![⟨451296186962689/281474976710656, 477368827432089/281474976710656⟩, ⟨87493082071993/70368744177664, 371620521508529/281474976710656⟩, ⟨76604576526493/70368744177664, 82609599535553/70368744177664⟩]
def scE179CutCaps : Fin 3 → Fin 3 → ℚ := ![![8793084519/100000000, 5381285779/100000000, 1451943/40000], ![1607756193/50000000, 2791041693/100000000, 366277291/20000000], ![4201333/1250000, 51949943/20000000, 45220853/20000000]]
def scE179CutWeightFloor : ℚ := 4743653/3125000
def scE179CutMargins : Fin 3 → ℚ := ![23527231/10000000000, 16017947/10000000000, 267889/250000000]

theorem scE179Cut_roots_ok : scE179CutCell.rootsOK scE179CutRoots = true := by decide +kernel

theorem scE179Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE179CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE179Cut_margin_le (i : Fin 3) : curvatureLoss scE179CutCell scE179CutCaps i ≤ scE179CutMargins i := by
  fin_cases i <;> decide +kernel

def scE180CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨17/40, 7/16⟩, ⟨1/8, 11/80⟩⟩
def scE180CutRoots : Fin 3 → RatBounds := ![⟨56582233800373/35184372088832, 480080211642329/281474976710656⟩, ⟨87497584420883/70368744177664, 373054328790541/281474976710656⟩, ⟨156913094212387/140737488355328, 21219402741357/17592186044416⟩]
def scE180CutCaps : Fin 3 → Fin 3 → ℚ := ![![417637331/5000000, 503913189/10000000, 55340443/1562500], ![379141037/12500000, 1298835797/50000000, 369076181/20000000], ![481165689/100000000, 183990563/50000000, 326622953/100000000]]
def scE180CutWeightFloor : ℚ := 72444669/50000000
def scE180CutMargins : Fin 3 → ℚ := ![11588907/5000000000, 3126869/2000000000, 11159751/10000000000]

theorem scE180Cut_roots_ok : scE180CutCell.rootsOK scE180CutRoots = true := by decide +kernel

theorem scE180Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE180CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE180Cut_margin_le (i : Fin 3) : curvatureLoss scE180CutCell scE180CutCaps i ≤ scE180CutMargins i := by
  fin_cases i <;> decide +kernel

def scE181CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨17/40, 7/16⟩, ⟨11/80, 3/20⟩⟩
def scE181CutRoots : Fin 3 → RatBounds := ![⟨28217284990311/17592186044416, 478814035962759/281474976710656⟩, ⟨174047517434989/140737488355328, 185503929364269/140737488355328⟩, ⟨311928990794961/281474976710656, 168724466985615/140737488355328⟩]
def scE181CutCaps : Fin 3 → Fin 3 → ℚ := ![![4256043139/50000000, 5140672227/100000000, 3618442719/100000000], ![617941531/20000000, 528774963/20000000, 939455977/50000000], ![92188191/20000000, 88064827/25000000, 3127441/1000000]]
def scE181CutWeightFloor : ℚ := 73695853/50000000
def scE181CutMargins : Fin 3 → ℚ := ![2356003/1000000000, 79461/50000000, 226957/200000000]

theorem scE181Cut_roots_ok : scE181CutCell.rootsOK scE181CutRoots = true := by decide +kernel

theorem scE181Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE181CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE181Cut_margin_le (i : Fin 3) : curvatureLoss scE181CutCell scE181CutCaps i ≤ scE181CutMargins i := by
  fin_cases i <;> decide +kernel

def scE182CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨17/40, 7/16⟩, ⟨3/20, 13/80⟩⟩
def scE182CutRoots : Fin 3 → RatBounds := ![⟨450335780626319/281474976710656, 477592436551401/281474976710656⟩, ⟨346269323850477/281474976710656, 369037968424915/281474976710656⟩, ⟨9690697445251/8796093022208, 335465455136035/281474976710656⟩]
def scE182CutCaps : Fin 3 → Fin 3 → ℚ := ![![8671305009/100000000, 1048380119/20000000, 3694922993/100000000], ![196633729/6250000, 2690007323/100000000, 956194657/50000000], ![441949843/100000000, 84377873/25000000, 299720837/100000000]]
def scE182CutWeightFloor : ℚ := 9368499/6250000
def scE182CutMargins : Fin 3 → ℚ := ![2394413/1000000000, 1615121/1000000000, 461487/400000000]

theorem scE182Cut_roots_ok : scE182CutCell.rootsOK scE182CutRoots = true := by decide +kernel

theorem scE182Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE182CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE182Cut_margin_le (i : Fin 3) : curvatureLoss scE182CutCell scE182CutCaps i ≤ scE182CutMargins i := by
  fin_cases i <;> decide +kernel

def scE183CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨17/40, 7/16⟩, ⟨13/80, 1/6⟩⟩
def scE183CutRoots : Fin 3 → RatBounds := ![⟨56273583737907/35184372088832, 476171291047281/281474976710656⟩, ⟨21605288336827/17592186044416, 367121521102293/281474976710656⟩, ⟨309516666294703/281474976710656, 333539045247087/281474976710656⟩]
def scE183CutCaps : Fin 3 → Fin 3 → ℚ := ![![4283209/50000, 518589931/10000000, 3611674499/100000000], ![777750647/25000000, 2624086711/100000000, 369840947/20000000], ![167462131/50000000, 254233023/100000000, 114521783/50000000]]
def scE183CutWeightFloor : ℚ := 38264743/25000000
def scE183CutMargins : Fin 3 → ℚ := ![11440073/5000000000, 3827263/2500000000, 5357743/5000000000]

theorem scE183Cut_roots_ok : scE183CutCell.rootsOK scE183CutRoots = true := by decide +kernel

theorem scE183Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE183CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE183Cut_margin_le (i : Fin 3) : curvatureLoss scE183CutCell scE183CutCaps i ≤ scE183CutMargins i := by
  fin_cases i <;> decide +kernel

def scE184CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨7/16, 9/20⟩, ⟨1/8, 11/80⟩⟩
def scE184CutRoots : Fin 3 → RatBounds := ![⟨225873667115343/140737488355328, 479117361698963/281474976710656⟩, ⟨345847110180127/281474976710656, 368733527151451/281474976710656⟩, ⟨158499554354991/140737488355328, 85678124731951/70368744177664⟩]
def scE184CutCaps : Fin 3 → Fin 3 → ℚ := ![![1633041721/20000000, 2436967741/50000000, 70693709/2000000], ![2950443143/100000000, 245165497/10000000, 467493703/25000000], ![11998823/2500000, 18028739/5000000, 165711357/50000000]]
def scE184CutWeightFloor : ℚ := 570864/390625
def scE184CutMargins : Fin 3 → ℚ := ![11323833/5000000000, 7506021/5000000000, 1400411/1250000000]

theorem scE184Cut_roots_ok : scE184CutCell.rootsOK scE184CutRoots = true := by decide +kernel

theorem scE184Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE184CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE184Cut_margin_le (i : Fin 3) : curvatureLoss scE184CutCell scE184CutCaps i ≤ scE184CutMargins i := by
  fin_cases i <;> decide +kernel

def scE185CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨7/16, 9/20⟩, ⟨11/80, 3/20⟩⟩
def scE185CutRoots : Fin 3 → RatBounds := ![⟨450570549541461/281474976710656, 238928079595119/140737488355328⟩, ⟨343952691741673/281474976710656, 366687100815037/281474976710656⟩, ⟨39387875184719/35184372088832, 5322719376191/4398046511104⟩]
def scE185CutCaps : Fin 3 → Fin 3 → ℚ := ![![8321128377/100000000, 4971975243/100000000, 451466259/12500000], ![3005397931/100000000, 2495264777/100000000, 380764771/20000000], ![91952953/20000000, 172579769/50000000, 3966681/1250000]]
def scE185CutWeightFloor : ℚ := 1189257/800000
def scE185CutMargins : Fin 3 → ℚ := ![230201/100000000, 15258593/10000000000, 11392361/10000000000]

theorem scE185Cut_roots_ok : scE185CutCell.rootsOK scE185CutRoots = true := by decide +kernel

theorem scE185Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE185CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE185Cut_margin_le (i : Fin 3) : curvatureLoss scE185CutCell scE185CutCaps i ≤ scE185CutMargins i := by
  fin_cases i <;> decide +kernel

def scE186CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨7/16, 9/20⟩, ⟨3/20, 13/80⟩⟩
def scE186CutRoots : Fin 3 → RatBounds := ![⟨56179268374773/35184372088832, 1861872535743/1099511627776⟩, ⟨342127934235749/281474976710656, 45589670865347/35184372088832⟩, ⟨9789915846533/8796093022208, 84668353183741/70368744177664⟩]
def scE186CutCaps : Fin 3 → Fin 3 → ℚ := ![![8476932537/100000000, 2534856447/50000000, 3688598287/100000000], ![3060209433/100000000, 1269404503/50000000, 968810113/50000000], ![44080881/10000000, 33069981/10000000, 304115107/100000000]]
def scE186CutWeightFloor : ℚ := 151175029/100000000
def scE186CutMargins : Fin 3 → ℚ := ![5848609/2500000000, 15506293/10000000000, 11582683/10000000000]

theorem scE186Cut_roots_ok : scE186CutCell.rootsOK scE186CutRoots = true := by decide +kernel

theorem scE186Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE186CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE186Cut_margin_le (i : Fin 3) : curvatureLoss scE186CutCell scE186CutCaps i ≤ scE186CutMargins i := by
  fin_cases i <;> decide +kernel

def scE187CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨7/16, 9/20⟩, ⟨13/80, 1/6⟩⟩
def scE187CutRoots : Fin 3 → RatBounds := ![⟨224644601013947/140737488355328, 29701376779009/17592186044416⟩, ⟨341543437608783/281474976710656, 362801409009377/281474976710656⟩, ⟨78173012302429/70368744177664, 168374742277703/140737488355328⟩]
def scE187CutCaps : Fin 3 → Fin 3 → ℚ := ![![2093320761/25000000, 5015461851/100000000, 3606055157/100000000], ![3025408571/100000000, 1236795177/50000000, 1874580497/100000000], ![333981217/100000000, 248981147/100000000, 116073761/50000000]]
def scE187CutWeightFloor : ℚ := 7717711/5000000
def scE187CutMargins : Fin 3 → ℚ := ![22335549/10000000000, 14337/9765625, 5377373/5000000000]

theorem scE187Cut_roots_ok : scE187CutCell.rootsOK scE187CutRoots = true := by decide +kernel

theorem scE187Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE187CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE187Cut_margin_le (i : Fin 3) : curvatureLoss scE187CutCell scE187CutCaps i ≤ scE187CutMargins i := by
  fin_cases i <;> decide +kernel

def scE188CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨9/20, 37/80⟩, ⟨1/8, 11/80⟩⟩
def scE188CutRoots : Fin 3 → RatBounds := ![⟨225521513118325/140737488355328, 119600182496549/70368744177664⟩, ⟨170920792707319/140737488355328, 182290960094669/140737488355328⟩, ⟨160127233361461/140737488355328, 10813446980373/8796093022208⟩]
def scE188CutCaps : Fin 3 → Fin 3 → ℚ := ![![4003924617/50000000, 4730686953/100000000, 3539610017/100000000], ![45075263/1562500, 46396559/2000000, 951034997/50000000], ![479034683/100000000, 8836793/2500000, 336429309/100000000]]
def scE188CutWeightFloor : ℚ := 147427151/100000000
def scE188CutMargins : Fin 3 → ℚ := ![11105177/5000000000, 903807/625000000, 1128537/1000000000]

theorem scE188Cut_roots_ok : scE188CutCell.rootsOK scE188CutRoots = true := by decide +kernel

theorem scE188Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE188CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE188Cut_margin_le (i : Fin 3) : curvatureLoss scE188CutCell scE188CutCaps i ≤ scE188CutMargins i := by
  fin_cases i <;> decide +kernel

def scE189CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨9/20, 37/80⟩, ⟨11/80, 3/20⟩⟩
def scE189CutRoots : Fin 3 → RatBounds := ![⟨112467421385729/70368744177664, 238571651698619/140737488355328⟩, ⟨42493467850887/35184372088832, 11329221225909/8796093022208⟩, ⟨318359307758581/281474976710656, 85993641293631/70368744177664⟩]
def scE189CutCaps : Fin 3 → Fin 3 → ℚ := ![![127514989/1562500, 241282931/5000000, 1808646999/50000000], ![2938457601/100000000, 23611/1000, 968183631/50000000], ![229437139/50000000, 67670433/20000000, 161062091/50000000]]
def scE189CutWeightFloor : ℚ := 149957087/100000000
def scE189CutMargins : Fin 3 → ℚ := ![5643697/2500000000, 14697483/10000000000, 717259/625000000]

theorem scE189Cut_roots_ok : scE189CutCell.rootsOK scE189CutRoots = true := by decide +kernel

theorem scE189Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE189CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE189Cut_margin_le (i : Fin 3) : curvatureLoss scE189CutCell scE189CutCaps i ≤ scE189CutMargins i := by
  fin_cases i <;> decide +kernel

def scE190CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨9/20, 37/80⟩, ⟨3/20, 13/80⟩⟩
def scE190CutRoots : Fin 3 → RatBounds := ![⟨448736613361413/281474976710656, 475930165062577/281474976710656⟩, ⟨169061818921449/140737488355328, 360565056364797/281474976710656⟩, ⟨158267225879597/140737488355328, 170998234082375/140737488355328⟩]
def scE190CutCaps : Fin 3 → Fin 3 → ℚ := ![![1039244713/12500000, 76880263/1562500, 3694798527/100000000], ![2991958469/100000000, 600577743/25000000, 1970612503/100000000], ![439945003/100000000, 1620851/500000, 308701583/100000000]]
def scE190CutWeightFloor : ℚ := 152489037/100000000
def scE190CutMargins : Fin 3 → ℚ := ![1433821/625000000, 1866899/1250000000, 11668189/10000000000]

theorem scE190Cut_roots_ok : scE190CutCell.rootsOK scE190CutRoots = true := by decide +kernel

theorem scE190Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE190CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE190Cut_margin_le (i : Fin 3) : curvatureLoss scE190CutCell scE190CutCaps i ≤ scE190CutMargins i := by
  fin_cases i <;> decide +kernel

def scE191CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨9/20, 37/80⟩, ⟨13/80, 1/6⟩⟩
def scE191CutRoots : Fin 3 → RatBounds := ![⟨224296647087777/140737488355328, 474515685428887/281474976710656⟩, ⟨21096203734033/17592186044416, 179324573243983/140737488355328⟩, ⟨78987385961673/70368744177664, 340074704481473/281474976710656⟩]
def scE191CutCaps : Fin 3 → Fin 3 → ℚ := ![![8211380399/100000000, 4867699081/100000000, 1806424817/50000000], ![739358919/25000000, 2337701267/100000000, 476906961/25000000], ![333268507/100000000, 15248437/6250000, 47083971/20000000]]
def scE191CutWeightFloor : ℚ := 155684907/100000000
def scE191CutMargins : Fin 3 → ℚ := ![10943209/5000000000, 7062997/5000000000, 1354159/1250000000]

theorem scE191Cut_roots_ok : scE191CutCell.rootsOK scE191CutRoots = true := by decide +kernel

theorem scE191Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE191CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE191Cut_margin_le (i : Fin 3) : curvatureLoss scE191CutCell scE191CutCaps i ≤ scE191CutMargins i := by
  fin_cases i <;> decide +kernel

def scE192CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨37/80, 19/40⟩, ⟨1/8, 11/80⟩⟩
def scE192CutRoots : Fin 3 → RatBounds := ![⟨225270742017137/140737488355328, 477926328692097/281474976710656⟩, ⟨168982467216349/140737488355328, 360589445104563/281474976710656⟩, ⟨323597670715043/281474976710656, 349469420321865/281474976710656⟩]
def scE192CutCaps : Fin 3 → Fin 3 → ℚ := ![![3939470651/50000000, 1151894871/25000000, 711318603/20000000], ![567060941/20000000, 2200666679/100000000, 1941886667/100000000], ![478403037/100000000, 173325801/50000000, 68329877/20000000]]
def scE192CutWeightFloor : ℚ := 5949981/4000000
def scE192CutMargins : Fin 3 → ℚ := ![21860643/10000000000, 1397441/1000000000, 11406503/10000000000]

theorem scE192Cut_roots_ok : scE192CutCell.rootsOK scE192CutRoots = true := by decide +kernel

theorem scE192Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE192CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE192Cut_margin_le (i : Fin 3) : curvatureLoss scE192CutCell scE192CutCaps i ≤ scE192CutMargins i := by
  fin_cases i <;> decide +kernel

def scE193CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨37/80, 19/40⟩, ⟨11/80, 3/20⟩⟩
def scE193CutRoots : Fin 3 → RatBounds := ![⟨224685259765385/140737488355328, 476671497015645/281474976710656⟩, ⟨336071384624479/281474976710656, 358541757512109/281474976710656⟩, ⟨321703300478939/281474976710656, 173708030523027/140737488355328⟩]
def scE193CutCaps : Fin 3 → Fin 3 → ℚ := ![![8029819561/100000000, 4699878819/100000000, 1817585097/50000000], ![2887923781/100000000, 2239829079/100000000, 988382889/50000000], ![57282729/12500000, 10369299/3125000, 163559827/50000000]]
def scE193CutWeightFloor : ℚ := 75646953/50000000
def scE193CutMargins : Fin 3 → ℚ := ![22218761/10000000000, 14202199/10000000000, 11599719/10000000000]

theorem scE193Cut_roots_ok : scE193CutCell.rootsOK scE193CutRoots = true := by decide +kernel

theorem scE193Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE193CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE193Cut_margin_le (i : Fin 3) : curvatureLoss scE193CutCell scE193CutCaps i ≤ scE193CutMargins i := by
  fin_cases i <;> decide +kernel

def scE194CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨37/80, 19/40⟩, ⟨3/20, 13/80⟩⟩
def scE194CutRoots : Fin 3 → RatBounds := ![⟨448239745013647/281474976710656, 475460868437421/281474976710656⟩, ⟨334247655953625/281474976710656, 178285512917097/140737488355328⟩, ⟨319879126246271/281474976710656, 86360040540823/70368744177664⟩]
def scE194CutCaps : Fin 3 → Fin 3 → ℚ := ![![8180588821/100000000, 598986531/12500000, 928391029/25000000], ![2940405709/100000000, 1139467163/50000000, 2011593139/100000000], ![17574041/4000000, 158951863/50000000, 78371631/25000000]]
def scE194CutWeightFloor : ℚ := 3076807/2000000
def scE194CutMargins : Fin 3 → ℚ := ![56447/25000000, 7215557/5000000000, 11794227/10000000000]

theorem scE194Cut_roots_ok : scE194CutCell.rootsOK scE194CutRoots = true := by decide +kernel

theorem scE194Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE194CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE194Cut_margin_le (i : Fin 3) : curvatureLoss scE194CutCell scE194CutCaps i ≤ scE194CutMargins i := by
  fin_cases i <;> decide +kernel

def scE195CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨37/80, 19/40⟩, ⟨13/80, 1/6⟩⟩
def scE195CutRoots : Fin 3 → RatBounds := ![⟨56012189646891/35184372088832, 237024160077019/140737488355328⟩, ⟨333663308894027/281474976710656, 44331843492423/35184372088832⟩, ⟨319294518861181/281474976710656, 343520234654985/281474976710656⟩]
def scE195CutCaps : Fin 3 → Fin 3 → ℚ := ![![8078924851/100000000, 4740742863/100000000, 363210177/10000000], ![726526047/25000000, 5537109/250000, 389714867/20000000], ![332779467/100000000, 47839557/20000000, 29858193/12500000]]
def scE195CutWeightFloor : ℚ := 157053409/100000000
def scE195CutMargins : Fin 3 → ℚ := ![21527353/10000000000, 170463/125000000, 2737899/2500000000]

theorem scE195Cut_roots_ok : scE195CutCell.rootsOK scE195CutRoots = true := by decide +kernel

theorem scE195Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE195CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE195Cut_margin_le (i : Fin 3) : curvatureLoss scE195CutCell scE195CutCaps i ≤ scE195CutMargins i := by
  fin_cases i <;> decide +kernel

def scE196CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨19/40, 39/80⟩, ⟨1/8, 11/80⟩⟩
def scE196CutRoots : Fin 3 → RatBounds := ![⟨225120133485815/140737488355328, 477691535287625/281474976710656⟩, ⟨334209014053315/281474976710656, 356746988632429/281474976710656⟩, ⟨163517226251457/140737488355328, 176518000995955/140737488355328⟩]
def scE196CutCaps : Fin 3 → Fin 3 → ℚ := ![![7777205089/100000000, 562893317/12500000, 3585851759/100000000], ![1400640929/50000000, 1046442469/50000000, 124367283/6250000], ![478052627/100000000, 340096469/100000000, 347091093/100000000]]
def scE196CutWeightFloor : ℚ := 75055359/50000000
def scE196CutMargins : Fin 3 → ℚ := ![5398701/2500000000, 108377/80000000, 11568007/10000000000]

theorem scE196Cut_roots_ok : scE196CutCell.rootsOK scE196CutRoots = true := by decide +kernel

theorem scE196Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE196CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE196Cut_margin_le (i : Fin 3) : curvatureLoss scE196CutCell scE196CutCaps i ≤ scE196CutMargins i := by
  fin_cases i <;> decide +kernel

def scE197CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨19/40, 39/80⟩, ⟨11/80, 3/20⟩⟩
def scE197CutRoots : Fin 3 → RatBounds := ![⟨224535310330447/140737488355328, 476438128358707/281474976710656⟩, ⟨166157748858685/140737488355328, 177349022860803/140737488355328⟩, ⟨81285173364117/70368744177664, 350984666454513/281474976710656⟩]
def scE197CutCaps : Fin 3 → Fin 3 → ℚ := ![![7926406429/100000000, 1148284807/25000000, 1832792253/50000000], ![2853163207/100000000, 2130144293/100000000, 405097539/20000000], ![57240283/12500000, 81384607/25000000, 83082199/25000000]]
def scE197CutWeightFloor : ℚ := 152670023/100000000
def scE197CutMargins : Fin 3 → ℚ := ![21948227/10000000000, 13767231/10000000000, 1470557/1250000000]

theorem scE197Cut_roots_ok : scE197CutCell.rootsOK scE197CutRoots = true := by decide +kernel

theorem scE197Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE197CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE197Cut_margin_le (i : Fin 3) : curvatureLoss scE197CutCell scE197CutCaps i ≤ scE197CutMargins i := by
  fin_cases i <;> decide +kernel

def scE198CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨19/40, 39/80⟩, ⟨3/20, 13/80⟩⟩
def scE198CutRoots : Fin 3 → RatBounds := ![⟨447941120602775/281474976710656, 237614439039953/140737488355328⟩, ⟨330491892061229/281474976710656, 176363104004799/140737488355328⟩, ⟨40414628367491/35184372088832, 174505310209929/140737488355328⟩]
def scE198CutCaps : Fin 3 → Fin 3 → ℚ := ![![8075500149/100000000, 2341426269/50000000, 3745129387/100000000], ![2904909661/100000000, 541837499/25000000, 128815443/6250000], ![439021897/100000000, 155941837/50000000, 159238793/50000000]]
def scE198CutWeightFloor : ℚ := 155231439/100000000
def scE198CutMargins : Fin 3 → ℚ := ![11151789/5000000000, 279769/200000000, 2392443/2000000000]

theorem scE198Cut_roots_ok : scE198CutCell.rootsOK scE198CutRoots = true := by decide +kernel

theorem scE198Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE198CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE198Cut_margin_le (i : Fin 3) : curvatureLoss scE198CutCell scE198CutCaps i ≤ scE198CutMargins i := by
  fin_cases i <;> decide +kernel

def scE199CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨19/40, 39/80⟩, ⟨13/80, 1/6⟩⟩
def scE199CutRoots : Fin 3 → RatBounds := ![⟨447799453477611/281474976710656, 473817340756827/281474976710656⟩, ⟨20619218488111/17592186044416, 87702292121571/70368744177664⟩, ⟨322732665128907/281474976710656, 173546093834581/140737488355328⟩]
def scE199CutCaps : Fin 3 → Fin 3 → ℚ := ![![1993648909/25000000, 926615437/20000000, 366404837/10000000], ![358845721/12500000, 2103690809/100000000, 249736283/12500000], ![20781851/6250000, 29329351/12500000, 1939927/800000]]
def scE199CutWeightFloor : ℚ := 158462233/100000000
def scE199CutMargins : Fin 3 → ℚ := ![10627253/5000000000, 1320867/1000000000, 5555549/5000000000]

theorem scE199Cut_roots_ok : scE199CutCell.rootsOK scE199CutRoots = true := by decide +kernel

theorem scE199Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE199CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE199Cut_margin_le (i : Fin 3) : curvatureLoss scE199CutCell scE199CutCaps i ≤ scE199CutMargins i := by
  fin_cases i <;> decide +kernel

def scE200CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨39/80, 1/2⟩, ⟨1/8, 11/80⟩⟩
def scE200CutRoots : Fin 3 → RatBounds := ![⟨450137922190781/281474976710656, 238847525718601/140737488355328⟩, ⟨165283144186081/140737488355328, 353046290203395/281474976710656⟩, ⟨330570913727641/281474976710656, 44592105015743/35184372088832⟩]
def scE200CutCaps : Fin 3 → Fin 3 → ℚ := ![![7701775817/100000000, 4416221863/100000000, 3627795237/100000000], ![698507831/25000000, 125478483/6250000, 2065412999/100000000], ![238990289/50000000, 333790499/100000000, 176382087/50000000]]
def scE200CutWeightFloor : ℚ := 151513289/100000000
def scE200CutMargins : Fin 3 → ℚ := ![1071659/500000000, 13198571/10000000000, 590427/500000000]

theorem scE200Cut_roots_ok : scE200CutCell.rootsOK scE200CutRoots = true := by decide +kernel

theorem scE200Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE200CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE200Cut_margin_le (i : Fin 3) : curvatureLoss scE200CutCell scE200CutCaps i ≤ scE200CutMargins i := by
  fin_cases i <;> decide +kernel

def scE201CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨39/80, 1/2⟩, ⟨11/80, 3/20⟩⟩
def scE201CutRoots : Fin 3 → RatBounds := ![⟨448968541754077/281474976710656, 59555238086323/35184372088832⟩, ⟨328672568326119/281474976710656, 175497851930937/140737488355328⟩, ⟨164338784786405/140737488355328, 354687157484343/281474976710656⟩]
def scE201CutCaps : Fin 3 → Fin 3 → ℚ := ![![3924920369/50000000, 4504249367/100000000, 741791691/20000000], ![569155267/20000000, 1021743491/50000000, 2102296653/100000000], ![228926403/50000000, 159749739/50000000, 67552207/20000000]]
def scE201CutWeightFloor : ℚ := 154088027/100000000
def scE201CutMargins : Fin 3 → ℚ := ![21784121/10000000000, 1341257/1000000000, 6004899/5000000000]

theorem scE201Cut_roots_ok : scE201CutCell.rootsOK scE201CutRoots = true := by decide +kernel

theorem scE201Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE201CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE201Cut_margin_le (i : Fin 3) : curvatureLoss scE201CutCell scE201CutCaps i ≤ scE201CutMargins i := by
  fin_cases i <;> decide +kernel

def scE202CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨39/80, 1/2⟩, ⟨3/20, 13/80⟩⟩
def scE202CutRoots : Fin 3 → RatBounds := ![⟨223919649222143/140737488355328, 118808226668679/70368744177664⟩, ⟨81712213465583/70368744177664, 174511191428883/140737488355328⟩, ⟨81713554638411/70368744177664, 352714603808995/281474976710656⟩]
def scE202CutCaps : Fin 3 → Fin 3 → ℚ := ![![7997798141/100000000, 918400609/20000000, 1894964167/50000000], ![181086679/6250000, 519816641/25000000, 2139127083/100000000], ![438954951/100000000, 306095307/100000000, 323683901/100000000]]
def scE202CutWeightFloor : ℚ := 78332461/50000000
def scE202CutMargins : Fin 3 → ℚ := ![22136993/10000000000, 6813833/5000000000, 6106191/5000000000]

theorem scE202Cut_roots_ok : scE202CutCell.rootsOK scE202CutRoots = true := by decide +kernel

theorem scE202Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE202CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE202Cut_margin_le (i : Fin 3) : curvatureLoss scE202CutCell scE202CutCaps i ≤ scE202CutMargins i := by
  fin_cases i <;> decide +kernel

def scE203CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨39/80, 1/2⟩, ⟨13/80, 1/6⟩⟩
def scE203CutRoots : Fin 3 → RatBounds := ![⟨223848831760843/140737488355328, 236910732312001/140737488355328⟩, ⟨163132167483485/140737488355328, 173552103962263/140737488355328⟩, ⟨40783755201903/35184372088832, 175398654605459/140737488355328⟩]
def scE203CutCaps : Fin 3 → Fin 3 → ℚ := ![![3948751373/50000000, 908699349/20000000, 3709124969/100000000], ![715808409/25000000, 2015974389/100000000, 83025269/4000000], ![332456569/100000000, 28784147/12500000, 123151751/50000000]]
def scE203CutWeightFloor : ℚ := 159914033/100000000
def scE203CutMargins : Fin 3 → ℚ := ![21089211/10000000000, 2512/1953125, 2270361/2000000000]

theorem scE203Cut_roots_ok : scE203CutCell.rootsOK scE203CutRoots = true := by decide +kernel

theorem scE203Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE203CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE203Cut_margin_le (i : Fin 3) : curvatureLoss scE203CutCell scE203CutCaps i ≤ scE203CutMargins i := by
  fin_cases i <;> decide +kernel


end HlawkaSchatten.BelowExponent.Vertex
