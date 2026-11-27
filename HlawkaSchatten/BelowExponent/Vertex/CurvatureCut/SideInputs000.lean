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

def scS0CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨3/16, 1/5⟩, ⟨0, 1/40⟩⟩
def scS0CutRoots : Fin 3 → RatBounds := ![⟨556699255552455/281474976710656, 151478115051975/70368744177664⟩, ⟨510358735327763/281474976710656, 139206690483897/70368744177664⟩, ⟨283134998891393/281474976710656, 325635155771723/281474976710656⟩]
def scS0CutCaps : Fin 3 → Fin 3 → ℚ := ![![6831590751/25000000, 21370533599/100000000, 7763344927/100000000], ![14179267117/100000000, 15300919891/100000000, 1769713839/50000000], ![262154351/20000000, 687560511/50000000, 286687241/50000000]]
def scS0CutWeightFloor : ℚ := 50294879/50000000
def scS0CutMargins : Fin 3 → ℚ := ![91306089/10000000000, 41183533/5000000000, 1659701/625000000]

theorem scS0Cut_roots_ok : scS0CutCell.rootsOK scS0CutRoots = true := by decide +kernel

theorem scS0Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS0CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS0Cut_margin_le (i : Fin 3) : curvatureLoss scS0CutCell scS0CutCaps i ≤ scS0CutMargins i := by
  fin_cases i <;> decide +kernel

def scS1CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨3/16, 1/5⟩, ⟨1/40, 1/20⟩⟩
def scS1CutRoots : Fin 3 → RatBounds := ![⟨138115251253947/70368744177664, 37561453788327/17592186044416⟩, ⟨504480593644521/281474976710656, 550069316974087/281474976710656⟩, ⟨69394159556565/70368744177664, 159451790916845/140737488355328⟩]
def scS1CutCaps : Fin 3 → Fin 3 → ℚ := ![![3574096411/12500000, 2799683101/12500000, 4041998539/50000000], ![1852559111/12500000, 7978554583/50000000, 3692028333/100000000], ![235623279/20000000, 38473419/3125000, 512925687/100000000]]
def scS1CutWeightFloor : ℚ := 105161811/100000000
def scS1CutMargins : Fin 3 → ℚ := ![93995527/10000000000, 84529633/10000000000, 13503641/5000000000]

theorem scS1Cut_roots_ok : scS1CutCell.rootsOK scS1CutRoots = true := by decide +kernel

theorem scS1Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS1CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS1Cut_margin_le (i : Fin 3) : curvatureLoss scS1CutCell scS1CutCaps i ≤ scS1CutMargins i := by
  fin_cases i <;> decide +kernel

def scS2CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨3/16, 1/5⟩, ⟨1/20, 3/40⟩⟩
def scS2CutRoots : Fin 3 → RatBounds := ![⟨17142123971219/8796093022208, 596452378308717/281474976710656⟩, ⟨31192387027435/17592186044416, 543882403038035/281474976710656⟩, ⟨68125120229005/70368744177664, 78195609474947/70368744177664⟩]
def scS2CutCaps : Fin 3 → Fin 3 → ℚ := ![![14925384549/50000000, 731711101/3125000, 4201055693/50000000], ![15457131617/100000000, 8304419569/50000000, 3843099549/100000000], ![1064024027/100000000, 1108045667/100000000, 23065293/5000000]]
def scS2CutWeightFloor : ℚ := 54869589/50000000
def scS2CutMargins : Fin 3 → ℚ := ![48402341/5000000000, 8682769/1000000000, 1376019/500000000]

theorem scS2Cut_roots_ok : scS2CutCell.rootsOK scS2CutRoots = true := by decide +kernel

theorem scS2Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS2CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS2Cut_margin_le (i : Fin 3) : curvatureLoss scS2CutCell scS2CutCaps i ≤ scS2CutMargins i := by
  fin_cases i <;> decide +kernel

def scS3CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨3/16, 1/5⟩, ⟨3/40, 1/10⟩⟩
def scS3CutRoots : Fin 3 → RatBounds := ![⟨136230912226645/70368744177664, 592272823155989/281474976710656⟩, ⟨247047559478231/140737488355328, 538195530115869/281474976710656⟩, ⟨133923165668001/140737488355328, 9599756549215/8796093022208⟩]
def scS3CutCaps : Fin 3 → Fin 3 → ℚ := ![![15550631241/50000000, 12211753311/50000000, 8717979327/100000000], ![16089695507/100000000, 17256567461/100000000, 249550453/6250000], ![96525737/10000000, 1002033843/100000000, 208452209/50000000]]
def scS3CutWeightFloor : ℚ := 57160509/50000000
def scS3CutMargins : Fin 3 → ℚ := ![49855457/5000000000, 17846957/2000000000, 28082821/10000000000]

theorem scS3Cut_roots_ok : scS3CutCell.rootsOK scS3CutRoots = true := by decide +kernel

theorem scS3Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS3CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS3Cut_margin_le (i : Fin 3) : curvatureLoss scS3CutCell scS3CutCaps i ≤ scS3CutMargins i := by
  fin_cases i <;> decide +kernel

def scS4CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨1/5, 17/80⟩, ⟨0, 1/40⟩⟩
def scS4CutRoots : Fin 3 → RatBounds := ![⟨547440698497491/281474976710656, 594304251156859/281474976710656⟩, ⟨498629866607079/281474976710656, 542743713035907/281474976710656⟩, ⟨285759420950517/281474976710656, 163380020692553/140737488355328⟩]
def scS4CutCaps : Fin 3 → Fin 3 → ℚ := ![![601382301/2500000, 3692367239/20000000, 6963524391/100000000], ![12151267603/100000000, 20976187/160000, 1579860567/50000000], ![1281373843/100000000, 165517989/12500000, 115101323/20000000]]
def scS4CutWeightFloor : ℚ := 5076107/5000000
def scS4CutMargins : Fin 3 → ℚ := ![8072667/1000000000, 36004423/5000000000, 2426811/1000000000]

theorem scS4Cut_roots_ok : scS4CutCell.rootsOK scS4CutRoots = true := by decide +kernel

theorem scS4Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS4CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS4Cut_margin_le (i : Fin 3) : curvatureLoss scS4CutCell scS4CutCaps i ≤ scS4CutMargins i := by
  fin_cases i <;> decide +kernel

def scS5CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨1/5, 17/80⟩, ⟨1/40, 1/20⟩⟩
def scS5CutRoots : Fin 3 → RatBounds := ![⟨8489267078227/4398046511104, 589509258894017/281474976710656⟩, ⟨246402825437097/140737488355328, 268030498669563/140737488355328⟩, ⟨280197676019739/281474976710656, 160031782366813/140737488355328⟩]
def scS5CutCaps : Fin 3 → Fin 3 → ℚ := ![![786430657/3125000, 19351526229/100000000, 7255087171/100000000], ![1270142987/10000000, 13672249329/100000000, 3297110611/100000000], ![575531717/50000000, 1184940063/100000000, 514670097/100000000]]
def scS5CutWeightFloor : ℚ := 106115639/100000000
def scS5CutMargins : Fin 3 → ℚ := ![1036901/125000000, 36878453/5000000000, 12315311/5000000000]

theorem scS5Cut_roots_ok : scS5CutCell.rootsOK scS5CutRoots = true := by decide +kernel

theorem scS5Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS5CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS5Cut_margin_le (i : Fin 3) : curvatureLoss scS5CutCell scS5CutCaps i ≤ scS5CutMargins i := by
  fin_cases i <;> decide +kernel

def scS6CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨1/5, 17/80⟩, ⟨1/20, 3/40⟩⟩
def scS6CutRoots : Fin 3 → RatBounds := ![⟨134875607435435/70368744177664, 585102355246527/281474976710656⟩, ⟨487454339797747/281474976710656, 2070095462763/1099511627776⟩, ⟨275118262073213/281474976710656, 156987055327461/140737488355328⟩]
def scS6CutCaps : Fin 3 → Fin 3 → ℚ := ![![5253832451/20000000, 5058206049/25000000, 2357593/31250], ![1655958087/12500000, 14230554141/100000000, 107284883/3125000], ![519529869/50000000, 1065977627/100000000, 462735993/100000000]]
def scS6CutWeightFloor : ℚ := 11071499/10000000
def scS6CutMargins : Fin 3 → ℚ := ![85298957/10000000000, 75639237/10000000000, 25055387/10000000000]

theorem scS6Cut_roots_ok : scS6CutCell.rootsOK scS6CutRoots = true := by decide +kernel

theorem scS6Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS6CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS6Cut_margin_le (i : Fin 3) : curvatureLoss scS6CutCell scS6CutCaps i ≤ scS6CutMargins i := by
  fin_cases i <;> decide +kernel

def scS7CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨1/5, 17/80⟩, ⟨3/40, 1/10⟩⟩
def scS7CutRoots : Fin 3 → RatBounds := ![⟨33498320677067/17592186044416, 18157428123825/8796093022208⟩, ⟨120629926198115/70368744177664, 524323885950079/281474976710656⟩, ⟨33807622464247/35184372088832, 308412625755111/281474976710656⟩]
def scS7CutCaps : Fin 3 → Fin 3 → ℚ := ![![27366193713/100000000, 4221337607/20000000, 3915712899/50000000], ![3447589577/25000000, 3696354383/25000000, 891971317/25000000], ![94215929/10000000, 481792187/50000000, 418078063/100000000]]
def scS7CutWeightFloor : ℚ := 23063853/20000000
def scS7CutMargins : Fin 3 → ℚ := ![87744511/10000000000, 19407443/2500000000, 5106103/2000000000]

theorem scS7Cut_roots_ok : scS7CutCell.rootsOK scS7CutRoots = true := by decide +kernel

theorem scS7Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS7CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS7Cut_margin_le (i : Fin 3) : curvatureLoss scS7CutCell scS7CutCaps i ≤ scS7CutMargins i := by
  fin_cases i <;> decide +kernel

def scS8CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨17/80, 9/40⟩, ⟨0, 1/40⟩⟩
def scS8CutRoots : Fin 3 → RatBounds := ![⟨134763531458819/70368744177664, 583890768915285/281474976710656⟩, ⟨30485694700529/17592186044416, 66231137034055/35184372088832⟩, ⟨18021315492663/17592186044416, 164015428347883/140737488355328⟩]
def scS8CutCaps : Fin 3 → Fin 3 → ℚ := ![![21396696119/100000000, 8064176141/50000000, 98729163/1562500], ![10522852959/100000000, 177296357/1562500, 2848624833/100000000], ![1255703463/100000000, 639008257/50000000, 578645061/100000000]]
def scS8CutWeightFloor : ℚ := 51219659/50000000
def scS8CutMargins : Fin 3 → ℚ := ![72153053/10000000000, 63647237/10000000000, 22425531/10000000000]

theorem scS8Cut_roots_ok : scS8CutCell.rootsOK scS8CutRoots = true := by decide +kernel

theorem scS8Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS8CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS8Cut_margin_le (i : Fin 3) : curvatureLoss scS8CutCell scS8CutCaps i ≤ scS8CutMargins i := by
  fin_cases i <;> decide +kernel

def scS9CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨17/80, 9/40⟩, ⟨1/40, 1/20⟩⟩
def scS9CutRoots : Fin 3 → RatBounds := ![⟨535027609628455/281474976710656, 579217225975697/281474976710656⟩, ⟨481994282477683/281474976710656, 523231246239745/281474976710656⟩, ⟨282777593562215/281474976710656, 321366894910153/281474976710656⟩]
def scS9CutCaps : Fin 3 → Fin 3 → ℚ := ![![11190469229/50000000, 16907790913/100000000, 3293960409/50000000], ![687497513/6250000, 5916743943/50000000, 1486730873/50000000], ![563714737/50000000, 1143151493/100000000, 517322289/100000000]]
def scS9CutWeightFloor : ℚ := 107053349/100000000
def scS9CutMargins : Fin 3 → ℚ := ![74005111/10000000000, 32533091/5000000000, 5679039/2500000000]

theorem scS9Cut_roots_ok : scS9CutCell.rootsOK scS9CutRoots = true := by decide +kernel

theorem scS9Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS9CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS9Cut_margin_le (i : Fin 3) : curvatureLoss scS9CutCell scS9CutCaps i ≤ scS9CutMargins i := by
  fin_cases i <;> decide +kernel

def scS10CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨17/80, 9/40⟩, ⟨1/20, 3/40⟩⟩
def scS10CutRoots : Fin 3 → RatBounds := ![⟨531310475087861/281474976710656, 17966328750787/8796093022208⟩, ⟨238343983666363/140737488355328, 129293975088553/70368744177664⟩, ⟨138848219824625/140737488355328, 315306767953345/281474976710656⟩]
def scS10CutCaps : Fin 3 → Fin 3 → ℚ := ![![23359152327/100000000, 17679881081/100000000, 856862713/12500000], ![2868408669/25000000, 12316677423/100000000, 774257779/25000000], ![1017241777/100000000, 51397753/5000000, 464989123/100000000]]
def scS10CutWeightFloor : ℚ := 111673793/100000000
def scS10CutMargins : Fin 3 → ℚ := ![75979989/10000000000, 8327241/1250000000, 23070097/10000000000]

theorem scS10Cut_roots_ok : scS10CutCell.rootsOK scS10CutRoots = true := by decide +kernel

theorem scS10Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS10CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS10Cut_margin_le (i : Fin 3) : curvatureLoss scS10CutCell scS10CutCaps i ≤ scS10CutMargins i := by
  fin_cases i <;> decide +kernel

def scS11CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨17/80, 9/40⟩, ⟨3/40, 1/10⟩⟩
def scS11CutRoots : Fin 3 → RatBounds := ![⟨65983497643043/35184372088832, 570961850109991/281474976710656⟩, ⟨117949020172875/70368744177664, 511613170778231/281474976710656⟩, ⟨273037403755489/281474976710656, 154885928022867/140737488355328⟩]
def scS11CutCaps : Fin 3 → Fin 3 → ℚ := ![![24331999099/100000000, 18445463997/100000000, 7119889949/100000000], ![2388842059/20000000, 6398435177/50000000, 3219467281/100000000], ![460982759/50000000, 928850237/100000000, 420001229/100000000]]
def scS11CutWeightFloor : ℚ := 116299629/100000000
def scS11CutMargins : Fin 3 → ℚ := ![19513707/2500000000, 68276827/10000000000, 23475317/10000000000]

theorem scS11Cut_roots_ok : scS11CutCell.rootsOK scS11CutRoots = true := by decide +kernel

theorem scS11Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS11CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS11Cut_margin_le (i : Fin 3) : curvatureLoss scS11CutCell scS11CutCaps i ≤ scS11CutMargins i := by
  fin_cases i <;> decide +kernel

def scS12CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨9/40, 19/80⟩, ⟨0, 1/40⟩⟩
def scS12CutRoots : Fin 3 → RatBounds := ![⟨531437985948181/281474976710656, 574515729778909/281474976710656⟩, ⟨477676167894115/281474976710656, 258990991731785/140737488355328⟩, ⟨290894257203051/281474976710656, 329433220908161/281474976710656⟩]
def scS12CutCaps : Fin 3 → Fin 3 → ℚ := ![![4802006859/25000000, 14232284709/100000000, 2898004807/50000000], ![367931103/4000000, 9909110717/100000000, 2590806443/100000000], ![1233155471/100000000, 247192693/20000000, 116528911/20000000]]
def scS12CutWeightFloor : ℚ := 129183/125000
def scS12CutMargins : Fin 3 → ℚ := ![16278773/2500000000, 7100891/1250000000, 20932411/10000000000]

theorem scS12Cut_roots_ok : scS12CutCell.rootsOK scS12CutRoots = true := by decide +kernel

theorem scS12Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS12CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS12Cut_margin_le (i : Fin 3) : curvatureLoss scS12CutCell scS12CutCaps i ≤ scS12CutMargins i := by
  fin_cases i <;> decide +kernel

def scS13CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨9/40, 19/80⟩, ⟨1/40, 1/20⟩⟩
def scS13CutRoots : Fin 3 → RatBounds := ![⟨16484500561475/8796093022208, 142488109845455/70368744177664⟩, ⟨471941030150045/281474976710656, 511420542970095/281474976710656⟩, ⟨285330470865137/281474976710656, 322799560961441/281474976710656⟩]
def scS13CutCaps : Fin 3 → Fin 3 → ℚ := ![![10044338587/50000000, 7460876493/50000000, 6045725053/100000000], ![4807994357/50000000, 10334009597/100000000, 2705160963/100000000], ![1106660399/100000000, 34533663/3125000, 520751223/100000000]]
def scS13CutWeightFloor : ℚ := 53990143/50000000
def scS13CutMargins : Fin 3 → ℚ := ![6666271/1000000000, 28980539/5000000000, 2644993/1250000000]

theorem scS13Cut_roots_ok : scS13CutCell.rootsOK scS13CutRoots = true := by decide +kernel

theorem scS13Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS13CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS13Cut_margin_le (i : Fin 3) : curvatureLoss scS13CutCell scS13CutCaps i ≤ scS13CutMargins i := by
  fin_cases i <;> decide +kernel

def scS14CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨9/40, 19/80⟩, ⟨1/20, 3/40⟩⟩
def scS14CutRoots : Fin 3 → RatBounds := ![⟨261936252824477/140737488355328, 282879795461163/140737488355328⟩, ⟨466674410343607/281474976710656, 252709284450207/140737488355328⟩, ⟨280248821777455/281474976710656, 316766733877101/281474976710656⟩]
def scS14CutCaps : Fin 3 → Fin 3 → ℚ := ![![4192833663/20000000, 15604703977/100000000, 629334567/10000000], ![5015333921/50000000, 5377993279/50000000, 2818348717/100000000], ![249515237/25000000, 993331659/100000000, 58493307/12500000]]
def scS14CutWeightFloor : ℚ := 22524233/20000000
def scS14CutMargins : Fin 3 → ℚ := ![68334141/10000000000, 3702883/625000000, 2145211/1000000000]

theorem scS14Cut_roots_ok : scS14CutCell.rootsOK scS14CutRoots = true := by decide +kernel

theorem scS14Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS14CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS14Cut_margin_le (i : Fin 3) : curvatureLoss scS14CutCell scS14CutCaps i ≤ scS14CutMargins i := by
  fin_cases i <;> decide +kernel

def scS15CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨9/40, 19/80⟩, ⟨3/40, 1/10⟩⟩
def scS15CutRoots : Fin 3 → RatBounds := ![⟨520509474839555/281474976710656, 70236665737555/35184372088832⟩, ⟨461820320675879/281474976710656, 249953185485505/140737488355328⟩, ⟨137794581084061/140737488355328, 311256530565911/281474976710656⟩]
def scS15CutCaps : Fin 3 → Fin 3 → ℚ := ![![21835064341/100000000, 1628188319/10000000, 130782619/2000000], ![10442606689/100000000, 11175332107/100000000, 2930491833/100000000], ![226051649/25000000, 448618993/50000000, 21128287/5000000]]
def scS15CutWeightFloor : ℚ := 1465849/1250000
def scS15CutMargins : Fin 3 → ℚ := ![70106441/10000000000, 30318523/5000000000, 5449163/2500000000]

theorem scS15Cut_roots_ok : scS15CutCell.rootsOK scS15CutRoots = true := by decide +kernel

theorem scS15Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS15CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS15Cut_margin_le (i : Fin 3) : curvatureLoss scS15CutCell scS15CutCaps i ≤ scS15CutMargins i := by
  fin_cases i <;> decide +kernel

def scS16CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨19/80, 1/4⟩, ⟨0, 1/40⟩⟩
def scS16CutRoots : Fin 3 → RatBounds := ![⟨262253909632535/140737488355328, 17689119894149/8796093022208⟩, ⟨117064042443747/70368744177664, 507010752354439/281474976710656⟩, ⟨146715487892831/140737488355328, 330956177813075/281474976710656⟩]
def scS16CutCaps : Fin 3 → Fin 3 → ℚ := ![![8692871079/50000000, 12668794627/100000000, 2677771533/50000000], ![4054273931/50000000, 872272637/10000000, 237504039/10000000], ![303313141/25000000, 299342333/25000000, 117478277/20000000]]
def scS16CutWeightFloor : ℚ := 13030953/12500000
def scS16CutMargins : Fin 3 → ℚ := ![59272071/10000000000, 51134763/10000000000, 1230487/625000000]

theorem scS16Cut_roots_ok : scS16CutCell.rootsOK scS16CutRoots = true := by decide +kernel

theorem scS16Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS16CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS16Cut_margin_le (i : Fin 3) : curvatureLoss scS16CutCell scS16CutCaps i ≤ scS16CutMargins i := by
  fin_cases i <;> decide +kernel

def scS17CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨19/80, 1/4⟩, ⟨1/40, 1/20⟩⟩
def scS17CutRoots : Fin 3 → RatBounds := ![⟨520658705317543/281474976710656, 140397219424975/70368744177664⟩, ⟨231278875122973/140737488355328, 500498410288577/281474976710656⟩, ⟨143933996728963/140737488355328, 40543862135391/35184372088832⟩]
def scS17CutCaps : Fin 3 → Fin 3 → ℚ := ![![18180391639/100000000, 3320978073/25000000, 5588833547/100000000], ![8477407719/100000000, 9096810869/100000000, 99222457/4000000], ![1088319143/100000000, 267539121/25000000, 262427173/50000000]]
def scS17CutWeightFloor : ℚ := 108900883/100000000
def scS17CutMargins : Fin 3 → ℚ := ![15142127/2500000000, 13018237/2500000000, 9930481/5000000000]

theorem scS17Cut_roots_ok : scS17CutCell.rootsOK scS17CutRoots = true := by decide +kernel

theorem scS17Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS17CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS17Cut_margin_le (i : Fin 3) : curvatureLoss scS17CutCell scS17CutCaps i ≤ scS17CutMargins i := by
  fin_cases i <;> decide +kernel

def scS18CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨19/80, 1/4⟩, ⟨1/20, 3/40⟩⟩
def scS18CutRoots : Fin 3 → RatBounds := ![⟨517105692849739/281474976710656, 278744361960453/140737488355328⟩, ⟨457326185525475/281474976710656, 494543025397937/281474976710656⟩, ⟨70696718343329/70368744177664, 318343606280893/281474976710656⟩]
def scS18CutCaps : Fin 3 → Fin 3 → ℚ := ![![9485288781/50000000, 13893198761/100000000, 1164034863/20000000], ![884356417/10000000, 4734156589/50000000, 517000469/20000000], ![98111561/10000000, 60099653/6250000, 235757523/50000000]]
def scS18CutWeightFloor : ℚ := 113561729/100000000
def scS18CutMargins : Fin 3 → ℚ := ![30994731/5000000000, 5314041/1000000000, 2512509/1250000000]

theorem scS18Cut_roots_ok : scS18CutCell.rootsOK scS18CutRoots = true := by decide +kernel

theorem scS18Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS18CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS18Cut_margin_le (i : Fin 3) : curvatureLoss scS18CutCell scS18CutCaps i ≤ scS18CutMargins i := by
  fin_cases i <;> decide +kernel

def scS19CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨19/80, 1/4⟩, ⟨3/40, 1/10⟩⟩
def scS19CutRoots : Fin 3 → RatBounds := ![⟨256907755816437/140737488355328, 276854186796699/140737488355328⟩, ⟨452505556212689/281474976710656, 489075049445365/281474976710656⟩, ⟨139063758711759/140737488355328, 39107060951743/35184372088832⟩]
def scS19CutCaps : Fin 3 → Fin 3 → ℚ := ![![617398277/3125000, 7248658739/50000000, 3024894937/50000000], ![2301818627/25000000, 491874353/5000000, 1344237369/50000000], ![44425611/5000000, 434138307/50000000, 212843487/50000000]]
def scS19CutWeightFloor : ℚ := 29557237/25000000
def scS19CutMargins : Fin 3 → ℚ := ![63511853/10000000000, 54312327/10000000000, 20392603/10000000000]

theorem scS19Cut_roots_ok : scS19CutCell.rootsOK scS19CutRoots = true := by decide +kernel

theorem scS19Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS19CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS19Cut_margin_le (i : Fin 3) : curvatureLoss scS19CutCell scS19CutCaps i ≤ scS19CutMargins i := by
  fin_cases i <;> decide +kernel

def scS20CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨1/4, 21/80⟩, ⟨0, 1/40⟩⟩
def scS20CutRoots : Fin 3 → RatBounds := ![⟨8096762500581/4398046511104, 69799288933793/35184372088832⟩, ⟨459436179346005/281474976710656, 496826537457077/281474976710656⟩, ⟨295961280602963/281474976710656, 83147848603725/70368744177664⟩]
def scS20CutCaps : Fin 3 → Fin 3 → ℚ := ![![7926723581/50000000, 11366250699/100000000, 4981209539/100000000], ![7211553777/100000000, 7733565567/100000000, 110378299/5000000], ![1195613401/100000000, 116173923/10000000, 592795673/100000000]]
def scS20CutWeightFloor : ℚ := 13143321/12500000
def scS20CutMargins : Fin 3 → ℚ := ![1359739/250000000, 46380417/10000000000, 9335897/5000000000]

theorem scS20Cut_roots_ok : scS20CutCell.rootsOK scS20CutRoots = true := by decide +kernel

theorem scS20Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS20CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS20Cut_margin_le (i : Fin 3) : curvatureLoss scS20CutCell scS20CutCaps i ≤ scS20CutMargins i := by
  fin_cases i <;> decide +kernel

def scS21CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨1/4, 21/80⟩, ⟨1/40, 1/20⟩⟩
def scS21CutRoots : Fin 3 → RatBounds := ![⟨514421558511787/281474976710656, 554022816337029/281474976710656⟩, ⟨453770098406665/281474976710656, 122589231149001/70368744177664⟩, ⟨145200019882233/140737488355328, 20375800043053/17592186044416⟩]
def scS21CutCaps : Fin 3 → Fin 3 → ℚ := ![![1035998563/6250000, 5959641277/50000000, 5200590083/100000000], ![1508166517/20000000, 8065305281/100000000, 92292331/4000000], ![1072056503/100000000, 1037938383/100000000, 105910127/20000000]]
def scS21CutWeightFloor : ℚ := 109818881/100000000
def scS21CutMargins : Fin 3 → ℚ := ![27739293/5000000000, 11785323/2500000000, 18800979/10000000000]

theorem scS21Cut_roots_ok : scS21CutCell.rootsOK scS21CutRoots = true := by decide +kernel

theorem scS21Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS21CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS21Cut_margin_le (i : Fin 3) : curvatureLoss scS21CutCell scS21CutCaps i ≤ scS21CutMargins i := by
  fin_cases i <;> decide +kernel

def scS22CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨1/4, 21/80⟩, ⟨1/20, 3/40⟩⟩
def scS22CutRoots : Fin 3 → RatBounds := ![⟨127735145844417/70368744177664, 550007166689797/281474976710656⟩, ⟨224284751513601/140737488355328, 484442217180367/281474976710656⟩, ⟨71330072827109/70368744177664, 160014745839029/140737488355328⟩]
def scS22CutCaps : Fin 3 → Fin 3 → ℚ := ![![2161872973/12500000, 6233719413/50000000, 2709239857/50000000], ![7867646523/100000000, 1049343453/12500000, 240598767/10000000], ![966084857/100000000, 932330929/100000000, 475621483/100000000]]
def scS22CutWeightFloor : ℚ := 57249693/50000000
def scS22CutMargins : Fin 3 → ℚ := ![56693301/10000000000, 24015147/5000000000, 4749489/2500000000]

theorem scS22Cut_roots_ok : scS22CutCell.rootsOK scS22CutRoots = true := by decide +kernel

theorem scS22Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS22CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS22Cut_margin_le (i : Fin 3) : curvatureLoss scS22CutCell scS22CutCaps i ≤ scS22CutMargins i := by
  fin_cases i <;> decide +kernel

def scS23CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨1/4, 21/80⟩, ⟨3/40, 1/10⟩⟩
def scS23CutRoots : Fin 3 → RatBounds := ![⟨253858625565517/140737488355328, 273152570631939/140737488355328⟩, ⟨110944628443787/70368744177664, 479012961340211/281474976710656⟩, ⟨70165499936241/70368744177664, 157282012158185/140737488355328⟩]
def scS23CutCaps : Fin 3 → Fin 3 → ℚ := ![![18010651831/100000000, 13011107277/100000000, 2817441319/50000000], ![1638445833/20000000, 8722115613/100000000, 2503714611/100000000], ![21864663/2500000, 841587377/100000000, 429298117/100000000]]
def scS23CutWeightFloor : ℚ := 59593387/50000000
def scS23CutMargins : Fin 3 → ℚ := ![5801021/1000000000, 49022603/10000000000, 1924959/1000000000]

theorem scS23Cut_roots_ok : scS23CutCell.rootsOK scS23CutRoots = true := by decide +kernel

theorem scS23Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS23CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS23Cut_margin_le (i : Fin 3) : curvatureLoss scS23CutCell scS23CutCaps i ≤ scS23CutMargins i := by
  fin_cases i <;> decide +kernel

def scS24CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨21/80, 11/40⟩, ⟨0, 1/40⟩⟩
def scS24CutRoots : Fin 3 → RatBounds := ![⟨512433105197461/281474976710656, 551456122615409/281474976710656⟩, ⟨225576233809795/140737488355328, 243669195555529/140737488355328⟩, ⟨298493839818683/281474976710656, 334332586133697/281474976710656⟩]
def scS24CutCaps : Fin 3 → Fin 3 → ℚ := ![![7277016463/50000000, 10271482731/100000000, 2330535443/50000000], ![404265101/6250000, 3450544497/50000000, 519981711/25000000], ![589964927/50000000, 1128670561/100000000, 119757173/20000000]]
def scS24CutWeightFloor : ℚ := 53023157/50000000
def scS24CutMargins : Fin 3 → ℚ := ![12569333/2500000000, 21178959/5000000000, 8922013/5000000000]

theorem scS24Cut_roots_ok : scS24CutCell.rootsOK scS24CutRoots = true := by decide +kernel

theorem scS24Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS24CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS24Cut_margin_le (i : Fin 3) : curvatureLoss scS24CutCell scS24CutCaps i ≤ scS24CutMargins i := by
  fin_cases i <;> decide +kernel

def scS25CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨21/80, 11/40⟩, ⟨1/40, 1/20⟩⟩
def scS25CutRoots : Fin 3 → RatBounds := ![⟨63591669794847/35184372088832, 547168101219293/281474976710656⟩, ⟨445514851181905/281474976710656, 240452960359465/140737488355328⟩, ⟨292935112414359/281474976710656, 327779171282557/281474976710656⟩]
def scS25CutCaps : Fin 3 → Fin 3 → ℚ := ![![15216068441/100000000, 21545411/200000, 4869072331/100000000], ![270560861/4000000, 3598604147/50000000, 2174162447/100000000], ![1057590311/100000000, 1008056079/100000000, 267387807/50000000]]
def scS25CutWeightFloor : ℚ := 13842187/12500000
def scS25CutMargins : Fin 3 → ℚ := ![1599759/312500000, 21486463/5000000000, 17934253/10000000000]

theorem scS25Cut_roots_ok : scS25CutCell.rootsOK scS25CutRoots = true := by decide +kernel

theorem scS25Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS25CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS25Cut_margin_le (i : Fin 3) : curvatureLoss scS25CutCell scS25CutCaps i ≤ scS25CutMargins i := by
  fin_cases i <;> decide +kernel

def scS26CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨21/80, 11/40⟩, ⟨1/20, 3/40⟩⟩
def scS26CutRoots : Fin 3 → RatBounds := ![⟨3947800916311/2199023255552, 543229575331335/281474976710656⟩, ⟨55042701115199/35184372088832, 475026702769155/281474976710656⟩, ⟨287857426790199/281474976710656, 321818456539147/281474976710656⟩]
def scS26CutCaps : Fin 3 → Fin 3 → ℚ := ![![7937343413/50000000, 11269179561/100000000, 2537668709/50000000], ![882196019/12500000, 3745635627/50000000, 453481361/20000000], ![952709381/100000000, 905205519/100000000, 30012961/6250000]]
def scS26CutWeightFloor : ℚ := 115437489/100000000
def scS26CutMargins : Fin 3 → ℚ := ![52232603/10000000000, 2732089/625000000, 9046459/5000000000]

theorem scS26Cut_roots_ok : scS26CutCell.rootsOK scS26CutRoots = true := by decide +kernel

theorem scS26Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS26CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS26Cut_margin_le (i : Fin 3) : curvatureLoss scS26CutCell scS26CutCaps i ≤ scS26CutMargins i := by
  fin_cases i <;> decide +kernel

def scS27CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨21/80, 11/40⟩, ⟨3/40, 1/10⟩⟩
def scS27CutRoots : Fin 3 → RatBounds := ![⟨62769569112761/35184372088832, 539599035384623/281474976710656⟩, ⟨54447109587121/35184372088832, 117407834136335/70368744177664⟩, ⟨283200821298999/281474976710656, 158186679635591/140737488355328⟩]
def scS27CutCaps : Fin 3 → Fin 3 → ℚ := ![![2066278539/12500000, 11761444967/100000000, 5280070479/100000000], ![7349090761/100000000, 3891737461/50000000, 2359761249/100000000], ![862190417/100000000, 163372431/20000000, 433346041/100000000]]
def scS27CutWeightFloor : ℚ := 120144883/100000000
def scS27CutMargins : Fin 3 → ℚ := ![26687579/5000000000, 2784713/625000000, 18307063/10000000000]

theorem scS27Cut_roots_ok : scS27CutCell.rootsOK scS27CutRoots = true := by decide +kernel

theorem scS27Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS27CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS27Cut_margin_le (i : Fin 3) : curvatureLoss scS27CutCell scS27CutCaps i ≤ scS27CutMargins i := by
  fin_cases i <;> decide +kernel

def scS28CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨11/40, 23/80⟩, ⟨0, 1/40⟩⟩
def scS28CutRoots : Fin 3 → RatBounds := ![⟨253588943284243/140737488355328, 545164405403313/281474976710656⟩, ⟨110837608281651/70368744177664, 239234824952755/140737488355328⟩, ⟨37629530310075/35184372088832, 336175098379957/281474976710656⟩]
def scS28CutCaps : Fin 3 → Fin 3 → ℚ := ![![6721920609/50000000, 4672055447/50000000, 4385823991/100000000], ![5842057443/100000000, 774330059/12500000, 493488703/25000000], ![1165950477/100000000, 137229047/12500000, 4728943/781250]]
def scS28CutWeightFloor : ℚ := 106949557/100000000
def scS28CutMargins : Fin 3 → ℚ := ![46776759/10000000000, 1946297/500000000, 8575193/5000000000]

theorem scS28Cut_roots_ok : scS28CutCell.rootsOK scS28CutRoots = true := by decide +kernel

theorem scS28Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS28CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS28Cut_margin_le (i : Fin 3) : curvatureLoss scS28CutCell scS28CutCaps i ≤ scS28CutMargins i := by
  fin_cases i <;> decide +kernel

def scS29CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨11/40, 23/80⟩, ⟨1/40, 1/20⟩⟩
def scS29CutRoots : Fin 3 → RatBounds := ![⟨62942971450693/35184372088832, 540952604737007/281474976710656⟩, ⟨437737838347475/281474976710656, 472069391072191/281474976710656⟩, ⟨295480660657659/281474976710656, 329645502034343/281474976710656⟩]
def scS29CutCaps : Fin 3 → Fin 3 → ℚ := ![![439183423/3125000, 1960175531/20000000, 4583675821/100000000], ![3054797063/50000000, 6460557181/100000000, 1031796083/50000000], ![10446903/1000000, 980208011/100000000, 54047773/10000000]]
def scS29CutWeightFloor : ℚ := 13957443/12500000
def scS29CutMargins : Fin 3 → ℚ := ![2971463/625000000, 3941849/1000000000, 4301357/2500000000]

theorem scS29Cut_roots_ok : scS29CutCell.rootsOK scS29CutRoots = true := by decide +kernel

theorem scS29Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS29CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS29Cut_margin_le (i : Fin 3) : curvatureLoss scS29CutCell scS29CutCaps i ≤ scS29CutMargins i := by
  fin_cases i <;> decide +kernel

def scS30CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨11/40, 23/80⟩, ⟨1/20, 3/40⟩⟩
def scS30CutRoots : Fin 3 → RatBounds := ![⟨500189638240787/281474976710656, 268542251332681/140737488355328⟩, ⟨108147183394601/70368744177664, 233110540631907/140737488355328⟩, ⟨290405601130319/281474976710656, 323706127958233/281474976710656⟩]
def scS30CutCaps : Fin 3 → Fin 3 → ℚ := ![![14660867439/100000000, 5126651771/50000000, 955976063/20000000], ![1593773299/25000000, 1681155549/25000000, 2152299007/100000000], ![940777567/100000000, 43997117/5000000, 485226059/100000000]]
def scS30CutWeightFloor : ℚ := 14547371/12500000
def scS30CutMargins : Fin 3 → ℚ := ![24217843/5000000000, 40034561/10000000000, 8665121/5000000000]

theorem scS30Cut_roots_ok : scS30CutCell.rootsOK scS30CutRoots = true := by decide +kernel

theorem scS30Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS30CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS30Cut_margin_le (i : Fin 3) : curvatureLoss scS30CutCell scS30CutCaps i ≤ scS30CutMargins i := by
  fin_cases i <;> decide +kernel

def scS31CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨11/40, 23/80⟩, ⟨3/40, 1/10⟩⟩
def scS31CutRoots : Fin 3 → RatBounds := ![⟨497084003675765/281474976710656, 533519239036171/281474976710656⟩, ⟨427847248474381/281474976710656, 1800216160507/1099511627776⟩, ⟨142875592935401/140737488355328, 318280241512975/281474976710656⟩]
def scS31CutCaps : Fin 3 → Fin 3 → ℚ := ![![7632566371/50000000, 10701881899/100000000, 4974631319/100000000], ![6638743431/100000000, 1746752633/25000000, 2240168773/100000000], ![851128801/100000000, 396923819/50000000, 43778831/10000000]]
def scS31CutWeightFloor : ℚ := 121106319/100000000
def scS31CutMargins : Fin 3 → ℚ := ![12357613/2500000000, 40750553/10000000000, 4377907/2500000000]

theorem scS31Cut_roots_ok : scS31CutCell.rootsOK scS31CutRoots = true := by decide +kernel

theorem scS31Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS31CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS31Cut_margin_le (i : Fin 3) : curvatureLoss scS31CutCell scS31CutCaps i ≤ scS31CutMargins i := by
  fin_cases i <;> decide +kernel


end HlawkaSchatten.BelowExponent.Vertex
