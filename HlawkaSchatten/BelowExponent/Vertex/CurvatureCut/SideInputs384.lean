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

def scE78CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨17/40, 7/16⟩, ⟨3/20, 13/80⟩⟩
def scE78CutRoots : Fin 3 → RatBounds := ![⟨228894673435851/140737488355328, 121488817281555/70368744177664⟩, ⟨349625979227151/281474976710656, 186499057506493/140737488355328⟩, ⟨154594875928215/140737488355328, 335068618966401/281474976710656⟩]
def scE78CutCaps : Fin 3 → Fin 3 → ℚ := ![![9003055747/100000000, 2719236663/50000000, 3699512829/100000000], ![1644091189/50000000, 1405347371/50000000, 1905487363/100000000], ![451533363/100000000, 42655253/12500000, 148734113/50000000]]
def scE78CutWeightFloor : ℚ := 149729113/100000000
def scE78CutMargins : Fin 3 → ℚ := ![12444113/5000000000, 3355629/2000000000, 11528259/10000000000]

theorem scE78Cut_roots_ok : scE78CutCell.rootsOK scE78CutRoots = true := by decide +kernel

theorem scE78Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE78CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE78Cut_margin_le (i : Fin 3) : curvatureLoss scE78CutCell scE78CutCaps i ≤ scE78CutMargins i := by
  fin_cases i <;> decide +kernel

def scE79CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨17/40, 7/16⟩, ⟨13/80, 1/6⟩⟩
def scE79CutRoots : Fin 3 → RatBounds := ![⟨228825761255859/140737488355328, 3785447511637/2199023255552⟩, ⟨21813825169719/17592186044416, 185527166007205/140737488355328⟩, ⟨154293282530919/140737488355328, 333117915691135/281474976710656⟩]
def scE79CutCaps : Fin 3 → Fin 3 → ℚ := ![![8900142313/100000000, 5383782041/100000000, 3617404271/100000000], ![1625926693/50000000, 1371752137/50000000, 1841301361/100000000], ![342726149/100000000, 32159071/12500000, 227677533/100000000]]
def scE79CutWeightFloor : ℚ := 152893701/100000000
def scE79CutMargins : Fin 3 → ℚ := ![23808743/10000000000, 7964719/5000000000, 334717/312500000]

theorem scE79Cut_roots_ok : scE79CutCell.rootsOK scE79CutRoots = true := by decide +kernel

theorem scE79Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE79CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE79Cut_margin_le (i : Fin 3) : curvatureLoss scE79CutCell scE79CutCaps i ≤ scE79CutMargins i := by
  fin_cases i <;> decide +kernel

def scE80CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨7/16, 9/20⟩, ⟨1/8, 11/80⟩⟩
def scE80CutRoots : Fin 3 → RatBounds := ![⟨459035128811435/281474976710656, 243643526296893/140737488355328⟩, ⟨174565672222821/140737488355328, 2910959068415/2199023255552⟩, ⟨316148384873719/281474976710656, 342369759011449/281474976710656⟩]
def scE80CutCaps : Fin 3 → Fin 3 → ℚ := ![![338197551/4000000, 630206199/12500000, 1767946597/50000000], ![3075202067/100000000, 511213829/20000000, 931245369/50000000], ![490522251/100000000, 36453419/10000000, 329037261/100000000]]
def scE80CutWeightFloor : ℚ := 72988197/50000000
def scE80CutMargins : Fin 3 → ℚ := ![11738929/5000000000, 3887819/2500000000, 1118637/1000000000]

theorem scE80Cut_roots_ok : scE80CutCell.rootsOK scE80CutRoots = true := by decide +kernel

theorem scE80Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE80CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE80Cut_margin_le (i : Fin 3) : curvatureLoss scE80CutCell scE80CutCaps i ≤ scE80CutMargins i := by
  fin_cases i <;> decide +kernel

def scE81CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨7/16, 9/20⟩, ⟨11/80, 3/20⟩⟩
def scE81CutRoots : Fin 3 → RatBounds := ![⟨457869718221435/281474976710656, 243018650517091/140737488355328⟩, ⟨173601341461779/140737488355328, 92629527133851/70368744177664⟩, ⟨314222179473213/281474976710656, 340276090343771/281474976710656⟩]
def scE81CutCaps : Fin 3 → Fin 3 → ℚ := ![![1722672271/20000000, 2570120661/50000000, 3609798969/100000000], ![3131990357/100000000, 1300524839/50000000, 1895886361/100000000], ![469740339/100000000, 2725607/781250, 157496329/50000000]]
def scE81CutWeightFloor : ℚ := 148493903/100000000
def scE81CutMargins : Fin 3 → ℚ := ![11928801/5000000000, 15801111/10000000000, 177633/156250000]

theorem scE81Cut_roots_ok : scE81CutCell.rootsOK scE81CutRoots = true := by decide +kernel

theorem scE81Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE81CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE81Cut_margin_le (i : Fin 3) : curvatureLoss scE81CutCell scE81CutCaps i ≤ scE81CutMargins i := by
  fin_cases i <;> decide +kernel

def scE82CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨7/16, 9/20⟩, ⟨3/20, 13/80⟩⟩
def scE82CutRoots : Fin 3 → RatBounds := ![⟨14273253215417/8796093022208, 484831347506013/281474976710656⟩, ⟨86336219305675/70368744177664, 368511491247981/281474976710656⟩, ⟨156183764298859/140737488355328, 338261599515453/281474976710656⟩]
def scE82CutCaps : Fin 3 → Fin 3 → ℚ := ![![4385828993/50000000, 2619262483/50000000, 3683535811/100000000], ![1594316547/50000000, 2645964291/100000000, 1929231657/100000000], ![450234139/100000000, 334195051/100000000, 301816893/100000000]]
def scE82CutWeightFloor : ℚ := 75506787/50000000
def scE82CutMargins : Fin 3 → ℚ := ![6059827/2500000000, 8026059/5000000000, 11551923/10000000000]

theorem scE82Cut_roots_ok : scE82CutCell.rootsOK scE82CutRoots = true := by decide +kernel

theorem scE82Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE82CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE82Cut_margin_le (i : Fin 3) : curvatureLoss scE82CutCell scE82CutCaps i ≤ scE82CutMargins i := by
  fin_cases i <;> decide +kernel

def scE83CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨7/16, 9/20⟩, ⟨13/80, 1/6⟩⟩
def scE83CutRoots : Fin 3 → RatBounds := ![⟨456608704171147/281474976710656, 241708860022351/140737488355328⟩, ⟨344740678311071/281474976710656, 183284460045607/140737488355328⟩, ⟨311764524259867/281474976710656, 336313236670033/281474976710656⟩]
def scE83CutCaps : Fin 3 → Fin 3 → ℚ := ![![541879391/6250000, 1037124627/20000000, 900553913/25000000], ![630535793/20000000, 2579545617/100000000, 1865261003/100000000], ![8541379/2500000, 251823121/100000000, 46146927/20000000]]
def scE83CutWeightFloor : ℚ := 154194673/100000000
def scE83CutMargins : Fin 3 → ℚ := ![23165451/10000000000, 3044199/2000000000, 5364369/5000000000]

theorem scE83Cut_roots_ok : scE83CutCell.rootsOK scE83CutRoots = true := by decide +kernel

theorem scE83Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE83CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE83Cut_margin_le (i : Fin 3) : curvatureLoss scE83CutCell scE83CutCaps i ≤ scE83CutMargins i := by
  fin_cases i <;> decide +kernel

def scE84CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨9/20, 37/80⟩, ⟨1/8, 11/80⟩⟩
def scE84CutRoots : Fin 3 → RatBounds := ![⟨114549140812467/70368744177664, 486411694292265/281474976710656⟩, ⟨172496628670127/140737488355328, 92073611811249/70368744177664⟩, ⟨79851548623391/70368744177664, 172836799021587/140737488355328⟩]
def scE84CutCaps : Fin 3 → Fin 3 → ℚ := ![![826306987/10000000, 1218198417/25000000, 882671809/25000000], ![299771769/10000000, 60309513/2500000, 94650213/5000000], ![489440281/100000000, 1395257/390625, 6679927/2000000]]
def scE84CutWeightFloor : ℚ := 18408381/12500000
def scE84CutMargins : Fin 3 → ℚ := ![717177/312500000, 2985297/2000000000, 2249097/2000000000]

theorem scE84Cut_roots_ok : scE84CutCell.rootsOK scE84CutRoots = true := by decide +kernel

theorem scE84Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE84CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE84Cut_margin_le (i : Fin 3) : curvatureLoss scE84CutCell scE84CutCaps i ≤ scE84CutMargins i := by
  fin_cases i <;> decide +kernel

def scE85CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨9/20, 37/80⟩, ⟨11/80, 3/20⟩⟩
def scE85CutRoots : Fin 3 → RatBounds := ![⟨457035163781851/281474976710656, 485166354722155/281474976710656⟩, ⟨85766478052201/70368744177664, 366210223502573/281474976710656⟩, ⟨158740276334713/140737488355328, 343582378348175/281474976710656⟩]
def scE85CutCaps : Fin 3 → Fin 3 → ℚ := ![![131531879/1562500, 993582667/20000000, 225311547/6250000], ![61059699/2000000, 2454835439/100000000, 1926818631/100000000], ![468691261/100000000, 341836223/100000000, 319734627/100000000]]
def scE85CutWeightFloor : ℚ := 74899401/50000000
def scE85CutMargins : Fin 3 → ℚ := ![23319759/10000000000, 7582603/5000000000, 5714393/5000000000]

theorem scE85Cut_roots_ok : scE85CutCell.rootsOK scE85CutRoots = true := by decide +kernel

theorem scE85Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE85CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE85Cut_margin_le (i : Fin 3) : curvatureLoss scE85CutCell scE85CutCaps i ≤ scE85CutMargins i := by
  fin_cases i <;> decide +kernel

def scE86CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨9/20, 37/80⟩, ⟨3/20, 13/80⟩⟩
def scE86CutRoots : Fin 3 → RatBounds := ![⟨455913427760773/281474976710656, 241982334209707/140737488355328⟩, ⟨341209476035651/281474976710656, 182102066524527/140737488355328⟩, ⟨315626369766289/281474976710656, 341570156281679/281474976710656⟩]
def scE86CutCaps : Fin 3 → Fin 3 → ℚ := ![![2143222431/25000000, 2531367231/50000000, 735822209/20000000], ![1554055209/50000000, 1248614647/50000000, 1960583397/100000000], ![22460833/5000000, 163720923/50000000, 153177767/50000000]]
def scE86CutWeightFloor : ℚ := 19041597/12500000
def scE86CutMargins : Fin 3 → ℚ := ![2369183/1000000000, 1540509/1000000000, 11613379/10000000000]

theorem scE86Cut_roots_ok : scE86CutCell.rootsOK scE86CutRoots = true := by decide +kernel

theorem scE86Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE86CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE86Cut_margin_le (i : Fin 3) : curvatureLoss scE86CutCell scE86CutCaps i ≤ scE86CutMargins i := by
  fin_cases i <;> decide +kernel

def scE87CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨9/20, 37/80⟩, ⟨13/80, 1/6⟩⟩
def scE87CutRoots : Fin 3 → RatBounds := ![⟨227889956806299/140737488355328, 30159651911411/17592186044416⟩, ⟨340605744197699/281474976710656, 362262290234541/281474976710656⟩, ⟨315023501611093/281474976710656, 339623804418355/281474976710656⟩]
def scE87CutCaps : Fin 3 → Fin 3 → ℚ := ![![8472470359/100000000, 78304431/1562500, 14056521/390625], ![3072470409/100000000, 2431481947/100000000, 1896732101/100000000], ![340817263/100000000, 123314541/50000000, 233958201/100000000]]
def scE87CutWeightFloor : ℚ := 38882719/25000000
def scE87CutMargins : Fin 3 → ℚ := ![904907/400000000, 3647641/2500000000, 2695897/2500000000]

theorem scE87Cut_roots_ok : scE87CutCell.rootsOK scE87CutRoots = true := by decide +kernel

theorem scE87Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE87CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE87Cut_margin_le (i : Fin 3) : curvatureLoss scE87CutCell scE87CutCaps i ≤ scE87CutMargins i := by
  fin_cases i <;> decide +kernel

def scE88CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨37/80, 19/40⟩, ⟨1/8, 11/80⟩⟩
def scE88CutRoots : Fin 3 → RatBounds := ![⟨228785243289585/140737488355328, 60723869944481/35184372088832⟩, ⟨340991965523885/281474976710656, 5689927077765/4398046511104⟩, ⟨161375407704273/140737488355328, 174549584867975/140737488355328⟩]
def scE88CutCaps : Fin 3 → Fin 3 → ℚ := ![![4050196663/50000000, 4725060081/100000000, 442059463/12500000], ![587490169/20000000, 2282413841/100000000, 1931076453/100000000], ![61081081/12500000, 175065801/50000000, 339165889/100000000]]
def scE88CutWeightFloor : ℚ := 148593893/100000000
def scE88CutMargins : Fin 3 → ℚ := ![11256341/5000000000, 3592581/2500000000, 11341247/10000000000]

theorem scE88Cut_roots_ok : scE88CutCell.rootsOK scE88CutRoots = true := by decide +kernel

theorem scE88Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE88CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE88Cut_margin_le (i : Fin 3) : curvatureLoss scE88CutCell scE88CutCaps i ≤ scE88CutMargins i := by
  fin_cases i <;> decide +kernel

def scE89CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨37/80, 19/40⟩, ⟨11/80, 3/20⟩⟩
def scE89CutRoots : Fin 3 → RatBounds := ![⟨3565718877419/2199023255552, 242274415970243/140737488355328⟩, ⟨5297900303451/4398046511104, 362071060862613/281474976710656⟩, ⟨320825575825325/281474976710656, 173505020854927/140737488355328⟩]
def scE89CutCaps : Fin 3 → Fin 3 → ℚ := ![![257890217/3125000, 481710969/10000000, 3611383863/100000000], ![2991505257/100000000, 2322585959/100000000, 1965437823/100000000], ![7311309/1562500, 335078309/100000000, 64935873/20000000]]
def scE89CutWeightFloor : ℚ := 75570179/50000000
def scE89CutMargins : Fin 3 → ℚ := ![5718709/2500000000, 14257/9765625, 1152637/1000000000]

theorem scE89Cut_roots_ok : scE89CutCell.rootsOK scE89CutRoots = true := by decide +kernel

theorem scE89Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE89CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE89Cut_margin_le (i : Fin 3) : curvatureLoss scE89CutCell scE89CutCaps i ≤ scE89CutMargins i := by
  fin_cases i <;> decide +kernel

def scE90CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨37/80, 19/40⟩, ⟨3/20, 13/80⟩⟩
def scE90CutRoots : Fin 3 → RatBounds := ![⟨227646556558903/140737488355328, 483350252377971/281474976710656⟩, ⟨337210243307905/281474976710656, 90016258512753/70368744177664⟩, ⟨159485851266893/140737488355328, 344999741214689/281474976710656⟩]
def scE90CutCaps : Fin 3 → Fin 3 → ℚ := ![![105055793/1250000, 613608653/12500000, 3686117889/100000000], ![1522710499/50000000, 472540257/20000000, 1999749963/100000000], ![448472381/100000000, 80240527/25000000, 155544837/50000000]]
def scE90CutWeightFloor : ℚ := 153689097/100000000
def scE90CutMargins : Fin 3 → ℚ := ![23238979/10000000000, 7414583/5000000000, 1464101/1250000000]

theorem scE90Cut_roots_ok : scE90CutCell.rootsOK scE90CutRoots = true := by decide +kernel

theorem scE90Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE90CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE90Cut_margin_le (i : Fin 3) : curvatureLoss scE90CutCell scE90CutCaps i ≤ scE90CutMargins i := by
  fin_cases i <;> decide +kernel

def scE91CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨37/80, 19/40⟩, ⟨13/80, 1/6⟩⟩
def scE91CutRoots : Fin 3 → RatBounds := ![⟨455160948980959/281474976710656, 120485612718131/70368744177664⟩, ⟨336606877097141/281474976710656, 358123465063133/281474976710656⟩, ⟨159184459215083/140737488355328, 343055059951927/281474976710656⟩]
def scE91CutCaps : Fin 3 → Fin 3 → ℚ := ![![8305062459/100000000, 4859143319/100000000, 1803024621/50000000], ![3010035893/100000000, 574382143/25000000, 96796167/5000000], ![85051199/25000000, 30209063/12500000, 1483453/625000]]
def scE91CutWeightFloor : ℚ := 156904721/100000000
def scE91CutMargins : Fin 3 → ℚ := ![22173631/10000000000, 7015161/5000000000, 5437837/5000000000]

theorem scE91Cut_roots_ok : scE91CutCell.rootsOK scE91CutRoots = true := by decide +kernel

theorem scE91Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE91CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE91Cut_margin_le (i : Fin 3) : curvatureLoss scE91CutCell scE91CutCaps i ≤ scE91CutMargins i := by
  fin_cases i <;> decide +kernel

def scE92CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨19/40, 39/80⟩, ⟨1/8, 11/80⟩⟩
def scE92CutRoots : Fin 3 → RatBounds := ![⟨57144221056821/35184372088832, 242710661081483/140737488355328⟩, ⟨168559323637755/140737488355328, 180087707639251/140737488355328⟩, ⟨326188023849885/281474976710656, 22040784102591/17592186044416⟩]
def scE92CutCaps : Fin 3 → Fin 3 → ℚ := ![![3982581251/50000000, 2298331367/50000000, 3553292361/100000000], ![2893552669/100000000, 432938799/20000000, 988508539/50000000], ![122035193/25000000, 171676167/50000000, 34455321/10000000]]
def scE92CutWeightFloor : ℚ := 149959373/100000000
def scE92CutMargins : Fin 3 → ℚ := ![22161829/10000000000, 2775277/2000000000, 5737171/5000000000]

theorem scE92Cut_roots_ok : scE92CutCell.rootsOK scE92CutRoots = true := by decide +kernel

theorem scE92Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE92CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE92Cut_margin_le (i : Fin 3) : curvatureLoss scE92CutCell scE92CutCaps i ≤ scE92CutMargins i := by
  fin_cases i <;> decide +kernel

def scE93CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨19/40, 39/80⟩, ⟨11/80, 3/20⟩⟩
def scE93CutRoots : Fin 3 → RatBounds := ![⟨455997157740505/281474976710656, 484181220465041/281474976710656⟩, ⟨335193009426869/281474976710656, 179045322500305/140737488355328⟩, ⟨162131503039837/140737488355328, 175282569191211/140737488355328⟩]
def scE93CutCaps : Fin 3 → Fin 3 → ℚ := ![![20287307/250000, 4686009247/100000000, 226814639/6250000], ![1473343061/50000000, 1101399973/50000000, 4024117/200000], ![29214471/6250000, 4107317/1250000, 329833979/100000000]]
def scE93CutWeightFloor : ℚ := 152521043/100000000
def scE93CutMargins : Fin 3 → ℚ := ![11258829/5000000000, 7048237/5000000000, 11661967/10000000000]

theorem scE93Cut_roots_ok : scE93CutCell.rootsOK scE93CutRoots = true := by decide +kernel

theorem scE93Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE93CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE93Cut_margin_le (i : Fin 3) : curvatureLoss scE93CutCell scE93CutCaps i ≤ scE93CutMargins i := by
  fin_cases i <;> decide +kernel

def scE94CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨19/40, 39/80⟩, ⟨3/20, 13/80⟩⟩
def scE94CutRoots : Fin 3 → RatBounds := ![⟨454880052786835/281474976710656, 482984600702653/281474976710656⟩, ⟨333338409665099/281474976710656, 356084244872423/281474976710656⟩, ⟨10075289548707/8796093022208, 87139099762847/70368744177664⟩]
def scE94CutCaps : Fin 3 → Fin 3 → ℚ := ![![1033071073/12500000, 95501463/2000000, 3704598391/100000000], ![2999683429/100000000, 560213211/25000000, 2047050719/100000000], ![447995177/100000000, 3147379/1000000, 158013101/50000000]]
def scE94CutWeightFloor : ℚ := 1938563/1250000
def scE94CutMargins : Fin 3 → ℚ := ![22875483/10000000000, 14317703/10000000000, 11850929/10000000000]

theorem scE94Cut_roots_ok : scE94CutCell.rootsOK scE94CutRoots = true := by decide +kernel

theorem scE94Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE94CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE94Cut_margin_le (i : Fin 3) : curvatureLoss scE94CutCell scE94CutCaps i ≤ scE94CutMargins i := by
  fin_cases i <;> decide +kernel

def scE95CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨19/40, 39/80⟩, ⟨13/80, 1/6⟩⟩
def scE95CutRoots : Fin 3 → RatBounds := ![⟨227374354407435/140737488355328, 240789147209777/140737488355328⟩, ⟨166367658021743/140737488355328, 44267815112633/35184372088832⟩, ⟨40225813418297/35184372088832, 346613034981105/281474976710656⟩]
def scE95CutCaps : Fin 3 → Fin 3 → ℚ := ![![8166041931/100000000, 2363378619/50000000, 3625000741/100000000], ![592899031/20000000, 544040257/25000000, 1983154507/100000000], ![84953069/25000000, 59234403/25000000, 240922991/100000000]]
def scE95CutWeightFloor : ℚ := 25331/16000
def scE95CutMargins : Fin 3 → ℚ := ![872523/400000000, 13533681/10000000000, 687857/625000000]

theorem scE95Cut_roots_ok : scE95CutCell.rootsOK scE95CutRoots = true := by decide +kernel

theorem scE95Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE95CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE95Cut_margin_le (i : Fin 3) : curvatureLoss scE95CutCell scE95CutCaps i ≤ scE95CutMargins i := by
  fin_cases i <;> decide +kernel

def scE96CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨39/80, 1/2⟩, ⟨1/8, 11/80⟩⟩
def scE96CutRoots : Fin 3 → RatBounds := ![⟨456944344721675/281474976710656, 121325172743939/70368744177664⟩, ⟨333365158850779/281474976710656, 356345642862391/281474976710656⟩, ⟨329723955916681/281474976710656, 356340443353223/281474976710656⟩]
def scE96CutCaps : Fin 3 → Fin 3 → ℚ := ![![3928021467/50000000, 4486129127/100000000, 895331779/25000000], ![717283731/25000000, 2062968263/100000000, 509976643/25000000], ![487912537/100000000, 336830961/100000000, 350167183/100000000]]
def scE96CutWeightFloor : ℚ := 37841519/25000000
def scE96CutMargins : Fin 3 → ℚ := ![2737571/1250000000, 13449079/10000000000, 11662893/10000000000]

theorem scE96Cut_roots_ok : scE96CutCell.rootsOK scE96CutRoots = true := by decide +kernel

theorem scE96Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE96CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE96Cut_margin_le (i : Fin 3) : curvatureLoss scE96CutCell scE96CutCaps i ≤ scE96CutMargins i := by
  fin_cases i <;> decide +kernel

def scE97CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨39/80, 1/2⟩, ⟨11/80, 3/20⟩⟩
def scE97CutRoots : Fin 3 → RatBounds := ![⟨227894265942353/140737488355328, 60507679706405/35184372088832⟩, ⟨331439963240249/281474976710656, 354259948548417/281474976710656⟩, ⟨327798959715037/281474976710656, 354254370035003/281474976710656⟩]
def scE97CutCaps : Fin 3 → Fin 3 → ℚ := ![![8003989627/100000000, 4573110359/100000000, 457266621/12500000], ![2921759417/100000000, 2099330051/100000000, 2075962699/100000000], ![467210577/100000000, 64468191/20000000, 167603529/50000000]]
def scE97CutWeightFloor : ℚ := 38485869/25000000
def scE97CutMargins : Fin 3 → ℚ := ![35603/16000000, 13661683/10000000000, 11854107/10000000000]

theorem scE97Cut_roots_ok : scE97CutCell.rootsOK scE97CutRoots = true := by decide +kernel

theorem scE97Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE97CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE97Cut_margin_le (i : Fin 3) : curvatureLoss scE97CutCell scE97CutCaps i ≤ scE97CutMargins i := by
  fin_cases i <;> decide +kernel

def scE98CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨39/80, 1/2⟩, ⟨3/20, 13/80⟩⟩
def scE98CutRoots : Fin 3 → RatBounds := ![⟨454672198286345/281474976710656, 30179102435571/17592186044416⟩, ⟨329585880103971/281474976710656, 352252761340909/281474976710656⟩, ⟨325945155937921/281474976710656, 22015425999729/17592186044416⟩]
def scE98CutCaps : Fin 3 → Fin 3 → ℚ := ![![8151823251/100000000, 4659815527/100000000, 3734756873/100000000], ![297424929/10000000, 213564171/10000000, 2111968911/100000000], ![223890613/50000000, 9648543/3125000, 160586719/50000000]]
def scE98CutWeightFloor : ℚ := 19565407/12500000
def scE98CutMargins : Fin 3 → ℚ := ![176603/78125000, 3468853/2500000000, 12046679/10000000000]

theorem scE98Cut_roots_ok : scE98CutCell.rootsOK scE98CutRoots = true := by decide +kernel

theorem scE98Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE98CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE98Cut_margin_le (i : Fin 3) : curvatureLoss scE98CutCell scE98CutCaps i ≤ scE98CutMargins i := by
  fin_cases i <;> decide +kernel

def scE99CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨39/80, 1/2⟩, ⟨13/80, 1/6⟩⟩
def scE99CutRoots : Fin 3 → RatBounds := ![⟨454541147625393/281474976710656, 481459894101047/281474976710656⟩, ⟨328982973862027/281474976710656, 175155238158355/140737488355328⟩, ⟨325342359196775/281474976710656, 350304400493915/281474976710656⟩]
def scE99CutCaps : Fin 3 → Fin 3 → ℚ := ![![402701573/5000000, 4612804303/100000000, 36555307/1000000], ![1469560111/50000000, 64729529/3125000, 2047821447/100000000], ![339636287/100000000, 58102641/25000000, 244676581/100000000]]
def scE99CutWeightFloor : ℚ := 3195513/2000000
def scE99CutMargins : Fin 3 → ℚ := ![10772353/5000000000, 1638177/1250000000, 5596229/5000000000]

theorem scE99Cut_roots_ok : scE99CutCell.rootsOK scE99CutRoots = true := by decide +kernel

theorem scE99Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE99CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE99Cut_margin_le (i : Fin 3) : curvatureLoss scE99CutCell scE99CutCaps i ≤ scE99CutMargins i := by
  fin_cases i <;> decide +kernel

def scE100CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨7/40, 3/16⟩, ⟨1/8, 11/80⟩⟩
def scE100CutRoots : Fin 3 → RatBounds := ![⟨267109271003781/140737488355328, 288750170943293/140737488355328⟩, ⟨244287930031081/140737488355328, 264450394158773/140737488355328⟩, ⟨130194364253107/140737488355328, 4620936602579/4398046511104⟩]
def scE100CutCaps : Fin 3 → Fin 3 → ℚ := ![![33611110391/100000000, 26823686213/100000000, 400249669/4000000], ![8770639063/50000000, 18835872111/100000000, 287030033/6250000], ![315370243/50000000, 667492127/100000000, 281003167/100000000]]
def scE100CutWeightFloor : ℚ := 2475941/2000000
def scE100CutMargins : Fin 3 → ℚ := ![25284731/2500000000, 90482521/10000000000, 7265491/2500000000]

theorem scE100Cut_roots_ok : scE100CutCell.rootsOK scE100CutRoots = true := by decide +kernel

theorem scE100Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE100CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE100Cut_margin_le (i : Fin 3) : curvatureLoss scE100CutCell scE100CutCaps i ≤ scE100CutMargins i := by
  fin_cases i <;> decide +kernel

def scE101CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨7/40, 3/16⟩, ⟨11/80, 3/20⟩⟩
def scE101CutRoots : Fin 3 → RatBounds := ![⟨133159528948141/70368744177664, 71972424279515/35184372088832⟩, ⟨486521028166157/281474976710656, 526659540476511/281474976710656⟩, ⟨129235389662643/140737488355328, 293543787052337/281474976710656⟩]
def scE101CutCaps : Fin 3 → Fin 3 → ℚ := ![![3426388139/10000000, 1094469049/4000000, 407319737/4000000], ![17870524457/100000000, 958937461/5000000, 4676051631/100000000], ![75776587/12500000, 320262831/50000000, 134745883/50000000]]
def scE101CutWeightFloor : ℚ := 126068537/100000000
def scE101CutMargins : Fin 3 → ℚ := ![103009021/10000000000, 92150393/10000000000, 7386981/2500000000]

theorem scE101Cut_roots_ok : scE101CutCell.rootsOK scE101CutRoots = true := by decide +kernel

theorem scE101Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE101CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE101Cut_margin_le (i : Fin 3) : curvatureLoss scE101CutCell scE101CutCaps i ≤ scE101CutMargins i := by
  fin_cases i <;> decide +kernel

def scE102CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨7/40, 3/16⟩, ⟨3/20, 13/80⟩⟩
def scE102CutRoots : Fin 3 → RatBounds := ![⟨132777823001353/70368744177664, 574118016771959/281474976710656⟩, ⟨121134595648629/70368744177664, 262249210921437/140737488355328⟩, ⟨256625038723699/281474976710656, 4553623317817/4398046511104⟩]
def scE102CutCaps : Fin 3 → Fin 3 → ℚ := ![![545551177/1562500, 27898127323/100000000, 414372853/4000000], ![4549742303/25000000, 19520895511/100000000, 4759399823/100000000], ![291532311/50000000, 615140361/100000000, 32332999/12500000]]
def scE102CutWeightFloor : ℚ := 128340901/100000000
def scE102CutMargins : Fin 3 → ℚ := ![104877557/10000000000, 3752669/400000000, 7508489/2500000000]

theorem scE102Cut_roots_ok : scE102CutCell.rootsOK scE102CutRoots = true := by decide +kernel

theorem scE102Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE102CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE102Cut_margin_le (i : Fin 3) : curvatureLoss scE102CutCell scE102CutCaps i ≤ scE102CutMargins i := by
  fin_cases i <;> decide +kernel

def scE103CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨7/40, 3/16⟩, ⟨13/80, 1/6⟩⟩
def scE103CutRoots : Fin 3 → RatBounds := ![⟨530775488449171/281474976710656, 286165410959191/140737488355328⟩, ⟨483905740640569/281474976710656, 522386096855489/281474976710656⟩, ⟨128015845367691/140737488355328, 289386064741207/281474976710656⟩]
def scE103CutCaps : Fin 3 → Fin 3 → ℚ := ![![34702820823/100000000, 13858832847/50000000, 2044435571/20000000], ![3627770617/20000000, 775549129/4000000, 4657980559/100000000], ![458209489/100000000, 4868039/1000000, 210034747/100000000]]
def scE103CutWeightFloor : ℚ := 65611051/50000000
def scE103CutMargins : Fin 3 → ℚ := ![103305833/10000000000, 92110319/10000000000, 2910839/1000000000]

theorem scE103Cut_roots_ok : scE103CutCell.rootsOK scE103CutRoots = true := by decide +kernel

theorem scE103Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE103CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE103Cut_margin_le (i : Fin 3) : curvatureLoss scE103CutCell scE103CutCaps i ≤ scE103CutMargins i := by
  fin_cases i <;> decide +kernel

def scE104CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨3/16, 1/5⟩, ⟨1/8, 11/80⟩⟩
def scE104CutRoots : Fin 3 → RatBounds := ![⟨8210016517769/4398046511104, 35408400181729/17592186044416⟩, ⟨477020930315717/281474976710656, 515116881503367/281474976710656⟩, ⟨262952355294775/281474976710656, 148484729907441/140737488355328⟩]
def scE104CutCaps : Fin 3 → Fin 3 → ℚ := ![![14660450523/50000000, 22964062449/100000000, 276767007/3125000], ![2985599293/20000000, 16026343503/100000000, 2016831633/50000000], ![609191271/100000000, 159018391/25000000, 27932239/10000000]]
def scE104CutWeightFloor : ℚ := 124835547/100000000
def scE104CutMargins : Fin 3 → ℚ := ![17522691/2000000000, 19348867/2500000000, 25721739/10000000000]

theorem scE104Cut_roots_ok : scE104CutCell.rootsOK scE104CutRoots = true := by decide +kernel

theorem scE104Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE104CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE104Cut_margin_le (i : Fin 3) : curvatureLoss scE104CutCell scE104CutCaps i ≤ scE104CutMargins i := by
  fin_cases i <;> decide +kernel

def scE105CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨3/16, 1/5⟩, ⟨11/80, 3/20⟩⟩
def scE105CutRoots : Fin 3 → RatBounds := ![⟨261950953044265/140737488355328, 564862149529423/281474976710656⟩, ⟨474986617095717/281474976710656, 512902691219747/281474976710656⟩, ⟨130516702378141/140737488355328, 294784895764381/281474976710656⟩]
def scE105CutCaps : Fin 3 → Fin 3 → ℚ := ![![3735968973/12500000, 4684873057/20000000, 9014739987/100000000], ![7603958669/50000000, 16315685509/100000000, 4106536587/100000000], ![585409259/100000000, 7628821/1250000, 133932701/50000000]]
def scE105CutWeightFloor : ℚ := 31779931/25000000
def scE105CutMargins : Fin 3 → ℚ := ![89220857/10000000000, 7880929/1000000000, 6537667/2500000000]

theorem scE105Cut_roots_ok : scE105CutCell.rootsOK scE105CutRoots = true := by decide +kernel

theorem scE105Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE105CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE105Cut_margin_le (i : Fin 3) : curvatureLoss scE105CutCell scE105CutCaps i ≤ scE105CutMargins i := by
  fin_cases i <;> decide +kernel

def scE106CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨3/16, 1/5⟩, ⟨3/20, 13/80⟩⟩
def scE106CutRoots : Fin 3 → RatBounds := ![⟨130603752442625/70368744177664, 281623930453697/140737488355328⟩, ⟨236511994735921/140737488355328, 63845989528517/35184372088832⟩, ⟨259186675883599/281474976710656, 73171029219037/70368744177664⟩]
def scE106CutCaps : Fin 3 → Fin 3 → ℚ := ![![30453455647/100000000, 23883263497/100000000, 2293137943/25000000], ![15487160581/100000000, 16604419551/100000000, 1044803901/25000000], ![562970037/100000000, 586052307/100000000, 128544759/50000000]]
def scE106CutWeightFloor : ℚ := 64702407/50000000
def scE106CutMargins : Fin 3 → ℚ := ![90827317/10000000000, 4011107/500000000, 26579799/10000000000]

theorem scE106Cut_roots_ok : scE106CutCell.rootsOK scE106CutRoots = true := by decide +kernel

theorem scE106Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE106CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE106Cut_margin_le (i : Fin 3) : curvatureLoss scE106CutCell scE106CutCaps i ≤ scE106CutMargins i := by
  fin_cases i <;> decide +kernel

def scE107CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨3/16, 1/5⟩, ⟨13/80, 1/6⟩⟩
def scE107CutRoots : Fin 3 → RatBounds := ![⟨65262258120095/35184372088832, 280750447414489/140737488355328⟩, ⟨472397599591601/281474976710656, 127170490740167/70368744177664⟩, ⟨32324137058673/35184372088832, 290648799243543/281474976710656⟩]
def scE107CutCaps : Fin 3 → Fin 3 → ℚ := ![![378188377/1250000, 23722932209/100000000, 9042498849/100000000], ![3857337027/25000000, 16477858529/100000000, 63773151/1562500], ![440217339/100000000, 14413649/3125000, 25943893/12500000]]
def scE107CutWeightFloor : ℚ := 132301787/100000000
def scE107CutMargins : Fin 3 → ℚ := ![89322913/10000000000, 15723453/2000000000, 3209727/1250000000]

theorem scE107Cut_roots_ok : scE107CutCell.rootsOK scE107CutRoots = true := by decide +kernel

theorem scE107Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE107CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE107Cut_margin_le (i : Fin 3) : curvatureLoss scE107CutCell scE107CutCaps i ≤ scE107CutMargins i := by
  fin_cases i <;> decide +kernel

def scE108CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨1/5, 17/80⟩, ⟨1/8, 11/80⟩⟩
def scE108CutRoots : Fin 3 → RatBounds := ![⟨129372687083753/70368744177664, 278348265018753/140737488355328⟩, ⟨466315386840835/281474976710656, 502482091882615/281474976710656⟩, ⟨265479594314415/281474976710656, 298332486734309/281474976710656⟩]
def scE108CutCaps : Fin 3 → Fin 3 → ℚ := ![![3235046159/12500000, 9952233641/50000000, 396411563/5000000], ![3213033641/25000000, 344739663/2500000, 143444849/4000000], ![590998961/100000000, 608391549/100000000, 34803081/12500000]]
def scE108CutWeightFloor : ℚ := 31463/25000
def scE108CutMargins : Fin 3 → ℚ := ![76803717/10000000000, 16749241/2500000000, 359887/156250000]

theorem scE108Cut_roots_ok : scE108CutCell.rootsOK scE108CutRoots = true := by decide +kernel

theorem scE108Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE108CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE108Cut_margin_le (i : Fin 3) : curvatureLoss scE108CutCell scE108CutCaps i ≤ scE108CutMargins i := by
  fin_cases i <;> decide +kernel

def scE109CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨1/5, 17/80⟩, ⟨11/80, 3/20⟩⟩
def scE109CutRoots : Fin 3 → RatBounds := ![⟨257994654664303/140737488355328, 555068383158767/281474976710656⟩, ⟨464299203150391/281474976710656, 125072887038029/70368744177664⟩, ⟨263560193991877/281474976710656, 148079318441591/140737488355328⟩]
def scE109CutCaps : Fin 3 → Fin 3 → ℚ := ![![26378882521/100000000, 2030407787/10000000, 8071497299/100000000], ![13092972917/100000000, 1754754839/12500000, 1825657323/50000000], ![70918243/12500000, 145831027/25000000, 2134973/800000]]
def scE109CutWeightFloor : ℚ := 128148237/100000000
def scE109CutMargins : Fin 3 → ℚ := ![39100783/5000000000, 8526719/1250000000, 23417351/10000000000]

theorem scE109Cut_roots_ok : scE109CutCell.rootsOK scE109CutRoots = true := by decide +kernel

theorem scE109Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE109CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE109Cut_margin_le (i : Fin 3) : curvatureLoss scE109CutCell scE109CutCaps i ≤ scE109CutMargins i := by
  fin_cases i <;> decide +kernel


end HlawkaSchatten.BelowExponent.Vertex
