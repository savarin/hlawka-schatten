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

def scS64CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨31/80, 2/5⟩, ⟨0, 1/40⟩⟩
def scS64CutRoots : Fin 3 → RatBounds := ![⟨238530889480339/140737488355328, 509962651323867/281474976710656⟩, ⟨388690807765017/281474976710656, 104559163633743/70368744177664⟩, ⟨325325398539033/281474976710656, 89266329656951/70368744177664⟩]
def scS64CutCaps : Fin 3 → Fin 3 → ℚ := ![![4087430317/50000000, 1257986217/25000000, 1569643027/50000000], ![3046742527/100000000, 144243543/5000000, 1605141771/100000000], ![1091748717/100000000, 22171223/2500000, 682568993/100000000]]
def scS64CutWeightFloor : ℚ := 115578799/100000000
def scS64CutMargins : Fin 3 → ℚ := ![30446481/10000000000, 11195519/5000000000, 14599031/10000000000]

theorem scS64Cut_roots_ok : scS64CutCell.rootsOK scS64CutRoots = true := by decide +kernel

theorem scS64Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS64CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS64Cut_margin_le (i : Fin 3) : curvatureLoss scS64CutCell scS64CutCaps i ≤ scS64CutMargins i := by
  fin_cases i <;> decide +kernel

def scS65CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨31/80, 2/5⟩, ⟨1/40, 1/20⟩⟩
def scS65CutRoots : Fin 3 → RatBounds := ![⟨236905419581507/140737488355328, 506188574302043/281474976710656⟩, ⟨383196300070925/281474976710656, 411974197499645/281474976710656⟩, ⟨319810893357287/281474976710656, 350702355310505/281474976710656⟩]
def scS65CutCaps : Fin 3 → Fin 3 → ℚ := ![![1708410269/20000000, 2639511357/50000000, 824016847/25000000], ![1593808543/50000000, 601787303/20000000, 1677007191/100000000], ![976104051/100000000, 790300587/100000000, 76075613/12500000]]
def scS65CutWeightFloor : ℚ := 24093843/20000000
def scS65CutMargins : Fin 3 → ℚ := ![15267661/5000000000, 5590411/2500000000, 14467763/10000000000]

theorem scS65Cut_roots_ok : scS65CutCell.rootsOK scS65CutRoots = true := by decide +kernel

theorem scS65Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS65CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS65Cut_margin_le (i : Fin 3) : curvatureLoss scS65CutCell scS65CutCaps i ≤ scS65CutMargins i := by
  fin_cases i <;> decide +kernel

def scS66CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨31/80, 2/5⟩, ⟨1/20, 3/40⟩⟩
def scS66CutRoots : Fin 3 → RatBounds := ![⟨470811058709021/281474976710656, 31420308074237/17592186044416⟩, ⟨189082085018137/140737488355328, 406262500257489/281474976710656⟩, ⟨157385220589133/140737488355328, 172455406866845/140737488355328⟩]
def scS66CutCaps : Fin 3 → Fin 3 → ℚ := ![![8907850701/100000000, 86307659/1562500, 13482579/390625], ![1663670311/50000000, 1566074673/50000000, 6829166/390625], ![219312791/25000000, 88522367/12500000, 272830283/50000000]]
def scS66CutWeightFloor : ℚ := 125374893/100000000
def scS66CutMargins : Fin 3 → ℚ := ![30750383/10000000000, 4487717/2000000000, 7209423/5000000000]

theorem scS66Cut_roots_ok : scS66CutCell.rootsOK scS66CutRoots = true := by decide +kernel

theorem scS66Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS66CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS66Cut_margin_le (i : Fin 3) : curvatureLoss scS66CutCell scS66CutCaps i ≤ scS66CutMargins i := by
  fin_cases i <;> decide +kernel

def scS67CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨31/80, 2/5⟩, ⟨3/40, 1/10⟩⟩
def scS67CutRoots : Fin 3 → RatBounds := ![⟨234017079222561/140737488355328, 31220911040851/17592186044416⟩, ⟨186768936249073/140737488355328, 100257821614481/70368744177664⟩, ⟨77536299965467/70368744177664, 84904177657443/70368744177664⟩]
def scS67CutCaps : Fin 3 → Fin 3 → ℚ := ![![9272383073/100000000, 360388883/6250000, 450732149/12500000], ![216625653/6250000, 813644427/25000000, 1818969293/100000000], ![19804177/2500000, 127561511/20000000, 61461929/12500000]]
def scS67CutWeightFloor : ℚ := 130293373/100000000
def scS67CutMargins : Fin 3 → ℚ := ![31068481/10000000000, 11300811/5000000000, 2887347/2000000000]

theorem scS67Cut_roots_ok : scS67CutCell.rootsOK scS67CutRoots = true := by decide +kernel

theorem scS67Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS67CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS67Cut_margin_le (i : Fin 3) : curvatureLoss scS67CutCell scS67CutCaps i ≤ scS67CutMargins i := by
  fin_cases i <;> decide +kernel

def scS68CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨2/5, 33/80⟩, ⟨0, 1/40⟩⟩
def scS68CutRoots : Fin 3 → RatBounds := ![⟨237611357112417/140737488355328, 63486203981549/35184372088832⟩, ⟨383876189623063/281474976710656, 413105380650327/281474976710656⟩, ⟨164136264069713/140737488355328, 359877258420649/281474976710656⟩]
def scS68CutCaps : Fin 3 → Fin 3 → ℚ := ![![7888966069/100000000, 2398967813/50000000, 3089335373/100000000], ![727711653/25000000, 2697911163/100000000, 1606372913/100000000], ![543774661/50000000, 434215069/50000000, 692940243/100000000]]
def scS68CutWeightFloor : ℚ := 11662583/10000000
def scS68CutMargins : Fin 3 → ℚ := ![3698733/1250000000, 21424937/10000000000, 14584901/10000000000]

theorem scS68Cut_roots_ok : scS68CutCell.rootsOK scS68CutRoots = true := by decide +kernel

theorem scS68Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS68CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS68Cut_margin_le (i : Fin 3) : curvatureLoss scS68CutCell scS68CutCaps i ≤ scS68CutMargins i := by
  fin_cases i <;> decide +kernel

def scS69CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨2/5, 33/80⟩, ⟨1/40, 1/20⟩⟩
def scS69CutRoots : Fin 3 → RatBounds := ![⟨471995419400785/281474976710656, 252071085712377/140737488355328⟩, ⟨378386542508995/281474976710656, 50855801415207/35184372088832⟩, ⟨322762732801085/281474976710656, 353528231860575/281474976710656⟩]
def scS69CutCaps : Fin 3 → Fin 3 → ℚ := ![![8243293687/100000000, 2516663967/50000000, 3245115481/100000000], ![3045438033/100000000, 1406975181/50000000, 209753161/12500000], ![38888613/4000000, 773784607/100000000, 617793031/100000000]]
def scS69CutWeightFloor : ℚ := 60769391/50000000
def scS69CutMargins : Fin 3 → ℚ := ![29643737/10000000000, 5342977/2500000000, 7221009/5000000000]

theorem scS69Cut_roots_ok : scS69CutCell.rootsOK scS69CutRoots = true := by decide +kernel

theorem scS69Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS69CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS69Cut_margin_le (i : Fin 3) : curvatureLoss scS69CutCell scS69CutCaps i ≤ scS69CutMargins i := by
  fin_cases i <;> decide +kernel

def scS70CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨2/5, 33/80⟩, ⟨1/20, 3/40⟩⟩
def scS70CutRoots : Fin 3 → RatBounds := ![⟨117254375062325/70368744177664, 125175780591363/70368744177664⟩, ⟨186679827111641/140737488355328, 401138867008601/281474976710656⟩, ⟨158863087703825/140737488355328, 347748850559971/281474976710656⟩]
def scS70CutCaps : Fin 3 → Fin 3 → ℚ := ![![8596308003/100000000, 1316605049/25000000, 1699794811/50000000], ![1589461883/50000000, 366149083/12500000, 1749088211/100000000], ![218410977/25000000, 21665417/3125000, 3461553/625000]]
def scS70CutWeightFloor : ℚ := 126467643/100000000
def scS70CutMargins : Fin 3 → ℚ := ![29823843/10000000000, 21423411/10000000000, 14382953/10000000000]

theorem scS70Cut_roots_ok : scS70CutCell.rootsOK scS70CutRoots = true := by decide +kernel

theorem scS70Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS70CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS70Cut_margin_le (i : Fin 3) : curvatureLoss scS70CutCell scS70CutCaps i ≤ scS70CutMargins i := by
  fin_cases i <;> decide +kernel

def scS71CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨2/5, 33/80⟩, ⟨3/40, 1/10⟩⟩
def scS71CutRoots : Fin 3 → RatBounds := ![⟨116565219073173/70368744177664, 497535570882089/281474976710656⟩, ⟨92184715495485/70368744177664, 197956147840901/140737488355328⟩, ⟨313104148355667/281474976710656, 342465405817789/281474976710656⟩]
def scS71CutCaps : Fin 3 → Fin 3 → ℚ := ![![2237031421/25000000, 13743687/250000, 3552910411/100000000], ![3311396407/100000000, 380462581/12500000, 1455687/80000], ![788814891/100000000, 312164333/50000000, 62378903/12500000]]
def scS71CutWeightFloor : ℚ := 131409847/100000000
def scS71CutMargins : Fin 3 → ℚ := ![7526749/2500000000, 21559551/10000000000, 14391883/10000000000]

theorem scS71Cut_roots_ok : scS71CutCell.rootsOK scS71CutRoots = true := by decide +kernel

theorem scS71Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS71CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS71Cut_margin_le (i : Fin 3) : curvatureLoss scS71CutCell scS71CutCaps i ≤ scS71CutMargins i := by
  fin_cases i <;> decide +kernel

def scS72CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨33/80, 17/40⟩, ⟨0, 1/40⟩⟩
def scS72CutRoots : Fin 3 → RatBounds := ![⟨473633712410495/281474976710656, 126529238100539/70368744177664⟩, ⟨379247081985917/281474976710656, 408202859262867/281474976710656⟩, ⟨41410857043091/35184372088832, 362796125397449/281474976710656⟩]
def scS72CutCaps : Fin 3 → Fin 3 → ℚ := ![![7637980279/100000000, 36731181/800000, 19063089/625000], ![698830447/25000000, 506060591/20000000, 807013351/50000000], ![541978899/50000000, 212678009/25000000, 70365323/10000000]]
def scS72CutWeightFloor : ℚ := 58848367/50000000
def scS72CutMargins : Fin 3 → ℚ := ![7211491/2500000000, 256947/125000000, 14606903/10000000000]

theorem scS72Cut_roots_ok : scS72CutCell.rootsOK scS72CutRoots = true := by decide +kernel

theorem scS72Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS72CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS72Cut_margin_le (i : Fin 3) : curvatureLoss scS72CutCell scS72CutCaps i ≤ scS72CutMargins i := by
  fin_cases i <;> decide +kernel

def scS73CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨33/80, 17/40⟩, ⟨1/40, 1/20⟩⟩
def scS73CutRoots : Fin 3 → RatBounds := ![⟨470426807140493/281474976710656, 251196200653645/140737488355328⟩, ⟨93440288197057/70368744177664, 100486421139387/70368744177664⟩, ⟨325781596184421/281474976710656, 356460159214997/281474976710656⟩]
def scS73CutCaps : Fin 3 → Fin 3 → ℚ := ![![7981109257/100000000, 963280449/20000000, 320535627/10000000], ![2924529389/100000000, 527830171/20000000, 337147117/20000000], ![968888749/100000000, 189477047/25000000, 5018333/800000]]
def scS73CutWeightFloor : ℚ := 122632939/100000000
def scS73CutMargins : Fin 3 → ℚ := ![28869519/10000000000, 4096557/2000000000, 1445363/1000000000]

theorem scS73Cut_roots_ok : scS73CutCell.rootsOK scS73CutRoots = true := by decide +kernel

theorem scS73Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS73CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS73Cut_margin_le (i : Fin 3) : curvatureLoss scS73CutCell scS73CutCaps i ≤ scS73CutMargins i := by
  fin_cases i <;> decide +kernel

def scS74CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨33/80, 17/40⟩, ⟨1/20, 3/40⟩⟩
def scS74CutRoots : Fin 3 → RatBounds := ![⟨467467738791115/281474976710656, 498974523190123/281474976710656⟩, ⟨368738428937149/281474976710656, 396240710719025/281474976710656⟩, ⟨80187188894713/70368744177664, 175346059115777/140737488355328⟩]
def scS74CutCaps : Fin 3 → Fin 3 → ℚ := ![![4161495407/50000000, 5039205173/100000000, 3359310679/100000000], ![381583833/12500000, 137362571/5000000, 439217187/25000000], ![870557579/100000000, 678993583/100000000, 56231963/10000000]]
def scS74CutWeightFloor : ℚ := 3987053/3125000
def scS74CutMargins : Fin 3 → ℚ := ![725483/250000000, 20512561/10000000000, 14385661/10000000000]

theorem scS74Cut_roots_ok : scS74CutCell.rootsOK scS74CutRoots = true := by decide +kernel

theorem scS74Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS74CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS74Cut_margin_le (i : Fin 3) : curvatureLoss scS74CutCell scS74CutCaps i ≤ scS74CutMargins i := by
  fin_cases i <;> decide +kernel

def scS75CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨33/80, 17/40⟩, ⟨3/40, 1/10⟩⟩
def scS75CutRoots : Fin 3 → RatBounds := ![⟨464728598330099/281474976710656, 123956649550343/70368744177664⟩, ⟨364122125105425/281474976710656, 391017299893303/281474976710656⟩, ⟨316129763555281/281474976710656, 345418563152975/281474976710656⟩]
def scS75CutCaps : Fin 3 → Fin 3 → ℚ := ![![346549411/4000000, 2630028849/50000000, 1756055283/50000000], ![198739631/6250000, 356832769/12500000, 228433883/12500000], ![785946421/100000000, 152847039/25000000, 506626399/100000000]]
def scS75CutWeightFloor : ℚ := 33138083/25000000
def scS75CutMargins : Fin 3 → ℚ := ![14636089/5000000000, 20625533/10000000000, 1438689/1000000000]

theorem scS75Cut_roots_ok : scS75CutCell.rootsOK scS75CutRoots = true := by decide +kernel

theorem scS75Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS75CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS75Cut_margin_le (i : Fin 3) : curvatureLoss scS75CutCell scS75CutCaps i ≤ scS75CutMargins i := by
  fin_cases i <;> decide +kernel

def scS76CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨17/40, 7/16⟩, ⟨0, 1/40⟩⟩
def scS76CutRoots : Fin 3 → RatBounds := ![⟨59035800376467/35184372088832, 504634034349375/281474976710656⟩, ⟨5856101898779/4398046511104, 403513413449591/281474976710656⟩, ⟨167186681425433/140737488355328, 365825864740951/281474976710656⟩]
def scS76CutCaps : Fin 3 → Fin 3 → ℚ := ![![1854623611/25000000, 88184697/2000000, 1510485701/50000000], ![674552113/25000000, 475929121/20000000, 1627996203/100000000], ![1080943487/100000000, 83364081/10000000, 357355983/50000000]]
def scS76CutWeightFloor : ℚ := 59396641/50000000
def scS76CutMargins : Fin 3 → ℚ := ![28204057/10000000000, 19772351/10000000000, 14663703/10000000000]

theorem scS76Cut_roots_ok : scS76CutCell.rootsOK scS76CutRoots = true := by decide +kernel

theorem scS76Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS76CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS76Cut_margin_le (i : Fin 3) : curvatureLoss scS76CutCell scS76CutCaps i ≤ scS76CutMargins i := by
  fin_cases i <;> decide +kernel

def scS77CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨17/40, 7/16⟩, ⟨1/40, 1/20⟩⟩
def scS77CutRoots : Fin 3 → RatBounds := ![⟨234548359306263/140737488355328, 500928795828291/281474976710656⟩, ⟨184653633562673/140737488355328, 397256461826677/281474976710656⟩, ⟨328872413791865/281474976710656, 359502071376441/281474976710656⟩]
def scS77CutCaps : Fin 3 → Fin 3 → ℚ := ![![7751930353/100000000, 72265657/1562500, 635236259/20000000], ![141142147/5000000, 2482033919/100000000, 2720041/160000], ![966096251/100000000, 371311101/50000000, 637104561/100000000]]
def scS77CutWeightFloor : ℚ := 15469189/12500000
def scS77CutMargins : Fin 3 → ℚ := ![14100741/5000000000, 9841333/5000000000, 7250611/5000000000]

theorem scS77Cut_roots_ok : scS77CutCell.rootsOK scS77CutRoots = true := by decide +kernel

theorem scS77Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS77CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS77Cut_margin_le (i : Fin 3) : curvatureLoss scS77CutCell scS77CutCaps i ≤ scS77CutMargins i := by
  fin_cases i <;> decide +kernel

def scS78CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨17/40, 7/16⟩, ⟨1/20, 3/40⟩⟩
def scS78CutRoots : Fin 3 → RatBounds := ![⟨233076785482393/140737488355328, 497528765666431/281474976710656⟩, ⟨364287723010323/281474976710656, 195776294435289/140737488355328⟩, ⟨323843066272841/281474976710656, 353744539762651/281474976710656⟩]
def scS78CutCaps : Fin 3 → Fin 3 → ℚ := ![![8084173709/100000000, 2419327633/50000000, 3330077801/100000000], ![589289019/20000000, 645929691/25000000, 442872561/25000000], ![173593277/20000000, 665234631/100000000, 571077733/100000000]]
def scS78CutWeightFloor : ℚ := 64365467/50000000
def scS78CutMargins : Fin 3 → ℚ := ![5665033/2000000000, 1969397/1000000000, 2885109/2000000000]

theorem scS78Cut_roots_ok : scS78CutCell.rootsOK scS78CutRoots = true := by decide +kernel

theorem scS78Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS78CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS78Cut_margin_le (i : Fin 3) : curvatureLoss scS78CutCell scS78CutCaps i ≤ scS78CutMargins i := by
  fin_cases i <;> decide +kernel

def scS79CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨17/40, 7/16⟩, ⟨3/40, 1/10⟩⟩
def scS79CutRoots : Fin 3 → RatBounds := ![⟨463429195939291/281474976710656, 494397387308971/281474976710656⟩, ⟨359674977080953/281474976710656, 96582740412103/70368744177664⟩, ⟨319226887644991/281474976710656, 348480094917077/281474976710656⟩]
def scS79CutCaps : Fin 3 → Fin 3 → ℚ := ![![8415329723/100000000, 63130449/1250000, 1741407493/50000000], ![191818739/6250000, 335594149/12500000, 921216531/50000000], ![156707579/20000000, 598944627/100000000, 128621127/25000000]]
def scS79CutWeightFloor : ℚ := 133722767/100000000
def scS79CutMargins : Fin 3 → ℚ := ![28551917/10000000000, 19787047/10000000000, 7210143/5000000000]

theorem scS79Cut_roots_ok : scS79CutCell.rootsOK scS79CutRoots = true := by decide +kernel

theorem scS79Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS79CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS79Cut_margin_le (i : Fin 3) : curvatureLoss scS79CutCell scS79CutCaps i ≤ scS79CutMargins i := by
  fin_cases i <;> decide +kernel

def scS80CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨7/16, 9/20⟩, ⟨0, 1/40⟩⟩
def scS80CutRoots : Fin 3 → RatBounds := ![⟨117793457318887/70368744177664, 503432210589247/281474976710656⟩, ⟨370494701098885/281474976710656, 199511480132981/140737488355328⟩, ⟨42192151483519/35184372088832, 23060684321891/17592186044416⟩]
def scS80CutCaps : Fin 3 → Fin 3 → ℚ := ![![7227693081/100000000, 2124429863/50000000, 750384647/25000000], ![130896467/5000000, 1121954899/50000000, 824135613/50000000], ![1078481297/100000000, 8171689/1000000, 363061399/50000000]]
def scS80CutWeightFloor : ℚ := 59958653/50000000
def scS80CutMargins : Fin 3 → ℚ := ![27655367/10000000000, 19065323/10000000000, 2950899/2000000000]

theorem scS80Cut_roots_ok : scS80CutCell.rootsOK scS80CutRoots = true := by decide +kernel

theorem scS80Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS80CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS80Cut_margin_le (i : Fin 3) : curvatureLoss scS80CutCell scS80CutCaps i ≤ scS80CutMargins i := by
  fin_cases i <;> decide +kernel

def scS81CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨7/16, 9/20⟩, ⟨1/40, 1/20⟩⟩
def scS81CutRoots : Fin 3 → RatBounds := ![⟨233999134550599/140737488355328, 499742778699383/281474976710656⟩, ⟨365013169257169/281474976710656, 392764767835639/281474976710656⟩, ⟨332040300680855/281474976710656, 181329211807969/140737488355328⟩]
def scS81CutCaps : Fin 3 → Fin 3 → ℚ := ![![7552811363/100000000, 178256641/4000000, 1578576037/50000000], ![2738729717/100000000, 2340482807/100000000, 1720883629/100000000], ![481907429/50000000, 727883203/100000000, 129447567/20000000]]
def scS81CutWeightFloor : ℚ := 24980479/20000000
def scS81CutMargins : Fin 3 → ℚ := ![2763047/1000000000, 18961781/10000000000, 364599/250000000]

theorem scS81Cut_roots_ok : scS81CutCell.rootsOK scS81CutRoots = true := by decide +kernel

theorem scS81Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS81CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS81Cut_margin_le (i : Fin 3) : curvatureLoss scS81CutCell scS81CutCaps i ≤ scS81CutMargins i := by
  fin_cases i <;> decide +kernel

def scS82CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨7/16, 9/20⟩, ⟨1/20, 3/40⟩⟩
def scS82CutRoots : Fin 3 → RatBounds := ![⟨232534089414955/140737488355328, 496357357445967/281474976710656⟩, ⟨89998976180135/70368744177664, 48382578273321/35184372088832⟩, ⟨327014177039899/281474976710656, 89227638424279/70368744177664⟩]
def scS82CutCaps : Fin 3 → Fin 3 → ℚ := ![![1575356371/20000000, 4661936527/100000000, 413930287/12500000], ![714631719/25000000, 60909777/2500000, 1792939413/100000000], ![432924611/50000000, 325988331/50000000, 290064221/50000000]]
def scS82CutWeightFloor : ℚ := 129905307/100000000
def scS82CutMargins : Fin 3 → ℚ := ![27731847/10000000000, 18957489/10000000000, 14501749/10000000000]

theorem scS82Cut_roots_ok : scS82CutCell.rootsOK scS82CutRoots = true := by decide +kernel

theorem scS82Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS82CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS82Cut_margin_le (i : Fin 3) : curvatureLoss scS82CutCell scS82CutCaps i ≤ scS82CutMargins i := by
  fin_cases i <;> decide +kernel

def scS83CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨7/16, 9/20⟩, ⟨3/40, 1/10⟩⟩
def scS83CutRoots : Fin 3 → RatBounds := ![⟨115588978316103/70368744177664, 493239523693729/281474976710656⟩, ⟨355385865034663/281474976710656, 381839498829137/281474976710656⟩, ⟨322400547924313/281474976710656, 351654423631411/281474976710656⟩]
def scS83CutCaps : Fin 3 → Fin 3 → ℚ := ![![1024963223/12500000, 4865653881/100000000, 1732282389/50000000], ![1488701317/50000000, 253168379/10000000, 1864480029/100000000], ![781569863/100000000, 117392291/20000000, 261305437/50000000]]
def scS83CutWeightFloor : ℚ := 134923159/100000000
def scS83CutMargins : Fin 3 → ℚ := ![5587261/2000000000, 9516781/5000000000, 14491189/10000000000]

theorem scS83Cut_roots_ok : scS83CutCell.rootsOK scS83CutRoots = true := by decide +kernel

theorem scS83Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS83CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS83Cut_margin_le (i : Fin 3) : curvatureLoss scS83CutCell scS83CutCaps i ≤ scS83CutMargins i := by
  fin_cases i <;> decide +kernel

def scS84CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨9/20, 37/80⟩, ⟨0, 1/40⟩⟩
def scS84CutRoots : Fin 3 → RatBounds := ![⟨117572585618561/70368744177664, 502504576911843/281474976710656⟩, ⟨183174414912577/140737488355328, 49339852612561/35184372088832⟩, ⟨85195948780647/70368744177664, 372236402865593/281474976710656⟩]
def scS84CutCaps : Fin 3 → Fin 3 → ℚ := ![![7063265793/100000000, 2054054651/50000000, 598303079/20000000], ![2553234637/100000000, 2121373277/100000000, 837467157/50000000], ![107655117/10000000, 32050167/4000000, 737894387/100000000]]
def scS84CutWeightFloor : ℚ := 4842829/4000000
def scS84CutMargins : Fin 3 → ℚ := ![1699549/625000000, 18426757/10000000000, 185987/125000000]

theorem scS84Cut_roots_ok : scS84CutCell.rootsOK scS84CutRoots = true := by decide +kernel

theorem scS84Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS84CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS84Cut_margin_le (i : Fin 3) : curvatureLoss scS84CutCell scS84CutCaps i ≤ scS84CutMargins i := by
  fin_cases i <;> decide +kernel

def scS85CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨9/20, 37/80⟩, ⟨1/40, 1/20⟩⟩
def scS85CutRoots : Fin 3 → RatBounds := ![⟨467125868267591/281474976710656, 249413759166141/140737488355328⟩, ⟨360868151635435/281474976710656, 194229009565845/140737488355328⟩, ⟨41911324892151/35184372088832, 365934216561189/281474976710656⟩]
def scS85CutCaps : Fin 3 → Fin 3 → ℚ := ![![7381336333/100000000, 2154188673/50000000, 786996133/25000000], ![667720657/25000000, 442540213/20000000, 21854929/1250000], ![962026211/100000000, 713652689/100000000, 164424887/25000000]]
def scS85CutWeightFloor : ℚ := 3152039/2500000
def scS85CutMargins : Fin 3 → ℚ := ![2714907/1000000000, 18311893/10000000000, 7350759/5000000000]

theorem scS85Cut_roots_ok : scS85CutCell.rootsOK scS85CutRoots = true := by decide +kernel

theorem scS85Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS85CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS85Cut_margin_le (i : Fin 3) : curvatureLoss scS85CutCell scS85CutCaps i ≤ scS85CutMargins i := by
  fin_cases i <;> decide +kernel

def scS86CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨9/20, 37/80⟩, ⟨1/20, 3/40⟩⟩
def scS86CutRoots : Fin 3 → RatBounds := ![⟨464206026170411/281474976710656, 495453534070481/281474976710656⟩, ⟨88963086014143/70368744177664, 382752327864605/281474976710656⟩, ⟨165133692176577/140737488355328, 90048784562177/70368744177664⟩]
def scS86CutCaps : Fin 3 → Fin 3 → ℚ := ![![7698294431/100000000, 563334899/12500000, 1651558179/50000000], ![2787552037/100000000, 1151699099/50000000, 1821303209/100000000], ![864189229/100000000, 639184371/100000000, 589479331/100000000]]
def scS86CutWeightFloor : ℚ := 2048607/1562500
def scS86CutMargins : Fin 3 → ℚ := ![850989/312500000, 18294561/10000000000, 730697/500000000]

theorem scS86Cut_roots_ok : scS86CutCell.rootsOK scS86CutRoots = true := by decide +kernel

theorem scS86Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS86CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS86Cut_margin_le (i : Fin 3) : curvatureLoss scS86CutCell scS86CutCaps i ≤ scS86CutMargins i := by
  fin_cases i <;> decide +kernel

def scS87CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨9/20, 37/80⟩, ⟨3/40, 1/10⟩⟩
def scS87CutRoots : Fin 3 → RatBounds := ![⟨115375816102367/70368744177664, 492346305153139/281474976710656⟩, ⟨351244231268529/281474976710656, 188765249624663/140737488355328⟩, ⟨162827999149113/140737488355328, 354946506239569/281474976710656⟩]
def scS87CutCaps : Fin 3 → Fin 3 → ℚ := ![![4007119197/50000000, 2351619857/50000000, 864267089/25000000], ![725830509/25000000, 598377621/25000000, 236712649/12500000], ![97503349/12500000, 287703081/50000000, 531012583/100000000]]
def scS87CutWeightFloor : ℚ := 136155599/100000000
def scS87CutMargins : Fin 3 → ℚ := ![685433/250000000, 18356201/10000000000, 7299629/5000000000]

theorem scS87Cut_roots_ok : scS87CutCell.rootsOK scS87CutRoots = true := by decide +kernel

theorem scS87Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS87CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS87Cut_margin_le (i : Fin 3) : curvatureLoss scS87CutCell scS87CutCaps i ≤ scS87CutMargins i := by
  fin_cases i <;> decide +kernel

def scS88CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨37/80, 19/40⟩, ⟨0, 1/40⟩⟩
def scS88CutRoots : Fin 3 → RatBounds := ![⟨469631518173693/281474976710656, 501845876612985/281474976710656⟩, ⟨362343011942685/281474976710656, 97647389930549/70368744177664⟩, ⟨172059388025851/140737488355328, 375627833929285/281474976710656⟩]
def scS88CutCaps : Fin 3 → Fin 3 → ℚ := ![![1730834661/25000000, 3985178949/100000000, 2990759309/100000000], ![2503160257/100000000, 2010569453/100000000, 213519967/12500000], ![537568837/50000000, 785859261/100000000, 750037723/100000000]]
def scS88CutWeightFloor : ℚ := 30563887/25000000
def scS88CutMargins : Fin 3 → ℚ := ![6702661/2500000000, 4462493/2500000000, 7518623/5000000000]

theorem scS88Cut_roots_ok : scS88CutCell.rootsOK scS88CutRoots = true := by decide +kernel

theorem scS88Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS88CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS88Cut_margin_le (i : Fin 3) : curvatureLoss scS88CutCell scS88CutCaps i ≤ scS88CutMargins i := by
  fin_cases i <;> decide +kernel

def scS89CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨37/80, 19/40⟩, ⟨1/40, 1/20⟩⟩
def scS89CutRoots : Fin 3 → RatBounds := ![⟨466475137249139/281474976710656, 249088906805069/140737488355328⟩, ⟨356862395326499/281474976710656, 384324864487499/281474976710656⟩, ⟨42328615293575/35184372088832, 369335028408203/281474976710656⟩]
def scS89CutCaps : Fin 3 → Fin 3 → ℚ := ![![7235547111/100000000, 4178994237/100000000, 3148538781/100000000], ![2618292853/100000000, 131072433/6250000, 891368931/50000000], ![96071619/10000000, 69989649/10000000, 8356249/1250000]]
def scS89CutWeightFloor : ℚ := 63646541/50000000
def scS89CutMargins : Fin 3 → ℚ := ![26751377/10000000000, 17726053/10000000000, 1856757/1250000000]

theorem scS89Cut_roots_ok : scS89CutCell.rootsOK scS89CutRoots = true := by decide +kernel

theorem scS89Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS89CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS89Cut_margin_le (i : Fin 3) : curvatureLoss scS89CutCell scS89CutCaps i ≤ scS89CutMargins i := by
  fin_cases i <;> decide +kernel

def scS90CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨37/80, 19/40⟩, ⟨1/20, 3/40⟩⟩
def scS90CutRoots : Fin 3 → RatBounds := ![⟨231781388181773/140737488355328, 30925759113385/17592186044416⟩, ⟨351847293551007/281474976710656, 378616421199209/281474976710656⟩, ⟨333608254801047/281474976710656, 363603843461365/281474976710656⟩]
def scS90CutCaps : Fin 3 → Fin 3 → ℚ := ![![301866783/4000000, 546363141/12500000, 660992521/20000000], ![170779209/6250000, 2183147579/100000000, 46419193/2500000], ![431486721/50000000, 156706603/25000000, 119827983/20000000]]
def scS90CutWeightFloor : ℚ := 13234969/10000000
def scS90CutMargins : Fin 3 → ℚ := ![1340921/500000000, 8848983/5000000000, 7381143/5000000000]

theorem scS90Cut_roots_ok : scS90CutCell.rootsOK scS90CutRoots = true := by decide +kernel

theorem scS90Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS90CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS90Cut_margin_le (i : Fin 3) : curvatureLoss scS90CutCell scS90CutCaps i ≤ scS90CutMargins i := by
  fin_cases i <;> decide +kernel

def scS91CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨37/80, 19/40⟩, ⟨3/40, 1/10⟩⟩
def scS91CutRoots : Fin 3 → RatBounds := ![⟨460866952021703/281474976710656, 245856314813617/140737488355328⟩, ⟨347240394961097/281474976710656, 373392763426565/281474976710656⟩, ⟨164499381012599/140737488355328, 44795233276899/35184372088832⟩]
def scS91CutCaps : Fin 3 → Fin 3 → ℚ := ![![7856802433/100000000, 1140282407/25000000, 692038147/20000000], ![711440167/25000000, 2268578323/100000000, 1930288587/100000000], ![389448371/50000000, 35265619/6250000, 539698499/100000000]]
def scS91CutWeightFloor : ℚ := 137422279/100000000
def scS91CutMargins : Fin 3 → ℚ := ![1079543/400000000, 4436869/2500000000, 589787/400000000]

theorem scS91Cut_roots_ok : scS91CutCell.rootsOK scS91CutRoots = true := by decide +kernel

theorem scS91Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS91CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS91Cut_margin_le (i : Fin 3) : curvatureLoss scS91CutCell scS91CutCaps i ≤ scS91CutMargins i := by
  fin_cases i <;> decide +kernel

def scS92CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨19/40, 39/80⟩, ⟨0, 1/40⟩⟩
def scS92CutRoots : Fin 3 → RatBounds := ![⟨469194091980649/281474976710656, 250726207217143/140737488355328⟩, ⟨44808517677865/35184372088832, 24164052967219/17592186044416⟩, ⟨173774068056481/140737488355328, 379151475037409/281474976710656⟩]
def scS92CutCaps : Fin 3 → Fin 3 → ℚ := ![![1701605353/25000000, 1939284961/50000000, 1499630121/50000000], ![616749223/25000000, 59695191/3125000, 1748215299/100000000], ![1074229691/100000000, 385475487/50000000, 762566197/100000000]]
def scS92CutWeightFloor : ℚ := 123473901/100000000
def scS92CutMargins : Fin 3 → ℚ := ![5300913/2000000000, 2166167/1250000000, 7614981/5000000000]

theorem scS92Cut_roots_ok : scS92CutCell.rootsOK scS92CutRoots = true := by decide +kernel

theorem scS92Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS92CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS92Cut_margin_le (i : Fin 3) : curvatureLoss scS92CutCell scS92CutCaps i ≤ scS92CutMargins i := by
  fin_cases i <;> decide +kernel

def scS93CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨19/40, 39/80⟩, ⟨1/40, 1/20⟩⟩
def scS93CutRoots : Fin 3 → RatBounds := ![⟨466042845043777/281474976710656, 497790008695877/281474976710656⟩, ⟨352986865491123/281474976710656, 380355049212843/281474976710656⟩, ⟨85515300050213/70368744177664, 93216763903803/70368744177664⟩]
def scS93CutCaps : Fin 3 → Fin 3 → ℚ := ![![1778472041/25000000, 4066695043/100000000, 1579406807/50000000], ![645054371/25000000, 498137559/25000000, 1824191739/100000000], ![119984329/12500000, 686584251/100000000, 169912839/25000000]]
def scS93CutWeightFloor : ℚ := 32134787/25000000
def scS93CutMargins : Fin 3 → ℚ := ![26432821/10000000000, 17198403/10000000000, 15042209/10000000000]

theorem scS93Cut_roots_ok : scS93CutCell.rootsOK scS93CutRoots = true := by decide +kernel

theorem scS93Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS93CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS93Cut_margin_le (i : Fin 3) : curvatureLoss scS93CutCell scS93CutCaps i ≤ scS93CutMargins i := by
  fin_cases i <;> decide +kernel

def scS94CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨19/40, 39/80⟩, ⟨1/20, 3/40⟩⟩
def scS94CutRoots : Fin 3 → RatBounds := ![⟨463135229353459/281474976710656, 61803696661665/35184372088832⟩, ⟨173985892290027/140737488355328, 187321360463935/140737488355328⟩, ⟨168521335205729/140737488355328, 367142831752317/281474976710656⟩]
def scS94CutCaps : Fin 3 → Fin 3 → ℚ := ![![927535847/12500000, 4252970427/100000000, 3316988521/100000000], ![1346248269/50000000, 2074279459/100000000, 1899620107/100000000], ![862192539/100000000, 61487493/10000000, 76140213/12500000]]
def scS94CutWeightFloor : ℚ := 33406021/25000000
def scS94CutMargins : Fin 3 → ℚ := ![2648741/1000000000, 17161621/10000000000, 14947453/10000000000]

theorem scS94Cut_roots_ok : scS94CutCell.rootsOK scS94CutRoots = true := by decide +kernel

theorem scS94Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS94CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS94Cut_margin_le (i : Fin 3) : curvatureLoss scS94CutCell scS94CutCaps i ≤ scS94CutMargins i := by
  fin_cases i <;> decide +kernel

def scS95CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨19/40, 39/80⟩, ⟨3/40, 1/10⟩⟩
def scS95CutRoots : Fin 3 → RatBounds := ![⟨28777737800771/17592186044416, 491334911550345/281474976710656⟩, ⟨343365449229903/281474976710656, 369416170889013/281474976710656⟩, ⟨166217338302267/140737488355328, 361906633961047/281474976710656⟩]
def scS95CutCaps : Fin 3 → Fin 3 → ℚ := ![![1545142543/20000000, 1109402011/25000000, 3473947927/100000000], ![1401954569/50000000, 2155474249/100000000, 39490781/2000000], ![389085567/50000000, 276733519/50000000, 13716983/2500000]]
def scS95CutWeightFloor : ℚ := 138725511/100000000
def scS95CutMargins : Fin 3 → ℚ := ![2664513/1000000000, 4300269/2500000000, 7464067/5000000000]

theorem scS95Cut_roots_ok : scS95CutCell.rootsOK scS95CutRoots = true := by decide +kernel

theorem scS95Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS95CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS95Cut_margin_le (i : Fin 3) : curvatureLoss scS95CutCell scS95CutCaps i ≤ scS95CutMargins i := by
  fin_cases i <;> decide +kernel


end HlawkaSchatten.BelowExponent.Vertex
