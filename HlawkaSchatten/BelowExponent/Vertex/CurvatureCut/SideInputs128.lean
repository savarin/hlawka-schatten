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

def scS128CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨21/80, 11/40⟩, ⟨0, 1/40⟩⟩
def scS128CutRoots : Fin 3 → RatBounds := ![⟨62693214754267/35184372088832, 67342508233625/35184372088832⟩, ⟨443902169558021/281474976710656, 478561529869249/281474976710656⟩, ⟨299267519853443/281474976710656, 10435773325981/8796093022208⟩]
def scS128CutCaps : Fin 3 → Fin 3 → ℚ := ![![13432137313/100000000, 9401523631/100000000, 2273836147/50000000], ![5904100051/100000000, 6345451401/100000000, 414035877/20000000], ![1149412947/100000000, 110760931/10000000, 301813157/50000000]]
def scS128CutWeightFloor : ℚ := 106321181/100000000
def scS128CutMargins : Fin 3 → ℚ := ![23372939/5000000000, 39409009/10000000000, 17641323/10000000000]

theorem scS128Cut_roots_ok : scS128CutCell.rootsOK scS128CutRoots = true := by decide +kernel

theorem scS128Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS128CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS128Cut_margin_le (i : Fin 3) : curvatureLoss scS128CutCell scS128CutCaps i ≤ scS128CutMargins i := by
  fin_cases i <;> decide +kernel

def scS129CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨21/80, 11/40⟩, ⟨1/40, 1/20⟩⟩
def scS129CutRoots : Fin 3 → RatBounds := ![⟨62229876743595/35184372088832, 534451078751077/281474976710656⟩, ⟨438407933289311/281474976710656, 472296747392209/281474976710656⟩, ⟨73444886507661/70368744177664, 327491029898995/281474976710656⟩]
def scS129CutCaps : Fin 3 → Fin 3 → ℚ := ![![14055627513/100000000, 9879445931/100000000, 594741171/12500000], ![6178829073/100000000, 662282333/10000000, 216573813/10000000], ![128839579/12500000, 247388763/25000000, 269599039/50000000]]
def scS129CutWeightFloor : ℚ := 27753691/25000000
def scS129CutMargins : Fin 3 → ℚ := ![47572897/10000000000, 19980947/5000000000, 8867637/5000000000]

theorem scS129Cut_roots_ok : scS129CutCell.rootsOK scS129CutRoots = true := by decide +kernel

theorem scS129Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS129CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS129Cut_margin_le (i : Fin 3) : curvatureLoss scS129CutCell scS129CutCaps i ≤ scS129CutMargins i := by
  fin_cases i <;> decide +kernel

def scS130CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨21/80, 11/40⟩, ⟨1/20, 3/40⟩⟩
def scS130CutRoots : Fin 3 → RatBounds := ![⟨247209764702595/140737488355328, 66314224987443/35184372088832⟩, ⟨433366737011159/281474976710656, 466571714053809/281474976710656⟩, ⟨288766327282769/281474976710656, 160810514614593/140737488355328⟩]
def scS130CutCaps : Fin 3 → Fin 3 → ℚ := ![![14675895193/100000000, 10352663289/100000000, 4966569409/100000000], ![1612845693/25000000, 1379639137/20000000, 452055899/20000000], ![232226093/25000000, 88885251/10000000, 484262473/100000000]]
def scS130CutWeightFloor : ℚ := 28929151/25000000
def scS130CutMargins : Fin 3 → ℚ := ![48521281/10000000000, 8127449/2000000000, 13983/7812500]

theorem scS130Cut_roots_ok : scS130CutCell.rootsOK scS130CutRoots = true := by decide +kernel

theorem scS130Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS130CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS130Cut_margin_le (i : Fin 3) : curvatureLoss scS130CutCell scS130CutCaps i ≤ scS130CutMargins i := by
  fin_cases i <;> decide +kernel

def scS131CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨21/80, 11/40⟩, ⟨3/40, 1/10⟩⟩
def scS131CutRoots : Fin 3 → RatBounds := ![⟨491254770868563/281474976710656, 526886200888537/281474976710656⟩, ⟨428724051077409/281474976710656, 14416207728197/8796093022208⟩, ⟨284168705277549/281474976710656, 316258825603129/281474976710656⟩]
def scS131CutCaps : Fin 3 → Fin 3 → ℚ := ![![7646624699/50000000, 10821710443/100000000, 5173784569/100000000], ![6721968173/100000000, 57374089/800000, 1176954129/50000000], ![420495197/50000000, 401163151/50000000, 218538481/50000000]]
def scS131CutWeightFloor : ℚ := 60212673/50000000
def scS131CutMargins : Fin 3 → ℚ := ![4956871/1000000000, 20705837/5000000000, 18117189/10000000000]

theorem scS131Cut_roots_ok : scS131CutCell.rootsOK scS131CutRoots = true := by decide +kernel

theorem scS131Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS131CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS131Cut_margin_le (i : Fin 3) : curvatureLoss scS131CutCell scS131CutCaps i ≤ scS131CutMargins i := by
  fin_cases i <;> decide +kernel

def scS132CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨11/40, 23/80⟩, ⟨0, 1/40⟩⟩
def scS132CutRoots : Fin 3 → RatBounds := ![⟨31046114236641/17592186044416, 266514648208717/140737488355328⟩, ⟨436520499951699/281474976710656, 470237387853735/281474976710656⟩, ⟨301770829254117/281474976710656, 167913448446653/140737488355328⟩]
def scS132CutCaps : Fin 3 → Fin 3 → ℚ := ![![2489527599/20000000, 858091959/10000000, 267340489/6250000], ![5354296699/100000000, 5716922853/100000000, 490939383/25000000], ![1136212847/100000000, 1078170837/100000000, 305132569/50000000]]
def scS132CutWeightFloor : ℚ := 21442107/20000000
def scS132CutMargins : Fin 3 → ℚ := ![43646067/10000000000, 9087171/2500000000, 16957551/10000000000]

theorem scS132Cut_roots_ok : scS132CutCell.rootsOK scS132CutRoots = true := by decide +kernel

theorem scS132Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS132CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS132Cut_margin_le (i : Fin 3) : curvatureLoss scS132CutCell scS132CutCaps i ≤ scS132CutMargins i := by
  fin_cases i <;> decide +kernel

def scS133CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨11/40, 23/80⟩, ⟨1/40, 1/20⟩⟩
def scS133CutRoots : Fin 3 → RatBounds := ![⟨493093335097969/281474976710656, 528812047334635/281474976710656⟩, ⟨215523115061567/140737488355328, 463998146852473/281474976710656⟩, ⟨1157373465689/1099511627776, 329396859218677/281474976710656⟩]
def scS133CutCaps : Fin 3 → Fin 3 → ℚ := ![![52094271/400000, 36070449/400000, 1119342561/25000000], ![5603605001/100000000, 5966701569/100000000, 2054515879/100000000], ![127315639/12500000, 962956951/100000000, 136253327/25000000]]
def scS133CutWeightFloor : ℚ := 111922961/100000000
def scS133CutMargins : Fin 3 → ℚ := ![1773537/400000000, 1839467/500000000, 17015507/10000000000]

theorem scS133Cut_roots_ok : scS133CutCell.rootsOK scS133CutRoots = true := by decide +kernel

theorem scS133Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS133CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS133Cut_margin_le (i : Fin 3) : curvatureLoss scS133CutCell scS133CutCaps i ≤ scS133CutMargins i := by
  fin_cases i <;> decide +kernel

def scS134CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨11/40, 23/80⟩, ⟨1/20, 3/40⟩⟩
def scS134CutRoots : Fin 3 → RatBounds := ![⟨30608210778941/17592186044416, 131235257283623/70368744177664⟩, ⟨426024490825191/281474976710656, 458297867062167/281474976710656⟩, ⟨291278480681025/281474976710656, 323548072634257/281474976710656⟩]
def scS134CutCaps : Fin 3 → Fin 3 → ℚ := ![![6798328877/50000000, 9450006437/100000000, 2337883189/50000000], ![1170185959/20000000, 1553670367/25000000, 1072161643/50000000], ![917619287/100000000, 216177939/25000000, 30586737/6250000]]
def scS134CutWeightFloor : ℚ := 58322113/50000000
def scS134CutMargins : Fin 3 → ℚ := ![45152471/10000000000, 7470131/2000000000, 1714383/1000000000]

theorem scS134Cut_roots_ok : scS134CutCell.rootsOK scS134CutRoots = true := by decide +kernel

theorem scS134Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS134CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS134Cut_margin_le (i : Fin 3) : curvatureLoss scS134CutCell scS134CutCaps i ≤ scS134CutMargins i := by
  fin_cases i <;> decide +kernel

def scS135CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨11/40, 23/80⟩, ⟨3/40, 1/10⟩⟩
def scS135CutRoots : Fin 3 → RatBounds := ![⟨486619969273873/281474976710656, 130343707464253/70368744177664⟩, ⟨52675088096299/35184372088832, 453068723858771/281474976710656⟩, ⟨286684392661641/281474976710656, 318204964825145/281474976710656⟩]
def scS135CutCaps : Fin 3 → Fin 3 → ℚ := ![![1416717487/10000000, 9878590277/100000000, 1218204387/25000000], ![6096457517/100000000, 323051807/5000000, 558320503/25000000], ![830521311/100000000, 156064949/20000000, 441619793/100000000]]
def scS135CutWeightFloor : ℚ := 60686439/50000000
def scS135CutMargins : Fin 3 → ℚ := ![9213171/2000000000, 1900481/500000000, 2166157/1250000000]

theorem scS135Cut_roots_ok : scS135CutCell.rootsOK scS135CutRoots = true := by decide +kernel

theorem scS135Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS135CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS135Cut_margin_le (i : Fin 3) : curvatureLoss scS135CutCell scS135CutCaps i ≤ scS135CutMargins i := by
  fin_cases i <;> decide +kernel

def scS136CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨23/80, 3/10⟩, ⟨0, 1/40⟩⟩
def scS136CutRoots : Fin 3 → RatBounds := ![⟨246174561359131/140737488355328, 263922291773105/140737488355328⟩, ⟨429534199682881/281474976710656, 462412292265259/281474976710656⟩, ⟨76073857866395/70368744177664, 337802322190117/281474976710656⟩]
def scS136CutCaps : Fin 3 → Fin 3 → ℚ := ![![2899826163/25000000, 7879707211/100000000, 4045102523/100000000], ![76356463/1562500, 323586877/6250000, 468969589/25000000], ![562219591/50000000, 210109353/20000000, 308681343/50000000]]
def scS136CutWeightFloor : ℚ := 54053727/50000000
def scS136CutMargins : Fin 3 → ℚ := ![40984131/10000000000, 1685477/500000000, 8193781/5000000000]

theorem scS136Cut_roots_ok : scS136CutCell.rootsOK scS136CutRoots = true := by decide +kernel

theorem scS136Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS136CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS136Cut_margin_le (i : Fin 3) : curvatureLoss scS136CutCell scS136CutCaps i ≤ scS136CutMargins i := by
  fin_cases i <;> decide +kernel

def scS137CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨23/80, 3/10⟩, ⟨1/40, 1/20⟩⟩
def scS137CutRoots : Fin 3 → RatBounds := ![⟨488761714591125/281474976710656, 130923219644845/70368744177664⟩, ⟨424077237129227/281474976710656, 456194825542759/281474976710656⟩, ⟨298817375555691/281474976710656, 331394840771371/281474976710656⟩]
def scS137CutCaps : Fin 3 → Fin 3 → ℚ := ![![3033607333/25000000, 2070273213/25000000, 847245679/20000000], ![5114505901/100000000, 5403540907/100000000, 49066273/2500000], ![251911599/25000000, 37520657/4000000, 551243231/100000000]]
def scS137CutWeightFloor : ℚ := 352621/312500
def scS137CutMargins : Fin 3 → ℚ := ![8312313/2000000000, 17028027/5000000000, 8206887/5000000000]

theorem scS137Cut_roots_ok : scS137CutCell.rootsOK scS137CutRoots = true := by decide +kernel

theorem scS137Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS137CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS137Cut_margin_le (i : Fin 3) : curvatureLoss scS137CutCell scS137CutCaps i ≤ scS137CutMargins i := by
  fin_cases i <;> decide +kernel

def scS138CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨23/80, 3/10⟩, ⟨1/20, 3/40⟩⟩
def scS138CutRoots : Fin 3 → RatBounds := ![⟨485452530769711/281474976710656, 519882400831915/281474976710656⟩, ⟨209536232845133/140737488355328, 450515792659617/281474976710656⟩, ⟨146906352682035/140737488355328, 162783115191109/140737488355328⟩]
def scS138CutCaps : Fin 3 → Fin 3 → ℚ := ![![12667036861/100000000, 2169631889/25000000, 2212953387/50000000], ![333773577/6250000, 5628063603/100000000, 128033007/6250000], ![226886457/25000000, 168418143/20000000, 494889823/100000000]]
def scS138CutWeightFloor : ℚ := 117579413/100000000
def scS138CutMargins : Fin 3 → ℚ := ![42260933/10000000000, 6904279/2000000000, 4127927/2500000000]

theorem scS138Cut_roots_ok : scS138CutCell.rootsOK scS138CutRoots = true := by decide +kernel

theorem scS138Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS138CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS138Cut_margin_le (i : Fin 3) : curvatureLoss scS138CutCell scS138CutCaps i ≤ scS138CutMargins i := by
  fin_cases i <;> decide +kernel

def scS139CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨23/80, 3/10⟩, ⟨3/40, 1/10⟩⟩
def scS139CutRoots : Fin 3 → RatBounds := ![⟨241195040502317/140737488355328, 516372301275473/281474976710656⟩, ⟨12952038908977/8796093022208, 222653650560253/140737488355328⟩, ⟨144611236367129/140737488355328, 320241255714127/281474976710656⟩]
def scS139CutCaps : Fin 3 → Fin 3 → ℚ := ![![13197358861/100000000, 907245969/10000000, 2307154841/50000000], ![347787293/6250000, 2925555223/50000000, 2133598837/100000000], ![205293369/25000000, 759721133/100000000, 446506351/100000000]]
def scS139CutWeightFloor : ℚ := 122327987/100000000
def scS139CutMargins : Fin 3 → ℚ := ![43059863/10000000000, 877073/250000000, 52087/31250000]

theorem scS139Cut_roots_ok : scS139CutCell.rootsOK scS139CutRoots = true := by decide +kernel

theorem scS139Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS139CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS139Cut_margin_le (i : Fin 3) : curvatureLoss scS139CutCell scS139CutCaps i ≤ scS139CutMargins i := by
  fin_cases i <;> decide +kernel

def scS140CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨3/10, 5/16⟩, ⟨0, 1/40⟩⟩
def scS140CutRoots : Fin 3 → RatBounds := ![⟨61043435000945/35184372088832, 523141763935585/281474976710656⟩, ⟨422907389408211/281474976710656, 113759520692027/70368744177664⟩, ⟨306846784501187/281474976710656, 339869529282803/281474976710656⟩]
def scS140CutCaps : Fin 3 → Fin 3 → ℚ := ![![5432130929/50000000, 727686901/10000000, 1922284501/50000000], ![897481489/20000000, 1178194731/25000000, 1804160901/100000000], ![1113929267/100000000, 512264201/50000000, 124977343/20000000]]
def scS140CutWeightFloor : ℚ := 27253469/25000000
def scS140CutMargins : Fin 3 → ℚ := ![19343151/5000000000, 3142141/1000000000, 3978651/2500000000]

theorem scS140Cut_roots_ok : scS140CutCell.rootsOK scS140CutRoots = true := by decide +kernel

theorem scS140Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS140CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS140Cut_margin_le (i : Fin 3) : curvatureLoss scS140CutCell scS140CutCaps i ≤ scS140CutMargins i := by
  fin_cases i <;> decide +kernel

def scS141CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨3/10, 5/16⟩, ⟨1/40, 1/20⟩⟩
def scS141CutRoots : Fin 3 → RatBounds := ![⟨121203091925893/70368744177664, 519049873376513/281474976710656⟩, ⟨417465344897929/281474976710656, 448839014062309/281474976710656⟩, ⟨301374222148925/281474976710656, 41685445159273/35184372088832⟩]
def scS141CutCaps : Fin 3 → Fin 3 → ℚ := ![![1136418543/10000000, 305913059/4000000, 503525391/12500000], ![2348327677/50000000, 4918649753/100000000, 471901637/25000000], ![997931207/100000000, 457271333/50000000, 557858749/100000000]]
def scS141CutWeightFloor : ℚ := 56882037/50000000
def scS141CutMargins : Fin 3 → ℚ := ![2447823/625000000, 7922191/2500000000, 3978147/2500000000]

theorem scS141Cut_roots_ok : scS141CutCell.rootsOK scS141CutRoots = true := by decide +kernel

theorem scS141Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS141CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS141Cut_margin_le (i : Fin 3) : curvatureLoss scS141CutCell scS141CutCaps i ≤ scS141CutMargins i := by
  fin_cases i <;> decide +kernel

def scS142CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨3/10, 5/16⟩, ⟨1/20, 3/40⟩⟩
def scS142CutRoots : Fin 3 → RatBounds := ![⟨240775766362187/140737488355328, 257647322212123/140737488355328⟩, ⟨412475303237229/281474976710656, 221589041777505/140737488355328⟩, ⟨296374292742727/281474976710656, 163837080625535/140737488355328⟩]
def scS142CutCaps : Fin 3 → Fin 3 → ℚ := ![![370683293/3125000, 8015132229/100000000, 263153623/6250000], ![30651401/625000, 640381851/12500000, 1970213377/100000000], ![44927333/5000000, 164162881/20000000, 250371113/50000000]]
def scS142CutWeightFloor : ℚ := 14815537/12500000
def scS142CutMargins : Fin 3 → ℚ := ![7953233/2000000000, 6414627/2000000000, 15983673/10000000000]

theorem scS142Cut_roots_ok : scS142CutCell.rootsOK scS142CutRoots = true := by decide +kernel

theorem scS142Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS142CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS142Cut_margin_le (i : Fin 3) : curvatureLoss scS142CutCell scS142CutCaps i ≤ scS142CutMargins i := by
  fin_cases i <;> decide +kernel

def scS143CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨3/10, 5/16⟩, ⟨3/40, 1/10⟩⟩
def scS143CutRoots : Fin 3 → RatBounds := ![⟨478533925353493/281474976710656, 511835741514467/281474976710656⟩, ⟨407882547728127/281474976710656, 437987308174411/281474976710656⟩, ⟨145894081787955/140737488355328, 80591605617335/70368744177664⟩]
def scS143CutCaps : Fin 3 → Fin 3 → ℚ := ![![3089375909/25000000, 1047400061/12500000, 548937181/12500000], ![5110272491/100000000, 5326128513/100000000, 2052062887/100000000], ![406410191/50000000, 740354729/100000000, 451712807/100000000]]
def scS143CutWeightFloor : ℚ := 123292897/100000000
def scS143CutMargins : Fin 3 → ℚ := ![4046691/1000000000, 32552243/10000000000, 8057043/5000000000]

theorem scS143Cut_roots_ok : scS143CutCell.rootsOK scS143CutRoots = true := by decide +kernel

theorem scS143Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS143CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS143Cut_margin_le (i : Fin 3) : curvatureLoss scS143CutCell scS143CutCaps i ≤ scS143CutMargins i := by
  fin_cases i <;> decide +kernel

def scS144CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨5/16, 13/40⟩, ⟨0, 1/40⟩⟩
def scS144CutRoots : Fin 3 → RatBounds := ![⟨242352557866837/140737488355328, 518883040838725/281474976710656⟩, ⟨104152144653425/70368744177664, 448073005288485/281474976710656⟩, ⟨154714992404629/140737488355328, 85506951406249/70368744177664⟩]
def scS144CutCaps : Fin 3 → Fin 3 → ℚ := ![![511219459/5000000, 270234233/4000000, 3671052939/100000000], ![4144815883/100000000, 1077848653/25000000, 54581567/3125000], ![276137059/25000000, 199988023/20000000, 79101499/12500000]]
def scS144CutWeightFloor : ℚ := 109931613/100000000
def scS144CutMargins : Fin 3 → ℚ := ![36694137/10000000000, 7356939/2500000000, 15525217/10000000000]

theorem scS144Cut_roots_ok : scS144CutCell.rootsOK scS144CutRoots = true := by decide +kernel

theorem scS144Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS144CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS144Cut_margin_le (i : Fin 3) : curvatureLoss scS144CutCell scS144CutCaps i ≤ scS144CutMargins i := by
  fin_cases i <;> decide +kernel

def scS145CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨5/16, 13/40⟩, ⟨1/40, 1/20⟩⟩
def scS145CutRoots : Fin 3 → RatBounds := ![⟨481217803725573/281474976710656, 128711408343875/70368744177664⟩, ⟨102794824724731/70368744177664, 441889294982463/281474976710656⟩, ⟨151981583234275/140737488355328, 167831186023299/140737488355328⟩]
def scS145CutCaps : Fin 3 → Fin 3 → ℚ := ![![2673451613/25000000, 7100442299/100000000, 153932589/4000000], ![2169133059/50000000, 4499547989/100000000, 91361489/5000000], ![494628209/50000000, 44618791/5000000, 564837481/100000000]]
def scS145CutWeightFloor : ℚ := 114700923/100000000
def scS145CutMargins : Fin 3 → ℚ := ![37088083/10000000000, 14813959/5000000000, 15497841/10000000000]

theorem scS145Cut_roots_ok : scS145CutCell.rootsOK scS145CutRoots = true := by decide +kernel

theorem scS145Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS145CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS145Cut_margin_le (i : Fin 3) : curvatureLoss scS145CutCell scS145CutCaps i ≤ scS145CutMargins i := by
  fin_cases i <;> decide +kernel

def scS146CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨5/16, 13/40⟩, ⟨1/20, 3/40⟩⟩
def scS146CutRoots : Fin 3 → RatBounds := ![⟨478001159193981/281474976710656, 255570364690267/140737488355328⟩, ⟨406201968440997/281474976710656, 54530454278267/35184372088832⟩, ⟨298968191655599/281474976710656, 329871274149457/281474976710656⟩]
def scS146CutCaps : Fin 3 → Fin 3 → ℚ := ![![1395151699/12500000, 7441636279/100000000, 2012128361/50000000], ![566269337/12500000, 2343223459/50000000, 953552047/50000000], ![890508627/100000000, 800736377/100000000, 253462423/50000000]]
def scS146CutWeightFloor : ℚ := 59740429/50000000
def scS146CutMargins : Fin 3 → ℚ := ![37604303/10000000000, 3742927/1250000000, 194313/125000000]

theorem scS146Cut_roots_ok : scS146CutCell.rootsOK scS146CutRoots = true := by decide +kernel

theorem scS146Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS146CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS146Cut_margin_le (i : Fin 3) : curvatureLoss scS146CutCell scS146CutCaps i ≤ scS146CutMargins i := by
  fin_cases i <;> decide +kernel

def scS147CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨5/16, 13/40⟩, ⟨3/40, 1/10⟩⟩
def scS147CutRoots : Fin 3 → RatBounds := ![⟨475024535504399/281474976710656, 507728460768917/281474976710656⟩, ⟨401621782365263/281474976710656, 215533964654669/140737488355328⟩, ⟨36798293622615/35184372088832, 40572490773139/35184372088832⟩]
def scS147CutCaps : Fin 3 → Fin 3 → ℚ := ![![1453348431/12500000, 7779822463/100000000, 4199035883/100000000], ![4720622761/100000000, 194885193/4000000, 1986260587/100000000], ![402678469/50000000, 28883601/4000000, 114305123/25000000]]
def scS147CutWeightFloor : ℚ := 4970787/4000000
def scS147CutMargins : Fin 3 → ℚ := ![38220387/10000000000, 30352173/10000000000, 15652693/10000000000]

theorem scS147Cut_roots_ok : scS147CutCell.rootsOK scS147CutRoots = true := by decide +kernel

theorem scS147Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS147CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS147Cut_margin_le (i : Fin 3) : curvatureLoss scS147CutCell scS147CutCaps i ≤ scS147CutMargins i := by
  fin_cases i <;> decide +kernel

def scS148CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨13/40, 27/80⟩, ⟨0, 1/40⟩⟩
def scS148CutRoots : Fin 3 → RatBounds := ![⟨240698971969281/140737488355328, 515035969245221/281474976710656⟩, ⟨410609989567015/281474976710656, 441480657951619/281474976710656⟩, ⟨156024931955647/140737488355328, 344277121302957/281474976710656⟩]
def scS148CutCaps : Fin 3 → Fin 3 → ℚ := ![![4832598579/50000000, 6303506909/100000000, 1760367913/50000000], ![1924949353/50000000, 3960546943/100000000, 850227829/50000000], ![27404563/2500000, 976631671/100000000, 641118427/100000000]]
def scS148CutWeightFloor : ℚ := 110862381/100000000
def scS148CutMargins : Fin 3 → ℚ := ![17480299/5000000000, 6919229/2500000000, 7603189/5000000000]

theorem scS148Cut_roots_ok : scS148CutCell.rootsOK scS148CutRoots = true := by decide +kernel

theorem scS148Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS148CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS148Cut_margin_le (i : Fin 3) : curvatureLoss scS148CutCell scS148CutCaps i ≤ scS148CutMargins i := by
  fin_cases i <;> decide +kernel

def scS149CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨13/40, 27/80⟩, ⟨1/40, 1/20⟩⟩
def scS149CutRoots : Fin 3 → RatBounds := ![⟨14936068484927/8796093022208, 255524028239535/140737488355328⟩, ⟨405191528796815/281474976710656, 108827389460615/70368744177664⟩, ⟨306588971013537/281474976710656, 337931293701235/281474976710656⟩]
def scS149CutCaps : Fin 3 → Fin 3 → ℚ := ![![10108079047/100000000, 1325025243/20000000, 3692597813/100000000], ![2014864891/50000000, 2066620291/50000000, 88937507/5000000], ![981517031/100000000, 435688821/50000000, 572160913/100000000]]
def scS149CutWeightFloor : ℚ := 115651059/100000000
def scS149CutMargins : Fin 3 → ℚ := ![3528101/1000000000, 27820073/10000000000, 7578117/5000000000]

theorem scS149Cut_roots_ok : scS149CutCell.rootsOK scS149CutRoots = true := by decide +kernel

theorem scS149Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS149CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS149Cut_margin_le (i : Fin 3) : curvatureLoss scS149CutCell scS149CutCaps i ≤ scS149CutMargins i := by
  fin_cases i <;> decide +kernel

def scS150CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨13/40, 27/80⟩, ⟨1/20, 3/40⟩⟩
def scS150CutRoots : Fin 3 → RatBounds := ![⟨474777815076577/281474976710656, 507388870228477/281474976710656⟩, ⟨100056270978391/70368744177664, 53709575535923/35184372088832⟩, ⟨301599101210687/281474976710656, 332157635124425/281474976710656⟩]
def scS150CutCaps : Fin 3 → Fin 3 → ℚ := ![![10549151159/100000000, 3471789397/50000000, 965797997/25000000], ![4208098853/100000000, 4304729519/100000000, 74252099/4000000], ![220833683/25000000, 156345883/20000000, 513420737/100000000]]
def scS150CutWeightFloor : ℚ := 120450969/100000000
def scS150CutMargins : Fin 3 → ℚ := ![35723807/10000000000, 14038307/5000000000, 3795497/2500000000]

theorem scS150Cut_roots_ok : scS150CutCell.rootsOK scS150CutRoots = true := by decide +kernel

theorem scS150Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS150CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS150Cut_margin_le (i : Fin 3) : curvatureLoss scS150CutCell scS150CutCaps i ≤ scS150CutMargins i := by
  fin_cases i <;> decide +kernel

def scS151CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨13/40, 27/80⟩, ⟨3/40, 1/10⟩⟩
def scS151CutRoots : Fin 3 → RatBounds := ![⟨471838535671175/281474976710656, 504018966895329/281474976710656⟩, ⟨395655751568413/281474976710656, 212256787572557/140737488355328⟩, ⟨297021669636077/281474976710656, 326881873972467/281474976710656⟩]
def scS151CutCaps : Fin 3 → Fin 3 → ℚ := ![![10988569013/100000000, 72592237/1000000, 504083657/12500000], ![137035541/3125000, 1118807309/25000000, 966622731/50000000], ![798694053/100000000, 140962093/20000000, 231507127/50000000]]
def scS151CutWeightFloor : ℚ := 62630133/50000000
def scS151CutMargins : Fin 3 → ℚ := ![4533321/1250000000, 14212593/5000000000, 15269477/10000000000]

theorem scS151Cut_roots_ok : scS151CutCell.rootsOK scS151CutRoots = true := by decide +kernel

theorem scS151Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS151CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS151Cut_margin_le (i : Fin 3) : curvatureLoss scS151CutCell scS151CutCaps i ≤ scS151CutMargins i := by
  fin_cases i <;> decide +kernel

def scS152CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨27/80, 7/20⟩, ⟨0, 1/40⟩⟩
def scS152CutRoots : Fin 3 → RatBounds := ![⟨239202527735889/140737488355328, 511572643585279/281474976710656⟩, ⟨202443502096287/140737488355328, 13600910719071/8796093022208⟩, ⟨314711068340243/281474976710656, 346618056156317/281474976710656⟩]
def scS152CutCaps : Fin 3 → Fin 3 → ℚ := ![![9175003489/100000000, 1477315609/25000000, 678111539/20000000], ![898870591/25000000, 1826259813/50000000, 208036273/12500000], ![272183909/25000000, 7456823/781250, 649790011/100000000]]
def scS152CutWeightFloor : ℚ := 111807831/100000000
def scS152CutMargins : Fin 3 → ℚ := ![33448103/10000000000, 26132179/10000000000, 2989847/2000000000]

theorem scS152Cut_roots_ok : scS152CutCell.rootsOK scS152CutRoots = true := by decide +kernel

theorem scS152Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS152CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS152Cut_margin_le (i : Fin 3) : curvatureLoss scS152CutCell scS152CutCaps i ≤ scS152CutMargins i := by
  fin_cases i <;> decide +kernel

def scS153CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨27/80, 7/20⟩, ⟨1/40, 1/20⟩⟩
def scS153CutRoots : Fin 3 → RatBounds := ![⟨118750210911595/70368744177664, 31726845801931/17592186044416⟩, ⟨399477599705339/281474976710656, 429068158341283/281474976710656⟩, ⟨154628109823723/140737488355328, 42536368155491/35184372088832⟩]
def scS153CutCaps : Fin 3 → Fin 3 → ℚ := ![![2398684859/25000000, 1552698533/25000000, 889468771/25000000], ![3763549937/100000000, 476468143/12500000, 870369281/50000000], ![974625131/100000000, 851430237/100000000, 289907513/50000000]]
def scS153CutWeightFloor : ℚ := 116616207/100000000
def scS153CutMargins : Fin 3 → ℚ := ![8426167/2500000000, 26227071/10000000000, 743933/500000000]

theorem scS153Cut_roots_ok : scS153CutCell.rootsOK scS153CutRoots = true := by decide +kernel

theorem scS153Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS153CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS153Cut_margin_le (i : Fin 3) : curvatureLoss scS153CutCell scS153CutCaps i ≤ scS153CutMargins i := by
  fin_cases i <;> decide +kernel

def scS154CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨27/80, 7/20⟩, ⟨1/20, 3/40⟩⟩
def scS154CutRoots : Fin 3 → RatBounds := ![⟨471861018331065/281474976710656, 504011730180941/281474976710656⟩, ⟨394520385222617/281474976710656, 423445584394991/281474976710656⟩, ⟨76067886915215/70368744177664, 167266949129375/140737488355328⟩]
def scS154CutCaps : Fin 3 → Fin 3 → ℚ := ![![5006985301/50000000, 813669581/12500000, 116434553/3125000], ![982560789/25000000, 1984924701/50000000, 1816470601/100000000], ![876944443/100000000, 763685809/100000000, 130054369/25000000]]
def scS154CutWeightFloor : ℚ := 60718211/50000000
def scS154CutMargins : Fin 3 → ℚ := ![34085921/10000000000, 5286699/2000000000, 14889153/10000000000]

theorem scS154Cut_roots_ok : scS154CutCell.rootsOK scS154CutRoots = true := by decide +kernel

theorem scS154Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS154CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS154Cut_margin_le (i : Fin 3) : curvatureLoss scS154CutCell scS154CutCaps i ≤ scS154CutMargins i := by
  fin_cases i <;> decide +kernel

def scS155CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨27/80, 7/20⟩, ⟨3/40, 1/10⟩⟩
def scS155CutRoots : Fin 3 → RatBounds := ![⟨29309727166803/17592186044416, 500680176106623/281474976710656⟩, ⟨389960349906247/281474976710656, 26143315922645/17592186044416⟩, ⟨149849299327003/140737488355328, 329272951495599/281474976710656⟩]
def scS155CutCaps : Fin 3 → Fin 3 → ℚ := ![![326012551/3125000, 26583151/390625, 121689237/3125000], ![1023921053/25000000, 103173243/2500000, 236443929/12500000], ![396378723/50000000, 688416993/100000000, 234541439/50000000]]
def scS155CutWeightFloor : ℚ := 126266533/100000000
def scS155CutMargins : Fin 3 → ℚ := ![17284293/5000000000, 26730243/10000000000, 3741181/2500000000]

theorem scS155Cut_roots_ok : scS155CutCell.rootsOK scS155CutRoots = true := by decide +kernel

theorem scS155Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS155CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS155Cut_margin_le (i : Fin 3) : curvatureLoss scS155CutCell scS155CutCaps i ≤ scS155CutMargins i := by
  fin_cases i <;> decide +kernel

def scS156CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨7/20, 29/80⟩, ⟨0, 1/40⟩⟩
def scS156CutRoots : Fin 3 → RatBounds := ![⟨475708291872889/281474976710656, 7944828799701/4398046511104⟩, ⟨199708854083313/140737488355328, 429290378825003/281474976710656⟩, ⟨158709063547583/140737488355328, 174525873243707/140737488355328⟩]
def scS156CutCaps : Fin 3 → Fin 3 → ℚ := ![![175002979/2000000, 2782290889/50000000, 3288017719/100000000], ![33757813/1000000, 3380843041/100000000, 1637065917/100000000], ![270531723/25000000, 186670843/20000000, 164703801/25000000]]
def scS156CutWeightFloor : ℚ := 28192393/25000000
def scS156CutMargins : Fin 3 → ℚ := ![16068787/5000000000, 24763363/10000000000, 7383149/5000000000]

theorem scS156Cut_roots_ok : scS156CutCell.rootsOK scS156CutRoots = true := by decide +kernel

theorem scS156Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS156CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS156Cut_margin_le (i : Fin 3) : curvatureLoss scS156CutCell scS156CutCaps i ≤ scS156CutMargins i := by
  fin_cases i <;> decide +kernel

def scS157CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨7/20, 29/80⟩, ⟨1/40, 1/20⟩⟩
def scS157CutRoots : Fin 3 → RatBounds := ![⟨59042474324975/35184372088832, 3941924194943/2199023255552⟩, ⟨24625984992833/17592186044416, 52892154523599/35184372088832⟩, ⟨155984691872585/140737488355328, 342742492322055/281474976710656⟩]
def scS157CutCaps : Fin 3 → Fin 3 → ℚ := ![![9152073503/100000000, 2924240647/50000000, 691136177/20000000], ![1766835543/50000000, 3528264299/100000000, 1712090479/100000000], ![48425339/5000000, 832432309/100000000, 293894791/50000000]]
def scS157CutWeightFloor : ℚ := 117598041/100000000
def scS157CutMargins : Fin 3 → ℚ := ![6468661/2000000000, 12408667/5000000000, 1468541/1000000000]

theorem scS157Cut_roots_ok : scS157CutCell.rootsOK scS157CutRoots = true := by decide +kernel

theorem scS157Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS157CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS157Cut_margin_le (i : Fin 3) : curvatureLoss scS157CutCell scS157CutCaps i ≤ scS157CutMargins i := by
  fin_cases i <;> decide +kernel

def scS158CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨7/20, 29/80⟩, ⟨1/20, 3/40⟩⟩
def scS158CutRoots : Fin 3 → RatBounds := ![⟨234616491100615/140737488355328, 250492889719475/140737488355328⟩, ⟨194533135966851/140737488355328, 417522919525259/281474976710656⟩, ⟨306989949354719/281474976710656, 337001255315997/281474976710656⟩]
def scS158CutCaps : Fin 3 → Fin 3 → ℚ := ![![9552377267/100000000, 6129585169/100000000, 905483503/25000000], ![3690261789/100000000, 918668397/25000000, 1786439839/100000000], ![871269777/100000000, 74651271/10000000, 1647831/312500]]
def scS158CutWeightFloor : ℚ := 122438959/100000000
def scS158CutMargins : Fin 3 → ℚ := ![1306853/400000000, 12490537/5000000000, 1835351/1250000000]

theorem scS158Cut_roots_ok : scS158CutCell.rootsOK scS158CutRoots = true := by decide +kernel

theorem scS158Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS158CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS158Cut_margin_le (i : Fin 3) : curvatureLoss scS158CutCell scS158CutCaps i ≤ scS158CutMargins i := by
  fin_cases i <;> decide +kernel

def scS159CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨7/20, 29/80⟩, ⟨3/40, 1/10⟩⟩
def scS159CutRoots : Fin 3 → RatBounds := ![⟨233179105928789/140737488355328, 248844388490379/140737488355328⟩, ⟨96128529525317/70368744177664, 103094726003243/70368744177664⟩, ⟨37802688178295/35184372088832, 165877186945079/140737488355328⟩]
def scS159CutCaps : Fin 3 → Fin 3 → ℚ := ![![9951196761/100000000, 640821047/10000000, 3786943483/100000000], ![961416919/25000000, 955032339/25000000, 930080611/50000000], ![787484407/100000000, 672824213/100000000, 237709071/50000000]]
def scS159CutWeightFloor : ℚ := 127290283/100000000
def scS159CutMargins : Fin 3 → ℚ := ![33099223/10000000000, 12616833/5000000000, 7371853/5000000000]

theorem scS159Cut_roots_ok : scS159CutCell.rootsOK scS159CutRoots = true := by decide +kernel

theorem scS159Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS159CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS159Cut_margin_le (i : Fin 3) : curvatureLoss scS159CutCell scS159CutCaps i ≤ scS159CutMargins i := by
  fin_cases i <;> decide +kernel


end HlawkaSchatten.BelowExponent.Vertex
