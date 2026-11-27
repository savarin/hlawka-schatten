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

def scS96CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨39/80, 1/2⟩, ⟨0, 1/40⟩⟩
def scS96CutRoots : Fin 3 → RatBounds := ![⟨117243978222275/70368744177664, 250660998498651/140737488355328⟩, ⟨354715809664779/281474976710656, 95703836204183/70368744177664⟩, ⟨175539112066107/140737488355328, 191407116801109/140737488355328⟩]
def scS96CutCaps : Fin 3 → Fin 3 → ℚ := ![![335568401/5000000, 946762013/25000000, 754284813/25000000], ![2446909817/100000000, 911597529/50000000, 901285217/50000000], ![1073820203/100000000, 756499853/100000000, 96936963/12500000]]
def scS96CutWeightFloor : ℚ := 3118201/2500000
def scS96CutMargins : Fin 3 → ℚ := ![13138241/5000000000, 8433831/5000000000, 1934007/1250000000]

theorem scS96Cut_roots_ok : scS96CutCell.rootsOK scS96CutRoots = true := by decide +kernel

theorem scS96Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS96CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS96Cut_margin_le (i : Fin 3) : curvatureLoss scS96CutCell scS96CutCaps i ≤ scS96CutMargins i := by
  fin_cases i <;> decide +kernel

def scS97CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨39/80, 1/2⟩, ⟨1/40, 1/20⟩⟩
def scS97CutRoots : Fin 3 → RatBounds := ![⟨465826862316939/281474976710656, 62207741758815/35184372088832⟩, ⟨349233219867355/281474976710656, 376539299619911/281474976710656⟩, ⟨43199216014039/35184372088832, 5883393167179/4398046511104⟩]
def scS97CutCaps : Fin 3 → Fin 3 → ℚ := ![![7015165217/100000000, 1985092469/50000000, 635789073/20000000], ![2559076053/100000000, 475472581/25000000, 1880639449/100000000], ![95949513/10000000, 673689007/100000000, 345584273/50000000]]
def scS97CutWeightFloor : ℚ := 202847/156250
def scS97CutMargins : Fin 3 → ℚ := ![13097873/5000000000, 16732093/10000000000, 3820439/2500000000]

theorem scS97Cut_roots_ok : scS97CutCell.rootsOK scS97CutRoots = true := by decide +kernel

theorem scS97Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS97CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS97Cut_margin_le (i : Fin 3) : curvatureLoss scS97CutCell scS97CutCaps i ≤ scS97CutMargins i := by
  fin_cases i <;> decide +kernel

def scS98CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨39/80, 1/2⟩, ⟨1/20, 3/40⟩⟩
def scS98CutRoots : Fin 3 → RatBounds := ![⟨115730318971117/70368744177664, 123575917265597/70368744177664⟩, ⟨86054384143499/70368744177664, 370822014557147/281474976710656⟩, ⟨85144219252899/70368744177664, 92704731864759/70368744177664⟩]
def scS98CutCaps : Fin 3 → Fin 3 → ℚ := ![![7317903729/100000000, 830304031/20000000, 3339345457/100000000], ![267031047/10000000, 1980030523/100000000, 1958155271/100000000], ![861840651/100000000, 603305163/100000000, 123887659/20000000]]
def scS98CutWeightFloor : ℚ := 67468207/50000000
def scS98CutMargins : Fin 3 → ℚ := ![26241361/10000000000, 16689007/10000000000, 15186043/10000000000]

theorem scS98Cut_roots_ok : scS98CutCell.rootsOK scS98CutRoots = true := by decide +kernel

theorem scS98Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS98CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS98Cut_margin_le (i : Fin 3) : curvatureLoss scS98CutCell scS98CutCaps i ≤ scS98CutMargins i := by
  fin_cases i <;> decide +kernel

def scS99CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨39/80, 1/2⟩, ⟨3/40, 1/10⟩⟩
def scS99CutRoots : Fin 3 → RatBounds := ![⟨230115866092813/140737488355328, 491211023963511/281474976710656⟩, ⟨84902792754599/70368744177664, 91397891575405/70368744177664⟩, ⟨335969941696893/281474976710656, 182793798060337/140737488355328⟩]
def scS99CutCaps : Fin 3 → Fin 3 → ℚ := ![![7619679067/100000000, 1082815101/25000000, 3498506079/100000000], ![1390343519/50000000, 514413591/25000000, 2035156539/100000000], ![31113783/4000000, 271517381/50000000, 557967659/100000000]]
def scS99CutWeightFloor : ℚ := 28013549/20000000
def scS99CutMargins : Fin 3 → ℚ := ![13195063/5000000000, 16720809/10000000000, 7583529/5000000000]

theorem scS99Cut_roots_ok : scS99CutCell.rootsOK scS99CutRoots = true := by decide +kernel

theorem scS99Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS99CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS99Cut_margin_le (i : Fin 3) : curvatureLoss scS99CutCell scS99CutCaps i ≤ scS99CutMargins i := by
  fin_cases i <;> decide +kernel

def scS100CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨7/40, 3/16⟩, ⟨0, 1/40⟩⟩
def scS100CutRoots : Fin 3 → RatBounds := ![⟨275514184359105/140737488355328, 9363886224735/4398046511104⟩, ⟨511082155851777/281474976710656, 557016070115723/281474976710656⟩, ⟨281732829587613/281474976710656, 323756969880779/281474976710656⟩]
def scS100CutCaps : Fin 3 → Fin 3 → ℚ := ![![28222851447/100000000, 22370976777/100000000, 1083016461/12500000], ![118007579/800000, 8026198423/50000000, 4008663433/100000000], ![1305473157/100000000, 174219011/12500000, 575000531/100000000]]
def scS100CutWeightFloor : ℚ := 100091607/100000000
def scS100CutMargins : Fin 3 → ℚ := ![9413221/1000000000, 4296717/500000000, 5848749/2000000000]

theorem scS100Cut_roots_ok : scS100CutCell.rootsOK scS100CutRoots = true := by decide +kernel

theorem scS100Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS100CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS100Cut_margin_le (i : Fin 3) : curvatureLoss scS100CutCell scS100CutCaps i ≤ scS100CutMargins i := by
  fin_cases i <;> decide +kernel

def scS101CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨7/40, 3/16⟩, ⟨1/40, 1/20⟩⟩
def scS101CutRoots : Fin 3 → RatBounds := ![⟨34168747324929/17592186044416, 297131620452611/140737488355328⟩, ⟨505339885449343/281474976710656, 550415662302379/281474976710656⟩, ⟨8632316977485/8796093022208, 317093894370525/281474976710656⟩]
def scS101CutCaps : Fin 3 → Fin 3 → ℚ := ![![29577078069/100000000, 23497974911/100000000, 9032357987/100000000], ![308702601/2000000, 1047585929/6250000, 4184215019/100000000], ![1174539121/100000000, 1248875243/100000000, 514609751/100000000]]
def scS101CutWeightFloor : ℚ := 52320511/50000000
def scS101CutMargins : Fin 3 → ℚ := ![24272639/2500000000, 88388381/10000000000, 3729251/1250000000]

theorem scS101Cut_roots_ok : scS101CutCell.rootsOK scS101CutRoots = true := by decide +kernel

theorem scS101Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS101CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS101Cut_margin_le (i : Fin 3) : curvatureLoss scS101CutCell scS101CutCaps i ≤ scS101CutMargins i := by
  fin_cases i <;> decide +kernel

def scS102CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨7/40, 3/16⟩, ⟨1/20, 3/40⟩⟩
def scS102CutRoots : Fin 3 → RatBounds := ![⟨542705499574825/281474976710656, 294822886588471/140737488355328⟩, ⟨500061365785653/281474976710656, 544371635424609/281474976710656⟩, ⟨271212496140393/281474976710656, 311035299377979/281474976710656⟩]
def scS102CutCaps : Fin 3 → Fin 3 → ℚ := ![![30921475927/100000000, 6153400679/25000000, 2349392787/25000000], ![16114000821/100000000, 27289291/156250, 4357961847/100000000], ![106179051/10000000, 562438129/50000000, 231507483/50000000]]
def scS102CutWeightFloor : ℚ := 54597531/50000000
def scS102CutMargins : Fin 3 → ℚ := ![25040351/2500000000, 90973153/10000000000, 1524179/500000000]

theorem scS102Cut_roots_ok : scS102CutCell.rootsOK scS102CutRoots = true := by decide +kernel

theorem scS102Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS102CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS102Cut_margin_le (i : Fin 3) : curvatureLoss scS102CutCell scS102CutCaps i ≤ scS102CutMargins i := by
  fin_cases i <;> decide +kernel

def scS103CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨7/40, 3/16⟩, ⟨3/40, 1/10⟩⟩
def scS103CutRoots : Fin 3 → RatBounds := ![⟨539007301410655/281474976710656, 585387935893493/281474976710656⟩, ⟨247595863035055/140737488355328, 16837980130711/8796093022208⟩, ⟨33326042859999/35184372088832, 152751211072557/140737488355328⟩]
def scS103CutCaps : Fin 3 → Fin 3 → ℚ := ![![3225710593/10000000, 12859583717/50000000, 9760125109/100000000], ![3357623649/20000000, 227053243/1250000, 4530104829/100000000], ![964077587/100000000, 254499119/25000000, 418615269/100000000]]
def scS103CutWeightFloor : ℚ := 56876491/50000000
def scS103CutMargins : Fin 3 → ℚ := ![10332331/1000000000, 23415729/2500000000, 15590519/5000000000]

theorem scS103Cut_roots_ok : scS103CutCell.rootsOK scS103CutRoots = true := by decide +kernel

theorem scS103Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS103CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS103Cut_margin_le (i : Fin 3) : curvatureLoss scS103CutCell scS103CutCaps i ≤ scS103CutMargins i := by
  fin_cases i <;> decide +kernel

def scS104CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨3/16, 1/5⟩, ⟨0, 1/40⟩⟩
def scS104CutRoots : Fin 3 → RatBounds := ![⟨67723849351335/35184372088832, 293868955271501/140737488355328⟩, ⟨499317878552909/281474976710656, 4241516436129/2199023255552⟩, ⟨35538221812741/35184372088832, 162418275387651/140737488355328⟩]
def scS104CutCaps : Fin 3 → Fin 3 → ℚ := ![![24661732003/100000000, 9580615419/50000000, 7663903511/100000000], ![12562773627/100000000, 6838843537/50000000, 440636847/12500000], ![1273309399/100000000, 1340625341/100000000, 288262567/50000000]]
def scS104CutWeightFloor : ℚ := 101005701/100000000
def scS104CutMargins : Fin 3 → ℚ := ![82651843/10000000000, 18653037/2500000000, 5271523/2000000000]

theorem scS104Cut_roots_ok : scS104CutCell.rootsOK scS104CutRoots = true := by decide +kernel

theorem scS104Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS104CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS104Cut_margin_le (i : Fin 3) : curvatureLoss scS104CutCell scS104CutCaps i ≤ scS104CutMargins i := by
  fin_cases i <;> decide +kernel

def scS105CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨3/16, 1/5⟩, ⟨1/40, 1/20⟩⟩
def scS105CutRoots : Fin 3 → RatBounds := ![⟨67197006702537/35184372088832, 291424984388381/140737488355328⟩, ⟨123406632177903/70368744177664, 134096140822885/70368744177664⟩, ⟨278804913634527/281474976710656, 318209624267063/281474976710656⟩]
def scS105CutCaps : Fin 3 → Fin 3 → ℚ := ![![5167454009/20000000, 20125668017/100000000, 7993954239/100000000], ![657248303/5000000, 14280234119/100000000, 3680806757/100000000], ![228986791/20000000, 48025649/4000000, 128951489/25000000]]
def scS105CutWeightFloor : ℚ := 105578477/100000000
def scS105CutMargins : Fin 3 → ℚ := ![85081977/10000000000, 38289519/5000000000, 13416001/5000000000]

theorem scS105Cut_roots_ok : scS105CutCell.rootsOK scS105CutRoots = true := by decide +kernel

theorem scS105Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS105CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS105Cut_margin_le (i : Fin 3) : curvatureLoss scS105CutCell scS105CutCaps i ≤ scS105CutMargins i := by
  fin_cases i <;> decide +kernel

def scS106CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨3/16, 1/5⟩, ⟨1/20, 3/40⟩⟩
def scS106CutRoots : Fin 3 → RatBounds := ![⟨266843367822297/140737488355328, 144589877904635/70368744177664⟩, ⟨122099089678577/70368744177664, 66300922375831/35184372088832⟩, ⟨68445281436637/70368744177664, 78045922670983/70368744177664⟩]
def scS106CutCaps : Fin 3 → Fin 3 → ℚ := ![![843892661/3125000, 10540197303/50000000, 130019699/1562500], ![6861328287/50000000, 2975678029/20000000, 1917455587/50000000], ![1034464793/100000000, 540450877/50000000, 115986979/25000000]]
def scS106CutWeightFloor : ℚ := 13769541/12500000
def scS106CutMargins : Fin 3 → ℚ := ![10953389/1250000000, 78676547/10000000000, 27367117/10000000000]

theorem scS106Cut_roots_ok : scS106CutCell.rootsOK scS106CutRoots = true := by decide +kernel

theorem scS106Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS106CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS106Cut_margin_le (i : Fin 3) : curvatureLoss scS106CutCell scS106CutCaps i ≤ scS106CutMargins i := by
  fin_cases i <;> decide +kernel

def scS107CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨3/16, 1/5⟩, ⟨3/40, 1/10⟩⟩
def scS107CutRoots : Fin 3 → RatBounds := ![⟨265043047338329/140737488355328, 287109674494851/140737488355328⟩, ⟨483572647254489/281474976710656, 524914217964367/281474976710656⟩, ⟨269174872739927/281474976710656, 76670114395487/70368744177664⟩]
def scS107CutCaps : Fin 3 → Fin 3 → ℚ := ![![28164498161/100000000, 22026520877/100000000, 8646144551/100000000], ![1787038147/12500000, 7736304537/50000000, 3987583667/100000000], ![938788949/100000000, 15277367/1562500, 104833983/25000000]]
def scS107CutWeightFloor : ℚ := 114738429/100000000
def scS107CutMargins : Fin 3 → ℚ := ![45132773/5000000000, 20219793/2500000000, 27951313/10000000000]

theorem scS107Cut_roots_ok : scS107CutCell.rootsOK scS107CutRoots = true := by decide +kernel

theorem scS107Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS107CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS107Cut_margin_le (i : Fin 3) : curvatureLoss scS107CutCell scS107CutCaps i ≤ scS107CutMargins i := by
  fin_cases i <;> decide +kernel

def scS108CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨1/5, 17/80⟩, ⟨0, 1/40⟩⟩
def scS108CutRoots : Fin 3 → RatBounds := ![⟨533419738004901/281474976710656, 144342688939425/70368744177664⟩, ⟨488428358358153/281474976710656, 530002826563655/281474976710656⟩, ⟨286836069283375/281474976710656, 326060637119529/281474976710656⟩]
def scS108CutCaps : Fin 3 → Fin 3 → ℚ := ![![21800940509/100000000, 4153084573/25000000, 6855837367/100000000], ![10823227551/100000000, 11784521329/100000000, 784389603/25000000], ![1245437197/100000000, 646383903/50000000, 289559677/50000000]]
def scS108CutWeightFloor : ℚ := 50952321/50000000
def scS108CutMargins : Fin 3 → ℚ := ![73449057/10000000000, 13112473/2000000000, 12021361/5000000000]

theorem scS108Cut_roots_ok : scS108CutCell.rootsOK scS108CutRoots = true := by decide +kernel

theorem scS108Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS108CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS108Cut_margin_le (i : Fin 3) : curvatureLoss scS108CutCell scS108CutCaps i ≤ scS108CutMargins i := by
  fin_cases i <;> decide +kernel

def scS109CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨1/5, 17/80⟩, ⟨1/40, 1/20⟩⟩
def scS109CutRoots : Fin 3 → RatBounds := ![⟨264654449757425/140737488355328, 143151835102147/70368744177664⟩, ⟨60347698475331/35184372088832, 523534609274677/281474976710656⟩, ⟨281334669437077/281474976710656, 79866817175425/70368744177664⟩]
def scS109CutCaps : Fin 3 → Fin 3 → ℚ := ![![11417134799/50000000, 17450181777/100000000, 3577596993/50000000], ![11324632331/100000000, 6151297083/50000000, 1638627039/50000000], ![139908271/12500000, 231444081/20000000, 258984133/50000000]]
def scS109CutWeightFloor : ℚ := 106499399/100000000
def scS109CutMargins : Fin 3 → ℚ := ![75460873/10000000000, 2686067/400000000, 24422503/10000000000]

theorem scS109Cut_roots_ok : scS109CutCell.rootsOK scS109CutRoots = true := by decide +kernel

theorem scS109Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS109CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS109Cut_margin_le (i : Fin 3) : curvatureLoss scS109CutCell scS109CutCaps i ≤ scS109CutMargins i := by
  fin_cases i <;> decide +kernel

def scS110CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨1/5, 17/80⟩, ⟨1/20, 3/40⟩⟩
def scS110CutRoots : Fin 3 → RatBounds := ![⟨262757841002735/140737488355328, 284115942454557/140737488355328⟩, ⟨238796928448401/140737488355328, 129403854016305/70368744177664⟩, ⟨69077555485017/70368744177664, 313471626312337/281474976710656⟩]
def scS110CutCaps : Fin 3 → Fin 3 → ℚ := ![![23860692019/100000000, 3655918003/20000000, 1490406357/20000000], ![11822168139/100000000, 12816902399/100000000, 3415497241/100000000], ![1010763369/100000000, 1041340139/100000000, 232878883/50000000]]
def scS110CutWeightFloor : ℚ := 11109971/10000000
def scS110CutMargins : Fin 3 → ℚ := ![19397419/2500000000, 68870807/10000000000, 3108047/1250000000]

theorem scS110Cut_roots_ok : scS110CutCell.rootsOK scS110CutRoots = true := by decide +kernel

theorem scS110Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS110CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS110Cut_margin_le (i : Fin 3) : curvatureLoss scS110CutCell scS110CutCaps i ≤ scS110CutMargins i := by
  fin_cases i <;> decide +kernel

def scS111CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨1/5, 17/80⟩, ⟨3/40, 1/10⟩⟩
def scS111CutRoots : Fin 3 → RatBounds := ![⟨522004206891727/281474976710656, 564198274592601/281474976710656⟩, ⟨472810551536215/281474976710656, 128044283305487/70368744177664⟩, ⟨271703216163347/281474976710656, 307995860286111/281474976710656⟩]
def scS111CutCaps : Fin 3 → Fin 3 → ℚ := ![![12440513543/50000000, 19101543983/100000000, 3873354753/50000000], ![12316225177/100000000, 416494777/3125000, 3552445833/100000000], ![14325729/1562500, 941566203/100000000, 420856081/100000000]]
def scS111CutWeightFloor : ℚ := 115704669/100000000
def scS111CutMargins : Fin 3 → ℚ := ![19953437/2500000000, 70694613/10000000000, 25356601/10000000000]

theorem scS111Cut_roots_ok : scS111CutCell.rootsOK scS111CutRoots = true := by decide +kernel

theorem scS111Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS111CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS111Cut_margin_le (i : Fin 3) : curvatureLoss scS111CutCell scS111CutCaps i ≤ scS111CutMargins i := by
  fin_cases i <;> decide +kernel

def scS112CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨17/80, 9/40⟩, ⟨0, 1/40⟩⟩
def scS112CutRoots : Fin 3 → RatBounds := ![⟨131453466094723/70368744177664, 284016004857027/140737488355328⟩, ⟨239153270560159/140737488355328, 259060435984949/140737488355328⟩, ⟨144668898295743/140737488355328, 40926837308943/35184372088832⟩]
def scS112CutCaps : Fin 3 → Fin 3 → ℚ := ![![19468888363/100000000, 14564476721/100000000, 6207258029/100000000], ![4709911821/50000000, 10252591833/100000000, 2822325921/100000000], ![305278149/25000000, 249861513/20000000, 582624191/100000000]]
def scS112CutWeightFloor : ℚ := 51396717/50000000
def scS112CutMargins : Fin 3 → ℚ := ![8245401/1250000000, 58231053/10000000000, 11093829/5000000000]

theorem scS112Cut_roots_ok : scS112CutCell.rootsOK scS112CutRoots = true := by decide +kernel

theorem scS112Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS112CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS112Cut_margin_le (i : Fin 3) : curvatureLoss scS112CutCell scS112CutCaps i ≤ scS112CutMargins i := by
  fin_cases i <;> decide +kernel

def scS113CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨17/80, 9/40⟩, ⟨1/40, 1/20⟩⟩
def scS113CutRoots : Fin 3 → RatBounds := ![⟨260899101998855/140737488355328, 140845427255799/70368744177664⟩, ⟨472698840034961/281474976710656, 3997701557955/2199023255552⟩, ⟨17739825348077/17592186044416, 320852673129987/281474976710656⟩]
def scS113CutCaps : Fin 3 → Fin 3 → ℚ := ![![20386921389/100000000, 61200053/400000, 6481125917/100000000], ![1232030809/12500000, 5351277397/50000000, 117955883/4000000], ![548427123/50000000, 558907989/50000000, 520952983/100000000]]
def scS113CutWeightFloor : ℚ := 859273/800000
def scS113CutMargins : Fin 3 → ℚ := ![33818931/5000000000, 14879801/2500000000, 22487959/10000000000]

theorem scS113Cut_roots_ok : scS113CutCell.rootsOK scS113CutRoots = true := by decide +kernel

theorem scS113Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS113CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS113Cut_margin_le (i : Fin 3) : curvatureLoss scS113CutCell scS113CutCaps i ≤ scS113CutMargins i := by
  fin_cases i <;> decide +kernel

def scS114CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨17/80, 9/40⟩, ⟨1/20, 3/40⟩⟩
def scS114CutRoots : Fin 3 → RatBounds := ![⟨259046506557773/140737488355328, 279555360007927/140737488355328⟩, ⟨467548409906245/281474976710656, 505837008549473/281474976710656⟩, ⟨139406658299723/140737488355328, 314885293144985/281474976710656⟩]
def scS114CutCaps : Fin 3 → Fin 3 → ℚ := ![![2129916949/10000000, 16028227729/100000000, 6752842631/100000000], ![10289300603/100000000, 1393657027/12500000, 24593169/800000], ![39602389/4000000, 502730263/50000000, 468314023/100000000]]
def scS114CutWeightFloor : ℚ := 56015437/50000000
def scS114CutMargins : Fin 3 → ℚ := ![69431073/10000000000, 7617023/1250000000, 22852041/10000000000]

theorem scS114Cut_roots_ok : scS114CutCell.rootsOK scS114CutRoots = true := by decide +kernel

theorem scS114Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS114CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS114Cut_margin_le (i : Fin 3) : curvatureLoss scS114CutCell scS114CutCaps i ≤ scS114CutMargins i := by
  fin_cases i <;> decide +kernel

def scS115CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨17/80, 9/40⟩, ⟨3/40, 1/10⟩⟩
def scS115CutRoots : Fin 3 → RatBounds := ![⟨514663208754559/281474976710656, 555173903818239/281474976710656⟩, ⟨462800707712911/281474976710656, 500446543255143/281474976710656⟩, ⟨274206663733253/281474976710656, 77358782156891/70368744177664⟩]
def scS115CutCaps : Fin 3 → Fin 3 → ℚ := ![![22206211351/100000000, 334999111/2000000, 3511327867/50000000], ![2143864271/20000000, 11593027271/100000000, 159910753/5000000], ![89767287/10000000, 908767893/100000000, 211528347/50000000]]
def scS115CutWeightFloor : ℚ := 29164423/25000000
def scS115CutMargins : Fin 3 → ℚ := ![71320751/10000000000, 31228569/5000000000, 23267769/10000000000]

theorem scS115Cut_roots_ok : scS115CutCell.rootsOK scS115CutRoots = true := by decide +kernel

theorem scS115Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS115CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS115Cut_margin_le (i : Fin 3) : curvatureLoss scS115CutCell scS115CutCaps i ≤ scS115CutMargins i := by
  fin_cases i <;> decide +kernel

def scS116CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨9/40, 19/80⟩, ⟨0, 1/40⟩⟩
def scS116CutRoots : Fin 3 → RatBounds := ![⟨259444452553921/140737488355328, 69949401914533/35184372088832⟩, ⟨468862984766393/281474976710656, 507136277751569/281474976710656⟩, ⟨72955656006527/70368744177664, 328887634529447/281474976710656⟩]
def scS116CutCaps : Fin 3 → Fin 3 → ℚ := ![![8771858141/50000000, 12896682117/100000000, 567876187/10000000], ![8273049243/100000000, 8996727467/100000000, 2562652821/100000000], ![239951707/20000000, 604779359/50000000, 586915569/100000000]]
def scS116CutWeightFloor : ℚ := 51838111/50000000
def scS116CutMargins : Fin 3 → ℚ := ![14949121/2500000000, 13052561/2500000000, 20681791/10000000000]

theorem scS116Cut_roots_ok : scS116CutCell.rootsOK scS116CutRoots = true := by decide +kernel

theorem scS116Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS116CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS116Cut_margin_le (i : Fin 3) : curvatureLoss scS116CutCell scS116CutCaps i ≤ scS116CutMargins i := by
  fin_cases i <;> decide +kernel

def scS117CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨9/40, 19/80⟩, ⟨1/40, 1/20⟩⟩
def scS117CutRoots : Fin 3 → RatBounds := ![⟨514960568655067/281474976710656, 555047922976245/281474976710656⟩, ⟨231644767332701/140737488355328, 500767281977515/281474976710656⟩, ⟨143161978191063/140737488355328, 322355033151747/281474976710656⟩]
def scS117CutCaps : Fin 3 → Fin 3 → ℚ := ![![4591771579/25000000, 13548952073/100000000, 5932152909/100000000], ![69252037/800000, 9391030591/100000000, 2678339059/100000000], ![21543391/2000000, 135225161/12500000, 524648011/100000000]]
def scS117CutWeightFloor : ℚ := 54156033/50000000
def scS117CutMargins : Fin 3 → ℚ := ![61195839/10000000000, 53256227/10000000000, 1045809/500000000]

theorem scS117Cut_roots_ok : scS117CutCell.rootsOK scS117CutRoots = true := by decide +kernel

theorem scS117Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS117CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS117Cut_margin_le (i : Fin 3) : curvatureLoss scS117CutCell scS117CutCaps i ≤ scS117CutMargins i := by
  fin_cases i <;> decide +kernel

def scS118CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨9/40, 19/80⟩, ⟨1/20, 3/40⟩⟩
def scS118CutRoots : Fin 3 → RatBounds := ![⟨15979254256689/8796093022208, 550872069708637/281474976710656⟩, ⟨458171909227739/281474976710656, 494942331919361/281474976710656⟩, ⟨8790675964113/8796093022208, 158207077733027/140737488355328⟩]
def scS118CutCaps : Fin 3 → Fin 3 → ℚ := ![![3837098213/20000000, 1419473771/10000000, 1236710873/20000000], ![9036992893/100000000, 4891240419/50000000, 698203271/25000000], ![7774943/800000, 194537649/20000000, 471514923/100000000]]
def scS118CutWeightFloor : ℚ := 112954493/100000000
def scS118CutMargins : Fin 3 → ℚ := ![62714757/10000000000, 850463/156250000, 21215679/10000000000]

theorem scS118Cut_roots_ok : scS118CutCell.rootsOK scS118CutRoots = true := by decide +kernel

theorem scS118Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS118CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS118Cut_margin_le (i : Fin 3) : curvatureLoss scS118CutCell scS118CutCaps i ≤ scS118CutMargins i := by
  fin_cases i <;> decide +kernel

def scS119CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨9/40, 19/80⟩, ⟨3/40, 1/10⟩⟩
def scS119CutRoots : Fin 3 → RatBounds := ![⟨253990627777255/140737488355328, 547023404390163/281474976710656⟩, ⟨113363901373019/70368744177664, 122398394133713/70368744177664⟩, ⟨276696240905405/281474976710656, 77746992986601/70368744177664⟩]
def scS119CutCaps : Fin 3 → Fin 3 → ℚ := ![![19999435133/100000000, 14834778863/100000000, 3216601557/50000000], ![73553169/781250, 10171364333/100000000, 2906203421/100000000], ![440409679/50000000, 439413867/50000000, 425844983/100000000]]
def scS119CutWeightFloor : ℚ := 117602427/100000000
def scS119CutMargins : Fin 3 → ℚ := ![64331091/10000000000, 27852983/5000000000, 21567943/10000000000]

theorem scS119Cut_roots_ok : scS119CutCell.rootsOK scS119CutRoots = true := by decide +kernel

theorem scS119Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS119CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS119Cut_margin_le (i : Fin 3) : curvatureLoss scS119CutCell scS119CutCaps i ≤ scS119CutMargins i := by
  fin_cases i <;> decide +kernel

def scS120CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨19/80, 1/4⟩, ⟨0, 1/40⟩⟩
def scS120CutRoots : Fin 3 → RatBounds := ![⟨128143549123243/70368744177664, 275978136790747/140737488355328⟩, ⟨460022277377335/281474976710656, 496939910211301/281474976710656⟩, ⟨147150197707235/140737488355328, 20654435600179/17592186044416⟩]
def scS120CutCaps : Fin 3 → Fin 3 → ℚ := ![![7968433531/50000000, 230378563/2000000, 5236937163/100000000], ![916230887/12500000, 7955320037/100000000, 2353899973/100000000], ![1180920611/100000000, 146621751/12500000, 591895647/100000000]]
def scS120CutWeightFloor : ℚ := 13069563/12500000
def scS120CutMargins : Fin 3 → ℚ := ![6833593/1250000000, 47199501/10000000000, 19450039/10000000000]

theorem scS120Cut_roots_ok : scS120CutCell.rootsOK scS120CutRoots = true := by decide +kernel

theorem scS120Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS120CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS120Cut_margin_le (i : Fin 3) : curvatureLoss scS120CutCell scS120CutCaps i ≤ scS120CutMargins i := by
  fin_cases i <;> decide +kernel

def scS121CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨19/80, 1/4⟩, ⟨1/40, 1/20⟩⟩
def scS121CutRoots : Fin 3 → RatBounds := ![⟨508726062160537/281474976710656, 547502961311283/281474976710656⟩, ⟨454478839890597/281474976710656, 245305418263837/140737488355328⟩, ⟨288804574011505/281474976710656, 80991527062959/70368744177664⟩]
def scS121CutCaps : Fin 3 → Fin 3 → ℚ := ![![16681587377/100000000, 12102342391/100000000, 109464527/2000000], ![3835272571/50000000, 8303595991/100000000, 615509267/25000000], ![1059795797/100000000, 209735291/20000000, 264482497/50000000]]
def scS121CutWeightFloor : ℚ := 109211933/100000000
def scS121CutMargins : Fin 3 → ℚ := ![27921207/5000000000, 24024067/5000000000, 19631101/10000000000]

theorem scS121Cut_roots_ok : scS121CutCell.rootsOK scS121CutRoots = true := by decide +kernel

theorem scS121Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS121CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS121Cut_margin_le (i : Fin 3) : curvatureLoss scS121CutCell scS121CutCaps i ≤ scS121CutMargins i := by
  fin_cases i <;> decide +kernel

def scS122CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨19/80, 1/4⟩, ⟨1/20, 3/40⟩⟩
def scS122CutRoots : Fin 3 → RatBounds := ![⟨505175797924905/281474976710656, 135853476930583/70368744177664⟩, ⟨56173757759021/35184372088832, 484824010669657/281474976710656⟩, ⟨283784641542335/281474976710656, 318050186219993/281474976710656⟩]
def scS122CutCaps : Fin 3 → Fin 3 → ℚ := ![![8711012023/50000000, 253599261/2000000, 2853835217/50000000], ![500535389/6250000, 216233891/2500000, 128449639/5000000], ![955805117/100000000, 942564969/100000000, 475280287/100000000]]
def scS122CutWeightFloor : ℚ := 11387449/10000000
def scS122CutMargins : Fin 3 → ℚ := ![1142727/200000000, 9804523/2000000000, 9939243/5000000000]

theorem scS122Cut_roots_ok : scS122CutCell.rootsOK scS122CutRoots = true := by decide +kernel

theorem scS122Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS122CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS122Cut_margin_le (i : Fin 3) : curvatureLoss scS122CutCell scS122CutCaps i ≤ scS122CutMargins i := by
  fin_cases i <;> decide +kernel

def scS123CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨19/80, 1/4⟩, ⟨3/40, 1/10⟩⟩
def scS123CutRoots : Fin 3 → RatBounds := ![⟨125472430862827/70368744177664, 539645670940183/281474976710656⟩, ⟨444701454249279/281474976710656, 239755820800355/140737488355328⟩, ⟨279181263619299/281474976710656, 312646557804313/281474976710656⟩]
def scS123CutCaps : Fin 3 → Fin 3 → ℚ := ![![3631720953/20000000, 6626225093/50000000, 5940488787/100000000], ![2086042903/25000000, 8992848137/100000000, 534978549/20000000], ![173186629/20000000, 851324039/100000000, 21457393/5000000]]
def scS123CutWeightFloor : ℚ := 118543007/100000000
def scS123CutMargins : Fin 3 → ℚ := ![29264169/5000000000, 25049409/5000000000, 4035927/2000000000]

theorem scS123Cut_roots_ok : scS123CutCell.rootsOK scS123CutRoots = true := by decide +kernel

theorem scS123Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS123CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS123Cut_margin_le (i : Fin 3) : curvatureLoss scS123CutCell scS123CutCaps i ≤ scS123CutMargins i := by
  fin_cases i <;> decide +kernel

def scS124CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨1/4, 21/80⟩, ⟨0, 1/40⟩⟩
def scS124CutRoots : Fin 3 → RatBounds := ![⟨126702512151107/70368744177664, 272514349830569/140737488355328⟩, ⟨451720309527333/281474976710656, 487440606894139/281474976710656⟩, ⟨4637180698037/4398046511104, 332158274668975/281474976710656⟩]
def scS124CutCaps : Fin 3 → Fin 3 → ℚ := ![![14582727801/100000000, 10369239311/100000000, 2432117161/50000000], ![6554641869/100000000, 7082926511/100000000, 549654329/25000000], ![29105907/2500000, 1139111289/100000000, 298743317/50000000]]
def scS124CutWeightFloor : ℚ := 105437281/100000000
def scS124CutMargins : Fin 3 → ℚ := ![25189761/5000000000, 42985569/10000000000, 18462497/10000000000]

theorem scS124Cut_roots_ok : scS124CutCell.rootsOK scS124CutRoots = true := by decide +kernel

theorem scS124Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS124CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS124Cut_margin_le (i : Fin 3) : curvatureLoss scS124CutCell scS124CutCaps i ≤ scS124CutMargins i := by
  fin_cases i <;> decide +kernel

def scS125CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨1/4, 21/80⟩, ⟨1/40, 1/20⟩⟩
def scS125CutRoots : Fin 3 → RatBounds := ![⟨251517807637735/140737488355328, 540661237576283/281474976710656⟩, ⟨446203137147533/281474976710656, 240573029560539/140737488355328⟩, ⟨291287352750553/281474976710656, 81419914431899/70368744177664⟩]
def scS125CutCaps : Fin 3 → Fin 3 → ℚ := ![![7630737069/50000000, 10895123597/100000000, 158942007/3125000], ![3429729647/50000000, 1478548047/20000000, 574975809/25000000], ![522200423/50000000, 127254709/12500000, 266916861/50000000]]
def scS125CutWeightFloor : ℚ := 27527977/25000000
def scS125CutMargins : Fin 3 → ℚ := ![5136433/1000000000, 1364747/312500000, 371929/200000000]

theorem scS125Cut_roots_ok : scS125CutCell.rootsOK scS125CutRoots = true := by decide +kernel

theorem scS125Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS125CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS125Cut_margin_le (i : Fin 3) : curvatureLoss scS125CutCell scS125CutCaps i ≤ scS125CutMargins i := by
  fin_cases i <;> decide +kernel

def scS126CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨1/4, 21/80⟩, ⟨1/20, 3/40⟩⟩
def scS126CutRoots : Fin 3 → RatBounds := ![⟨249776751816785/140737488355328, 134162869159097/70368744177664⟩, ⟨55142463255889/35184372088832, 475392342747937/281474976710656⟩, ⟨143135248471243/140737488355328, 79946828887175/70368744177664⟩]
def scS126CutCaps : Fin 3 → Fin 3 → ℚ := ![![7968434981/50000000, 2854038493/25000000, 5306662231/100000000], ![7161873363/100000000, 962539771/12500000, 2400095591/100000000], ![9415661/1000000, 914720517/100000000, 119886607/25000000]]
def scS126CutWeightFloor : ℚ := 114794221/100000000
def scS126CutMargins : Fin 3 → ℚ := ![52470719/10000000000, 22241557/5000000000, 9399359/5000000000]

theorem scS126Cut_roots_ok : scS126CutCell.rootsOK scS126CutRoots = true := by decide +kernel

theorem scS126Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS126CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS126Cut_margin_le (i : Fin 3) : curvatureLoss scS126CutCell scS126CutCaps i ≤ scS126CutMargins i := by
  fin_cases i <;> decide +kernel

def scS127CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨1/4, 21/80⟩, ⟨3/40, 1/10⟩⟩
def scS127CutRoots : Fin 3 → RatBounds := ![⟨496330651467921/281474976710656, 532956713648897/281474976710656⟩, ⟨27279719790475/17592186044416, 470111687855599/281474976710656⟩, ⟨140834873029473/140737488355328, 157202486017191/140737488355328⟩]
def scS127CutCaps : Fin 3 → Fin 3 → ℚ := ![![16609149839/100000000, 5966395487/50000000, 2762925001/50000000], ![3731057847/50000000, 8005878751/100000000, 624827221/25000000], ![170546519/20000000, 825916273/100000000, 13528353/3125000]]
def scS127CutWeightFloor : ℚ := 119482959/100000000
def scS127CutMargins : Fin 3 → ℚ := ![13419041/2500000000, 22697593/5000000000, 19056227/10000000000]

theorem scS127Cut_roots_ok : scS127CutCell.rootsOK scS127CutRoots = true := by decide +kernel

theorem scS127Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS127CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS127Cut_margin_le (i : Fin 3) : curvatureLoss scS127CutCell scS127CutCaps i ≤ scS127CutMargins i := by
  fin_cases i <;> decide +kernel


end HlawkaSchatten.BelowExponent.Vertex
