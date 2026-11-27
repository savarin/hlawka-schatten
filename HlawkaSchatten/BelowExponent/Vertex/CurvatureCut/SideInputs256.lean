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

def scD52CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨3/16, 1/5⟩, ⟨1/10, 9/80⟩⟩
def scD52CutRoots : Fin 3 → RatBounds := ![⟨264343847387297/140737488355328, 285032962778125/140737488355328⟩, ⟨481321195330253/281474976710656, 519802233219115/281474976710656⟩, ⟨133512288577359/140737488355328, 301610852500289/281474976710656⟩]
def scD52CutCaps : Fin 3 → Fin 3 → ℚ := ![![5636700409/20000000, 11019458229/50000000, 8538909823/100000000], ![14365981607/100000000, 7722855583/50000000, 3887291739/100000000], ![661224161/100000000, 692675501/100000000, 152258891/50000000]]
def scD52CutWeightFloor : ℚ := 6013509/5000000
def scD52CutMargins : Fin 3 → ℚ := ![42197957/5000000000, 37282523/5000000000, 24864687/10000000000]

theorem scD52Cut_roots_ok : scD52CutCell.rootsOK scD52CutRoots = true := by decide +kernel

theorem scD52Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD52CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD52Cut_margin_le (i : Fin 3) : curvatureLoss scD52CutCell scD52CutCaps i ≤ scD52CutMargins i := by
  fin_cases i <;> decide +kernel

def scD53CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨3/16, 1/5⟩, ⟨9/80, 1/8⟩⟩
def scD53CutRoots : Fin 3 → RatBounds := ![⟨527035302750875/281474976710656, 284133920021349/140737488355328⟩, ⟨479130995194127/281474976710656, 517415077034889/281474976710656⟩, ⟨66236963315649/70368744177664, 299242929729329/281474976710656⟩]
def scD53CutCaps : Fin 3 → Fin 3 → ℚ := ![![28752840403/100000000, 11251137477/50000000, 543621387/6250000], ![2929472703/20000000, 3934090739/25000000, 495073167/12500000], ![317211743/50000000, 663483221/100000000, 291518439/100000000]]
def scD53CutWeightFloor : ℚ := 24510469/20000000
def scD53CutMargins : Fin 3 → ℚ := ![21501283/2500000000, 37990353/5000000000, 25293059/10000000000]

theorem scD53Cut_roots_ok : scD53CutCell.rootsOK scD53CutRoots = true := by decide +kernel

theorem scD53Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD53CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD53Cut_margin_le (i : Fin 3) : curvatureLoss scD53CutCell scD53CutCaps i ≤ scD53CutMargins i := by
  fin_cases i <;> decide +kernel

def scD54CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨1/5, 17/80⟩, ⟨1/10, 9/80⟩⟩
def scD54CutRoots : Fin 3 → RatBounds := ![⟨260329000968369/140737488355328, 560135163316923/281474976710656⟩, ⟨58822256966359/35184372088832, 507118243896739/281474976710656⟩, ⟨269552680106959/281474976710656, 302951002576985/281474976710656⟩]
def scD54CutCaps : Fin 3 → Fin 3 → ℚ := ![![24880272609/100000000, 4775327917/25000000, 3820283903/50000000], ![12368594191/100000000, 531641349/4000000, 863794989/25000000], ![643045241/100000000, 663665243/100000000, 151949651/50000000]]
def scD54CutWeightFloor : ℚ := 2425253/2000000
def scD54CutMargins : Fin 3 → ℚ := ![74007641/10000000000, 64562521/10000000000, 2783117/1250000000]

theorem scD54Cut_roots_ok : scD54CutCell.rootsOK scD54CutRoots = true := by decide +kernel

theorem scD54Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD54CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD54Cut_margin_le (i : Fin 3) : curvatureLoss scD54CutCell scD54CutCaps i ≤ scD54CutMargins i := by
  fin_cases i <;> decide +kernel

def scD55CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨1/5, 17/80⟩, ⟨9/80, 1/8⟩⟩
def scD55CutRoots : Fin 3 → RatBounds := ![⟨259522992571445/140737488355328, 8724755148543/4398046511104⟩, ⟨234203440477613/140737488355328, 504756012884705/281474976710656⟩, ⟨267475530796343/281474976710656, 18787173121737/17592186044416⟩]
def scD55CutCaps : Fin 3 → Fin 3 → ℚ := ![![634521283/2500000, 9751785087/50000000, 1556919081/20000000], ![12610685457/100000000, 1692574249/12500000, 3520746229/100000000], ![123241393/20000000, 635136573/100000000, 145374533/50000000]]
def scD55CutWeightFloor : ℚ := 61778391/50000000
def scD55CutMargins : Fin 3 → ℚ := ![301623/40000000, 13155977/2000000000, 4529723/2000000000]

theorem scD55Cut_roots_ok : scD55CutCell.rootsOK scD55CutRoots = true := by decide +kernel

theorem scD55Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD55CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD55Cut_margin_le (i : Fin 3) : curvatureLoss scD55CutCell scD55CutCaps i ≤ scD55CutMargins i := by
  fin_cases i <;> decide +kernel

def scD56CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨17/80, 9/40⟩, ⟨1/10, 9/80⟩⟩
def scD56CutRoots : Fin 3 → RatBounds := ![⟨64170627537601/35184372088832, 34449534769243/17592186044416⟩, ⟨230292458916051/140737488355328, 247717037888283/140737488355328⟩, ⟨136028198412183/140737488355328, 76103325314429/70368744177664⟩]
def scD56CutCaps : Fin 3 → Fin 3 → ℚ := ![![22190597561/100000000, 1046219513/6250000, 3457910239/50000000], ![5379072981/50000000, 2309807959/20000000, 193983531/6250000], ![156895197/25000000, 1993253/312500, 18999071/6250000]]
def scD56CutWeightFloor : ℚ := 24448141/20000000
def scD56CutMargins : Fin 3 → ℚ := ![65578759/10000000000, 28248431/5000000000, 20163169/10000000000]

theorem scD56Cut_roots_ok : scD56CutCell.rootsOK scD56CutRoots = true := by decide +kernel

theorem scD56Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD56CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD56Cut_margin_le (i : Fin 3) : curvatureLoss scD56CutCell scD56CutCaps i ≤ scD56CutMargins i := by
  fin_cases i <;> decide +kernel

def scD57CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨17/80, 9/40⟩, ⟨9/80, 1/8⟩⟩
def scD57CutRoots : Fin 3 → RatBounds := ![⟨63973746718851/35184372088832, 549484659679263/281474976710656⟩, ⟨114607638429587/70368744177664, 246546821569839/140737488355328⟩, ⟨67494828666749/70368744177664, 302067946494299/281474976710656⟩]
def scD57CutCaps : Fin 3 → Fin 3 → ℚ := ![![22635397837/100000000, 3418500281/20000000, 1761887931/25000000], ![10968631111/100000000, 2941370311/25000000, 1581488133/50000000], ![601262043/100000000, 610325733/100000000, 2271907/781250]]
def scD57CutWeightFloor : ℚ := 4981853/4000000
def scD57CutMargins : Fin 3 → ℚ := ![66807209/10000000000, 5755529/1000000000, 4102083/2000000000]

theorem scD57Cut_roots_ok : scD57CutCell.rootsOK scD57CutRoots = true := by decide +kernel

theorem scD57Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD57CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD57Cut_margin_le (i : Fin 3) : curvatureLoss scD57CutCell scD57CutCaps i ≤ scD57CutMargins i := by
  fin_cases i <;> decide +kernel

def scD58CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨9/40, 19/80⟩, ⟨1/10, 9/80⟩⟩
def scD58CutRoots : Fin 3 → RatBounds := ![⟨253363647535827/140737488355328, 543116280314603/281474976710656⟩, ⟨451254551188825/281474976710656, 121155438808987/70368744177664⟩, ⟨137273331026403/140737488355328, 76496920223463/70368744177664⟩]
def scD58CutCaps : Fin 3 → Fin 3 → ℚ := ![![3994508917/20000000, 7409129763/50000000, 197767101/3125000], ![9442890807/100000000, 2530532423/25000000, 703567421/25000000], ![153517797/25000000, 61447203/10000000, 12184233/4000000]]
def scD58CutWeightFloor : ℚ := 12320957/10000000
def scD58CutMargins : Fin 3 → ℚ := ![58651381/10000000000, 49911839/10000000000, 9225999/5000000000]

theorem scD58Cut_roots_ok : scD58CutCell.rootsOK scD58CutRoots = true := by decide +kernel

theorem scD58Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD58CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD58Cut_margin_le (i : Fin 3) : curvatureLoss scD58CutCell scD58CutCaps i ≤ scD58CutMargins i := by
  fin_cases i <;> decide +kernel

def scD59CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨9/40, 19/80⟩, ⟨9/80, 1/8⟩⟩
def scD59CutRoots : Fin 3 → RatBounds := ![⟨505186154797487/281474976710656, 541447497686075/281474976710656⟩, ⟨449115057801985/281474976710656, 241150207201587/140737488355328⟩, ⟨136235025644631/140737488355328, 303652497038105/281474976710656⟩]
def scD59CutCaps : Fin 3 → Fin 3 → ℚ := ![![814873209/4000000, 15131410111/100000000, 6450553259/100000000], ![9627612891/100000000, 10311516731/100000000, 286826609/10000000], ![36762689/6250000, 587877661/100000000, 291371727/100000000]]
def scD59CutWeightFloor : ℚ := 31381581/25000000
def scD59CutMargins : Fin 3 → ℚ := ![59741497/10000000000, 6355177/1250000000, 3753981/2000000000]

theorem scD59Cut_roots_ok : scD59CutCell.rootsOK scD59CutRoots = true := by decide +kernel

theorem scD59Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD59CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD59Cut_margin_le (i : Fin 3) : curvatureLoss scD59CutCell scD59CutCaps i ≤ scD59CutMargins i := by
  fin_cases i <;> decide +kernel

def scD60CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨19/80, 1/4⟩, ⟨1/10, 9/80⟩⟩
def scD60CutRoots : Fin 3 → RatBounds := ![⟨250338265737177/140737488355328, 267903030692453/140737488355328⟩, ⟨3457135938263/2199023255552, 237287714852263/140737488355328⟩, ⟨138516358562105/140737488355328, 2403644422123/2199023255552⟩]
def scD60CutCaps : Fin 3 → Fin 3 → ℚ := ![![18124696343/100000000, 6616610421/50000000, 5839407013/100000000], ![8363454961/100000000, 2234943683/25000000, 2584949997/100000000], ![602208921/100000000, 118637121/20000000, 152846953/50000000]]
def scD60CutWeightFloor : ℚ := 7760851/6250000
def scD60CutMargins : Fin 3 → ℚ := ![2645543/500000000, 22232599/5000000000, 17050881/10000000000]

theorem scD60Cut_roots_ok : scD60CutCell.rootsOK scD60CutRoots = true := by decide +kernel

theorem scD60Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD60CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD60Cut_margin_le (i : Fin 3) : curvatureLoss scD60CutCell scD60CutCaps i ≤ scD60CutMargins i := by
  fin_cases i <;> decide +kernel

def scD61CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨19/80, 1/4⟩, ⟨9/80, 1/8⟩⟩
def scD61CutRoots : Fin 3 → RatBounds := ![⟨499166520504173/281474976710656, 66771621937281/35184372088832⟩, ⟨220193534095257/140737488355328, 472270819926633/281474976710656⟩, ⟨274956909333825/281474976710656, 19083803107569/17592186044416⟩]
def scD61CutCaps : Fin 3 → Fin 3 → ℚ := ![![18485931657/100000000, 13513214537/100000000, 5953087783/100000000], ![266478989/3125000, 4553399457/50000000, 1317614627/50000000], ![576733453/100000000, 567433583/100000000, 58477427/20000000]]
def scD61CutWeightFloor : ℚ := 126501253/100000000
def scD61CutMargins : Fin 3 → ℚ := ![10777341/2000000000, 45287983/10000000000, 8672563/5000000000]

theorem scD61Cut_roots_ok : scD61CutCell.rootsOK scD61CutRoots = true := by decide +kernel

theorem scD61Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD61CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD61Cut_margin_le (i : Fin 3) : curvatureLoss scD61CutCell scD61CutCaps i ≤ scD61CutMargins i := by
  fin_cases i <;> decide +kernel

def scD62CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨1/4, 21/80⟩, ⟨1/10, 9/80⟩⟩
def scD62CutRoots : Fin 3 → RatBounds := ![⟨247577524116301/140737488355328, 529178601737517/281474976710656⟩, ⟨217149463038663/140737488355328, 232603331337627/140737488355328⟩, ⟨139761257018639/140737488355328, 309443943963233/281474976710656⟩]
def scD62CutCaps : Fin 3 → Fin 3 → ℚ := ![![16568791013/100000000, 5955391921/50000000, 84798987/1562500], ![7474851859/100000000, 1987500053/25000000, 2412200589/100000000], ![147937097/25000000, 28684053/5000000, 153597049/50000000]]
def scD62CutWeightFloor : ℚ := 15642071/12500000
def scD62CutMargins : Fin 3 → ℚ := ![48115999/10000000000, 7982213/2000000000, 1988899/1250000000]

theorem scD62Cut_roots_ok : scD62CutCell.rootsOK scD62CutRoots = true := by decide +kernel

theorem scD62Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD62CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD62Cut_margin_le (i : Fin 3) : curvatureLoss scD62CutCell scD62CutCaps i ≤ scD62CutMargins i := by
  fin_cases i <;> decide +kernel

def scD63CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨1/4, 21/80⟩, ⟨9/80, 1/8⟩⟩
def scD63CutRoots : Fin 3 → RatBounds := ![⟨246836816438977/140737488355328, 263789066884605/140737488355328⟩, ⟨54023030213011/35184372088832, 462916710628637/281474976710656⟩, ⟨138723890112515/140737488355328, 153563649331773/140737488355328⟩]
def scD63CutCaps : Fin 3 → Fin 3 → ℚ := ![![16898079067/100000000, 1520383293/12500000, 1106760799/20000000], ![7621287359/100000000, 101229317/1250000, 1229605243/50000000], ![56661719/10000000, 548704717/100000000, 293797903/100000000]]
def scD63CutWeightFloor : ℚ := 63737459/50000000
def scD63CutMargins : Fin 3 → ℚ := ![24498031/5000000000, 40644759/10000000000, 16185181/10000000000]

theorem scD63Cut_roots_ok : scD63CutCell.rootsOK scD63CutRoots = true := by decide +kernel

theorem scD63Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD63CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD63Cut_margin_le (i : Fin 3) : curvatureLoss scD63CutCell scD63CutCaps i ≤ scD63CutMargins i := by
  fin_cases i <;> decide +kernel

def scD64CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨21/80, 11/40⟩, ⟨1/10, 9/80⟩⟩
def scD64CutRoots : Fin 3 → RatBounds := ![⟨122528453957147/70368744177664, 523164150376665/281474976710656⟩, ⟨426557557129107/281474976710656, 456440901064149/281474976710656⟩, ⟨282023017344563/281474976710656, 155657889635153/140737488355328⟩]
def scD64CutCaps : Fin 3 → Fin 3 → ℚ := ![![952973267/6250000, 134969037/1250000, 1269269517/25000000], ![6729402037/100000000, 7113905399/100000000, 2269522647/100000000], ![116498373/20000000, 138928451/25000000, 61812313/20000000]]
def scD64CutWeightFloor : ℚ := 25220331/20000000
def scD64CutMargins : Fin 3 → ℚ := ![22030729/5000000000, 18034319/5000000000, 7476233/5000000000]

theorem scD64Cut_roots_ok : scD64CutCell.rootsOK scD64CutRoots = true := by decide +kernel

theorem scD64Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD64CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD64Cut_margin_le (i : Fin 3) : curvatureLoss scD64CutCell scD64CutCaps i ≤ scD64CutMargins i := by
  fin_cases i <;> decide +kernel

def scD65CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨21/80, 11/40⟩, ⟨9/80, 1/8⟩⟩
def scD65CutRoots : Fin 3 → RatBounds := ![⟨488658669930177/281474976710656, 521593505918363/281474976710656⟩, ⟨424453172948489/281474976710656, 454163774442575/281474976710656⟩, ⟨279949577362731/281474976710656, 309007622134443/281474976710656⟩]
def scD65CutCaps : Fin 3 → Fin 3 → ℚ := ![![15549820411/100000000, 5513222471/50000000, 2588909009/50000000], ![6861217757/100000000, 7246504079/100000000, 2313806869/100000000], ![278831643/50000000, 265727687/50000000, 295560781/100000000]]
def scD65CutWeightFloor : ℚ := 128450621/100000000
def scD65CutMargins : Fin 3 → ℚ := ![22430373/5000000000, 36727353/10000000000, 3802337/2500000000]

theorem scD65Cut_roots_ok : scD65CutCell.rootsOK scD65CutRoots = true := by decide +kernel

theorem scD65Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD65CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD65Cut_margin_le (i : Fin 3) : curvatureLoss scD65CutCell scD65CutCaps i ≤ scD65CutMargins i := by
  fin_cases i <;> decide +kernel

def scD66CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨11/40, 23/80⟩, ⟨1/10, 9/80⟩⟩
def scD66CutRoots : Fin 3 → RatBounds := ![⟨485510927566749/281474976710656, 517703895022021/281474976710656⟩, ⟨419243086164693/281474976710656, 448214783993445/281474976710656⟩, ⟨284540433548979/281474976710656, 39159866217751/35184372088832⟩]
def scD66CutCaps : Fin 3 → Fin 3 → ℚ := ![![14117328087/100000000, 4926462671/50000000, 2389026263/50000000], ![3049783303/50000000, 256071793/4000000, 2151439561/100000000], ![574279723/100000000, 53908369/10000000, 155630509/50000000]]
def scD66CutWeightFloor : ℚ := 63535863/50000000
def scD66CutMargins : Fin 3 → ℚ := ![40607763/10000000000, 32800399/10000000000, 883881/625000000]

theorem scD66Cut_roots_ok : scD66CutCell.rootsOK scD66CutRoots = true := by decide +kernel

theorem scD66Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD66CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD66Cut_margin_le (i : Fin 3) : curvatureLoss scD66CutCell scD66CutCaps i ≤ scD66CutMargins i := by
  fin_cases i <;> decide +kernel

def scD67CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨11/40, 23/80⟩, ⟨9/80, 1/8⟩⟩
def scD67CutRoots : Fin 3 → RatBounds := ![⟨484079902955965/281474976710656, 516160520324881/281474976710656⟩, ⟨104286949488683/70368744177664, 222974427104095/140737488355328⟩, ⟨282468463505923/281474976710656, 310978801159883/281474976710656⟩]
def scD67CutCaps : Fin 3 → Fin 3 → ℚ := ![![14396520459/100000000, 2515498667/25000000, 4873759577/100000000], ![3109516509/50000000, 6521004911/100000000, 219343879/10000000], ![549717873/100000000, 257746487/50000000, 148820991/50000000]]
def scD67CutWeightFloor : ℚ := 129431269/100000000
def scD67CutMargins : Fin 3 → ℚ := ![41338421/10000000000, 16697747/5000000000, 7192227/5000000000]

theorem scD67Cut_roots_ok : scD67CutCell.rootsOK scD67CutRoots = true := by decide +kernel

theorem scD67Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD67CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD67Cut_margin_le (i : Fin 3) : curvatureLoss scD67CutCell scD67CutCaps i ≤ scD67CutMargins i := by
  fin_cases i <;> decide +kernel

def scD68CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨23/80, 3/10⟩, ⟨1/10, 9/80⟩⟩
def scD68CutRoots : Fin 3 → RatBounds := ![⟨240655197705275/140737488355328, 512747953227349/281474976710656⟩, ⟨412315406479317/281474976710656, 440474065539659/281474976710656⟩, ⟨287080388323077/281474976710656, 157665667505527/140737488355328⟩]
def scD68CutCaps : Fin 3 → Fin 3 → ℚ := ![![13144229677/100000000, 4522919271/50000000, 2260702683/50000000], ![5564370837/100000000, 5792436537/100000000, 102717041/5000000], ![566981059/100000000, 32726537/6250000, 62752779/20000000]]
def scD68CutWeightFloor : ℚ := 64024669/50000000
def scD68CutMargins : Fin 3 → ℚ := ![37647621/10000000000, 30003711/10000000000, 538243/400000000]

theorem scD68Cut_roots_ok : scD68CutCell.rootsOK scD68CutRoots = true := by decide +kernel

theorem scD68Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD68CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD68Cut_margin_le (i : Fin 3) : curvatureLoss scD68CutCell scD68CutCaps i ≤ scD68CutMargins i := by
  fin_cases i <;> decide +kernel

def scD69CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨23/80, 3/10⟩, ⟨9/80, 1/8⟩⟩
def scD69CutRoots : Fin 3 → RatBounds := ![⟨239950748638309/140737488355328, 255614749684025/140737488355328⟩, ⟨51278516719709/35184372088832, 438217877431099/281474976710656⟩, ⟨142505013225039/140737488355328, 78259702545653/70368744177664⟩]
def scD69CutCaps : Fin 3 → Fin 3 → ℚ := ![![13403637457/100000000, 577369693/6250000, 922565901/20000000], ![2836680777/50000000, 147506661/2500000, 2094457451/100000000], ![542654767/100000000, 50065767/10000000, 150007083/50000000]]
def scD69CutWeightFloor : ℚ := 8151217/6250000
def scD69CutMargins : Fin 3 → ℚ := ![38319637/10000000000, 954519/312500000, 1710767/1250000000]

theorem scD69Cut_roots_ok : scD69CutCell.rootsOK scD69CutRoots = true := by decide +kernel

theorem scD69Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD69CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD69Cut_margin_le (i : Fin 3) : curvatureLoss scD69CutCell scD69CutCaps i ≤ scD69CutMargins i := by
  fin_cases i <;> decide +kernel

def scD70CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨3/10, 5/16⟩, ⟨1/10, 9/80⟩⟩
def scD70CutRoots : Fin 3 → RatBounds := ![⟨59685149079679/35184372088832, 508253807313751/281474976710656⟩, ⟨101434875823061/70368744177664, 54146499027481/35184372088832⟩, ⟨72412016425051/70368744177664, 317471778295671/281474976710656⟩]
def scD70CutCaps : Fin 3 → Fin 3 → ℚ := ![![6150891519/50000000, 8352012159/100000000, 2150182577/50000000], ![510737929/10000000, 5268528333/100000000, 1975289701/100000000], ![560487699/100000000, 50919747/10000000, 316547093/100000000]]
def scD70CutWeightFloor : ℚ := 129036821/100000000
def scD70CutMargins : Fin 3 → ℚ := ![35096973/10000000000, 5519429/2000000000, 2575079/2000000000]

theorem scD70Cut_roots_ok : scD70CutCell.rootsOK scD70CutRoots = true := by decide +kernel

theorem scD70Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD70CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD70Cut_margin_le (i : Fin 3) : curvatureLoss scD70CutCell scD70CutCaps i ≤ scD70CutMargins i := by
  fin_cases i <;> decide +kernel

def scD71CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨3/10, 5/16⟩, ⟨9/80, 1/8⟩⟩
def scD71CutRoots : Fin 3 → RatBounds := ![⟨476092558802669/281474976710656, 506758100544433/281474976710656⟩, ⟨201829636601609/140737488355328, 26932764951903/17592186044416⟩, ⟨287579417021083/281474976710656, 315186460340727/281474976710656⟩]
def scD71CutCaps : Fin 3 → Fin 3 → ℚ := ![![12544120827/100000000, 8529451403/100000000, 1097035609/25000000], ![2603714237/50000000, 2683258017/50000000, 2013825729/100000000], ![134092423/25000000, 486815681/100000000, 302655229/100000000]]
def scD71CutWeightFloor : ℚ := 26283521/20000000
def scD71CutMargins : Fin 3 → ℚ := ![558103/156250000, 14045687/5000000000, 1636871/1250000000]

theorem scD71Cut_roots_ok : scD71CutCell.rootsOK scD71CutRoots = true := by decide +kernel

theorem scD71Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD71CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD71Cut_margin_le (i : Fin 3) : curvatureLoss scD71CutCell scD71CutCaps i ≤ scD71CutMargins i := by
  fin_cases i <;> decide +kernel

def scD72CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨5/16, 13/40⟩, ⟨1/10, 9/80⟩⟩
def scD72CutRoots : Fin 3 → RatBounds := ![⟨59249560785645/35184372088832, 504185072634879/281474976710656⟩, ⟨99871160513487/70368744177664, 213134010945941/140737488355328⟩, ⟨292248319263473/281474976710656, 319699767603729/281474976710656⟩]
def scD72CutCaps : Fin 3 → Fin 3 → ℚ := ![![11569018633/100000000, 155047177/2000000, 4109585147/100000000], ![4715261707/100000000, 601643231/12500000, 955415353/50000000], ![69338997/12500000, 99137441/20000000, 319593997/100000000]]
def scD72CutWeightFloor : ℚ := 65018169/50000000
def scD72CutMargins : Fin 3 → ℚ := ![32888657/10000000000, 25510141/10000000000, 773927/625000000]

theorem scD72Cut_roots_ok : scD72CutCell.rootsOK scD72CutRoots = true := by decide +kernel

theorem scD72Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD72CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD72Cut_margin_le (i : Fin 3) : curvatureLoss scD72CutCell scD72CutCaps i ≤ scD72CutMargins i := by
  fin_cases i <;> decide +kernel

def scD73CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨5/16, 13/40⟩, ⟨9/80, 1/8⟩⟩
def scD73CutRoots : Fin 3 → RatBounds := ![⟨236313184809941/140737488355328, 502710089609587/281474976710656⟩, ⟨198705287939585/140737488355328, 106006881384759/70368744177664⟩, ⟨290181459322433/281474976710656, 158710640924835/140737488355328⟩]
def scD73CutCaps : Fin 3 → Fin 3 → ℚ := ![![1179656159/10000000, 494819953/6250000, 419426147/10000000], ![240381761/5000000, 4902611223/100000000, 1948063541/100000000], ![530778713/100000000, 473856759/100000000, 305549771/100000000]]
def scD73CutWeightFloor : ℚ := 132427871/100000000
def scD73CutMargins : Fin 3 → ℚ := ![133867/40000000, 12982019/5000000000, 6296753/5000000000]

theorem scD73Cut_roots_ok : scD73CutCell.rootsOK scD73CutRoots = true := by decide +kernel

theorem scD73Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD73CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD73Cut_margin_le (i : Fin 3) : curvatureLoss scD73CutCell scD73CutCaps i ≤ scD73CutMargins i := by
  fin_cases i <;> decide +kernel

def scD74CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨13/40, 27/80⟩, ⟨1/10, 9/80⟩⟩
def scD74CutRoots : Fin 3 → RatBounds := ![⟨235416508574651/140737488355328, 250255259717759/140737488355328⟩, ⟨196761854768901/140737488355328, 209863401094713/140737488355328⟩, ⟨147442881276807/140737488355328, 161007723389465/140737488355328⟩]
def scD74CutCaps : Fin 3 → Fin 3 → ℚ := ![![437167269/4000000, 7231704757/100000000, 1972404929/50000000], ![1094435851/25000000, 4415602151/100000000, 185917369/10000000], ![274789121/50000000, 30187117/6250000, 64577879/20000000]]
def scD74CutWeightFloor : ℚ := 409531/312500
def scD74CutMargins : Fin 3 → ℚ := ![15484867/5000000000, 11845997/5000000000, 11966549/10000000000]

theorem scD74Cut_roots_ok : scD74CutCell.rootsOK scD74CutRoots = true := by decide +kernel

theorem scD74Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD74CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD74Cut_margin_le (i : Fin 3) : curvatureLoss scD74CutCell scD74CutCaps i ≤ scD74CutMargins i := by
  fin_cases i <;> decide +kernel

def scD75CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨13/40, 27/80⟩, ⟨9/80, 1/8⟩⟩
def scD75CutRoots : Fin 3 → RatBounds := ![⟨469479770527789/281474976710656, 249527183158395/140737488355328⟩, ⟨391455011332409/281474976710656, 208746247478413/140737488355328⟩, ⟨4575324068635/4398046511104, 159871717978639/140737488355328⟩]
def scD75CutCaps : Fin 3 → Fin 3 → ℚ := ![![11143854821/100000000, 7385429101/100000000, 503357427/12500000], ![2231751817/50000000, 2248800761/50000000, 1895313863/100000000], ![262903861/50000000, 461683671/100000000, 308682249/100000000]]
def scD75CutWeightFloor : ℚ := 133452339/100000000
def scD75CutMargins : Fin 3 → ℚ := ![31510091/10000000000, 24110771/10000000000, 304241/250000000]

theorem scD75Cut_roots_ok : scD75CutCell.rootsOK scD75CutRoots = true := by decide +kernel

theorem scD75Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD75CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD75Cut_margin_le (i : Fin 3) : curvatureLoss scD75CutCell scD75CutCaps i ≤ scD75CutMargins i := by
  fin_cases i <;> decide +kernel

def scD76CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨27/80, 7/20⟩, ⟨1/10, 9/80⟩⟩
def scD76CutRoots : Fin 3 → RatBounds := ![⟨467970595686853/281474976710656, 62150411246663/35184372088832⟩, ⟨387832674710707/281474976710656, 51689668563983/35184372088832⟩, ⟨297564843980187/281474976710656, 324419529528537/281474976710656⟩]
def scD76CutCaps : Fin 3 → Fin 3 → ℚ := ![![10370452597/100000000, 1694469677/25000000, 761100407/20000000], ![4086597753/100000000, 101673969/2500000, 18187993/1000000], ![27251041/5000000, 471030143/100000000, 163209713/50000000]]
def scD76CutWeightFloor : ℚ := 16509939/12500000
def scD76CutMargins : Fin 3 → ℚ := ![29300921/10000000000, 2762663/1250000000, 5811251/5000000000]

theorem scD76Cut_roots_ok : scD76CutCell.rootsOK scD76CutRoots = true := by decide +kernel

theorem scD76Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD76CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD76Cut_margin_le (i : Fin 3) : curvatureLoss scD76CutCell scD76CutCaps i ≤ scD76CutMargins i := by
  fin_cases i <;> decide +kernel

def scD77CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨27/80, 7/20⟩, ⟨9/80, 1/8⟩⟩
def scD77CutRoots : Fin 3 → RatBounds := ![⟨233316329506625/140737488355328, 123941046162591/70368744177664⟩, ⟨96442155418851/70368744177664, 205644129741473/140737488355328⟩, ⟨147750842255317/140737488355328, 322153649675887/281474976710656⟩]
def scD77CutCaps : Fin 3 → Fin 3 → ℚ := ![![2643867131/25000000, 6922013009/100000000, 971734271/25000000], ![4166646677/100000000, 828479473/20000000, 927025429/50000000], ![130348501/25000000, 450212949/100000000, 312039949/100000000]]
def scD77CutWeightFloor : ℚ := 67246493/50000000
def scD77CutMargins : Fin 3 → ℚ := ![14905771/5000000000, 22489499/10000000000, 11822321/10000000000]

theorem scD77Cut_roots_ok : scD77CutCell.rootsOK scD77CutRoots = true := by decide +kernel

theorem scD77Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD77CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD77Cut_margin_le (i : Fin 3) : curvatureLoss scD77CutCell scD77CutCaps i ≤ scD77CutMargins i := by
  fin_cases i <;> decide +kernel

def scD78CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨7/20, 29/80⟩, ⟨1/10, 9/80⟩⟩
def scD78CutRoots : Fin 3 → RatBounds := ![⟨465391689873193/281474976710656, 494240267711227/281474976710656⟩, ⟨382390144343777/281474976710656, 407612377073575/281474976710656⟩, ⟨300289910165773/281474976710656, 326913251498821/281474976710656⟩]
def scD78CutCaps : Fin 3 → Fin 3 → ℚ := ![![9888586641/100000000, 797630569/12500000, 3700292927/100000000], ![1917576611/50000000, 2349593/62500, 1788404533/100000000], ![67623321/12500000, 91944611/20000000, 165087589/50000000]]
def scD78CutWeightFloor : ℚ := 8320437/6250000
def scD78CutMargins : Fin 3 → ℚ := ![13930397/5000000000, 20703353/10000000000, 5682493/5000000000]

theorem scD78Cut_roots_ok : scD78CutCell.rootsOK scD78CutRoots = true := by decide +kernel

theorem scD78Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD78CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD78Cut_margin_le (i : Fin 3) : curvatureLoss scD78CutCell scD78CutCaps i ≤ scD78CutMargins i := by
  fin_cases i <;> decide +kernel

def scD79CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨7/20, 29/80⟩, ⟨9/80, 1/8⟩⟩
def scD79CutRoots : Fin 3 → RatBounds := ![⟨232033789401417/140737488355328, 492816524530201/281474976710656⟩, ⟨380330078625393/281474976710656, 405387619782285/281474976710656⟩, ⟨298228616044281/281474976710656, 324653168404509/281474976710656⟩]
def scD79CutCaps : Fin 3 → Fin 3 → ℚ := ![![2521239337/25000000, 6516782317/100000000, 3780440061/100000000], ![782052021/20000000, 1914518631/50000000, 455743013/25000000], ![129371581/25000000, 21968719/5000000, 315614377/100000000]]
def scD79CutWeightFloor : ℚ := 135551723/100000000
def scD79CutMargins : Fin 3 → ℚ := ![226761/80000000, 164569/78125000, 11560599/10000000000]

theorem scD79Cut_roots_ok : scD79CutCell.rootsOK scD79CutRoots = true := by decide +kernel

theorem scD79Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD79CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD79Cut_margin_le (i : Fin 3) : curvatureLoss scD79CutCell scD79CutCaps i ≤ scD79CutMargins i := by
  fin_cases i <;> decide +kernel

def scD80CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨29/80, 3/8⟩, ⟨1/10, 9/80⟩⟩
def scD80CutRoots : Fin 3 → RatBounds := ![⟨463081086712783/281474976710656, 245800783123045/140737488355328⟩, ⟨377176994175341/281474976710656, 100496939904633/70368744177664⟩, ⟨37883157586827/35184372088832, 329498336833135/281474976710656⟩]
def scD80CutCaps : Fin 3 → Fin 3 → ℚ := ![![9466968559/100000000, 1508310211/25000000, 3612710411/100000000], ![226126923/6250000, 3486823213/100000000, 441771899/25000000], ![33589579/6250000, 14031607/3125000, 20884473/6250000]]
def scD80CutWeightFloor : ℚ := 67097103/50000000
def scD80CutMargins : Fin 3 → ℚ := ![13303157/5000000000, 19470851/10000000000, 5580029/5000000000]

theorem scD80Cut_roots_ok : scD80CutCell.rootsOK scD80CutRoots = true := by decide +kernel

theorem scD80Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD80CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD80Cut_margin_le (i : Fin 3) : curvatureLoss scD80CutCell scD80CutCaps i ≤ scD80CutMargins i := by
  fin_cases i <;> decide +kernel

def scD81CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨29/80, 3/8⟩, ⟨9/80, 1/8⟩⟩
def scD81CutRoots : Fin 3 → RatBounds := ![⟨115442345692085/70368744177664, 30636973923705/17592186044416⟩, ⟨187560157925719/140737488355328, 199883260853139/140737488355328⟩, ⟨301005813787655/281474976710656, 81810930727571/70368744177664⟩]
def scD81CutCaps : Fin 3 → Fin 3 → ℚ := ![![9654857119/100000000, 3080759109/50000000, 3691629133/100000000], ![737771889/20000000, 1775712191/50000000, 900569383/50000000], ![514045563/100000000, 429110189/100000000, 319401611/100000000]]
def scD81CutWeightFloor : ℚ := 5465217/4000000
def scD81CutMargins : Fin 3 → ℚ := ![13532971/5000000000, 19808697/10000000000, 5675947/5000000000]

theorem scD81Cut_roots_ok : scD81CutCell.rootsOK scD81CutRoots = true := by decide +kernel

theorem scD81Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD81CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD81Cut_margin_le (i : Fin 3) : curvatureLoss scD81CutCell scD81CutCaps i ≤ scD81CutMargins i := by
  fin_cases i <;> decide +kernel

def scD82CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨3/8, 31/80⟩, ⟨1/10, 9/80⟩⟩
def scD82CutRoots : Fin 3 → RatBounds := ![⟨461025613307321/281474976710656, 489270113530257/281474976710656⟩, ⟨46522007597897/35184372088832, 396622074468651/281474976710656⟩, ⟨152947598276857/140737488355328, 166088488318797/140737488355328⟩]
def scD82CutCaps : Fin 3 → Fin 3 → ℚ := ![![2274321991/25000000, 5727825671/100000000, 3540812377/100000000], ![1715440143/50000000, 324455873/10000000, 1754205137/100000000], ![534334117/100000000, 87769629/20000000, 169175237/50000000]]
def scD82CutWeightFloor : ℚ := 135282983/100000000
def scD82CutMargins : Fin 3 → ℚ := ![255127/100000000, 9190657/5000000000, 687667/625000000]

theorem scD82Cut_roots_ok : scD82CutCell.rootsOK scD82CutRoots = true := by decide +kernel

theorem scD82Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD82CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD82Cut_margin_le (i : Fin 3) : curvatureLoss scD82CutCell scD82CutCaps i ≤ scD82CutMargins i := by
  fin_cases i <;> decide +kernel

def scD83CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨3/8, 31/80⟩, ⟨9/80, 1/8⟩⟩
def scD83CutRoots : Fin 3 → RatBounds := ![⟨459724955146169/281474976710656, 243936179503695/140737488355328⟩, ⟨370122221834879/281474976710656, 24650225551393/17592186044416⟩, ⟨151918779527747/140737488355328, 329927508119511/281474976710656⟩]
def scD83CutCaps : Fin 3 → Fin 3 → ℚ := ![![9277780123/100000000, 584952463/10000000, 3618809571/100000000], ![3498010387/100000000, 3304645117/100000000, 1787897693/100000000], ![127760657/25000000, 419372777/100000000, 161700859/50000000]]
def scD83CutWeightFloor : ℚ := 137730951/100000000
def scD83CutMargins : Fin 3 → ℚ := ![12975423/5000000000, 9349163/5000000000, 559581/500000000]

theorem scD83Cut_roots_ok : scD83CutCell.rootsOK scD83CutRoots = true := by decide +kernel

theorem scD83Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD83CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD83Cut_margin_le (i : Fin 3) : curvatureLoss scD83CutCell scD83CutCaps i ≤ scD83CutMargins i := by
  fin_cases i <;> decide +kernel


end HlawkaSchatten.BelowExponent.Vertex
