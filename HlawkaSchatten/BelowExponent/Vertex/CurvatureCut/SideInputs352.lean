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

def scE46CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨13/40, 27/80⟩, ⟨3/20, 13/80⟩⟩
def scE46CutRoots : Fin 3 → RatBounds := ![⟨474812463277223/281474976710656, 126346922234417/70368744177664⟩, ⟨390612630979373/281474976710656, 52142956697105/35184372088832⟩, ⟨143051945151289/140737488355328, 156601247299165/140737488355328⟩]
def scE46CutCaps : Fin 3 → Fin 3 → ℚ := ![![501878949/4000000, 8373078101/100000000, 1085696231/25000000], ![5061197169/100000000, 202408039/4000000, 400667861/20000000], ![474098087/100000000, 205866359/50000000, 269303483/100000000]]
def scE46CutWeightFloor : ℚ := 70222801/50000000
def scE46CutMargins : Fin 3 → ℚ := ![8829233/2500000000, 27041039/10000000000, 6460379/5000000000]

theorem scE46Cut_roots_ok : scE46CutCell.rootsOK scE46CutRoots = true := by decide +kernel

theorem scE46Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE46CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE46Cut_margin_le (i : Fin 3) : curvatureLoss scE46CutCell scE46CutCaps i ≤ scE46CutMargins i := by
  fin_cases i <;> decide +kernel

def scE47CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨13/40, 27/80⟩, ⟨13/80, 1/6⟩⟩
def scE47CutRoots : Fin 3 → RatBounds := ![⟨474634291703957/281474976710656, 251947908899547/140737488355328⟩, ⟨389997845755021/281474976710656, 103791957965037/70368744177664⟩, ⟨285498272239031/281474976710656, 77805461140205/70368744177664⟩]
def scE47CutCaps : Fin 3 → Fin 3 → ℚ := ![![6212221133/50000000, 4148242941/50000000, 850419983/20000000], ![1254841851/25000000, 249113123/5000000, 966686969/50000000], ![180757059/50000000, 62647731/20000000, 104563347/50000000]]
def scE47CutWeightFloor : ℚ := 143491693/100000000
def scE47CutMargins : Fin 3 → ℚ := ![6829679/2000000000, 26003033/10000000000, 3031597/2500000000]

theorem scE47Cut_roots_ok : scE47CutCell.rootsOK scE47CutRoots = true := by decide +kernel

theorem scE47Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE47CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE47Cut_margin_le (i : Fin 3) : curvatureLoss scE47CutCell scE47CutCaps i ≤ scE47CutMargins i := by
  fin_cases i <;> decide +kernel

def scE48CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨27/80, 7/20⟩, ⟨1/8, 11/80⟩⟩
def scE48CutRoots : Fin 3 → RatBounds := ![⟨118543401322273/70368744177664, 504424357165023/281474976710656⟩, ⟨97131917781147/70368744177664, 414785217195873/281474976710656⟩, ⟨146300673438203/140737488355328, 319775035858903/281474976710656⟩]
def scE48CutCaps : Fin 3 → Fin 3 → ℚ := ![![715558611/6250000, 940811947/12500000, 4036095139/100000000], ![4540221957/100000000, 561137687/12500000, 1889714907/100000000], ![63924633/12500000, 43726289/10000000, 148271787/50000000]]
def scE48CutWeightFloor : ℚ := 8543333/6250000
def scE48CutMargins : Fin 3 → ℚ := ![644553/200000000, 24321993/10000000000, 2430607/2000000000]

theorem scE48Cut_roots_ok : scE48CutCell.rootsOK scE48CutRoots = true := by decide +kernel

theorem scE48Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE48CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE48Cut_margin_le (i : Fin 3) : curvatureLoss scE48CutCell scE48CutCaps i ≤ scE48CutMargins i := by
  fin_cases i <;> decide +kernel

def scE49CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨27/80, 7/20⟩, ⟨11/80, 3/20⟩⟩
def scE49CutRoots : Fin 3 → RatBounds := ![⟨472934058830015/281474976710656, 503092348538155/281474976710656⟩, ⟨386572987638221/281474976710656, 412675352881869/281474976710656⟩, ⟨290667027092545/281474976710656, 19853113821205/17592186044416⟩]
def scE49CutCaps : Fin 3 → Fin 3 → ℚ := ![![11661790059/100000000, 3837199957/50000000, 4115078321/100000000], ![578057509/12500000, 571021527/12500000, 962210761/50000000], ![97995087/20000000, 20932313/5000000, 283968337/100000000]]
def scE49CutWeightFloor : ℚ := 139110207/100000000
def scE49CutMargins : Fin 3 → ℚ := ![16383033/5000000000, 24728943/10000000000, 3087631/2500000000]

theorem scE49Cut_roots_ok : scE49CutCell.rootsOK scE49CutRoots = true := by decide +kernel

theorem scE49Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE49CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE49Cut_margin_le (i : Fin 3) : curvatureLoss scE49CutCell scE49CutCaps i ≤ scE49CutMargins i := by
  fin_cases i <;> decide +kernel

def scE50CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨27/80, 7/20⟩, ⟨3/20, 13/80⟩⟩
def scE50CutRoots : Fin 3 → RatBounds := ![⟨471736737322947/281474976710656, 31362927625577/17592186044416⟩, ⟨384689145540771/281474976710656, 410643372161879/281474976710656⟩, ⟨144402530712341/140737488355328, 315605569010767/281474976710656⟩]
def scE50CutCaps : Fin 3 → Fin 3 → ℚ := ![![2968601539/25000000, 3910934809/50000000, 1048469057/25000000], ![941698083/20000000, 4647141563/100000000, 979539253/50000000], ![117463917/25000000, 1567106/390625, 8505193/3125000]]
def scE50CutWeightFloor : ℚ := 2211387/1562500
def scE50CutMargins : Fin 3 → ℚ := ![33306157/10000000000, 25137091/10000000000, 2509813/2000000000]

theorem scE50Cut_roots_ok : scE50CutCell.rootsOK scE50CutRoots = true := by decide +kernel

theorem scE50Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE50CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE50Cut_margin_le (i : Fin 3) : curvatureLoss scE50CutCell scE50CutCaps i ≤ scE50CutMargins i := by
  fin_cases i <;> decide +kernel

def scE51CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨27/80, 7/20⟩, ⟨13/80, 1/6⟩⟩
def scE51CutRoots : Fin 3 → RatBounds := ![⟨235782905077185/140737488355328, 15635264596489/8796093022208⟩, ⟨384076271939397/281474976710656, 204337116298661/140737488355328⟩, ⟨288199785435123/281474976710656, 78407437276529/70368744177664⟩]
def scE51CutCaps : Fin 3 → Fin 3 → ℚ := ![![11753636533/100000000, 774898317/10000000, 4102472037/100000000], ![4667624509/100000000, 4571179227/100000000, 472588071/25000000], ![357954971/100000000, 6094079/2000000, 210848353/100000000]]
def scE51CutWeightFloor : ℚ := 72294331/50000000
def scE51CutMargins : Fin 3 → ℚ := ![32150457/10000000000, 24128943/10000000000, 11750493/10000000000]

theorem scE51Cut_roots_ok : scE51CutCell.rootsOK scE51CutRoots = true := by decide +kernel

theorem scE51Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE51CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE51Cut_margin_le (i : Fin 3) : curvatureLoss scE51CutCell scE51CutCaps i ≤ scE51CutMargins i := by
  fin_cases i <;> decide +kernel

def scE52CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨7/20, 29/80⟩, ⟨1/8, 11/80⟩⟩
def scE52CutRoots : Fin 3 → RatBounds := ![⟨471370839650091/281474976710656, 62647588267245/35184372088832⟩, ⟨191429809803249/140737488355328, 102150221775159/70368744177664⟩, ⟨36918006304067/35184372088832, 161129177895029/140737488355328⟩]
def scE52CutCaps : Fin 3 → Fin 3 → ℚ := ![![2721180797/25000000, 3531019933/50000000, 122492097/3125000], ![2123296261/50000000, 827639001/20000000, 232182061/12500000], ![101477151/20000000, 106617023/25000000, 299906627/100000000]]
def scE52CutWeightFloor : ℚ := 137771367/100000000
def scE52CutMargins : Fin 3 → ℚ := ![30544339/10000000000, 4541681/2000000000, 2967339/2500000000]

theorem scE52Cut_roots_ok : scE52CutCell.rootsOK scE52CutRoots = true := by decide +kernel

theorem scE52Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE52CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE52Cut_margin_le (i : Fin 3) : curvatureLoss scE52CutCell scE52CutCaps i ≤ scE52CutMargins i := by
  fin_cases i <;> decide +kernel

def scE53CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨7/20, 29/80⟩, ⟨11/80, 3/20⟩⟩
def scE53CutRoots : Fin 3 → RatBounds := ![⟨470145009106473/281474976710656, 249931996538289/140737488355328⟩, ⟨11903440168955/8796093022208, 101624190830271/70368744177664⟩, ⟨73352730346579/70368744177664, 320138222549373/281474976710656⟩]
def scE53CutCaps : Fin 3 → Fin 3 → ℚ := ![![11086935703/100000000, 7200820353/100000000, 1998544707/50000000], ![2162695763/50000000, 4211065967/100000000, 945749731/50000000], ![486088151/100000000, 51035407/12500000, 287174249/100000000]]
def scE53CutWeightFloor : ℚ := 17524973/12500000
def scE53CutMargins : Fin 3 → ℚ := ![31051593/10000000000, 23086269/10000000000, 6031019/5000000000]

theorem scE53Cut_roots_ok : scE53CutCell.rootsOK scE53CutRoots = true := by decide +kernel

theorem scE53Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE53CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE53Cut_margin_le (i : Fin 3) : curvatureLoss scE53CutCell scE53CutCaps i ≤ scE53CutMargins i := by
  fin_cases i <;> decide +kernel

def scE54CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨7/20, 29/80⟩, ⟨3/20, 13/80⟩⟩
def scE54CutRoots : Fin 3 → RatBounds := ![⟨234480477275405/140737488355328, 498593279221903/281474976710656⟩, ⟨189515671167075/140737488355328, 202235232723601/140737488355328⟩, ⟨145775024489665/140737488355328, 19881174715813/17592186044416⟩]
def scE54CutCaps : Fin 3 → Fin 3 → ℚ := ![![11288933357/100000000, 733919173/10000000, 4074250049/100000000], ![440399479/10000000, 1070953521/25000000, 1925476667/100000000], ![116521807/25000000, 48902841/12500000, 275225439/100000000]]
def scE54CutWeightFloor : ℚ := 142629943/100000000
def scE54CutMargins : Fin 3 → ℚ := ![31560577/10000000000, 23465291/10000000000, 6127883/5000000000]

theorem scE54Cut_roots_ok : scE54CutCell.rootsOK scE54CutRoots = true := by decide +kernel

theorem scE54Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE54CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE54Cut_margin_le (i : Fin 3) : curvatureLoss scE54CutCell scE54CutCaps i ≤ scE54CutMargins i := by
  fin_cases i <;> decide +kernel

def scE55CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨7/20, 29/80⟩, ⟨13/80, 1/6⟩⟩
def scE55CutRoots : Fin 3 → RatBounds := ![⟨468796597699493/281474976710656, 248563526194227/140737488355328⟩, ⟨378420156677539/281474976710656, 402507109853353/281474976710656⟩, ⟨145472558520579/140737488355328, 308718249913/274877906944⟩]
def scE55CutCaps : Fin 3 → Fin 3 → ℚ := ![![11171999619/100000000, 7269736451/100000000, 996216227/25000000], ![54550067/1250000, 4209548141/100000000, 464444561/25000000], ![354803643/100000000, 18543749/6250000, 53187763/25000000]]
def scE55CutWeightFloor : ℚ := 7285193/5000000
def scE55CutMargins : Fin 3 → ℚ := ![15210379/5000000000, 11242433/5000000000, 11457583/10000000000]

theorem scE55Cut_roots_ok : scE55CutCell.rootsOK scE55CutRoots = true := by decide +kernel

theorem scE55Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE55CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE55Cut_margin_le (i : Fin 3) : curvatureLoss scE55CutCell scE55CutCaps i ≤ scE55CutMargins i := by
  fin_cases i <;> decide +kernel

def scE56CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨29/80, 3/8⟩, ⟨1/8, 11/80⟩⟩
def scE56CutRoots : Fin 3 → RatBounds := ![⟨468853514884463/281474976710656, 249142321520613/140737488355328⟩, ⟨2948730302323/2199023255552, 402718766410307/281474976710656⟩, ⟨298135045079565/281474976710656, 324833961982213/281474976710656⟩]
def scE56CutCaps : Fin 3 → Fin 3 → ℚ := ![![10388774509/100000000, 831764163/12500000, 955236633/25000000], ![798597057/20000000, 1914000391/50000000, 57326573/3125000], ![251918163/50000000, 208126579/50000000, 60695019/20000000]]
def scE56CutWeightFloor : ℚ := 138868981/100000000
def scE56CutMargins : Fin 3 → ℚ := ![2907343/1000000000, 10642937/5000000000, 5819211/5000000000]

theorem scE56Cut_roots_ok : scE56CutCell.rootsOK scE56CutRoots = true := by decide +kernel

theorem scE56Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE56CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE56Cut_margin_le (i : Fin 3) : curvatureLoss scE56CutCell scE56CutCaps i ≤ scE56CutMargins i := by
  fin_cases i <;> decide +kernel

def scE57CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨29/80, 3/8⟩, ⟨11/80, 3/20⟩⟩
def scE57CutRoots : Fin 3 → RatBounds := ![⟨29227501793567/17592186044416, 248490833520793/140737488355328⟩, ⟨187746226392777/140737488355328, 400619519540319/281474976710656⟩, ⟨296203095395907/281474976710656, 80679645481555/70368744177664⟩]
def scE57CutCaps : Fin 3 → Fin 3 → ℚ := ![![5290831287/50000000, 3392425717/50000000, 974239231/25000000], ![508384263/12500000, 3895394323/100000000, 1867990021/100000000], ![241324013/50000000, 398479057/100000000, 290577667/100000000]]
def scE57CutWeightFloor : ℚ := 141309177/100000000
def scE57CutMargins : Fin 3 → ℚ := ![14776743/5000000000, 4327627/2000000000, 11827197/10000000000]

theorem scE57Cut_roots_ok : scE57CutCell.rootsOK scE57CutRoots = true := by decide +kernel

theorem scE57Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE57CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE57Cut_margin_le (i : Fin 3) : curvatureLoss scE57CutCell scE57CutCaps i ≤ scE57CutMargins i := by
  fin_cases i <;> decide +kernel

def scE58CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨29/80, 3/8⟩, ⟨3/20, 13/80⟩⟩
def scE58CutRoots : Fin 3 → RatBounds := ![⟨233233957125467/140737488355328, 247862119289539/140737488355328⟩, ⟨373618185699281/281474976710656, 199299033348509/140737488355328⟩, ⟨147171651416097/140737488355328, 320683661390331/281474976710656⟩]
def scE58CutCaps : Fin 3 → Fin 3 → ℚ := ![![336698567/3125000, 864400373/12500000, 3972788439/100000000], ![4140977667/100000000, 990669103/25000000, 950733709/50000000], ![11568797/2500000, 190902587/50000000, 69618687/25000000]]
def scE58CutWeightFloor : ℚ := 143751177/100000000
def scE58CutMargins : Fin 3 → ℚ := ![750883/250000000, 5497893/2500000000, 3004263/2500000000]

theorem scE58Cut_roots_ok : scE58CutCell.rootsOK scE58CutRoots = true := by decide +kernel

theorem scE58Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE58CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE58Cut_margin_le (i : Fin 3) : curvatureLoss scE58CutCell scE58CutCaps i ≤ scE58CutMargins i := by
  fin_cases i <;> decide +kernel

def scE59CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨29/80, 3/8⟩, ⟨13/80, 1/6⟩⟩
def scE59CutRoots : Fin 3 → RatBounds := ![⟨233154740111923/140737488355328, 123567222378235/70368744177664⟩, ⟨93252121043247/70368744177664, 396639674047859/281474976710656⟩, ⟨146869355028475/140737488355328, 318716555267783/281474976710656⟩]
def scE59CutCaps : Fin 3 → Fin 3 → ℚ := ![![5330574217/50000000, 684887783/10000000, 3885324217/100000000], ![4101782011/100000000, 972480233/25000000, 458662051/25000000], ![88005821/25000000, 57834749/20000000, 214827823/100000000]]
def scE59CutWeightFloor : ℚ := 36709843/25000000
def scE59CutMargins : Fin 3 → ℚ := ![28910243/10000000000, 5259243/2500000000, 5609221/5000000000]

theorem scE59Cut_roots_ok : scE59CutCell.rootsOK scE59CutRoots = true := by decide +kernel

theorem scE59Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE59CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE59Cut_margin_le (i : Fin 3) : curvatureLoss scE59CutCell scE59CutCaps i ≤ scE59CutMargins i := by
  fin_cases i <;> decide +kernel

def scE60CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨3/8, 31/80⟩, ⟨1/8, 11/80⟩⟩
def scE60CutRoots : Fin 3 → RatBounds := ![⟨233303310898843/140737488355328, 247858243575013/140737488355328⟩, ⟨186121163787929/140737488355328, 397114954338201/281474976710656⟩, ⟨75244697373333/70368744177664, 327503828639089/281474976710656⟩]
def scE60CutCaps : Fin 3 → Fin 3 → ℚ := ![![4976206367/50000000, 6294950183/100000000, 3738028659/100000000], ![377412167/10000000, 3552705799/100000000, 910006159/50000000], ![500711667/100000000, 2541023/625000, 61448779/20000000]]
def scE60CutWeightFloor : ℚ := 69994067/50000000
def scE60CutMargins : Fin 3 → ℚ := ![2778759/1000000000, 20027773/10000000000, 2291127/2000000000]

theorem scE60Cut_roots_ok : scE60CutCell.rootsOK scE60CutRoots = true := by decide +kernel

theorem scE60Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE60CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE60Cut_margin_le (i : Fin 3) : curvatureLoss scE60CutCell scE60CutCaps i ≤ scE60CutMargins i := by
  fin_cases i <;> decide +kernel

def scE61CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨3/8, 31/80⟩, ⟨11/80, 3/20⟩⟩
def scE61CutRoots : Fin 3 → RatBounds := ![⟨465404167883315/281474976710656, 494425764960333/281474976710656⟩, ⟨23143826563623/17592186044416, 395019792306757/281474976710656⟩, ⟨74761996822367/70368744177664, 325392878162663/281474976710656⟩]
def scE61CutCaps : Fin 3 → Fin 3 → ℚ := ![![10137116911/100000000, 3209286993/50000000, 762583939/20000000], ![1922066189/50000000, 3615241303/100000000, 463299441/25000000], ![479619241/100000000, 389181251/100000000, 294173759/100000000]]
def scE61CutWeightFloor : ℚ := 7122019/5000000
def scE61CutMargins : Fin 3 → ℚ := ![7060971/2500000000, 2544677/1250000000, 5820597/5000000000]

theorem scE61Cut_roots_ok : scE61CutCell.rootsOK scE61CutRoots = true := by decide +kernel

theorem scE61Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE61CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE61Cut_margin_le (i : Fin 3) : curvatureLoss scE61CutCell scE61CutCaps i ≤ scE61CutMargins i := by
  fin_cases i <;> decide +kernel

def scE62CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨3/8, 31/80⟩, ⟨3/20, 13/80⟩⟩
def scE62CutRoots : Fin 3 → RatBounds := ![⟨232121362137497/140737488355328, 493180187403371/281474976710656⟩, ⟨184215432598875/140737488355328, 393002415959283/281474976710656⟩, ⟨148594620677367/140737488355328, 161681075072275/140737488355328⟩]
def scE62CutCaps : Fin 3 → Fin 3 → ℚ := ![![5160824707/50000000, 6541836149/100000000, 777540699/20000000], ![3913966971/100000000, 1838837679/50000000, 1886323829/100000000], ![45981503/10000000, 372875951/100000000, 140954751/50000000]]
def scE62CutWeightFloor : ℚ := 36223623/25000000
def scE62CutMargins : Fin 3 → ℚ := ![5740403/2000000000, 20688257/10000000000, 5914001/5000000000]

theorem scE62Cut_roots_ok : scE62CutCell.rootsOK scE62CutRoots = true := by decide +kernel

theorem scE62Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE62CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE62Cut_margin_le (i : Fin 3) : curvatureLoss scE62CutCell scE62CutCaps i ≤ scE62CutMargins i := by
  fin_cases i <;> decide +kernel

def scE63CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨3/8, 31/80⟩, ⟨13/80, 1/6⟩⟩
def scE63CutRoots : Fin 3 → RatBounds := ![⟨232044794355609/140737488355328, 245867256322961/140737488355328⟩, ⟨45977807714979/35184372088832, 195524116483771/140737488355328⟩, ⟨148292488203361/140737488355328, 160699469292037/140737488355328⟩]
def scE63CutCaps : Fin 3 → Fin 3 → ℚ := ![![10211727269/100000000, 809792869/12500000, 3801957753/100000000], ![775097347/20000000, 3606286233/100000000, 910129067/50000000], ![69916221/20000000, 70519421/25000000, 108536213/50000000]]
def scE63CutWeightFloor : ℚ := 147997253/100000000
def scE63CutMargins : Fin 3 → ℚ := ![13794977/5000000000, 19757757/10000000000, 11027999/10000000000]

theorem scE63Cut_roots_ok : scE63CutCell.rootsOK scE63CutRoots = true := by decide +kernel

theorem scE63Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE63CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE63Cut_margin_le (i : Fin 3) : curvatureLoss scE63CutCell scE63CutCaps i ≤ scE63CutMargins i := by
  fin_cases i <;> decide +kernel

def scE64CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨31/80, 2/5⟩, ⟨1/8, 11/80⟩⟩
def scE64CutRoots : Fin 3 → RatBounds := ![⟨29038575077491/17592186044416, 493459397103035/281474976710656⟩, ⟨183628589991543/140737488355328, 97942058066583/70368744177664⟩, ⟨303879758011757/281474976710656, 165135206520995/140737488355328⟩]
def scE64CutCaps : Fin 3 → Fin 3 → ℚ := ![![9568780487/100000000, 5978329107/100000000, 3672287083/100000000], ![1792848911/50000000, 3307478223/100000000, 906797597/50000000], ![497980413/100000000, 397352329/100000000, 311209807/100000000]]
def scE64CutWeightFloor : ℚ := 141130783/100000000
def scE64CutMargins : Fin 3 → ℚ := ![26664959/10000000000, 9456211/5000000000, 5661223/5000000000]

theorem scE64Cut_roots_ok : scE64CutCell.rootsOK scE64CutRoots = true := by decide +kernel

theorem scE64Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE64CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE64Cut_margin_le (i : Fin 3) : curvatureLoss scE64CutCell scE64CutCaps i ≤ scE64CutMargins i := by
  fin_cases i <;> decide +kernel

def scE65CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨31/80, 2/5⟩, ⟨11/80, 3/20⟩⟩
def scE65CutRoots : Fin 3 → RatBounds := ![⟨231712259476957/140737488355328, 246089755030763/140737488355328⟩, ⟨365319466116977/281474976710656, 194838213005849/140737488355328⟩, ⟨4717969561045/4398046511104, 41020446320895/35184372088832⟩]
def scE65CutCaps : Fin 3 → Fin 3 → ℚ := ![![9746341941/100000000, 6095667473/100000000, 187318969/5000000], ![1826091723/50000000, 3365689413/100000000, 1846566121/100000000], ![372634/78125, 380344243/100000000, 297959481/100000000]]
def scE65CutWeightFloor : ℚ := 143595377/100000000
def scE65CutMargins : Fin 3 → ℚ := ![1355029/500000000, 19222073/10000000000, 5752837/5000000000]

theorem scE65Cut_roots_ok : scE65CutCell.rootsOK scE65CutRoots = true := by decide +kernel

theorem scE65Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE65CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE65Cut_margin_le (i : Fin 3) : curvatureLoss scE65CutCell scE65CutCaps i ≤ scE65CutMargins i := by
  fin_cases i <;> decide +kernel

def scE66CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨31/80, 2/5⟩, ⟨3/20, 13/80⟩⟩
def scE66CutRoots : Fin 3 → RatBounds := ![⟨462272526703077/281474976710656, 245472205703541/140737488355328⟩, ⟨90863123387821/70368744177664, 193831209319653/140737488355328⟩, ⟨300092300557547/281474976710656, 326136722887993/281474976710656⟩]
def scE66CutCaps : Fin 3 → Fin 3 → ℚ := ![![9924556879/100000000, 77659049/1250000, 3820559057/100000000], ![148740037/4000000, 684761613/20000000, 1879480247/100000000], ![228623719/50000000, 182195553/50000000, 285526819/100000000]]
def scE66CutWeightFloor : ℚ := 73030949/50000000
def scE66CutMargins : Fin 3 → ℚ := ![27539659/10000000000, 19533053/10000000000, 11690559/10000000000]

theorem scE66Cut_roots_ok : scE66CutCell.rootsOK scE66CutRoots = true := by decide +kernel

theorem scE66Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE66CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE66Cut_margin_le (i : Fin 3) : curvatureLoss scE66CutCell scE66CutCaps i ≤ scE66CutMargins i := by
  fin_cases i <;> decide +kernel

def scE67CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨31/80, 2/5⟩, ⟨13/80, 1/6⟩⟩
def scE67CutRoots : Fin 3 → RatBounds := ![⟨462124085290973/281474976710656, 489507264793129/281474976710656⟩, ⟨11338913060659/8796093022208, 385711751684021/281474976710656⟩, ⟨299488345967351/281474976710656, 324177100638065/281474976710656⟩]
def scE67CutCaps : Fin 3 → Fin 3 → ℚ := ![![4908312241/50000000, 1230335913/20000000, 747072901/20000000], ![3680661719/100000000, 1676824233/50000000, 362809117/20000000], ![347450731/100000000, 1075672/390625, 219481193/100000000]]
def scE67CutWeightFloor : ℚ := 149179549/100000000
def scE67CutMargins : Fin 3 → ℚ := ![26437289/10000000000, 9312427/5000000000, 10886323/10000000000]

theorem scE67Cut_roots_ok : scE67CutCell.rootsOK scE67CutRoots = true := by decide +kernel

theorem scE67Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE67CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE67Cut_margin_le (i : Fin 3) : curvatureLoss scE67CutCell scE67CutCaps i ≤ scE67CutMargins i := by
  fin_cases i <;> decide +kernel

def scE68CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨2/5, 33/80⟩, ⟨1/8, 11/80⟩⟩
def scE68CutRoots : Fin 3 → RatBounds := ![⟨462874116313641/281474976710656, 491499034021851/281474976710656⟩, ⟨181233364323651/140737488355328, 96664923913119/70368744177664⟩, ⟨38355310764069/35184372088832, 166568323593813/140737488355328⟩]
def scE68CutCaps : Fin 3 → Fin 3 → ℚ := ![![4615828057/50000000, 2849374443/50000000, 361994511/10000000], ![26751561/781250, 24706427/800000, 453704749/25000000], ![61952017/12500000, 388577777/100000000, 315371307/100000000]]
def scE68CutWeightFloor : ℚ := 1422989/1000000
def scE68CutMargins : Fin 3 → ℚ := ![25686469/10000000000, 17921153/10000000000, 5615367/5000000000]

theorem scE68Cut_roots_ok : scE68CutCell.rootsOK scE68CutRoots = true := by decide +kernel

theorem scE68Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE68CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE68Cut_margin_le (i : Fin 3) : curvatureLoss scE68CutCell scE68CutCaps i ≤ scE68CutMargins i := by
  fin_cases i <;> decide +kernel

def scE69CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨2/5, 33/80⟩, ⟨11/80, 3/20⟩⟩
def scE69CutRoots : Fin 3 → RatBounds := ![⟨230844994636701/140737488355328, 7659822166029/4398046511104⟩, ⟨45066489261225/35184372088832, 192285285875821/140737488355328⟩, ⟨38114225743571/35184372088832, 331033590713129/281474976710656⟩]
def scE69CutCaps : Fin 3 → Fin 3 → ℚ := ![![2350784019/25000000, 2905263001/50000000, 3693576211/100000000], ![3487648743/100000000, 1571326007/50000000, 923853617/50000000], ![237339677/50000000, 46491027/12500000, 301933417/100000000]]
def scE69CutWeightFloor : ℚ := 18097021/12500000
def scE69CutMargins : Fin 3 → ℚ := ![26104423/10000000000, 18213099/10000000000, 11412533/10000000000]

theorem scE69Cut_roots_ok : scE69CutCell.rootsOK scE69CutRoots = true := by decide +kernel

theorem scE69Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE69CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE69Cut_margin_le (i : Fin 3) : curvatureLoss scE69CutCell scE69CutCaps i ≤ scE69CutMargins i := by
  fin_cases i <;> decide +kernel

def scE70CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨2/5, 33/80⟩, ⟨3/20, 13/80⟩⟩
def scE70CutRoots : Fin 3 → RatBounds := ![⟨115136567936227/70368744177664, 244501340116407/140737488355328⟩, ⟨179333926319323/140737488355328, 382559279716557/281474976710656⟩, ⟨303056979000821/281474976710656, 329010310695749/281474976710656⟩]
def scE70CutCaps : Fin 3 → Fin 3 → ℚ := ![![4787841273/50000000, 185064449/3125000, 3767458223/100000000], ![355093647/10000000, 639383203/20000000, 1880540851/100000000], ![455024467/100000000, 1425249/400000, 144662693/50000000]]
def scE70CutWeightFloor : ℚ := 73627711/50000000
def scE70CutMargins : Fin 3 → ℚ := ![3315831/1250000000, 4626607/2500000000, 11596337/10000000000]

theorem scE70Cut_roots_ok : scE70CutCell.rootsOK scE70CutRoots = true := by decide +kernel

theorem scE70Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE70CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE70Cut_margin_le (i : Fin 3) : curvatureLoss scE70CutCell scE70CutCaps i ≤ scE70CutMargins i := by
  fin_cases i <;> decide +kernel

def scE71CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨2/5, 33/80⟩, ⟨13/80, 1/6⟩⟩
def scE71CutRoots : Fin 3 → RatBounds := ![⟨460401937453081/281474976710656, 243786482221781/140737488355328⟩, ⟨358061549037909/281474976710656, 380611487879557/281474976710656⟩, ⟨151226655694145/140737488355328, 327053971825237/281474976710656⟩]
def scE71CutCaps : Fin 3 → Fin 3 → ℚ := ![![1893921669/20000000, 1172663481/20000000, 3683419857/100000000], ![1756833729/50000000, 390982641/12500000, 907813243/50000000], ![345609963/100000000, 67255541/25000000, 55512987/25000000]]
def scE71CutWeightFloor : ℚ := 150388319/100000000
def scE71CutMargins : Fin 3 → ℚ := ![25432963/10000000000, 8809639/5000000000, 5394257/5000000000]

theorem scE71Cut_roots_ok : scE71CutCell.rootsOK scE71CutRoots = true := by decide +kernel

theorem scE71Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE71CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE71Cut_margin_le (i : Fin 3) : curvatureLoss scE71CutCell scE71CutCaps i ≤ scE71CutMargins i := by
  fin_cases i <;> decide +kernel

def scE72CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨33/80, 17/40⟩, ⟨1/8, 11/80⟩⟩
def scE72CutRoots : Fin 3 → RatBounds := ![⟨57670983089811/35184372088832, 122455821848393/70368744177664⟩, ⟨89464282273465/70368744177664, 190886223619535/140737488355328⟩, ⟨77467903262085/70368744177664, 168052969208545/140737488355328⟩]
def scE72CutCaps : Fin 3 → Fin 3 → ℚ := ![![2234034527/25000000, 5451792627/100000000, 3580137489/100000000], ![3286761353/100000000, 57836437/2000000, 72937597/4000000], ![493596697/100000000, 380203813/100000000, 63945689/20000000]]
def scE72CutWeightFloor : ℚ := 143494491/100000000
def scE72CutMargins : Fin 3 → ℚ := ![24836907/10000000000, 4259677/2500000000, 2794583/2500000000]

theorem scE72Cut_roots_ok : scE72CutCell.rootsOK scE72CutRoots = true := by decide +kernel

theorem scE72Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE72CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE72Cut_margin_le (i : Fin 3) : curvatureLoss scE72CutCell scE72CutCaps i ≤ scE72CutMargins i := by
  fin_cases i <;> decide +kernel

def scE73CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨33/80, 17/40⟩, ⟨11/80, 3/20⟩⟩
def scE73CutRoots : Fin 3 → RatBounds := ![⟨460191114336183/281474976710656, 244280513436063/140737488355328⟩, ⟨88981191355915/70368744177664, 379685381510443/281474976710656⟩, ⟨153971935178505/140737488355328, 20875396451151/17592186044416⟩]
def scE73CutCaps : Fin 3 → Fin 3 → ℚ := ![![9102824273/100000000, 5558666769/100000000, 730743939/20000000], ![836902291/25000000, 294271003/10000000, 1856372751/100000000], ![3781771/800000, 181949139/50000000, 306095669/100000000]]
def scE73CutWeightFloor : ℚ := 9124049/6250000
def scE73CutMargins : Fin 3 → ℚ := ![25240537/10000000000, 17314991/10000000000, 11359743/10000000000]

theorem scE73Cut_roots_ok : scE73CutCell.rootsOK scE73CutRoots = true := by decide +kernel

theorem scE73Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE73CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE73Cut_margin_le (i : Fin 3) : curvatureLoss scE73CutCell scE73CutCaps i ≤ scE73CutMargins i := by
  fin_cases i <;> decide +kernel

def scE74CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨33/80, 17/40⟩, ⟨3/20, 13/80⟩⟩
def scE74CutRoots : Fin 3 → RatBounds := ![⟨459054531480635/281474976710656, 243671487654951/140737488355328⟩, ⟨354063178636163/281474976710656, 188838099434199/140737488355328⟩, ⟨306087879931439/281474976710656, 82996578867317/70368744177664⟩]
def scE74CutCaps : Fin 3 → Fin 3 → ℚ := ![![1158739023/12500000, 5665253431/100000000, 3727330949/100000000], ![426037723/12500000, 2993520581/100000000, 1889252751/100000000], ![11328137/2500000, 348605743/100000000, 146652673/50000000]]
def scE74CutWeightFloor : ℚ := 148477123/100000000
def scE74CutMargins : Fin 3 → ℚ := ![6411787/2500000000, 17592539/10000000000, 11542753/10000000000]

theorem scE74Cut_roots_ok : scE74CutCell.rootsOK scE74CutRoots = true := by decide +kernel

theorem scE74Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE74CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE74Cut_margin_le (i : Fin 3) : curvatureLoss scE74CutCell scE74CutCaps i ≤ scE74CutMargins i := by
  fin_cases i <;> decide +kernel

def scE75CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨33/80, 17/40⟩, ⟨13/80, 1/6⟩⟩
def scE75CutRoots : Fin 3 → RatBounds := ![⟨458913732048151/281474976710656, 485919634339433/281474976710656⟩, ⟨176728852071845/140737488355328, 375730687890221/281474976710656⟩, ⟨305484470149151/281474976710656, 165016475609631/140737488355328⟩]
def scE75CutCaps : Fin 3 → Fin 3 → ℚ := ![![9165506799/100000000, 1402154973/25000000, 1822159281/50000000], ![337153527/10000000, 365681653/12500000, 1824753223/100000000], ![43005029/12500000, 65749459/25000000, 224783893/100000000]]
def scE75CutWeightFloor : ℚ := 30325131/20000000
def scE75CutMargins : Fin 3 → ℚ := ![1535067/625000000, 8362593/5000000000, 10730563/10000000000]

theorem scE75Cut_roots_ok : scE75CutCell.rootsOK scE75CutRoots = true := by decide +kernel

theorem scE75Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE75CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE75Cut_margin_le (i : Fin 3) : curvatureLoss scE75CutCell scE75CutCaps i ≤ scE75CutMargins i := by
  fin_cases i <;> decide +kernel

def scE76CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨17/40, 7/16⟩, ⟨1/8, 11/80⟩⟩
def scE76CutRoots : Fin 3 → RatBounds := ![⟨460090424613327/281474976710656, 30526378296157/17592186044416⟩, ⟨353415815720613/281474976710656, 377091340001895/281474976710656⟩, ⟨312971922866589/281474976710656, 169591089126627/140737488355328⟩]
def scE76CutCaps : Fin 3 → Fin 3 → ℚ := ![![1735641087/20000000, 5233776743/100000000, 3552216511/100000000], ![3171053967/100000000, 2715206921/100000000, 183933443/10000000], ![98380747/20000000, 11631207/3125000, 162141383/50000000]]
def scE76CutWeightFloor : ℚ := 144719613/100000000
def scE76CutMargins : Fin 3 → ℚ := ![4820767/2000000000, 1625231/1000000000, 5581869/5000000000]

theorem scE76Cut_roots_ok : scE76CutCell.rootsOK scE76CutRoots = true := by decide +kernel

theorem scE76Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE76CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE76Cut_margin_le (i : Fin 3) : curvatureLoss scE76CutCell scE76CutCaps i ≤ scE76CutMargins i := by
  fin_cases i <;> decide +kernel

def scE77CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨17/40, 7/16⟩, ⟨11/80, 3/20⟩⟩
def scE77CutRoots : Fin 3 → RatBounds := ![⟨458919904212813/281474976710656, 121791667360129/70368744177664⟩, ⟨351485491737387/281474976710656, 187502875959131/140737488355328⟩, ⟨311045011109367/281474976710656, 42135714335151/35184372088832⟩]
def scE77CutCaps : Fin 3 → Fin 3 → ℚ := ![![276271773/3125000, 5336284447/100000000, 3625948293/100000000], ![3229693171/100000000, 2762986541/100000000, 468109149/25000000], ![235539931/50000000, 356223773/100000000, 310447773/100000000]]
def scE77CutWeightFloor : ℚ := 147223311/100000000
def scE77CutMargins : Fin 3 → ℚ := ![24495059/10000000000, 16514639/10000000000, 11345377/10000000000]

theorem scE77Cut_roots_ok : scE77CutCell.rootsOK scE77CutRoots = true := by decide +kernel

theorem scE77Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE77CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE77Cut_margin_le (i : Fin 3) : curvatureLoss scE77CutCell scE77CutCaps i ≤ scE77CutMargins i := by
  fin_cases i <;> decide +kernel


end HlawkaSchatten.BelowExponent.Vertex
