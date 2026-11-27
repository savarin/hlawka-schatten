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

def scD20CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨5/16, 13/40⟩, ⟨1/10, 9/80⟩⟩
def scD20CutRoots : Fin 3 → RatBounds := ![⟨483389599341941/281474976710656, 514939050768673/281474976710656⟩, ⟨404852879268519/281474976710656, 6760530143189/4398046511104⟩, ⟨291351339586741/281474976710656, 319617474512113/281474976710656⟩]
def scD20CutCaps : Fin 3 → Fin 3 → ℚ := ![![12365464909/100000000, 4161574281/50000000, 83858729/2000000], ![2539343073/50000000, 5154524607/100000000, 956357821/50000000], ![71105119/12500000, 252004011/50000000, 317570177/100000000]]
def scD20CutWeightFloor : ℚ := 5192169/4000000
def scD20CutMargins : Fin 3 → ℚ := ![17590813/5000000000, 6826993/2500000000, 3136339/2500000000]

theorem scD20Cut_roots_ok : scD20CutCell.rootsOK scD20CutRoots = true := by decide +kernel

theorem scD20Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD20CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD20Cut_margin_le (i : Fin 3) : curvatureLoss scD20CutCell scD20CutCaps i ≤ scD20CutMargins i := by
  fin_cases i <;> decide +kernel

def scD21CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨5/16, 13/40⟩, ⟨9/80, 1/8⟩⟩
def scD21CutRoots : Fin 3 → RatBounds := ![⟨241012229643027/140737488355328, 64183486384481/35184372088832⟩, ⟨100682757505693/70368744177664, 215189628806083/140737488355328⟩, ⟨36157033584811/35184372088832, 317302762959249/281474976710656⟩]
def scD21CutCaps : Fin 3 → Fin 3 → ℚ := ![![12604903233/100000000, 8494390083/100000000, 2138241347/50000000], ![207080143/4000000, 524909727/10000000, 974748649/50000000], ![544137413/100000000, 96343299/20000000, 60714133/20000000]]
def scD21CutWeightFloor : ℚ := 16524399/12500000
def scD21CutMargins : Fin 3 → ℚ := ![1118533/312500000, 13891801/5000000000, 12753029/10000000000]

theorem scD21Cut_roots_ok : scD21CutCell.rootsOK scD21CutRoots = true := by decide +kernel

theorem scD21Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD21CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD21Cut_margin_le (i : Fin 3) : curvatureLoss scD21CutCell scD21CutCaps i ≤ scD21CutMargins i := by
  fin_cases i <;> decide +kernel

def scD22CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨13/40, 27/80⟩, ⟨1/10, 9/80⟩⟩
def scD22CutRoots : Fin 3 → RatBounds := ![⟨239963089932865/140737488355328, 255444153124827/140737488355328⟩, ⟨199306701424667/140737488355328, 425784639138699/281474976710656⟩, ⟨294008433419057/281474976710656, 321907667613907/281474976710656⟩]
def scD22CutCaps : Fin 3 → Fin 3 → ℚ := ![![2329502757/20000000, 7738881143/100000000, 100511899/2500000], ![1174652543/25000000, 4715172361/100000000, 232607441/12500000], ![563428113/100000000, 490799731/100000000, 320811407/100000000]]
def scD22CutWeightFloor : ℚ := 130827077/100000000
def scD22CutMargins : Fin 3 → ℚ := ![33026469/10000000000, 25282917/10000000000, 12113569/10000000000]

theorem scD22Cut_roots_ok : scD22CutCell.rootsOK scD22CutRoots = true := by decide +kernel

theorem scD22Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD22CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD22Cut_margin_le (i : Fin 3) : curvatureLoss scD22CutCell scD22CutCaps i ≤ scD22CutMargins i := by
  fin_cases i <;> decide +kernel

def scD23CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨13/40, 27/80⟩, ⟨9/80, 1/8⟩⟩
def scD23CutRoots : Fin 3 → RatBounds := ![⟨478578893700371/281474976710656, 509437163795957/281474976710656⟩, ⟨99124589813405/70368744177664, 423497921242181/281474976710656⟩, ⟨145957356925019/140737488355328, 159799667443407/140737488355328⟩]
def scD23CutCaps : Fin 3 → Fin 3 → ℚ := ![![371024607/3125000, 7898179817/100000000, 2050671993/50000000], ![4789610913/100000000, 2400834513/50000000, 29634341/1562500], ![67362173/12500000, 469052169/100000000, 306649729/100000000]]
def scD23CutWeightFloor : ℚ := 26645809/20000000
def scD23CutMargins : Fin 3 → ℚ := ![33596281/10000000000, 2572051/1000000000, 1539207/1250000000]

theorem scD23Cut_roots_ok : scD23CutCell.rootsOK scD23CutRoots = true := by decide +kernel

theorem scD23Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD23CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD23Cut_margin_le (i : Fin 3) : curvatureLoss scD23CutCell scD23CutCaps i ≤ scD23CutMargins i := by
  fin_cases i <;> decide +kernel

def scD24CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨27/80, 7/20⟩, ⟨1/10, 9/80⟩⟩
def scD24CutRoots : Fin 3 → RatBounds := ![⟨476788731704999/281474976710656, 507238459698157/281474976710656⟩, ⟨98166594275523/70368744177664, 209628727862577/140737488355328⟩, ⟨296704662253685/281474976710656, 324288461984903/281474976710656⟩]
def scD24CutCaps : Fin 3 → Fin 3 → ℚ := ![![11022476521/100000000, 7229282713/100000000, 484691097/12500000], ![4371082443/100000000, 433052951/10000000, 182008051/10000000], ![558611627/100000000, 239181809/50000000, 162146861/50000000]]
def scD24CutWeightFloor : ℚ := 16483137/12500000
def scD24CutMargins : Fin 3 → ℚ := ![3894573/1250000000, 23512063/10000000000, 1176153/1000000000]

theorem scD24Cut_roots_ok : scD24CutCell.rootsOK scD24CutRoots = true := by decide +kernel

theorem scD24Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD24CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD24Cut_margin_le (i : Fin 3) : curvatureLoss scD24CutCell scD24CutCaps i ≤ scD24CutMargins i := by
  fin_cases i <;> decide +kernel

def scD25CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨27/80, 7/20⟩, ⟨9/80, 1/8⟩⟩
def scD25CutRoots : Fin 3 → RatBounds := ![⟨118864418386903/70368744177664, 252902731498129/140737488355328⟩, ⟨390557317474245/281474976710656, 416977585816611/281474976710656⟩, ⟨2301658878147/2199023255552, 160993069108909/140737488355328⟩]
def scD25CutCaps : Fin 3 → Fin 3 → ℚ := ![![11235837483/100000000, 7378132021/100000000, 1978457929/50000000], ![2227883119/50000000, 2204944639/50000000, 1854935603/100000000], ![534233871/100000000, 457130907/100000000, 61992019/20000000]]
def scD25CutWeightFloor : ℚ := 134278247/100000000
def scD25CutMargins : Fin 3 → ℚ := ![3169109/1000000000, 23916313/10000000000, 1494583/1250000000]

theorem scD25Cut_roots_ok : scD25CutCell.rootsOK scD25CutRoots = true := by decide +kernel

theorem scD25Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD25CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD25Cut_margin_le (i : Fin 3) : curvatureLoss scD25CutCell scD25CutCaps i ≤ scD25CutMargins i := by
  fin_cases i <;> decide +kernel

def scD26CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨7/20, 29/80⟩, ⟨1/10, 9/80⟩⟩
def scD26CutRoots : Fin 3 → RatBounds := ![⟨59244636380923/35184372088832, 503962600787435/281474976710656⟩, ⟨386987892108341/281474976710656, 413061489799927/281474976710656⟩, ⟨149722329417185/140737488355328, 326760774485949/281474976710656⟩]
def scD26CutCaps : Fin 3 → Fin 3 → ℚ := ![![2095921991/20000000, 3391578537/50000000, 1882237033/50000000], ![4088369803/100000000, 998015993/25000000, 1789162367/100000000], ![277167863/50000000, 466620979/100000000, 82001663/25000000]]
def scD26CutWeightFloor : ℚ := 132920269/100000000
def scD26CutMargins : Fin 3 → ℚ := ![29535773/10000000000, 21956723/10000000000, 2297517/2000000000]

theorem scD26Cut_roots_ok : scD26CutCell.rootsOK scD26CutRoots = true := by decide +kernel

theorem scD26Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD26CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD26Cut_margin_le (i : Fin 3) : curvatureLoss scD26CutCell scD26CutCaps i ≤ scD26CutMargins i := by
  fin_cases i <;> decide +kernel

def scD27CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨7/20, 29/80⟩, ⟨9/80, 1/8⟩⟩
def scD27CutRoots : Fin 3 → RatBounds := ![⟨29540044961595/17592186044416, 502545986975617/281474976710656⟩, ⟨384884070195389/281474976710656, 410787461857805/281474976710656⟩, ⟨148676871836273/140737488355328, 81116025465193/70368744177664⟩]
def scD27CutCaps : Fin 3 → Fin 3 → ℚ := ![![1335285637/12500000, 6922827107/100000000, 3842212487/100000000], ![833517711/20000000, 2032598061/50000000, 1823345063/100000000], ![530093109/100000000, 445877009/100000000, 313491781/100000000]]
def scD27CutWeightFloor : ℚ := 135344817/100000000
def scD27CutMargins : Fin 3 → ℚ := ![15019499/5000000000, 22331837/10000000000, 11677831/10000000000]

theorem scD27Cut_roots_ok : scD27CutCell.rootsOK scD27CutRoots = true := by decide +kernel

theorem scD27Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD27CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD27Cut_margin_le (i : Fin 3) : curvatureLoss scD27CutCell scD27CutCaps i ≤ scD27CutMargins i := by
  fin_cases i <;> decide +kernel

def scD28CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨29/80, 3/8⟩, ⟨1/10, 9/80⟩⟩
def scD28CutRoots : Fin 3 → RatBounds := ![⟨471413778096547/281474976710656, 501037611498983/281474976710656⟩, ⟨381556656678591/281474976710656, 407169542811613/281474976710656⟩, ⟨151116481071073/140737488355328, 164663030595217/140737488355328⟩]
def scD28CutCaps : Fin 3 → Fin 3 → ℚ := ![![10002369127/100000000, 319569397/5000000, 3668346311/100000000], ![1922108271/50000000, 1846430567/50000000, 1767174173/100000000], ![550553253/100000000, 455503977/100000000, 331942301/100000000]]
def scD28CutWeightFloor : ℚ := 133994529/100000000
def scD28CutMargins : Fin 3 → ℚ := ![7029853/2500000000, 1286591/625000000, 176009/156250000]

theorem scD28Cut_roots_ok : scD28CutCell.rootsOK scD28CutRoots = true := by decide +kernel

theorem scD28Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD28CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD28Cut_margin_le (i : Fin 3) : curvatureLoss scD28CutCell scD28CutCaps i ≤ scD28CutMargins i := by
  fin_cases i <;> decide +kernel

def scD29CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨29/80, 3/8⟩, ⟨9/80, 1/8⟩⟩
def scD29CutRoots : Fin 3 → RatBounds := ![⟨470110624721455/281474976710656, 499635711316247/281474976710656⟩, ⟨379457393243069/281474976710656, 404900437933409/281474976710656⟩, ⟨18758965695365/17592186044416, 163517345172811/140737488355328⟩]
def scD29CutCaps : Fin 3 → Fin 3 → ℚ := ![![509784009/5000000, 652296669/10000000, 149789871/4000000], ![979675629/25000000, 3760491293/100000000, 1800845911/100000000], ![131607409/25000000, 217612611/50000000, 317237273/100000000]]
def scD29CutWeightFloor : ℚ := 68215359/50000000
def scD29CutMargins : Fin 3 → ℚ := ![28595337/10000000000, 20934929/10000000000, 286271/250000000]

theorem scD29Cut_roots_ok : scD29CutCell.rootsOK scD29CutRoots = true := by decide +kernel

theorem scD29Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD29CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD29Cut_margin_le (i : Fin 3) : curvatureLoss scD29CutCell scD29CutCaps i ≤ scD29CutMargins i := by
  fin_cases i <;> decide +kernel

def scD30CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨3/8, 31/80⟩, ⟨1/10, 9/80⟩⟩
def scD30CutRoots : Fin 3 → RatBounds := ![⟨234571829292875/140737488355328, 498443652706145/281474976710656⟩, ⟨47044204034905/35184372088832, 200778781790817/140737488355328⟩, ⟨152537037079933/140737488355328, 41498285757349/35184372088832⟩]
def scD30CutCaps : Fin 3 → Fin 3 → ℚ := ![![9582433787/100000000, 3023261401/50000000, 717558967/20000000], ![3633538457/100000000, 1713657151/50000000, 1753454153/100000000], ![136806077/25000000, 444953859/100000000, 42011879/12500000]]
def scD30CutWeightFloor : ℚ := 67544893/50000000
def scD30CutMargins : Fin 3 → ℚ := ![6720311/2500000000, 19372639/10000000000, 11088563/10000000000]

theorem scD30Cut_roots_ok : scD30CutCell.rootsOK scD30CutRoots = true := by decide +kernel

theorem scD30Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD30CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD30Cut_margin_le (i : Fin 3) : curvatureLoss scD30CutCell scD30CutCaps i ≤ scD30CutMargins i := by
  fin_cases i <;> decide +kernel

def scD31CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨3/8, 31/80⟩, ⟨9/80, 1/8⟩⟩
def scD31CutRoots : Fin 3 → RatBounds := ![⟨58481539860019/35184372088832, 7766482460237/4398046511104⟩, ⟨23391144243815/17592186044416, 399292539315509/281474976710656⟩, ⟨151492969348079/140737488355328, 329699872906185/281474976710656⟩]
def scD31CutCaps : Fin 3 → Fin 3 → ℚ := ![![1220940459/12500000, 6170941927/100000000, 3663007427/100000000], ![462990827/12500000, 1745032429/50000000, 893382617/50000000], ![104640997/20000000, 106279757/25000000, 321191221/100000000]]
def scD31CutWeightFloor : ℚ := 137537887/100000000
def scD31CutMargins : Fin 3 → ℚ := ![427083/156250000, 3939893/2000000000, 5635707/5000000000]

theorem scD31Cut_roots_ok : scD31CutCell.rootsOK scD31CutRoots = true := by decide +kernel

theorem scD31Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD31CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD31Cut_margin_le (i : Fin 3) : curvatureLoss scD31CutCell scD31CutCaps i ≤ scD31CutMargins i := by
  fin_cases i <;> decide +kernel

def scD32CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨31/80, 2/5⟩, ⟨1/10, 9/80⟩⟩
def scD32CutRoots : Fin 3 → RatBounds := ![⟨233566832599171/140737488355328, 124040936773859/70368744177664⟩, ⟨371361727104577/281474976710656, 396204201081507/281474976710656⟩, ⟨38496563796903/35184372088832, 167371950883329/140737488355328⟩]
def scD32CutCaps : Fin 3 → Fin 3 → ℚ := ![![9213118061/100000000, 574252197/10000000, 1761777133/50000000], ![345219033/10000000, 99711373/3125000, 349494907/20000000], ![136078791/25000000, 108729881/25000000, 170230613/50000000]]
def scD32CutWeightFloor : ℚ := 6810397/5000000
def scD32CutMargins : Fin 3 → ℚ := ![25800047/10000000000, 18297277/10000000000, 5479971/5000000000]

theorem scD32Cut_roots_ok : scD32CutCell.rootsOK scD32CutRoots = true := by decide +kernel

theorem scD32Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD32CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD32Cut_margin_le (i : Fin 3) : curvatureLoss scD32CutCell scD32CutCaps i ≤ scD32CutMargins i := by
  fin_cases i <;> decide +kernel

def scD33CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨31/80, 2/5⟩, ⟨9/80, 1/8⟩⟩
def scD33CutRoots : Fin 3 → RatBounds := ![⟨116463197385109/70368744177664, 494786577223425/281474976710656⟩, ⟨23079360999873/17592186044416, 196971241140859/140737488355328⟩, ⟨152942850462203/140737488355328, 332462104618357/281474976710656⟩]
def scD33CutCaps : Fin 3 → Fin 3 → ℚ := ![![1173880279/12500000, 5860621121/100000000, 224875979/6250000], ![140761449/4000000, 1624585481/50000000, 1780565387/100000000], ![520386641/100000000, 83101853/20000000, 325350213/100000000]]
def scD33CutWeightFloor : ℚ := 138668253/100000000
def scD33CutMargins : Fin 3 → ℚ := ![13115689/5000000000, 3720821/2000000000, 11140491/10000000000]

theorem scD33Cut_roots_ok : scD33CutCell.rootsOK scD33CutRoots = true := by decide +kernel

theorem scD33Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD33CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD33Cut_margin_le (i : Fin 3) : curvatureLoss scD33CutCell scD33CutCaps i ≤ scD33CutMargins i := by
  fin_cases i <;> decide +kernel

def scD34CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨2/5, 33/80⟩, ⟨1/10, 9/80⟩⟩
def scD34CutRoots : Fin 3 → RatBounds := ![⟨14542892748885/8796093022208, 494183439692753/281474976710656⟩, ⟨366565538822657/281474976710656, 391090433868899/281474976710656⟩, ⟨310932845870437/281474976710656, 337601840891465/281474976710656⟩]
def scD34CutCaps : Fin 3 → Fin 3 → ℚ := ![![8888506709/100000000, 5474139213/100000000, 1736110433/50000000], ![3296787939/100000000, 2327609/78125, 1748870879/100000000], ![270898701/50000000, 212678179/50000000, 345039107/100000000]]
def scD34CutWeightFloor : ℚ := 137350911/100000000
def scD34CutMargins : Fin 3 → ℚ := ![12428801/5000000000, 693659/400000000, 217427/200000000]

theorem scD34Cut_roots_ok : scD34CutCell.rootsOK scD34CutRoots = true := by decide +kernel

theorem scD34Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD34CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD34Cut_margin_le (i : Fin 3) : curvatureLoss scD34CutCell scD34CutCaps i ≤ scD34CutMargins i := by
  fin_cases i <;> decide +kernel

def scD35CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨2/5, 33/80⟩, ⟨9/80, 1/8⟩⟩
def scD35CutRoots : Fin 3 → RatBounds := ![⟨464100854053029/281474976710656, 1925064119889/1099511627776⟩, ⟨364476443506885/281474976710656, 388831304807955/281474976710656⟩, ⟨38605911592089/35184372088832, 83831079454305/70368744177664⟩]
def scD35CutCaps : Fin 3 → Fin 3 → ℚ := ![![566260501/6250000, 5586630883/100000000, 3546177649/100000000], ![3360582189/100000000, 1516933483/50000000, 178187421/10000000], ![517947207/100000000, 406353009/100000000, 82428151/25000000]]
def scD35CutWeightFloor : ℚ := 69911881/50000000
def scD35CutMargins : Fin 3 → ℚ := ![12635447/5000000000, 17630569/10000000000, 5525161/5000000000]

theorem scD35Cut_roots_ok : scD35CutCell.rootsOK scD35CutRoots = true := by decide +kernel

theorem scD35Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD35CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD35Cut_margin_le (i : Fin 3) : curvatureLoss scD35CutCell scD35CutCaps i ≤ scD35CutMargins i := by
  fin_cases i <;> decide +kernel

def scD36CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨33/80, 17/40⟩, ⟨1/10, 9/80⟩⟩
def scD36CutRoots : Fin 3 → RatBounds := ![⟨231925392555281/140737488355328, 246245260815923/140737488355328⟩, ⟨180975568481915/140737488355328, 386199261248219/281474976710656⟩, ⟨78489939623571/70368744177664, 170281758109869/140737488355328⟩]
def scD36CutCaps : Fin 3 → Fin 3 → ℚ := ![![8603885777/100000000, 5237128107/100000000, 686590761/20000000], ![3164571037/100000000, 1394900683/50000000, 1757408563/100000000], ![539647217/100000000, 325176/78125, 87457151/25000000]]
def scD36CutWeightFloor : ℚ := 138520649/100000000
def scD36CutMargins : Fin 3 → ℚ := ![12019633/5000000000, 16490537/10000000000, 5410343/5000000000]

theorem scD36Cut_roots_ok : scD36CutCell.rootsOK scD36CutRoots = true := by decide +kernel

theorem scD36Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD36CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD36Cut_margin_le (i : Fin 3) : curvatureLoss scD36CutCell scD36CutCaps i ≤ scD36CutMargins i := by
  fin_cases i <;> decide +kernel

def scD37CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨33/80, 17/40⟩, ⟨9/80, 1/8⟩⟩
def scD37CutRoots : Fin 3 → RatBounds := ![⟨462586971050583/281474976710656, 15347882219179/8796093022208⟩, ⟨179932211828147/140737488355328, 191971029385369/140737488355328⟩, ⟨311875372342863/281474976710656, 338289922568775/281474976710656⟩]
def scD37CutCaps : Fin 3 → Fin 3 → ℚ := ![![8770093173/100000000, 83509991/1562500, 3506640329/100000000], ![201609449/6250000, 1420426629/50000000, 1398791/78125], ![103172747/20000000, 397612653/100000000, 33427839/10000000]]
def scD37CutWeightFloor : ℚ := 17625799/12500000
def scD37CutMargins : Fin 3 → ℚ := ![2443693/1000000000, 8381939/5000000000, 2749693/2500000000]

theorem scD37Cut_roots_ok : scD37CutCell.rootsOK scD37CutRoots = true := by decide +kernel

theorem scD37Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD37CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD37Cut_margin_le (i : Fin 3) : curvatureLoss scD37CutCell scD37CutCaps i ≤ scD37CutMargins i := by
  fin_cases i <;> decide +kernel

def scD38CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨17/40, 7/16⟩, ⟨1/10, 9/80⟩⟩
def scD38CutRoots : Fin 3 → RatBounds := ![⟨462560227695315/281474976710656, 245537403052015/140737488355328⟩, ⟨178752938892451/140737488355328, 190757722257131/140737488355328⟩, ⟨317058070363017/281474976710656, 343632829372981/281474976710656⟩]
def scD38CutCaps : Fin 3 → Fin 3 → ℚ := ![![8355354089/100000000, 628493179/12500000, 340511879/10000000], ![381662191/12500000, 523884691/20000000, 177296913/10000000], ![537844863/100000000, 10187299/2500000, 88707817/25000000]]
def scD38CutWeightFloor : ℚ := 69859579/50000000
def scD38CutMargins : Fin 3 → ℚ := ![23333001/10000000000, 15732151/10000000000, 10806483/10000000000]

theorem scD38Cut_roots_ok : scD38CutCell.rootsOK scD38CutRoots = true := by decide +kernel

theorem scD38Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD38CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD38Cut_margin_le (i : Fin 3) : curvatureLoss scD38CutCell scD38CutCaps i ≤ scD38CutMargins i := by
  fin_cases i <;> decide +kernel

def scD39CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨17/40, 7/16⟩, ⟨9/80, 1/8⟩⟩
def scD39CutRoots : Fin 3 → RatBounds := ![⟨230651542853405/140737488355328, 244861940625583/140737488355328⟩, ⟨177710556205051/140737488355328, 94814888014481/70368744177664⟩, ⟨314974742492169/281474976710656, 341362815404109/281474976710656⟩]
def scD39CutCaps : Fin 3 → Fin 3 → ℚ := ![![4258419601/50000000, 1026206427/20000000, 3478760929/100000000], ![622451573/20000000, 666838353/25000000, 361235837/20000000], ![514117187/100000000, 194627581/50000000, 339049119/100000000]]
def scD39CutWeightFloor : ℚ := 142218173/100000000
def scD39CutMargins : Fin 3 → ℚ := ![741163/312500000, 7995743/5000000000, 5492177/5000000000]

theorem scD39Cut_roots_ok : scD39CutCell.rootsOK scD39CutRoots = true := by decide +kernel

theorem scD39Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD39CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD39Cut_margin_le (i : Fin 3) : curvatureLoss scD39CutCell scD39CutCaps i ≤ scD39CutMargins i := by
  fin_cases i <;> decide +kernel

def scD40CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨7/16, 9/20⟩, ⟨1/10, 9/80⟩⟩
def scD40CutRoots : Fin 3 → RatBounds := ![⟨230747086400031/140737488355328, 61240993494459/35184372088832⟩, ⟨353218245877483/281474976710656, 188512644567619/140737488355328⟩, ⟨80058197191269/70368744177664, 346814187303219/281474976710656⟩]
def scD40CutCaps : Fin 3 → Fin 3 → ℚ := ![![8139693379/100000000, 2421814729/50000000, 338826493/10000000], ![1480580863/50000000, 2465901457/100000000, 897771057/50000000], ![134093551/25000000, 99781543/25000000, 45006277/12500000]]
def scD40CutWeightFloor : ℚ := 140948509/100000000
def scD40CutMargins : Fin 3 → ℚ := ![5682241/2500000000, 15055971/10000000000, 10827847/10000000000]

theorem scD40Cut_roots_ok : scD40CutCell.rootsOK scD40CutRoots = true := by decide +kernel

theorem scD40Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD40CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD40Cut_margin_le (i : Fin 3) : curvatureLoss scD40CutCell scD40CutCaps i ≤ scD40CutMargins i := by
  fin_cases i <;> decide +kernel

def scD41CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨7/16, 9/20⟩, ⟨9/80, 1/8⟩⟩
def scD41CutRoots : Fin 3 → RatBounds := ![⟨230121251719225/140737488355328, 488583054675075/281474976710656⟩, ⟨351135030604373/281474976710656, 187385065737945/140737488355328⟩, ⟨318150391153743/281474976710656, 86136848968521/70368744177664⟩]
def scD41CutCaps : Fin 3 → Fin 3 → ℚ := ![![8297124457/100000000, 4942787449/100000000, 1731041739/50000000], ![1509130777/50000000, 2511020493/100000000, 1829043199/100000000], ![512692013/100000000, 381251443/100000000, 68805569/20000000]]
def scD41CutWeightFloor : ℚ := 28692241/20000000
def scD41CutMargins : Fin 3 → ℚ := ![4620343/2000000000, 15302851/10000000000, 5503081/5000000000]

theorem scD41Cut_roots_ok : scD41CutCell.rootsOK scD41CutRoots = true := by decide +kernel

theorem scD41Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD41CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD41Cut_margin_le (i : Fin 3) : curvatureLoss scD41CutCell scD41CutCaps i ≤ scD41CutMargins i := by
  fin_cases i <;> decide +kernel

def scD42CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨9/20, 37/80⟩, ⟨1/10, 9/80⟩⟩
def scD42CutRoots : Fin 3 → RatBounds := ![⟨460647161189469/281474976710656, 489043300363463/281474976710656⟩, ⟨349077717902619/281474976710656, 93179115161159/70368744177664⟩, ⟨323489147432791/281474976710656, 350112526508473/281474976710656⟩]
def scD42CutCaps : Fin 3 → Fin 3 → ℚ := ![![3977133449/50000000, 187268157/4000000, 169105419/5000000], ![2886731479/100000000, 2327279597/100000000, 9126103/500000], ![53522237/10000000, 391101259/100000000, 91372527/25000000]]
def scD42CutWeightFloor : ℚ := 142210859/100000000
def scD42CutMargins : Fin 3 → ℚ := ![11109591/5000000000, 14453291/10000000000, 10884413/10000000000]

theorem scD42Cut_roots_ok : scD42CutCell.rootsOK scD42CutRoots = true := by decide +kernel

theorem scD42Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD42CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD42Cut_margin_le (i : Fin 3) : curvatureLoss scD42CutCell scD42CutCaps i ≤ scD42CutMargins i := by
  fin_cases i <;> decide +kernel

def scD43CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨9/20, 37/80⟩, ⟨9/80, 1/8⟩⟩
def scD43CutRoots : Fin 3 → RatBounds := ![⟨229699893988449/140737488355328, 487703132003235/281474976710656⟩, ⟨346995688138685/281474976710656, 185230749623713/140737488355328⟩, ⟨321407532577763/281474976710656, 173924295389833/140737488355328⟩]
def scD43CutCaps : Fin 3 → Fin 3 → ℚ := ![![4054130363/50000000, 298586181/6250000, 3456322219/100000000], ![2942302159/100000000, 148116411/6250000, 929569383/50000000], ![511575807/100000000, 93393959/25000000, 349219107/100000000]]
def scD43CutWeightFloor : ℚ := 72368837/50000000
def scD43CutMargins : Fin 3 → ℚ := ![22582303/10000000000, 14689097/10000000000, 11063829/10000000000]

theorem scD43Cut_roots_ok : scD43CutCell.rootsOK scD43CutRoots = true := by decide +kernel

theorem scD43Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD43CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD43Cut_margin_le (i : Fin 3) : curvatureLoss scD43CutCell scD43CutCaps i ≤ scD43CutMargins i := by
  fin_cases i <;> decide +kernel

def scD44CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨37/80, 19/40⟩, ⟨1/10, 9/80⟩⟩
def scD44CutRoots : Fin 3 → RatBounds := ![⟨115003729065105/70368744177664, 7631496930759/4398046511104⟩, ⟨345074644703211/281474976710656, 368577828490055/281474976710656⟩, ⟨163416324540299/140737488355328, 176766672542725/140737488355328⟩]
def scD44CutCaps : Fin 3 → Fin 3 → ℚ := ![![7796940653/100000000, 2270051037/50000000, 13546087/400000], ![2828900369/100000000, 110094609/5000000, 372440027/20000000], ![534379483/100000000, 76678737/20000000, 185578581/50000000]]
def scD44CutWeightFloor : ℚ := 143508469/100000000
def scD44CutMargins : Fin 3 → ℚ := ![10898653/5000000000, 6958387/5000000000, 10976327/10000000000]

theorem scD44Cut_roots_ok : scD44CutCell.rootsOK scD44CutRoots = true := by decide +kernel

theorem scD44Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD44CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD44Cut_margin_le (i : Fin 3) : curvatureLoss scD44CutCell scD44CutCaps i ≤ scD44CutMargins i := by
  fin_cases i <;> decide +kernel

def scD45CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨37/80, 19/40⟩, ⟨9/80, 1/8⟩⟩
def scD45CutRoots : Fin 3 → RatBounds := ![⟨458770680643071/281474976710656, 121769768642809/70368744177664⟩, ⟨85748366621591/70368744177664, 11447579917755/8796093022208⟩, ⟨40593956203943/35184372088832, 351271886198181/281474976710656⟩]
def scD45CutCaps : Fin 3 → Fin 3 → ℚ := ![![3974088651/50000000, 579088013/12500000, 1730691621/50000000], ![57665029/2000000, 1121091589/50000000, 474166097/25000000], ![127689763/25000000, 366205681/100000000, 354628939/100000000]]
def scD45CutWeightFloor : ℚ := 146049869/100000000
def scD45CutMargins : Fin 3 → ℚ := ![22152711/10000000000, 353569/250000000, 2789393/2500000000]

theorem scD45Cut_roots_ok : scD45CutCell.rootsOK scD45CutRoots = true := by decide +kernel

theorem scD45Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD45CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD45Cut_margin_le (i : Fin 3) : curvatureLoss scD45CutCell scD45CutCaps i ≤ scD45CutMargins i := by
  fin_cases i <;> decide +kernel

def scD46CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨19/40, 39/80⟩, ⟨1/10, 9/80⟩⟩
def scD46CutRoots : Fin 3 → RatBounds := ![⟨459594281842455/281474976710656, 488041901901129/281474976710656⟩, ⟨341200148728093/281474976710656, 364599333240835/281474976710656⟩, ⟨165134555043019/140737488355328, 357082742988787/281474976710656⟩]
def scD46CutCaps : Fin 3 → Fin 3 → ℚ := ![![1916505753/25000000, 4417106551/100000000, 3401528619/100000000], ![557370447/20000000, 1044158309/50000000, 1906780879/100000000], ![106767691/20000000, 375982667/100000000, 377059189/100000000]]
def scD46CutWeightFloor : ℚ := 72421861/50000000
def scD46CutMargins : Fin 3 → ℚ := ![10729213/5000000000, 6720123/5000000000, 2776059/2500000000]

theorem scD46Cut_roots_ok : scD46CutCell.rootsOK scD46CutRoots = true := by decide +kernel

theorem scD46Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD46CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD46Cut_margin_le (i : Fin 3) : curvatureLoss scD46CutCell scD46CutCaps i ≤ scD46CutMargins i := by
  fin_cases i <;> decide +kernel

def scD47CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨19/40, 39/80⟩, ⟨9/80, 1/8⟩⟩
def scD47CutRoots : Fin 3 → RatBounds := ![⟨458352038397435/281474976710656, 121676835421015/70368744177664⟩, ⟨339119516468027/281474976710656, 181171637619411/140737488355328⟩, ⟨164094269140813/140737488355328, 88705841919059/70368744177664⟩]
def scD47CutCaps : Fin 3 → Fin 3 → ℚ := ![![1563056499/20000000, 4507017721/100000000, 1738681209/50000000], ![710069223/25000000, 106326671/5000000, 970962511/50000000], ![510234919/100000000, 89780241/25000000, 360264907/100000000]]
def scD47CutWeightFloor : ℚ := 36850051/25000000
def scD47CutMargins : Fin 3 → ℚ := ![21808193/10000000000, 13657563/10000000000, 11288189/10000000000]

theorem scD47Cut_roots_ok : scD47CutCell.rootsOK scD47CutRoots = true := by decide +kernel

theorem scD47Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD47CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD47Cut_margin_le (i : Fin 3) : curvatureLoss scD47CutCell scD47CutCaps i ≤ scD47CutMargins i := by
  fin_cases i <;> decide +kernel

def scD48CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨39/80, 1/2⟩, ⟨1/10, 9/80⟩⟩
def scD48CutRoots : Fin 3 → RatBounds := ![⟨459383177028501/281474976710656, 487919486359659/281474976710656⟩, ⟨168723017119849/140737488355328, 360771873464963/281474976710656⟩, ⟨333804708202533/281474976710656, 5636991736221/4398046511104⟩]
def scD48CutCaps : Fin 3 → Fin 3 → ℚ := ![![1890054877/25000000, 4311302039/100000000, 3427302811/100000000], ![2763457327/100000000, 1990088519/100000000, 1967638789/100000000], ![133398711/25000000, 368849863/100000000, 11975177/3125000]]
def scD48CutWeightFloor : ℚ := 146219141/100000000
def scD48CutMargins : Fin 3 → ℚ := ![21205609/10000000000, 6513907/5000000000, 2821361/2500000000]

theorem scD48Cut_roots_ok : scD48CutCell.rootsOK scD48CutRoots = true := by decide +kernel

theorem scD48Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD48CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD48Cut_margin_le (i : Fin 3) : curvatureLoss scD48CutCell scD48CutCaps i ≤ scD48CutMargins i := by
  fin_cases i <;> decide +kernel

def scD49CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨39/80, 1/2⟩, ⟨9/80, 1/8⟩⟩
def scD49CutRoots : Fin 3 → RatBounds := ![⟨229070894425633/140737488355328, 60823229177913/35184372088832⟩, ⟨167682834384567/140737488355328, 179257288448063/140737488355328⟩, ⟨331724355106199/281474976710656, 358509769210637/281474976710656⟩]
def scD49CutCaps : Fin 3 → Fin 3 → ℚ := ![![3853989001/50000000, 4398856287/100000000, 3504328677/100000000], ![2816369717/100000000, 405310981/20000000, 2003799089/100000000], ![101999827/20000000, 17615201/5000000, 22883511/6250000]]
def scD49CutWeightFloor : ℚ := 148791233/100000000
def scD49CutMargins : Fin 3 → ℚ := ![21551459/10000000000, 6618863/5000000000, 2868293/2500000000]

theorem scD49Cut_roots_ok : scD49CutCell.rootsOK scD49CutRoots = true := by decide +kernel

theorem scD49Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD49CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD49Cut_margin_le (i : Fin 3) : curvatureLoss scD49CutCell scD49CutCaps i ≤ scD49CutMargins i := by
  fin_cases i <;> decide +kernel

def scD50CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨7/40, 3/16⟩, ⟨1/10, 9/80⟩⟩
def scD50CutRoots : Fin 3 → RatBounds := ![⟨537552062304551/281474976710656, 145283604186961/70368744177664⟩, ⟨30807420712151/17592186044416, 533642507084767/281474976710656⟩, ⟨66114727306503/70368744177664, 18775379314375/17592186044416⟩]
def scD50CutCaps : Fin 3 → Fin 3 → ℚ := ![![6460241141/20000000, 25742323799/100000000, 4825711027/50000000], ![8440106787/50000000, 226888421/1250000, 1106637749/25000000], ![684385917/100000000, 726712887/100000000, 76578903/25000000]]
def scD50CutWeightFloor : ℚ := 14907117/12500000
def scD50CutMargins : Fin 3 → ℚ := ![97394151/10000000000, 43574327/5000000000, 14047157/5000000000]

theorem scD50Cut_roots_ok : scD50CutCell.rootsOK scD50CutRoots = true := by decide +kernel

theorem scD50Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD50CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD50Cut_margin_le (i : Fin 3) : curvatureLoss scD50CutCell scD50CutCaps i ≤ scD50CutMargins i := by
  fin_cases i <;> decide +kernel

def scD51CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨7/40, 3/16⟩, ⟨9/80, 1/8⟩⟩
def scD51CutRoots : Fin 3 → RatBounds := ![⟨535855481497523/281474976710656, 289642082000921/140737488355328⟩, ⟨490706960921685/281474976710656, 132806695644129/70368744177664⟩, ⟨131191606111045/140737488355328, 298025509916943/281474976710656⟩]
def scD51CutCaps : Fin 3 → Fin 3 → ℚ := ![![32956920067/100000000, 26283920623/100000000, 1965813109/20000000], ![8605594579/50000000, 3698700219/20000000, 1127354967/25000000], ![131351581/20000000, 69617231/10000000, 36657039/12500000]]
def scD51CutWeightFloor : ℚ := 3797703/3125000
def scD51CutMargins : Fin 3 → ℚ := ![99267319/10000000000, 44407807/5000000000, 28577621/10000000000]

theorem scD51Cut_roots_ok : scD51CutCell.rootsOK scD51CutRoots = true := by decide +kernel

theorem scD51Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD51CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD51Cut_margin_le (i : Fin 3) : curvatureLoss scD51CutCell scD51CutCaps i ≤ scD51CutMargins i := by
  fin_cases i <;> decide +kernel


end HlawkaSchatten.BelowExponent.Vertex
