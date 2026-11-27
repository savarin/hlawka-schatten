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

def vcM76CutCell : ParameterCell := ⟨⟨1/10, 1/8⟩, ⟨13/40, 7/20⟩, ⟨0, 1/36⟩⟩
def vcM76CutRoots : Fin 3 → RatBounds := ![⟨417250148891839/281474976710656, 29173916107363/17592186044416⟩, ⟨184576339786833/140737488355328, 415533529089973/281474976710656⟩, ⟨310337567452827/281474976710656, 360991068793133/281474976710656⟩]
def vcM76CutCaps : Fin 3 → Fin 3 → ℚ := ![![6345532953/50000000, 1902858011/20000000, 8207084707/100000000], ![621652971/12500000, 2534721741/50000000, 3876168549/100000000], ![1534007299/100000000, 1403972429/100000000, 562116149/50000000]]
def vcM76CutWeightFloor : ℚ := 27563513/25000000
def vcM76CutMargins : Fin 3 → ℚ := ![152797859/10000000000, 6373841/500000000, 52621853/5000000000]

theorem vcM76Cut_roots_ok : vcM76CutCell.rootsOK vcM76CutRoots = true := by decide +kernel

theorem vcM76Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM76CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM76Cut_margin_le (i : Fin 3) : curvatureLoss vcM76CutCell vcM76CutCaps i ≤ vcM76CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM77CutCell : ParameterCell := ⟨⟨1/10, 1/8⟩, ⟨13/40, 7/20⟩, ⟨1/36, 1/18⟩⟩
def vcM77CutRoots : Fin 3 → RatBounds := ![⟨206656653995761/140737488355328, 462125010859343/281474976710656⟩, ⟨91005401017423/70368744177664, 409445701642297/281474976710656⟩, ⟨9531162040335/8796093022208, 354517505456789/281474976710656⟩]
def vcM77CutCaps : Fin 3 → Fin 3 → ℚ := ![![6806999949/50000000, 10193914193/100000000, 8808101433/100000000], ![5312664593/100000000, 676140489/12500000, 4131937873/100000000], ![343882353/25000000, 626736021/50000000, 20064409/2000000]]
def vcM77CutWeightFloor : ℚ := 114748987/100000000
def vcM77CutMargins : Fin 3 → ℚ := ![161131633/10000000000, 133988551/10000000000, 110770181/10000000000]

theorem vcM77Cut_roots_ok : vcM77CutCell.rootsOK vcM77CutRoots = true := by decide +kernel

theorem vcM77Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM77CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM77Cut_margin_le (i : Fin 3) : curvatureLoss vcM77CutCell vcM77CutCaps i ≤ vcM77CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM78CutCell : ParameterCell := ⟨⟨1/10, 1/8⟩, ⟨7/20, 3/8⟩, ⟨0, 1/36⟩⟩
def vcM78CutRoots : Fin 3 → RatBounds := ![⟨25915333960263/17592186044416, 463651800156085/281474976710656⟩, ⟨180496964577967/140737488355328, 406535663175051/281474976710656⟩, ⟨157829466823673/140737488355328, 365987714059155/281474976710656⟩]
def vcM78CutCaps : Fin 3 → Fin 3 → ℚ := ![![2418308937/20000000, 4450423103/50000000, 7947566911/100000000], ![1082403527/25000000, 4323896591/100000000, 870546103/25000000], ![755762931/50000000, 1347563367/100000000, 114864593/10000000]]
def vcM78CutWeightFloor : ℚ := 112144581/100000000
def vcM78CutMargins : Fin 3 → ℚ := ![17858633/1250000000, 23263127/2000000000, 50186847/5000000000]

theorem vcM78Cut_roots_ok : vcM78CutCell.rootsOK vcM78CutRoots = true := by decide +kernel

theorem vcM78Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM78CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM78Cut_margin_le (i : Fin 3) : curvatureLoss vcM78CutCell vcM78CutCaps i ≤ vcM78CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM79CutCell : ParameterCell := ⟨⟨1/10, 1/8⟩, ⟨7/20, 3/8⟩, ⟨1/36, 1/18⟩⟩
def vcM79CutRoots : Fin 3 → RatBounds := ![⟨102688927860813/70368744177664, 57381311123635/35184372088832⟩, ⟨88960803563209/70368744177664, 200208659353753/140737488355328⟩, ⟨310346592177179/281474976710656, 359574273570805/281474976710656⟩]
def vcM79CutCaps : Fin 3 → Fin 3 → ℚ := ![![12971245631/100000000, 2383565729/25000000, 1067485533/12500000], ![2311352311/50000000, 4611395353/100000000, 74256753/2000000], ![677518057/50000000, 48105909/4000000, 512453917/50000000]]
def vcM79CutWeightFloor : ℚ := 116683617/100000000
def vcM79CutMargins : Fin 3 → ℚ := ![4703817/312500000, 122112567/10000000000, 10560969/1000000000]

theorem vcM79Cut_roots_ok : vcM79CutCell.rootsOK vcM79CutRoots = true := by decide +kernel

theorem vcM79Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM79CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM79Cut_margin_le (i : Fin 3) : curvatureLoss vcM79CutCell vcM79CutCaps i ≤ vcM79CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM80CutCell : ParameterCell := ⟨⟨1/10, 1/8⟩, ⟨3/8, 2/5⟩, ⟨0, 1/36⟩⟩
def vcM80CutRoots : Fin 3 → RatBounds := ![⟨206364314451065/140737488355328, 461461397535207/281474976710656⟩, ⟨176682282068879/140737488355328, 398296326829737/281474976710656⟩, ⟨160598772572861/140737488355328, 92856757625581/70368744177664⟩]
def vcM80CutCaps : Fin 3 → Fin 3 → ℚ := ![![11851384581/100000000, 8580777143/100000000, 1985959213/25000000], ![781368343/20000000, 949651257/25000000, 649157869/20000000], ![374078527/25000000, 1297000891/100000000, 73533671/6250000]]
def vcM80CutWeightFloor : ℚ := 114112291/100000000
def vcM80CutMargins : Fin 3 → ℚ := ![27508637/2000000000, 109223577/10000000000, 12345843/1250000000]

theorem vcM80Cut_roots_ok : vcM80CutCell.rootsOK vcM80CutRoots = true := by decide +kernel

theorem vcM80Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM80CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM80Cut_margin_le (i : Fin 3) : curvatureLoss vcM80CutCell vcM80CutCaps i ≤ vcM80CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM81CutCell : ParameterCell := ⟨⟨1/10, 1/8⟩, ⟨3/8, 2/5⟩, ⟨1/36, 1/18⟩⟩
def vcM81CutRoots : Fin 3 → RatBounds := ![⟨408873066879893/281474976710656, 228450275295085/140737488355328⟩, ⟨348192030177811/281474976710656, 196071335717291/140737488355328⟩, ⟨78978260224983/70368744177664, 45633702720243/35184372088832⟩]
def vcM81CutCaps : Fin 3 → Fin 3 → ℚ := ![![2542908067/20000000, 9188586203/100000000, 4272279023/50000000], ![2084741559/50000000, 506172713/12500000, 1730459801/50000000], ![1341170173/100000000, 1157176113/100000000, 1049760179/100000000]]
def vcM81CutWeightFloor : ℚ := 118689023/100000000
def vcM81CutMargins : Fin 3 → ℚ := ![144842103/10000000000, 5729133/500000000, 25979449/2500000000]

theorem vcM81Cut_roots_ok : vcM81CutCell.rootsOK vcM81CutRoots = true := by decide +kernel

theorem vcM81Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM81CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM81Cut_margin_le (i : Fin 3) : curvatureLoss vcM81CutCell vcM81CutCaps i ≤ vcM81CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM82CutCell : ParameterCell := ⟨⟨1/10, 1/8⟩, ⟨2/5, 17/40⟩, ⟨0, 1/36⟩⟩
def vcM82CutRoots : Fin 3 → RatBounds := ![⟨25716743904263/17592186044416, 28760372770885/17592186044416⟩, ⟨43275062225255/35184372088832, 97682665022319/70368744177664⟩, ⟨326985066643141/281474976710656, 377335377780085/281474976710656⟩]
def vcM82CutCaps : Fin 3 → Fin 3 → ℚ := ![![11931343813/100000000, 1702622041/20000000, 8187791241/100000000], ![3672984861/100000000, 3459416011/100000000, 790297863/25000000], ![1487638101/100000000, 1251455061/100000000, 30199711/2500000]]
def vcM82CutWeightFloor : ℚ := 116168431/100000000
def vcM82CutMargins : Fin 3 → ℚ := ![6812859/500000000, 105605723/10000000000, 100315051/10000000000]

theorem vcM82Cut_roots_ok : vcM82CutCell.rootsOK vcM82CutRoots = true := by decide +kernel

theorem vcM82Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM82CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM82Cut_margin_le (i : Fin 3) : curvatureLoss vcM82CutCell vcM82CutCaps i ≤ vcM82CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM83CutCell : ParameterCell := ⟨⟨1/10, 1/8⟩, ⟨2/5, 17/40⟩, ⟨1/36, 1/18⟩⟩
def vcM83CutRoots : Fin 3 → RatBounds := ![⟨407633741707141/281474976710656, 227815183593227/140737488355328⟩, ⟨341004336776903/281474976710656, 384537323940991/281474976710656⟩, ⟨160863985878549/140737488355328, 371030062132129/281474976710656⟩]
def vcM83CutCaps : Fin 3 → Fin 3 → ℚ := ![![1600294979/12500000, 9112669927/100000000, 550870739/6250000], ![489910181/12500000, 1843773059/50000000, 134844541/4000000], ![33331649/2500000, 139536599/12500000, 1077851463/100000000]]
def vcM83CutWeightFloor : ℚ := 24155453/20000000
def vcM83CutMargins : Fin 3 → ℚ := ![28699451/2000000000, 110768401/10000000000, 105591611/10000000000]

theorem vcM83Cut_roots_ok : vcM83CutCell.rootsOK vcM83CutRoots = true := by decide +kernel

theorem vcM83Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM83CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM83Cut_margin_le (i : Fin 3) : curvatureLoss vcM83CutCell vcM83CutCaps i ≤ vcM83CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM84CutCell : ParameterCell := ⟨⟨1/10, 1/8⟩, ⟨17/40, 9/20⟩, ⟨0, 1/36⟩⟩
def vcM84CutRoots : Fin 3 → RatBounds := ![⟨410842570677077/281474976710656, 459739240515233/281474976710656⟩, ⟨169723381854811/140737488355328, 191884888502901/140737488355328⟩, ⟨83263906419669/70368744177664, 383747880774181/281474976710656⟩]
def vcM84CutCaps : Fin 3 → Fin 3 → ℚ := ![![12336407779/100000000, 8686130569/100000000, 8699479601/100000000], ![718060283/20000000, 1631580499/50000000, 128575103/4000000], ![742551477/50000000, 605158213/50000000, 310799901/25000000]]
def vcM84CutWeightFloor : ℚ := 118325127/100000000
def vcM84CutMargins : Fin 3 → ℚ := ![69375663/5000000000, 52513709/5000000000, 105067747/10000000000]

theorem vcM84Cut_roots_ok : vcM84CutCell.rootsOK vcM84CutRoots = true := by decide +kernel

theorem vcM84Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM84CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM84Cut_margin_le (i : Fin 3) : curvatureLoss vcM84CutCell vcM84CutCaps i ≤ vcM84CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM85CutCell : ParameterCell := ⟨⟨1/10, 1/8⟩, ⟨17/40, 9/20⟩, ⟨1/36, 1/18⟩⟩
def vcM85CutRoots : Fin 3 → RatBounds := ![⟨407017439966075/281474976710656, 455214065905933/281474976710656⟩, ⟨83556371830889/70368744177664, 94383171324069/70368744177664⟩, ⟨327825285035529/281474976710656, 377490758857381/281474976710656⟩]
def vcM85CutCaps : Fin 3 → Fin 3 → ℚ := ![![6620034691/50000000, 2323423951/25000000, 9369853159/100000000], ![3831500663/100000000, 1739400243/50000000, 342818213/10000000], ![1330965909/100000000, 1079436557/100000000, 554685917/50000000]]
def vcM85CutWeightFloor : ℚ := 61480393/50000000
def vcM85CutMargins : Fin 3 → ℚ := ![14620889/1000000000, 2754909/250000000, 110684611/10000000000]

theorem vcM85Cut_roots_ok : vcM85CutCell.rootsOK vcM85CutRoots = true := by decide +kernel

theorem vcM85Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM85CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM85Cut_margin_le (i : Fin 3) : curvatureLoss vcM85CutCell vcM85CutCaps i ≤ vcM85CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM90CutCell : ParameterCell := ⟨⟨1/8, 3/20⟩, ⟨7/40, 1/5⟩, ⟨0, 1/36⟩⟩
def vcM90CutRoots : Fin 3 → RatBounds := ![⟨109081453592317/70368744177664, 492594007196115/281474976710656⟩, ⟨212767301925509/140737488355328, 480970491302053/281474976710656⟩, ⟨285152778932399/281474976710656, 341172969988433/281474976710656⟩]
def vcM90CutCaps : Fin 3 → Fin 3 → ℚ := ![![165147229/781250, 4525901581/25000000, 745757367/6250000], ![302393083/1250000, 5038599333/20000000, 7731101131/50000000], ![653135821/50000000, 265060193/20000000, 46475713/6250000]]
def vcM90CutWeightFloor : ℚ := 104562287/100000000
def vcM90CutMargins : Fin 3 → ℚ := ![366741977/10000000000, 351037321/10000000000, 6912197/312500000]

theorem vcM90Cut_roots_ok : vcM90CutCell.rootsOK vcM90CutRoots = true := by decide +kernel

theorem vcM90Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM90CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM90Cut_margin_le (i : Fin 3) : curvatureLoss vcM90CutCell vcM90CutCaps i ≤ vcM90CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM91CutCell : ParameterCell := ⟨⟨1/8, 3/20⟩, ⟨7/40, 1/5⟩, ⟨1/36, 1/18⟩⟩
def vcM91CutRoots : Fin 3 → RatBounds := ![⟨6746287531637/4398046511104, 487179903993985/281474976710656⟩, ⟨3286179967205/2199023255552, 237576617286115/140737488355328⟩, ⟨139856153988119/140737488355328, 334362541909283/281474976710656⟩]
def vcM91CutCaps : Fin 3 → Fin 3 → ℚ := ![![11304641067/50000000, 19372079379/100000000, 6344040831/50000000], ![12939057899/50000000, 26961255729/100000000, 16404801041/100000000], ![585668829/50000000, 296463203/25000000, 331306963/50000000]]
def vcM91CutWeightFloor : ℚ := 109299761/100000000
def vcM91CutMargins : Fin 3 → ℚ := ![390105421/10000000000, 74683361/2000000000, 233679099/10000000000]

theorem vcM91Cut_roots_ok : vcM91CutCell.rootsOK vcM91CutRoots = true := by decide +kernel

theorem vcM91Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM91CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM91Cut_margin_le (i : Fin 3) : curvatureLoss vcM91CutCell vcM91CutCaps i ≤ vcM91CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM92CutCell : ParameterCell := ⟨⟨1/8, 3/20⟩, ⟨1/5, 9/40⟩, ⟨0, 1/36⟩⟩
def vcM92CutRoots : Fin 3 → RatBounds := ![⟨429009495054829/281474976710656, 120699521322331/70368744177664⟩, ⟨206477709038755/140737488355328, 232784607552017/140737488355328⟩, ⟨289609656128617/281474976710656, 343711526534401/281474976710656⟩]
def vcM92CutCaps : Fin 3 → Fin 3 → ℚ := ![![280374179/1000000, 24059135601/100000000, 18513876647/100000000], ![25734261487/100000000, 26323386551/100000000, 2281740117/12500000], ![113242691/6250000, 226726089/12500000, 552881307/50000000]]
def vcM92CutWeightFloor : ℚ := 51445009/50000000
def vcM92CutMargins : Fin 3 → ℚ := ![43756697/1000000000, 51388469/1250000000, 9309799/312500000]

theorem vcM92Cut_roots_ok : vcM92CutCell.rootsOK vcM92CutRoots = true := by decide +kernel

theorem vcM92Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM92CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM92Cut_margin_le (i : Fin 3) : curvatureLoss vcM92CutCell vcM92CutCaps i ≤ vcM92CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM93CutCell : ParameterCell := ⟨⟨1/8, 3/20⟩, ⟨1/5, 9/40⟩, ⟨1/36, 1/18⟩⟩
def vcM93CutRoots : Fin 3 → RatBounds := ![⟨424584622220553/281474976710656, 477555715776855/281474976710656⟩, ⟨102011505701173/70368744177664, 114938144397333/70368744177664⟩, ⟨284203204983739/281474976710656, 42125006550255/35184372088832⟩]
def vcM93CutCaps : Fin 3 → Fin 3 → ℚ := ![![30118410047/100000000, 25825714363/100000000, 19715926391/100000000], ![5517703121/20000000, 28232606299/100000000, 1939880983/10000000], ![1630345099/100000000, 1627988317/100000000, 494752339/50000000]]
def vcM93CutWeightFloor : ℚ := 53429541/50000000
def vcM93CutMargins : Fin 3 → ℚ := ![58320017/1250000000, 219016339/5000000000, 315127711/10000000000]

theorem vcM93Cut_roots_ok : vcM93CutCell.rootsOK vcM93CutRoots = true := by decide +kernel

theorem vcM93Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM93CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM93Cut_margin_le (i : Fin 3) : curvatureLoss vcM93CutCell vcM93CutCaps i ≤ vcM93CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM94CutCell : ParameterCell := ⟨⟨1/8, 3/20⟩, ⟨9/40, 1/4⟩, ⟨0, 1/36⟩⟩
def vcM94CutRoots : Fin 3 → RatBounds := ![⟨422813842704351/281474976710656, 474643944718281/281474976710656⟩, ⟨100382217315131/70368744177664, 451869108739517/281474976710656⟩, ⟨147066474855879/140737488355328, 346712774580843/281474976710656⟩]
def vcM94CutCaps : Fin 3 → Fin 3 → ℚ := ![![22251015973/100000000, 3725602441/20000000, 14823204437/100000000], ![8285170789/50000000, 4267274189/25000000, 6094053687/50000000], ![1722106341/100000000, 1705210731/100000000, 277240313/25000000]]
def vcM94CutWeightFloor : ℚ := 20899403/20000000
def vcM94CutMargins : Fin 3 → ℚ := ![159950839/5000000000, 295330527/10000000000, 110860937/5000000000]

theorem vcM94Cut_roots_ok : vcM94CutCell.rootsOK vcM94CutRoots = true := by decide +kernel

theorem vcM94Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM94CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM94Cut_margin_le (i : Fin 3) : curvatureLoss vcM94CutCell vcM94CutCaps i ≤ vcM94CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM95CutCell : ParameterCell := ⟨⟨1/8, 3/20⟩, ⟨9/40, 1/4⟩, ⟨1/36, 1/18⟩⟩
def vcM95CutRoots : Fin 3 → RatBounds := ![⟨209253597212439/140737488355328, 469546421341253/281474976710656⟩, ⟨396608265943629/281474976710656, 446043194366051/281474976710656⟩, ⟨144380489971439/140737488355328, 340091790978003/281474976710656⟩]
def vcM95CutCaps : Fin 3 → Fin 3 → ℚ := ![![23903031051/100000000, 2499705317/12500000, 790527773/5000000], ![17769141699/100000000, 3660641783/20000000, 6485233911/50000000], ![24194287/1562500, 1528740027/100000000, 19836467/2000000]]
def vcM95CutWeightFloor : ℚ := 27149167/25000000
def vcM95CutMargins : Fin 3 → ℚ := ![68099719/2000000000, 156985097/5000000000, 117208971/5000000000]

theorem vcM95Cut_roots_ok : vcM95CutCell.rootsOK vcM95CutRoots = true := by decide +kernel

theorem vcM95Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM95CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM95Cut_margin_le (i : Fin 3) : curvatureLoss vcM95CutCell vcM95CutCaps i ≤ vcM95CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM96CutCell : ParameterCell := ⟨⟨1/8, 3/20⟩, ⟨1/4, 11/40⟩, ⟨0, 1/36⟩⟩
def vcM96CutRoots : Fin 3 → RatBounds := ![⟨104399733573211/70368744177664, 233947191869593/140737488355328⟩, ⟨391079483366987/281474976710656, 439586103078847/281474976710656⟩, ⟨74688462207469/70368744177664, 350144782605119/281474976710656⟩]
def vcM96CutCaps : Fin 3 → Fin 3 → ℚ := ![![9282753171/50000000, 3035756043/20000000, 1246577709/10000000], ![5754510861/50000000, 11895278321/100000000, 8733306651/100000000], ![1653538773/100000000, 1613781133/100000000, 1117742937/100000000]]
def vcM96CutWeightFloor : ℚ := 1658417/1562500
def vcM96CutMargins : Fin 3 → ℚ := ![50181147/2000000000, 227081101/10000000000, 88199271/5000000000]

theorem vcM96Cut_roots_ok : vcM96CutCell.rootsOK vcM96CutRoots = true := by decide +kernel

theorem vcM96Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM96CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM96Cut_margin_le (i : Fin 3) : curvatureLoss vcM96CutCell vcM96CutCaps i ≤ vcM96CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM97CutCell : ParameterCell := ⟨⟨1/8, 3/20⟩, ⟨1/4, 11/40⟩, ⟨1/36, 1/18⟩⟩
def vcM97CutRoots : Fin 3 → RatBounds := ![⟨51674042501733/35184372088832, 28932392884141/17592186044416⟩, ⟨386143254893991/281474976710656, 216871378422499/140737488355328⟩, ⟨293416623456253/281474976710656, 85901823380277/70368744177664⟩]
def vcM97CutCaps : Fin 3 → Fin 3 → ℚ := ![![19942943431/100000000, 3259143609/20000000, 13315081951/100000000], ![1542620957/12500000, 12751237547/100000000, 581636439/6250000], ![743016591/50000000, 1445512399/100000000, 999326367/100000000]]
def vcM97CutWeightFloor : ℚ := 110339593/100000000
def vcM97CutMargins : Fin 3 → ℚ := ![133275469/5000000000, 240871397/10000000000, 93183599/5000000000]

theorem vcM97Cut_roots_ok : vcM97CutCell.rootsOK vcM97CutRoots = true := by decide +kernel

theorem vcM97Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM97CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM97Cut_margin_le (i : Fin 3) : curvatureLoss vcM97CutCell vcM97CutCaps i ≤ vcM97CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM98CutCell : ParameterCell := ⟨⟨1/8, 3/20⟩, ⟨11/40, 3/10⟩, ⟨0, 1/36⟩⟩
def vcM98CutRoots : Fin 3 → RatBounds := ![⟨206628283663597/140737488355328, 7224555957827/4398046511104⟩, ⟨381466750181849/281474976710656, 428500958853097/281474976710656⟩, ⟨151750323492771/140737488355328, 176995238304659/140737488355328⟩]
def vcM98CutCaps : Fin 3 → Fin 3 → ℚ := ![![505104713/3125000, 12926246353/100000000, 10942310593/100000000], ![1705915439/20000000, 8804753811/100000000, 3327359259/50000000], ![800566783/50000000, 1535367489/100000000, 1131292281/100000000]]
def vcM98CutWeightFloor : ℚ := 10782509/10000000
def vcM98CutMargins : Fin 3 → ℚ := ![208356533/10000000000, 184582153/10000000000, 74194087/5000000000]

theorem vcM98Cut_roots_ok : vcM98CutCell.rootsOK vcM98CutRoots = true := by decide +kernel

theorem vcM98Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM98CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM98Cut_margin_le (i : Fin 3) : curvatureLoss vcM98CutCell vcM98CutCaps i ≤ vcM98CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM99CutCell : ParameterCell := ⟨⟨1/8, 3/20⟩, ⟨11/40, 3/10⟩, ⟨1/36, 1/18⟩⟩
def vcM99CutRoots : Fin 3 → RatBounds := ![⟨204566760843033/140737488355328, 457496103083973/281474976710656⟩, ⟨376511239075211/281474976710656, 422633327845681/281474976710656⟩, ⟨74549564193379/70368744177664, 43441319453421/35184372088832⟩]
def vcM99CutCaps : Fin 3 → Fin 3 → ℚ := ![![1736068007/10000000, 2775387831/20000000, 5851745969/50000000], ![914372123/10000000, 2358412721/25000000, 1420059607/20000000], ![1438336521/100000000, 687143097/50000000, 1011175353/100000000]]
def vcM99CutWeightFloor : ℚ := 14013247/12500000
def vcM99CutMargins : Fin 3 → ℚ := ![2761731/125000000, 9768453/500000000, 78328729/5000000000]

theorem vcM99Cut_roots_ok : vcM99CutCell.rootsOK vcM99CutRoots = true := by decide +kernel

theorem vcM99Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM99CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM99Cut_margin_le (i : Fin 3) : curvatureLoss vcM99CutCell vcM99CutCaps i ≤ vcM99CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM100CutCell : ParameterCell := ⟨⟨1/8, 3/20⟩, ⟨3/10, 13/40⟩, ⟨0, 1/36⟩⟩
def vcM100CutRoots : Fin 3 → RatBounds := ![⟨51212868264467/35184372088832, 228970852599191/140737488355328⟩, ⟨372576494376963/281474976710656, 104610421762019/70368744177664⟩, ⟨308400194840069/281474976710656, 358244355803897/281474976710656⟩]
def vcM100CutCaps : Fin 3 → Fin 3 → ℚ := ![![7311581023/50000000, 11464035299/100000000, 399974773/4000000], ![1342101353/20000000, 6877264317/100000000, 168005133/3125000], ![1561462329/100000000, 733568749/50000000, 574545611/50000000]]
def vcM100CutWeightFloor : ℚ := 109565759/100000000
def vcM100CutMargins : Fin 3 → ℚ := ![181729689/10000000000, 31488407/2000000000, 32801103/2500000000]

theorem vcM100Cut_roots_ok : vcM100CutCell.rootsOK vcM100CutRoots = true := by decide +kernel

theorem vcM100Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM100CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM100Cut_margin_le (i : Fin 3) : curvatureLoss vcM100CutCell vcM100CutCaps i ≤ vcM100CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM101CutCell : ParameterCell := ⟨⟨1/8, 3/20⟩, ⟨3/10, 13/40⟩, ⟨1/36, 1/18⟩⟩
def vcM101CutRoots : Fin 3 → RatBounds := ![⟨202824118722375/140737488355328, 453148018298153/281474976710656⟩, ⟨91899662680395/70368744177664, 412543900204789/281474976710656⟩, ⟨303132574473921/281474976710656, 43982107258027/35184372088832⟩]
def vcM101CutCaps : Fin 3 → Fin 3 → ℚ := ![![3928930069/25000000, 12305695127/100000000, 2681729209/25000000], ![1797585601/25000000, 3682776393/50000000, 5742057569/100000000], ![1402226387/100000000, 656220123/50000000, 256724089/25000000]]
def vcM101CutWeightFloor : ℚ := 14238831/12500000
def vcM101CutMargins : Fin 3 → ℚ := ![7699127/400000000, 5198131/312500000, 69284171/5000000000]

theorem vcM101Cut_roots_ok : vcM101CutCell.rootsOK vcM101CutRoots = true := by decide +kernel

theorem vcM101Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM101CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM101Cut_margin_le (i : Fin 3) : curvatureLoss vcM101CutCell vcM101CutCaps i ≤ vcM101CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM102CutCell : ParameterCell := ⟨⟨1/8, 3/20⟩, ⟨13/40, 7/20⟩, ⟨0, 1/36⟩⟩
def vcM102CutRoots : Fin 3 → RatBounds := ![⟨406873555193913/281474976710656, 56813073106777/35184372088832⟩, ⟨364314699050679/281474976710656, 204635779989481/140737488355328⟩, ⟨313479006630171/281474976710656, 45363815494553/35184372088832⟩]
def vcM102CutCaps : Fin 3 → Fin 3 → ℚ := ![![2742442567/20000000, 10558657199/100000000, 2375930437/25000000], ![1392832923/25000000, 351460843/6250000, 1144441027/25000000], ![766088459/50000000, 1407103949/100000000, 585419633/50000000]]
def vcM102CutWeightFloor : ℚ := 22274023/20000000
def vcM102CutMargins : Fin 3 → ℚ := ![165430633/10000000000, 3499843/250000000, 60652213/5000000000]

theorem vcM102Cut_roots_ok : vcM102CutCell.rootsOK vcM102CutRoots = true := by decide +kernel

theorem vcM102Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM102CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM102Cut_margin_le (i : Fin 3) : curvatureLoss vcM102CutCell vcM102CutCaps i ≤ vcM102CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM103CutCell : ParameterCell := ⟨⟨1/8, 3/20⟩, ⟨13/40, 7/20⟩, ⟨1/36, 1/18⟩⟩
def vcM103CutRoots : Fin 3 → RatBounds := ![⟨402872969736353/281474976710656, 224887675253625/140737488355328⟩, ⟨89827991335363/70368744177664, 100834621843769/70368744177664⟩, ⟨308245943219353/281474976710656, 356590870161265/281474976710656⟩]
def vcM103CutCaps : Fin 3 → Fin 3 → ℚ := ![![3685758897/25000000, 11331506923/100000000, 127733223/1250000], ![5966287349/100000000, 1204059197/20000000, 4892692069/100000000], ![1375569017/100000000, 1258135877/100000000, 523107877/50000000]]
def vcM103CutWeightFloor : ℚ := 115766527/100000000
def vcM103CutMargins : Fin 3 → ℚ := ![87529517/5000000000, 147695759/10000000000, 128148237/10000000000]

theorem vcM103Cut_roots_ok : vcM103CutCell.rootsOK vcM103CutRoots = true := by decide +kernel

theorem vcM103Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM103CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM103Cut_margin_le (i : Fin 3) : curvatureLoss vcM103CutCell vcM103CutCaps i ≤ vcM103CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM104CutCell : ParameterCell := ⟨⟨1/8, 3/20⟩, ⟨7/20, 3/8⟩, ⟨0, 1/36⟩⟩
def vcM104CutRoots : Fin 3 → RatBounds := ![⟨202359768747533/140737488355328, 112996675380077/70368744177664⟩, ⟨89150747774489/70368744177664, 400880744060175/281474976710656⟩, ⟨318764169076283/281474976710656, 368001606703801/281474976710656⟩]
def vcM104CutCaps : Fin 3 → Fin 3 → ℚ := ![![1664900537/12500000, 10092150459/100000000, 7512249/80000], ![483910323/10000000, 4784823061/100000000, 2039089211/50000000], ![302336571/20000000, 1353844173/100000000, 598204451/50000000]]
def vcM104CutWeightFloor : ℚ := 56623891/50000000
def vcM104CutMargins : Fin 3 → ℚ := ![39110513/2500000000, 129284267/10000000000, 58381007/5000000000]

theorem vcM104Cut_roots_ok : vcM104CutCell.rootsOK vcM104CutRoots = true := by decide +kernel

theorem vcM104Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM104CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM104Cut_margin_le (i : Fin 3) : curvatureLoss vcM104CutCell vcM104CutCaps i ≤ vcM104CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM105CutCell : ParameterCell := ⟨⟨1/8, 3/20⟩, ⟨7/20, 3/8⟩, ⟨1/36, 1/18⟩⟩
def vcM105CutRoots : Fin 3 → RatBounds := ![⟨200379808612495/140737488355328, 223652840511241/140737488355328⟩, ⟨351573213850521/281474976710656, 394907810250271/281474976710656⟩, ⟨313565304486875/281474976710656, 22609100931769/17592186044416⟩]
def vcM105CutCaps : Fin 3 → Fin 3 → ℚ := ![![3580231527/25000000, 1353437139/12500000, 1263411247/12500000], ![2589688593/50000000, 5120285249/100000000, 4360640711/100000000], ![678458303/50000000, 1210057089/100000000, 534509507/50000000]]
def vcM105CutWeightFloor : ℚ := 29421377/25000000
def vcM105CutMargins : Fin 3 → ℚ := ![2584901/156250000, 68131563/5000000000, 123341463/10000000000]

theorem vcM105Cut_roots_ok : vcM105CutCell.rootsOK vcM105CutRoots = true := by decide +kernel

theorem vcM105Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM105CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM105Cut_margin_le (i : Fin 3) : curvatureLoss vcM105CutCell vcM105CutCaps i ≤ vcM105CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM106CutCell : ParameterCell := ⟨⟨1/8, 3/20⟩, ⟨3/8, 2/5⟩, ⟨0, 1/36⟩⟩
def vcM106CutRoots : Fin 3 → RatBounds := ![⟨403205142653955/281474976710656, 450336442108347/281474976710656⟩, ⟨349375276692779/281474976710656, 393180352073423/281474976710656⟩, ⟨162142075824467/140737488355328, 186769157260105/140737488355328⟩]
def vcM106CutCaps : Fin 3 → Fin 3 → ℚ := ![![2670362963/20000000, 1246568113/12500000, 4805878173/50000000], ![2192133737/50000000, 2111823647/50000000, 3791596487/100000000], ![1498937991/100000000, 163291023/12500000, 1225823179/100000000]]
def vcM106CutWeightFloor : ℚ := 28799063/25000000
def vcM106CutMargins : Fin 3 → ℚ := ![153020493/10000000000, 15438421/1250000000, 23307367/2000000000]

theorem vcM106Cut_roots_ok : vcM106CutCell.rootsOK vcM106CutRoots = true := by decide +kernel

theorem vcM106Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM106CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM106Cut_margin_le (i : Fin 3) : curvatureLoss vcM106CutCell vcM106CutCaps i ≤ vcM106CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM107CutCell : ParameterCell := ⟨⟨1/8, 3/20⟩, ⟨3/8, 2/5⟩, ⟨1/36, 1/18⟩⟩
def vcM107CutRoots : Fin 3 → RatBounds := ![⟨399272980902641/281474976710656, 222844087711235/140737488355328⟩, ⟨172158318915323/140737488355328, 96790846574509/70368744177664⟩, ⟨79779744872439/70368744177664, 367342063442153/281474976710656⟩]
def vcM107CutCaps : Fin 3 → Fin 3 → ℚ := ![![7178621677/50000000, 2673781723/25000000, 10353896247/100000000], ![4690494587/100000000, 4517708207/100000000, 2027570617/50000000], ![1345323677/100000000, 1167251307/100000000, 1095329961/100000000]]
def vcM107CutWeightFloor : ℚ := 11967907/10000000
def vcM107CutMargins : Fin 3 → ℚ := ![161786183/10000000000, 65054243/5000000000, 123135131/10000000000]

theorem vcM107Cut_roots_ok : vcM107CutCell.rootsOK vcM107CutRoots = true := by decide +kernel

theorem vcM107Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM107CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM107Cut_margin_le (i : Fin 3) : curvatureLoss vcM107CutCell vcM107CutCaps i ≤ vcM107CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM108CutCell : ParameterCell := ⟨⟨1/8, 3/20⟩, ⟨2/5, 17/40⟩, ⟨0, 1/36⟩⟩
def vcM108CutRoots : Fin 3 → RatBounds := ![⟨402305965502671/281474976710656, 449520971428703/281474976710656⟩, ⟨85643796717387/70368744177664, 193049079995323/140737488355328⟩, ⟨330069590048385/281474976710656, 379549525305761/281474976710656⟩]
def vcM108CutCaps : Fin 3 → Fin 3 → ℚ := ![![13801029731/100000000, 5086570447/50000000, 2036462659/20000000], ![839717017/20000000, 245397627/6250000, 1871928137/50000000], ![746665317/50000000, 1263810937/100000000, 251849927/20000000]]
def vcM108CutWeightFloor : ℚ := 4685929/4000000
def vcM108CutMargins : Fin 3 → ℚ := ![155025257/10000000000, 61170951/5000000000, 120943741/10000000000]

theorem vcM108Cut_roots_ok : vcM108CutCell.rootsOK vcM108CutRoots = true := by decide +kernel

theorem vcM108Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM108CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM108Cut_margin_le (i : Fin 3) : curvatureLoss vcM108CutCell vcM108CutCaps i ≤ vcM108CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM109CutCell : ParameterCell := ⟨⟨1/8, 3/20⟩, ⟨2/5, 17/40⟩, ⟨1/36, 1/18⟩⟩
def vcM109CutRoots : Fin 3 → RatBounds := ![⟨49798628583263/35184372088832, 222445250360009/140737488355328⟩, ⟨168743074997119/140737488355328, 47504158891341/35184372088832⟩, ⟨324937447661725/281474976710656, 373409237693209/281474976710656⟩]
def vcM109CutCaps : Fin 3 → Fin 3 → ℚ := ![![7421189153/50000000, 1090538167/10000000, 87794647/800000], ![224590279/5000000, 4198987391/100000000, 2002593199/50000000], ![1340236059/100000000, 1129029497/100000000, 1125305179/100000000]]
def vcM109CutWeightFloor : ℚ := 121663107/100000000
def vcM109CutMargins : Fin 3 → ℚ := ![40993743/2500000000, 128892443/10000000000, 127881117/10000000000]

theorem vcM109Cut_roots_ok : vcM109CutCell.rootsOK vcM109CutRoots = true := by decide +kernel

theorem vcM109Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM109CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM109Cut_margin_le (i : Fin 3) : curvatureLoss vcM109CutCell vcM109CutCaps i ≤ vcM109CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM110CutCell : ParameterCell := ⟨⟨1/8, 3/20⟩, ⟨17/40, 9/20⟩, ⟨0, 1/36⟩⟩
def vcM110CutRoots : Fin 3 → RatBounds := ![⟨201003897681029/140737488355328, 224762165435039/140737488355328⟩, ⟨168077050772353/140737488355328, 47446938025395/35184372088832⟩, ⟨168077050772353/140737488355328, 386072836681697/281474976710656⟩]
def vcM110CutCaps : Fin 3 → Fin 3 → ℚ := ![![14722673151/100000000, 5358298949/50000000, 2791352091/25000000], ![2112273941/50000000, 3826253983/100000000, 1953450857/50000000], ![186826533/12500000, 612882241/50000000, 1297008723/100000000]]
def vcM110CutWeightFloor : ℚ := 119192441/100000000
def vcM110CutMargins : Fin 3 → ℚ := ![20305099/1250000000, 25087721/2000000000, 16282769/1250000000]

theorem vcM110Cut_roots_ok : vcM110CutCell.rootsOK vcM110CutRoots = true := by decide +kernel

theorem vcM110Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM110CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM110Cut_margin_le (i : Fin 3) : curvatureLoss vcM110CutCell vcM110CutCaps i ≤ vcM110CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM111CutCell : ParameterCell := ⟨⟨1/8, 3/20⟩, ⟨17/40, 9/20⟩, ⟨1/36, 1/18⟩⟩
def vcM111CutRoots : Fin 3 → RatBounds := ![⟨49761720196711/35184372088832, 444896951573585/281474976710656⟩, ⟨331033369612017/281474976710656, 373458971466485/281474976710656⟩, ⟨82763539240791/70368744177664, 94996193534793/70368744177664⟩]
def vcM111CutCaps : Fin 3 → Fin 3 → ℚ := ![![3167253533/20000000, 11482053653/100000000, 2407433767/20000000], ![452076197/10000000, 818440669/20000000, 13063143/312500], ![670714841/50000000, 136862903/12500000, 1159241793/100000000]]
def vcM111CutWeightFloor : ℚ := 123724653/100000000
def vcM111CutMargins : Fin 3 → ℚ := ![171977467/10000000000, 33058573/2500000000, 68939599/5000000000]

theorem vcM111Cut_roots_ok : vcM111CutCell.rootsOK vcM111CutRoots = true := by decide +kernel

theorem vcM111Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM111CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM111Cut_margin_le (i : Fin 3) : curvatureLoss vcM111CutCell vcM111CutCaps i ≤ vcM111CutMargins i := by
  fin_cases i <;> decide +kernel


end HlawkaSchatten.BelowExponent.Vertex
