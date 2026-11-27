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

def vcM114CutCell : ParameterCell := ⟨⟨3/20, 7/40⟩, ⟨7/40, 1/5⟩, ⟨0, 1/36⟩⟩
def vcM114CutRoots : Fin 3 → RatBounds := ![⟨423012741828365/281474976710656, 238058386552371/140737488355328⟩, ⟨417672212144967/281474976710656, 470388036018559/281474976710656⟩, ⟨72276606022153/70368744177664, 342973068091903/281474976710656⟩]
def vcM114CutCaps : Fin 3 → Fin 3 → ℚ := ![![4996503787/25000000, 2190204553/12500000, 3027331207/25000000], ![876267533/3125000, 586437587/2000000, 3792268247/20000000], ![4012351/312500, 649933821/50000000, 771963789/100000000]]
def vcM114CutWeightFloor : ℚ := 105800643/100000000
def vcM114CutMargins : Fin 3 → ℚ := ![193795713/5000000000, 378502271/10000000000, 125092609/5000000000]

theorem vcM114Cut_roots_ok : vcM114CutCell.rootsOK vcM114CutRoots = true := by decide +kernel

theorem vcM114Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM114CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM114Cut_margin_le (i : Fin 3) : curvatureLoss vcM114CutCell vcM114CutCaps i ≤ vcM114CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM115CutCell : ParameterCell := ⟨⟨3/20, 7/40⟩, ⟨7/40, 1/5⟩, ⟨1/36, 1/18⟩⟩
def vcM115CutRoots : Fin 3 → RatBounds := ![⟨418432259262471/281474976710656, 470691780561389/281474976710656⟩, ⟨206465256766447/140737488355328, 464772041317323/281474976710656⟩, ⟨35465178995505/35184372088832, 336287159301015/281474976710656⟩]
def vcM115CutCaps : Fin 3 → Fin 3 → ℚ := ![![21410966801/100000000, 9382768597/50000000, 6446062679/50000000], ![30020784377/100000000, 31415420441/100000000, 20146424493/100000000], ![28792361/2500000, 291094503/25000000, 68833651/10000000]]
def vcM115CutWeightFloor : ℚ := 110492101/100000000
def vcM115CutMargins : Fin 3 → ℚ := ![412918721/10000000000, 40326923/1000000000, 264752719/10000000000]

theorem vcM115Cut_roots_ok : vcM115CutCell.rootsOK vcM115CutRoots = true := by decide +kernel

theorem vcM115Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM115CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM115Cut_margin_le (i : Fin 3) : curvatureLoss vcM115CutCell vcM115CutCaps i ≤ vcM115CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM116CutCell : ParameterCell := ⟨⟨3/20, 7/40⟩, ⟨1/5, 9/40⟩, ⟨0, 1/36⟩⟩
def vcM116CutRoots : Fin 3 → RatBounds := ![⟨208290574747751/140737488355328, 233817851158043/140737488355328⟩, ⟨405970089477699/281474976710656, 28518068468759/17592186044416⟩, ⟨146697346521125/140737488355328, 172821879239115/140737488355328⟩]
def vcM116CutCaps : Fin 3 → Fin 3 → ℚ := ![![7000634437/25000000, 6115863397/25000000, 4891493947/25000000], ![7773931033/25000000, 7938339667/25000000, 22989332169/100000000], ![1800314617/100000000, 902305717/50000000, 576619053/50000000]]
def vcM116CutWeightFloor : ℚ := 104234733/100000000
def vcM116CutMargins : Fin 3 → ℚ := ![479069317/10000000000, 91319887/2000000000, 343586397/10000000000]

theorem vcM116Cut_roots_ok : vcM116CutCell.rootsOK vcM116CutRoots = true := by decide +kernel

theorem vcM116Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM116CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM116Cut_margin_le (i : Fin 3) : curvatureLoss vcM116CutCell vcM116CutCaps i ≤ vcM116CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM117CutCell : ParameterCell := ⟨⟨3/20, 7/40⟩, ⟨1/5, 9/40⟩, ⟨1/36, 1/18⟩⟩
def vcM117CutRoots : Fin 3 → RatBounds := ![⟨412128891281975/281474976710656, 462367844371645/281474976710656⟩, ⟨401211646482449/281474976710656, 225329090107375/140737488355328⟩, ⟨72013316348495/70368744177664, 169529493408681/140737488355328⟩]
def vcM117CutCaps : Fin 3 → Fin 3 → ℚ := ![![335956231/2000000, 7144197059/50000000, 5121401227/50000000], ![2299168847/12500000, 4814997901/25000000, 12747183471/100000000], ![273668833/25000000, 34368249/3125000, 347659171/50000000]]
def vcM117CutWeightFloor : ℚ := 6998723/6250000
def vcM117CutMargins : Fin 3 → ℚ := ![285489167/10000000000, 34088031/1250000000, 93157827/5000000000]

theorem vcM117Cut_roots_ok : vcM117CutCell.rootsOK vcM117CutRoots = true := by decide +kernel

theorem vcM117Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM117CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM117Cut_margin_le (i : Fin 3) : curvatureLoss vcM117CutCell vcM117CutCaps i ≤ vcM117CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM118CutCell : ParameterCell := ⟨⟨3/20, 7/40⟩, ⟨9/40, 1/4⟩, ⟨0, 1/36⟩⟩
def vcM118CutRoots : Fin 3 → RatBounds := ![⟨25696368824667/17592186044416, 460579415164087/281474976710656⟩, ⟨395291501409161/281474976710656, 443673292804269/281474976710656⟩, ⟨148892914332627/140737488355328, 174378992638453/140737488355328⟩]
def vcM118CutCaps : Fin 3 → Fin 3 → ℚ := ![![5668692509/25000000, 19380645783/100000000, 3199895303/20000000], ![1983386167/10000000, 4066170221/20000000, 950741901/6250000], ![1710699569/100000000, 169578187/10000000, 1154656441/100000000]]
def vcM118CutWeightFloor : ℚ := 52897389/50000000
def vcM118CutMargins : Fin 3 → ℚ := ![348598489/10000000000, 326601991/10000000000, 254975381/10000000000]

theorem vcM118Cut_roots_ok : vcM118CutCell.rootsOK vcM118CutRoots = true := by decide +kernel

theorem vcM118Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM118CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM118Cut_margin_le (i : Fin 3) : curvatureLoss vcM118CutCell vcM118CutCaps i ≤ vcM118CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM119CutCell : ParameterCell := ⟨⟨3/20, 7/40⟩, ⟨9/40, 1/4⟩, ⟨1/36, 1/18⟩⟩
def vcM119CutRoots : Fin 3 → RatBounds := ![⟨101699695004617/70368744177664, 227721983259463/140737488355328⟩, ⟨195256020977309/140737488355328, 438019561640891/281474976710656⟩, ⟨292487450114143/281474976710656, 342266394550177/281474976710656⟩]
def vcM119CutCaps : Fin 3 → Fin 3 → ℚ := ![![6098251931/25000000, 20826035751/100000000, 17097940073/100000000], ![10643727487/50000000, 21839231909/100000000, 3243815201/20000000], ![307876337/20000000, 1522350341/100000000, 1033819811/100000000]]
def vcM119CutWeightFloor : ℚ := 109781731/100000000
def vcM119CutMargins : Fin 3 → ℚ := ![371726047/10000000000, 348005567/10000000000, 54052089/2000000000]

theorem vcM119Cut_roots_ok : vcM119CutCell.rootsOK vcM119CutRoots = true := by decide +kernel

theorem vcM119Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM119CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM119Cut_margin_le (i : Fin 3) : curvatureLoss vcM119CutCell vcM119CutCaps i ≤ vcM119CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM120CutCell : ParameterCell := ⟨⟨3/20, 7/40⟩, ⟨1/4, 11/40⟩, ⟨0, 1/36⟩⟩
def vcM120CutRoots : Fin 3 → RatBounds := ![⟨101645162642683/70368744177664, 454759335019893/281474976710656⟩, ⟨385487692372301/281474976710656, 432306973065709/281474976710656⟩, ⟨302304577179595/281474976710656, 352291460541039/281474976710656⟩]
def vcM120CutCaps : Fin 3 → Fin 3 → ℚ := ![![4808192809/25000000, 1609469783/10000000, 3420604887/25000000], ![849142709/6250000, 1394415047/10000000, 2687845903/25000000], ![329196409/20000000, 1609508581/100000000, 582226881/50000000]]
def vcM120CutWeightFloor : ℚ := 671251/625000
def vcM120CutMargins : Fin 3 → ℚ := ![272274463/10000000000, 31275289/1250000000, 50530079/2500000000]

theorem vcM120Cut_roots_ok : vcM120CutCell.rootsOK vcM120CutRoots = true := by decide +kernel

theorem vcM120Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM120CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM120Cut_margin_le (i : Fin 3) : curvatureLoss vcM120CutCell vcM120CutCaps i ≤ vcM120CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM121CutCell : ParameterCell := ⟨⟨3/20, 7/40⟩, ⟨1/4, 11/40⟩, ⟨1/36, 1/18⟩⟩
def vcM121CutRoots : Fin 3 → RatBounds := ![⟨100582354553879/70368744177664, 224867233536433/140737488355328⟩, ⟨380683674062343/281474976710656, 426623812749203/281474976710656⟩, ⟨297048732337005/281474976710656, 172943202891307/140737488355328⟩]
def vcM121CutCaps : Fin 3 → Fin 3 → ℚ := ![![10346470393/50000000, 17296510759/100000000, 14645332433/100000000], ![455796439/3125000, 14978887839/100000000, 358755883/3125000], ![740266287/50000000, 90230067/6250000, 65142877/6250000]]
def vcM121CutWeightFloor : ℚ := 11149289/10000000
def vcM121CutMargins : Fin 3 → ℚ := ![144946269/5000000000, 53215189/2000000000, 13384909/625000000]

theorem vcM121Cut_roots_ok : vcM121CutCell.rootsOK vcM121CutRoots = true := by decide +kernel

theorem vcM121Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM121CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM121Cut_margin_le (i : Fin 3) : curvatureLoss vcM121CutCell vcM121CutCaps i ≤ vcM121CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM122CutCell : ParameterCell := ⟨⟨3/20, 7/40⟩, ⟨11/40, 3/10⟩, ⟨0, 1/36⟩⟩
def vcM122CutRoots : Fin 3 → RatBounds := ![⟨402808596154361/281474976710656, 450033133318557/281474976710656⟩, ⟨376438309779247/281474976710656, 26375469409847/17592186044416⟩, ⟨153487301384799/140737488355328, 356232568138011/281474976710656⟩]
def vcM122CutCaps : Fin 3 → Fin 3 → ℚ := ![![682735807/4000000, 1401157221/10000000, 12256077343/100000000], ![9938666169/100000000, 1271616417/12500000, 1616999341/20000000], ![399161411/25000000, 383884549/25000000, 1179023029/100000000]]
def vcM122CutWeightFloor : ℚ := 109059287/100000000
def vcM122CutMargins : Fin 3 → ℚ := ![226392413/10000000000, 40750359/2000000000, 170286391/10000000000]

theorem vcM122Cut_roots_ok : vcM122CutCell.rootsOK vcM122CutRoots = true := by decide +kernel

theorem vcM122Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM122CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM122Cut_margin_le (i : Fin 3) : curvatureLoss vcM122CutCell vcM122CutCaps i ≤ vcM122CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM123CutCell : ParameterCell := ⟨⟨3/20, 7/40⟩, ⟨11/40, 3/10⟩, ⟨1/36, 1/18⟩⟩
def vcM123CutRoots : Fin 3 → RatBounds := ![⟨99658359460831/70368744177664, 445099215977647/281474976710656⟩, ⟨185803383761895/140737488355328, 416289268275199/281474976710656⟩, ⟨301760757667375/281474976710656, 174954187807111/140737488355328⟩]
def vcM123CutCaps : Fin 3 → Fin 3 → ℚ := ![![18364751521/100000000, 15057262407/100000000, 13136725743/100000000], ![5334683109/50000000, 437082657/4000000, 1080599303/12500000], ![1435675363/100000000, 275273697/20000000, 105511261/10000000]]
def vcM123CutWeightFloor : ℚ := 113234057/100000000
def vcM123CutMargins : Fin 3 → ℚ := ![240676223/10000000000, 6758679/312500000, 180344753/10000000000]

theorem vcM123Cut_roots_ok : vcM123CutCell.rootsOK vcM123CutRoots = true := by decide +kernel

theorem vcM123Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM123CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM123Cut_margin_le (i : Fin 3) : curvatureLoss vcM123CutCell vcM123CutCaps i ≤ vcM123CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM124CutCell : ParameterCell := ⟨⟨3/20, 7/40⟩, ⟨3/10, 13/40⟩, ⟨0, 1/36⟩⟩
def vcM124CutRoots : Fin 3 → RatBounds := ![⟨99939234740785/70368744177664, 446293508680227/281474976710656⟩, ⟨368044672159085/281474976710656, 412630144360001/281474976710656⟩, ⟨311819426350551/281474976710656, 360579906422215/281474976710656⟩]
def vcM124CutCaps : Fin 3 → Fin 3 → ℚ := ![![1970840169/12500000, 6360593447/50000000, 5723506127/50000000], ![7707760053/100000000, 7838503743/100000000, 1286589667/20000000], ![779868157/50000000, 294253831/20000000, 1197962701/100000000]]
def vcM124CutWeightFloor : ℚ := 55390257/50000000
def vcM124CutMargins : Fin 3 → ℚ := ![9921907/500000000, 34962613/2000000000, 151241617/10000000000]

theorem vcM124Cut_roots_ok : vcM124CutCell.rootsOK vcM124CutRoots = true := by decide +kernel

theorem vcM124Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM124CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM124Cut_margin_le (i : Fin 3) : curvatureLoss vcM124CutCell vcM124CutCaps i ≤ vcM124CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM125CutCell : ParameterCell := ⟨⟨3/20, 7/40⟩, ⟨3/10, 13/40⟩, ⟨1/36, 1/18⟩⟩
def vcM125CutRoots : Fin 3 → RatBounds := ![⟨197821576632613/140737488355328, 441432578640809/281474976710656⟩, ⟨181591551389877/140737488355328, 406871887585219/281474976710656⟩, ⟨76661753060395/70368744177664, 354331622312951/281474976710656⟩]
def vcM125CutCaps : Fin 3 → Fin 3 → ℚ := ![![16976476613/100000000, 13668596881/100000000, 6152793553/50000000], ![2068154717/25000000, 841591483/10000000, 3442656363/50000000], ![280424379/20000000, 1318005521/100000000, 1071931059/100000000]]
def vcM125CutWeightFloor : ℚ := 11501889/10000000
def vcM125CutMargins : Fin 3 → ℚ := ![210782111/10000000000, 185247493/10000000000, 160267747/10000000000]

theorem vcM125Cut_roots_ok : vcM125CutCell.rootsOK vcM125CutRoots = true := by decide +kernel

theorem vcM125Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM125CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM125Cut_margin_le (i : Fin 3) : curvatureLoss vcM125CutCell vcM125CutCaps i ≤ vcM125CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM126CutCell : ParameterCell := ⟨⟨3/20, 7/40⟩, ⟨13/40, 7/20⟩, ⟨0, 1/36⟩⟩
def vcM126CutRoots : Fin 3 → RatBounds := ![⟨198686480879267/140737488355328, 110865140223483/70368744177664⟩, ⟨360224877919495/281474976710656, 404058836579229/281474976710656⟩, ⟨316863197664269/281474976710656, 182670420951605/140737488355328⟩]
def vcM126CutCaps : Fin 3 → Fin 3 → ℚ := ![![302720431/2000000, 375621309/3125000, 11150633517/100000000], ![6330378871/100000000, 1588563999/25000000, 2704829843/50000000], ![1533221109/100000000, 707441027/50000000, 1221073499/100000000]]
def vcM126CutWeightFloor : ℚ := 112511427/100000000
def vcM126CutMargins : Fin 3 → ℚ := ![91247133/5000000000, 157194577/10000000000, 7057731/500000000]

theorem vcM126Cut_roots_ok : vcM126CutCell.rootsOK vcM126CutRoots = true := by decide +kernel

theorem vcM126Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM126CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM126Cut_margin_le (i : Fin 3) : curvatureLoss vcM126CutCell vcM126CutCaps i ≤ vcM126CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM127CutCell : ParameterCell := ⟨⟨3/20, 7/40⟩, ⟨13/40, 7/20⟩, ⟨1/36, 1/18⟩⟩
def vcM127CutRoots : Fin 3 → RatBounds := ![⟨98326675293203/70368744177664, 219327951720479/140737488355328⟩, ⟨177665575639681/140737488355328, 49782020993487/35184372088832⟩, ⟨311731595778657/281474976710656, 359164040281143/281474976710656⟩]
def vcM127CutCaps : Fin 3 → Fin 3 → ℚ := ![![8150482003/50000000, 6455921727/50000000, 12005456339/100000000], ![6791654787/100000000, 3410488419/50000000, 5795979931/100000000], ![1378024351/100000000, 1266907721/100000000, 546279873/50000000]]
def vcM127CutWeightFloor : ℚ := 29204213/25000000
def vcM127CutMargins : Fin 3 → ℚ := ![38740443/2000000000, 83191031/5000000000, 18701441/1250000000]

theorem vcM127Cut_roots_ok : vcM127CutCell.rootsOK vcM127CutRoots = true := by decide +kernel

theorem vcM127Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM127CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM127Cut_margin_le (i : Fin 3) : curvatureLoss vcM127CutCell vcM127CutCaps i ≤ vcM127CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM128CutCell : ParameterCell := ⟨⟨3/20, 7/40⟩, ⟨7/20, 3/8⟩, ⟨0, 1/36⟩⟩
def vcM128CutRoots : Fin 3 → RatBounds := ![⟨395617248814171/281474976710656, 220738292904737/140737488355328⟩, ⟨88227545607461/70368744177664, 396199797403359/281474976710656⟩, ⟨161065692337947/140737488355328, 370530774025435/281474976710656⟩]
def vcM128CutCaps : Fin 3 → Fin 3 → ℚ := ![![15073285097/100000000, 2949782157/25000000, 1413410003/12500000], ![2753010771/50000000, 5410286977/100000000, 4805005799/100000000], ![1515736097/100000000, 682542229/50000000, 1248326599/100000000]]
def vcM128CutWeightFloor : ℚ := 57149537/50000000
def vcM128CutMargins : Fin 3 → ℚ := ![87697601/5000000000, 36903721/2500000000, 137917421/10000000000]

theorem vcM128Cut_roots_ok : vcM128CutCell.rootsOK vcM128CutRoots = true := by decide +kernel

theorem vcM128Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM128CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM128Cut_margin_le (i : Fin 3) : curvatureLoss vcM128CutCell vcM128CutCaps i ≤ vcM128CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM129CutCell : ParameterCell := ⟨⟨3/20, 7/40⟩, ⟨7/20, 3/8⟩, ⟨1/36, 1/18⟩⟩
def vcM129CutRoots : Fin 3 → RatBounds := ![⟨391585303451231/281474976710656, 109178098596555/70368744177664⟩, ⟨173991235951475/140737488355328, 390348707041757/281474976710656⟩, ⟨9907497215237/8796093022208, 364421404728113/281474976710656⟩]
def vcM129CutCaps : Fin 3 → Fin 3 → ℚ := ![![4058516451/25000000, 6335140681/50000000, 6092318067/50000000], ![2952153171/50000000, 725734687/12500000, 2575729917/50000000], ![1362144401/100000000, 610938921/50000000, 558487147/50000000]]
def vcM129CutWeightFloor : ℚ := 118641197/100000000
def vcM129CutMargins : Fin 3 → ℚ := ![93047/5000000, 156130079/10000000000, 9138221/625000000]

theorem vcM129Cut_roots_ok : vcM129CutCell.rootsOK vcM129CutRoots = true := by decide +kernel

theorem vcM129Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM129CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM129Cut_margin_le (i : Fin 3) : curvatureLoss vcM129CutCell vcM129CutCaps i ≤ vcM129CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM130CutCell : ParameterCell := ⟨⟨3/20, 7/40⟩, ⟨3/8, 2/5⟩, ⟨0, 1/36⟩⟩
def vcM130CutRoots : Fin 3 → RatBounds := ![⟨98615433979711/70368744177664, 13759455349683/8796093022208⟩, ⟨346042266011051/281474976710656, 388976830597259/281474976710656⟩, ⟨327651440823555/281474976710656, 376172944845343/281474976710656⟩]
def vcM130CutCaps : Fin 3 → Fin 3 → ℚ := ![![15555500827/100000000, 12016963973/100000000, 2980107903/25000000], ![633564213/12500000, 4854706149/100000000, 141414599/3125000], ![150643223/10000000, 1320955219/100000000, 1279853083/100000000]]
def vcM130CutWeightFloor : ℚ := 58079831/50000000
def vcM130CutMargins : Fin 3 → ℚ := ![87827373/5000000000, 72275309/5000000000, 35206571/2500000000]

theorem vcM130Cut_roots_ok : vcM130CutCell.rootsOK vcM130CutRoots = true := by decide +kernel

theorem vcM130Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM130CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM130Cut_margin_le (i : Fin 3) : curvatureLoss vcM130CutCell vcM130CutCaps i ≤ vcM130CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM131CutCell : ParameterCell := ⟨⟨3/20, 7/40⟩, ⟨3/8, 2/5⟩, ⟨1/36, 1/18⟩⟩
def vcM131CutRoots : Fin 3 → RatBounds := ![⟨390451347417755/281474976710656, 108890914885559/70368744177664⟩, ⟨341078993242461/281474976710656, 95768393407175/70368744177664⟩, ⟨80649832340645/70368744177664, 370127207879255/281474976710656⟩]
def vcM131CutCaps : Fin 3 → Fin 3 → ℚ := ![![1047122161/6250000, 644922151/5000000, 128527417/1000000], ![271677589/5000000, 5207634123/100000000, 2426726367/50000000], ![1353712309/100000000, 591031041/50000000, 572648851/50000000]]
def vcM131CutWeightFloor : ℚ := 30131767/25000000
def vcM131CutMargins : Fin 3 → ℚ := ![186396533/10000000000, 15285479/1000000000, 9336007/625000000]

theorem vcM131Cut_roots_ok : vcM131CutCell.rootsOK vcM131CutRoots = true := by decide +kernel

theorem vcM131Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM131CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM131Cut_margin_le (i : Fin 3) : curvatureLoss vcM131CutCell vcM131CutCaps i ≤ vcM131CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM132CutCell : ParameterCell := ⟨⟨3/20, 7/40⟩, ⟨2/5, 17/40⟩, ⟨0, 1/36⟩⟩
def vcM132CutRoots : Fin 3 → RatBounds := ![⟨393888389842135/281474976710656, 439915950163869/281474976710656⟩, ⟨42446392225193/35184372088832, 382327958446141/281474976710656⟩, ⟨83363374765285/70368744177664, 95574678107253/70368744177664⟩]
def vcM132CutCaps : Fin 3 → Fin 3 → ℚ := ![![4158021079/25000000, 12686706397/100000000, 13056021469/100000000], ![4981334249/100000000, 4640906621/100000000, 4585295261/100000000], ![376221471/25000000, 1281847941/100000000, 263190043/20000000]]
def vcM132CutWeightFloor : ℚ := 118103589/100000000
def vcM132CutMargins : Fin 3 → ℚ := ![3667391/200000000, 3693387/250000000, 150515209/10000000000]

theorem vcM132Cut_roots_ok : vcM132CutCell.rootsOK vcM132CutRoots = true := by decide +kernel

theorem vcM132Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM132CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM132Cut_margin_le (i : Fin 3) : curvatureLoss vcM132CutCell vcM132CutCaps i ≤ vcM132CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM133CutCell : ParameterCell := ⟨⟨3/20, 7/40⟩, ⟨2/5, 17/40⟩, ⟨1/36, 1/18⟩⟩
def vcM133CutRoots : Fin 3 → RatBounds := ![⟨194943542859123/140737488355328, 435187498395263/281474976710656⟩, ⟨334570928130153/281474976710656, 376368948669319/281474976710656⟩, ⟨328439884463873/281474976710656, 376312949232413/281474976710656⟩]
def vcM133CutCaps : Fin 3 → Fin 3 → ℚ := ![![4478439927/25000000, 13609935759/100000000, 3520313781/25000000], ![5340934661/100000000, 1244231267/25000000, 2459472589/50000000], ![1352345299/100000000, 229372159/20000000, 1177806039/100000000]]
def vcM133CutWeightFloor : ℚ := 15310643/12500000
def vcM133CutMargins : Fin 3 → ℚ := ![97360377/5000000000, 78135697/5000000000, 159799077/10000000000]

theorem vcM133Cut_roots_ok : vcM133CutCell.rootsOK vcM133CutRoots = true := by decide +kernel

theorem vcM133Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM133CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM133Cut_margin_le (i : Fin 3) : curvatureLoss vcM133CutCell vcM133CutCaps i ≤ vcM133CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM134CutCell : ParameterCell := ⟨⟨7/40, 1/5⟩, ⟨7/40, 1/5⟩, ⟨0, 1/36⟩⟩
def vcM134CutRoots : Fin 3 → RatBounds := ![⟨410978835920699/281474976710656, 230767129695411/140737488355328⟩, ⟨410978835920699/281474976710656, 230767129695411/140737488355328⟩, ⟨9160938890155/8796093022208, 172645016070743/140737488355328⟩]
def vcM134CutCaps : Fin 3 → Fin 3 → ℚ := ![![18649811143/100000000, 4185551897/25000000, 12075328759/100000000], ![31349308829/100000000, 3309742277/10000000, 22295024129/100000000], ![50568661/4000000, 641043291/50000000, 100059223/12500000]]
def vcM134CutWeightFloor : ℚ := 26774887/25000000
def vcM134CutMargins : Fin 3 → ℚ := ![100702893/2500000000, 401737917/10000000000, 276239001/10000000000]

theorem vcM134Cut_roots_ok : vcM134CutCell.rootsOK vcM134CutRoots = true := by decide +kernel

theorem vcM134Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM134CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM134Cut_margin_le (i : Fin 3) : curvatureLoss vcM134CutCell vcM134CutCaps i ≤ vcM134CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM135CutCell : ParameterCell := ⟨⟨7/40, 1/5⟩, ⟨7/40, 1/5⟩, ⟨1/36, 1/18⟩⟩
def vcM135CutRoots : Fin 3 → RatBounds := ![⟨406376223421881/281474976710656, 228044473759621/140737488355328⟩, ⟨406376223421881/281474976710656, 228044473759621/140737488355328⟩, ⟨287818751996049/281474976710656, 84679314644291/70368744177664⟩]
def vcM135CutCaps : Fin 3 → Fin 3 → ℚ := ![![10001844183/50000000, 17942021017/100000000, 12863391397/100000000], ![33580082013/100000000, 7096618571/20000000, 23714658797/100000000], ![1133992141/100000000, 1149414697/100000000, 142839841/20000000]]
def vcM135CutWeightFloor : ℚ := 55875363/50000000
def vcM135CutMargins : Fin 3 → ℚ := ![429560631/10000000000, 214234939/5000000000, 292654513/10000000000]

theorem vcM135Cut_roots_ok : vcM135CutCell.rootsOK vcM135CutRoots = true := by decide +kernel

theorem vcM135Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM135CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM135Cut_margin_le (i : Fin 3) : curvatureLoss vcM135CutCell vcM135CutCaps i ≤ vcM135CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM136CutCell : ParameterCell := ⟨⟨7/40, 1/5⟩, ⟨1/5, 9/40⟩, ⟨0, 1/36⟩⟩
def vcM136CutRoots : Fin 3 → RatBounds := ![⟨202648503748977/140737488355328, 113534831045549/70368744177664⟩, ⟨400023667527527/281474976710656, 448516956278625/281474976710656⟩, ⟨297305915422201/281474976710656, 174035955716555/140737488355328⟩]
def vcM136CutCaps : Fin 3 → Fin 3 → ℚ := ![![27443336101/100000000, 12205133847/50000000, 10083388991/50000000], ![36296829929/100000000, 4655762343/12500000, 13953130843/50000000], ![1789829171/100000000, 361137191/20000000, 601757887/50000000]]
def vcM136CutWeightFloor : ℚ := 105455283/100000000
def vcM136CutMargins : Fin 3 → ℚ := ![25761653/500000000, 124776579/2500000000, 387178607/10000000000]

theorem vcM136Cut_roots_ok : vcM136CutCell.rootsOK vcM136CutRoots = true := by decide +kernel

theorem vcM136Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM136CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM136Cut_margin_le (i : Fin 3) : curvatureLoss vcM136CutCell vcM136CutCaps i ≤ vcM136CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM137CutCell : ParameterCell := ⟨⟨7/40, 1/5⟩, ⟨1/5, 9/40⟩, ⟨1/36, 1/18⟩⟩
def vcM137CutRoots : Fin 3 → RatBounds := ![⟨400813326484623/281474976710656, 448838413210537/281474976710656⟩, ⟨98848694655189/70368744177664, 110760906287397/70368744177664⟩, ⟨292026834097755/281474976710656, 341603071124151/281474976710656⟩]
def vcM137CutCaps : Fin 3 → Fin 3 → ℚ := ![![802953489/5000000, 14036527393/100000000, 2093422789/20000000], ![20673564337/100000000, 43603363/200000, 3015377679/20000000], ![538223601/50000000, 1085115313/100000000, 721636861/100000000]]
def vcM137CutWeightFloor : ℚ := 28301717/25000000
def vcM137CutMargins : Fin 3 → ℚ := ![37169513/1250000000, 72613003/2500000000, 206522751/10000000000]

theorem vcM137Cut_roots_ok : vcM137CutCell.rootsOK vcM137CutRoots = true := by decide +kernel

theorem vcM137Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM137CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM137Cut_margin_le (i : Fin 3) : curvatureLoss vcM137CutCell vcM137CutCaps i ≤ vcM137CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM138CutCell : ParameterCell := ⟨⟨7/40, 1/5⟩, ⟨9/40, 1/4⟩, ⟨0, 1/36⟩⟩
def vcM138CutRoots : Fin 3 → RatBounds := ![⟨12515781998195/8796093022208, 448001356624361/281474976710656⟩, ⟨389988295054207/281474976710656, 436813082955303/281474976710656⟩, ⟨301594801463413/281474976710656, 175642965785207/140737488355328⟩]
def vcM138CutCaps : Fin 3 → Fin 3 → ℚ := ![![4561004159/20000000, 124440599/625000, 3388973543/20000000], ![4624362963/20000000, 23745216681/100000000, 18390714203/100000000], ![1700886601/100000000, 847940193/50000000, 241010409/20000000]]
def vcM138CutWeightFloor : ℚ := 10701613/10000000
def vcM138CutMargins : Fin 3 → ℚ := ![4690107/125000000, 178708563/5000000000, 71920509/2500000000]

theorem vcM138Cut_roots_ok : vcM138CutCell.rootsOK vcM138CutRoots = true := by decide +kernel

theorem vcM138Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM138CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM138Cut_margin_le (i : Fin 3) : curvatureLoss vcM138CutCell vcM138CutCaps i ≤ vcM138CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM139CutCell : ParameterCell := ⟨⟨7/40, 1/5⟩, ⟨9/40, 1/4⟩, ⟨1/36, 1/18⟩⟩
def vcM139CutRoots : Fin 3 → RatBounds := ![⟨396122161219579/281474976710656, 221410899000947/140737488355328⟩, ⟨385329688886113/281474976710656, 431305307630515/281474976710656⟩, ⟨296366648470005/281474976710656, 172456714463689/140737488355328⟩]
def vcM139CutCaps : Fin 3 → Fin 3 → ℚ := ![![24557091511/100000000, 21409186847/100000000, 9067262569/50000000], ![24828062583/100000000, 2553209129/10000000, 19633356619/100000000], ![1530194891/100000000, 1522807323/100000000, 134897581/12500000]]
def vcM139CutWeightFloor : ℚ := 22182841/20000000
def vcM139CutMargins : Fin 3 → ℚ := ![400580341/10000000000, 381416307/10000000000, 305470341/10000000000]

theorem vcM139Cut_roots_ok : vcM139CutCell.rootsOK vcM139CutRoots = true := by decide +kernel

theorem vcM139Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM139CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM139Cut_margin_le (i : Fin 3) : curvatureLoss vcM139CutCell vcM139CutCaps i ≤ vcM139CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM140CutCell : ParameterCell := ⟨⟨7/40, 1/5⟩, ⟨1/4, 11/40⟩, ⟨0, 1/36⟩⟩
def vcM140CutRoots : Fin 3 → RatBounds := ![⟨396508253038855/281474976710656, 110741965893321/70368744177664⟩, ⟨380744736510581/281474976710656, 426226743924937/281474976710656⟩, ⟨38254614251199/35184372088832, 88728393147779/70368744177664⟩]
def vcM140CutCaps : Fin 3 → Fin 3 → ℚ := ![![247833139/1250000, 8501946161/50000000, 14874162033/100000000], ![1971447031/12500000, 2022131613/12500000, 6464030249/50000000], ![327657711/20000000, 805579671/50000000, 303594047/25000000]]
def vcM140CutWeightFloor : ℚ := 108594891/100000000
def vcM140CutMargins : Fin 3 → ℚ := ![146956273/5000000000, 137382933/5000000000, 228917597/10000000000]

theorem vcM140Cut_roots_ok : vcM140CutCell.rootsOK vcM140CutRoots = true := by decide +kernel

theorem vcM140Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM140CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM140Cut_margin_le (i : Fin 3) : curvatureLoss vcM140CutCell vcM140CutCaps i ≤ vcM140CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM141CutCell : ParameterCell := ⟨⟨7/40, 1/5⟩, ⟨1/4, 11/40⟩, ⟨1/36, 1/18⟩⟩
def vcM141CutRoots : Fin 3 → RatBounds := ![⟨196104844584149/140737488355328, 27368066556365/17592186044416⟩, ⟨376053524065971/281474976710656, 105169761868299/70368744177664⟩, ⟨300858549870291/281474976710656, 348631010407585/281474976710656⟩]
def vcM141CutCaps : Fin 3 → Fin 3 → ℚ := ![![21357094101/100000000, 285704407/1562500, 7972899031/50000000], ![4235707861/25000000, 17401711343/100000000, 345706737/2500000], ![368415041/25000000, 722939681/50000000, 217489719/20000000]]
def vcM141CutWeightFloor : ℚ := 112599139/100000000
def vcM141CutMargins : Fin 3 → ℚ := ![9794741/312500000, 29274867/1000000000, 60774603/2500000000]

theorem vcM141Cut_roots_ok : vcM141CutCell.rootsOK vcM141CutRoots = true := by decide +kernel

theorem vcM141Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM141CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM141Cut_margin_le (i : Fin 3) : curvatureLoss vcM141CutCell vcM141CutCaps i ≤ vcM141CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM142CutCell : ParameterCell := ⟨⟨7/40, 1/5⟩, ⟨11/40, 3/10⟩, ⟨0, 1/36⟩⟩
def vcM142CutRoots : Fin 3 → RatBounds := ![⟨393233072624797/281474976710656, 438923360987735/281474976710656⟩, ⟨372188532706451/281474976710656, 416603238652223/281474976710656⟩, ⟨155326324325869/140737488355328, 358947497617197/281474976710656⟩]
def vcM142CutCaps : Fin 3 → Fin 3 → ℚ := ![![2250425869/12500000, 15187033407/100000000, 6821414913/50000000], ![2294737511/20000000, 2928968193/25000000, 9656310319/100000000], ![397818707/25000000, 1539618327/100000000, 30726863/2500000]]
def vcM142CutWeightFloor : ℚ := 4408247/4000000
def vcM142CutMargins : Fin 3 → ℚ := ![49127549/2000000000, 225028669/10000000000, 24234879/1250000000]

theorem vcM142Cut_roots_ok : vcM142CutCell.rootsOK vcM142CutRoots = true := by decide +kernel

theorem vcM142Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM142CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM142Cut_margin_le (i : Fin 3) : curvatureLoss vcM142CutCell vcM142CutCaps i ≤ vcM142CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM143CutCell : ParameterCell := ⟨⟨7/40, 1/5⟩, ⟨11/40, 3/10⟩, ⟨1/36, 1/18⟩⟩
def vcM143CutRoots : Fin 3 → RatBounds := ![⟨194501765930857/140737488355328, 216963300142913/140737488355328⟩, ⟨367462260529261/281474976710656, 411010849719611/281474976710656⟩, ⟨305523029792467/281474976710656, 352749379101869/281474976710656⟩]
def vcM143CutCaps : Fin 3 → Fin 3 → ℚ := ![![9698914557/50000000, 16330425817/100000000, 14649645049/100000000], ![3081938449/25000000, 3151361749/25000000, 5172578427/50000000], ![89449817/6250000, 1380964813/100000000, 34393291/3125000]]
def vcM143CutWeightFloor : ℚ := 28572821/25000000
def vcM143CutMargins : Fin 3 → ℚ := ![261660101/10000000000, 119690499/5000000000, 1608493/78125000]

theorem vcM143Cut_roots_ok : vcM143CutCell.rootsOK vcM143CutRoots = true := by decide +kernel

theorem vcM143Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM143CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM143Cut_margin_le (i : Fin 3) : curvatureLoss vcM143CutCell vcM143CutCaps i ≤ vcM143CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM144CutCell : ParameterCell := ⟨⟨7/40, 1/5⟩, ⟨3/10, 13/40⟩, ⟨0, 1/36⟩⟩
def vcM144CutRoots : Fin 3 → RatBounds := ![⟨195311293414851/140737488355328, 435780978774359/281474976710656⟩, ⟨182116689478799/140737488355328, 50977365542587/35184372088832⟩, ⟨39432900126007/35184372088832, 363389671773189/281474976710656⟩]
def vcM144CutCaps : Fin 3 → Fin 3 → ℚ := ![![852667521/5000000, 14172054613/100000000, 13079889887/100000000], ![277094241/3125000, 4488180951/50000000, 7638185023/100000000], ![389318049/25000000, 1478538973/100000000, 1248907357/100000000]]
def vcM144CutWeightFloor : ℚ := 111862191/100000000
def vcM144CutMargins : Fin 3 → ℚ := ![217522847/10000000000, 48776901/2500000000, 173905749/10000000000]

theorem vcM144Cut_roots_ok : vcM144CutCell.rootsOK vcM144CutRoots = true := by decide +kernel

theorem vcM144Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM144CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM144Cut_margin_le (i : Fin 3) : curvatureLoss vcM144CutCell vcM144CutCaps i ≤ vcM144CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM145CutCell : ParameterCell := ⟨⟨7/40, 1/5⟩, ⟨3/10, 13/40⟩, ⟨1/36, 1/18⟩⟩
def vcM145CutRoots : Fin 3 → RatBounds := ![⟨386447756243483/281474976710656, 215424474562213/140737488355328⟩, ⟨359469939492713/281474976710656, 402177591570123/281474976710656⟩, ⟨155190670994917/140737488355328, 357271176337997/281474976710656⟩]
def vcM145CutCaps : Fin 3 → Fin 3 → ℚ := ![![143644331/781250, 15236221139/100000000, 3520241291/25000000], ![9526478521/100000000, 603526733/6250000, 1638628709/20000000], ![350288663/25000000, 165781051/12500000, 559432983/50000000]]
def vcM145CutWeightFloor : ℚ := 116007837/100000000
def vcM145CutMargins : Fin 3 → ℚ := ![28948021/1250000000, 6477049/312500000, 92404003/5000000000]

theorem vcM145Cut_roots_ok : vcM145CutCell.rootsOK vcM145CutRoots = true := by decide +kernel

theorem vcM145Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM145CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM145Cut_margin_le (i : Fin 3) : curvatureLoss vcM145CutCell vcM145CutCaps i ≤ vcM145CutMargins i := by
  fin_cases i <;> decide +kernel


end HlawkaSchatten.BelowExponent.Vertex
