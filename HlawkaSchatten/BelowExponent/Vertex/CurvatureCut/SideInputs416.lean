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

def scE110CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨1/5, 17/80⟩, ⟨3/20, 13/80⟩⟩
def scE110CutRoots : Fin 3 → RatBounds := ![⟨257269446605079/140737488355328, 553496747071557/281474976710656⟩, ⟨115588569233181/70368744177664, 498179813598361/281474976710656⟩, ⟨261713005702325/281474976710656, 294068128187357/281474976710656⟩]
def scE110CutCaps : Fin 3 → Fin 3 → ℚ := ![![26876443187/100000000, 20702471339/100000000, 8214413829/100000000], ![13333229861/100000000, 1428597621/10000000, 3716335539/100000000], ![68190037/12500000, 560085843/100000000, 256122903/100000000]]
def scE110CutWeightFloor : ℚ := 130445427/100000000
def scE110CutMargins : Fin 3 → ℚ := ![79599987/10000000000, 6943073/1000000000, 4760497/2000000000]

theorem scE110Cut_roots_ok : scE110CutCell.rootsOK scE110CutRoots = true := by decide +kernel

theorem scE110Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE110CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE110Cut_margin_le (i : Fin 3) : curvatureLoss scE110CutCell scE110CutCaps i ≤ scE110CutMargins i := by
  fin_cases i <;> decide +kernel

def scE111CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨1/5, 17/80⟩, ⟨13/80, 1/6⟩⟩
def scE111CutRoots : Fin 3 → RatBounds := ![⟨257119656244927/140737488355328, 551786036163793/281474976710656⟩, ⟨7214584453601/4398046511104, 496116972483351/281474976710656⟩, ⟨130559681251859/140737488355328, 146021254159175/140737488355328⟩]
def scE111CutCaps : Fin 3 → Fin 3 → ℚ := ![![13344610011/50000000, 10277514209/50000000, 4044996913/50000000], ![6638798773/50000000, 3541758017/25000000, 3623301757/100000000], ![424657529/100000000, 438564043/100000000, 41130893/20000000]]
def scE111CutWeightFloor : ℚ := 66678693/50000000
def scE111CutMargins : Fin 3 → ℚ := ![19538087/2500000000, 67911699/10000000000, 22922161/10000000000]

theorem scE111Cut_roots_ok : scE111CutCell.rootsOK scE111CutRoots = true := by decide +kernel

theorem scE111Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE111CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE111Cut_margin_le (i : Fin 3) : curvatureLoss scE111CutCell scE111CutCaps i ≤ scE111CutMargins i := by
  fin_cases i <;> decide +kernel

def scE112CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨17/80, 9/40⟩, ⟨1/8, 11/80⟩⟩
def scE112CutRoots : Fin 3 → RatBounds := ![⟨15945951733401/8796093022208, 273919165446827/140737488355328⟩, ⟨456355484661183/281474976710656, 245420485729035/140737488355328⟩, ⟨133991705372511/140737488355328, 299816067770527/281474976710656⟩]
def scE112CutCaps : Fin 3 → Fin 3 → ℚ := ![![1442456749/6250000, 3488862803/20000000, 448684581/6250000], ![5589279243/50000000, 1497679663/12500000, 644409003/20000000], ![576549093/100000000, 292268089/50000000, 55690467/20000000]]
def scE112CutWeightFloor : ℚ := 31713271/25000000
def scE112CutMargins : Fin 3 → ℚ := ![531531/78125000, 58613843/10000000000, 20858303/10000000000]

theorem scE112Cut_roots_ok : scE112CutCell.rootsOK scE112CutRoots = true := by decide +kernel

theorem scE112Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE112CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE112Cut_margin_le (i : Fin 3) : curvatureLoss scE112CutCell scE112CutCaps i ≤ scE112CutMargins i := by
  fin_cases i <;> decide +kernel

def scE113CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨17/80, 9/40⟩, ⟨11/80, 3/20⟩⟩
def scE113CutRoots : Fin 3 → RatBounds := ![⟨254401773548399/140737488355328, 546250263471251/281474976710656⟩, ⟨454355350619975/281474976710656, 244335572885695/140737488355328⟩, ⟨266064011540341/281474976710656, 74413044575547/70368744177664⟩]
def scE113CutCaps : Fin 3 → Fin 3 → ℚ := ![![11761187423/50000000, 17795015007/100000000, 7310044039/100000000], ![5693977593/50000000, 609846559/5000000, 1640475659/50000000], ![553315023/100000000, 560332053/100000000, 133431143/50000000]]
def scE113CutWeightFloor : ℚ := 32290227/25000000
def scE113CutMargins : Fin 3 → ℚ := ![17316233/2500000000, 59672419/10000000000, 10603377/5000000000]

theorem scE113Cut_roots_ok : scE113CutCell.rootsOK scE113CutRoots = true := by decide +kernel

theorem scE113Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE113CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE113Cut_margin_le (i : Fin 3) : curvatureLoss scE113CutCell scE113CutCaps i ≤ scE113CutMargins i := by
  fin_cases i <;> decide +kernel

def scE114CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨17/80, 9/40⟩, ⟨3/20, 13/80⟩⟩
def scE114CutRoots : Fin 3 → RatBounds := ![⟨507386533204411/281474976710656, 17022418304263/8796093022208⟩, ⟨226213054389217/140737488355328, 486579615266017/281474976710656⟩, ⟨132108397892385/140737488355328, 295571212830013/281474976710656⟩]
def scE114CutCaps : Fin 3 → Fin 3 → ℚ := ![![2396464199/10000000, 70877596/390625, 930105173/12500000], ![11596846549/100000000, 6205992299/50000000, 1669851589/50000000], ![531445139/100000000, 134396753/25000000, 127986551/50000000]]
def scE114CutWeightFloor : ℚ := 13146973/10000000
def scE114CutMargins : Fin 3 → ℚ := ![17623503/2500000000, 60730931/10000000000, 21555699/10000000000]

theorem scE114Cut_roots_ok : scE114CutCell.rootsOK scE114CutRoots = true := by decide +kernel

theorem scE114Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE114CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE114Cut_margin_le (i : Fin 3) : curvatureLoss scE114CutCell scE114CutCaps i ≤ scE114CutMargins i := by
  fin_cases i <;> decide +kernel

def scE115CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨17/80, 9/40⟩, ⟨13/80, 1/6⟩⟩
def scE115CutRoots : Fin 3 → RatBounds := ![⟨507102965512981/281474976710656, 271519731169031/140737488355328⟩, ⟨225905057871637/140737488355328, 60567135829941/35184372088832⟩, ⟨131811612875295/140737488355328, 146777295855435/140737488355328⟩]
def scE115CutCaps : Fin 3 → Fin 3 → ℚ := ![![5946991387/25000000, 2251039131/12500000, 7320534723/100000000], ![11543249157/100000000, 6149878629/50000000, 812682223/25000000], ![205598751/50000000, 209180927/50000000, 102139111/50000000]]
def scE115CutWeightFloor : ℚ := 134396073/100000000
def scE115CutMargins : Fin 3 → ℚ := ![13819103/2000000000, 59286241/10000000000, 20691331/10000000000]

theorem scE115Cut_roots_ok : scE115CutCell.rootsOK scE115CutRoots = true := by decide +kernel

theorem scE115Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE115CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE115Cut_margin_le (i : Fin 3) : curvatureLoss scE115CutCell scE115CutCaps i ≤ scE115CutMargins i := by
  fin_cases i <;> decide +kernel

def scE116CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨9/40, 19/80⟩, ⟨1/8, 11/80⟩⟩
def scE116CutRoots : Fin 3 → RatBounds := ![⟨251849697147135/140737488355328, 269919473529891/140737488355328⟩, ⟨223527266959679/140737488355328, 120016593239037/70368744177664⟩, ⟨16904660381013/17592186044416, 150705170826623/140737488355328⟩]
def scE116CutCaps : Fin 3 → Fin 3 → ℚ := ![![10385193827/50000000, 3088708837/20000000, 657227219/10000000], ![4905922461/50000000, 5250242487/50000000, 584421699/20000000], ![563919681/100000000, 56295607/10000000, 139485863/50000000]]
def scE116CutWeightFloor : ℚ := 7990267/6250000
def scE116CutMargins : Fin 3 → ℚ := ![60832329/10000000000, 808929/156250000, 19088579/10000000000]

theorem scE116Cut_roots_ok : scE116CutCell.rootsOK scE116CutRoots = true := by decide +kernel

theorem scE116Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE116CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE116Cut_margin_le (i : Fin 3) : curvatureLoss scE116CutCell scE116CutCaps i ≤ scE116CutMargins i := by
  fin_cases i <;> decide +kernel

def scE117CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨9/40, 19/80⟩, ⟨11/80, 3/20⟩⟩
def scE117CutRoots : Fin 3 → RatBounds := ![⟨251132076890545/140737488355328, 538287390500627/281474976710656⟩, ⟨445068626964829/281474976710656, 477914729530133/281474976710656⟩, ⟨67138884309229/70368744177664, 74813938951815/70368744177664⟩]
def scE117CutCaps : Fin 3 → Fin 3 → ℚ := ![![5292059769/25000000, 15754702531/100000000, 6693707209/100000000], ![4997805283/50000000, 10689054239/100000000, 1487902263/50000000], ![108219097/20000000, 269785523/50000000, 33417223/12500000]]
def scE117CutWeightFloor : ℚ := 16270417/12500000
def scE117CutMargins : Fin 3 → ℚ := ![61923721/10000000000, 52701813/10000000000, 1940791/1000000000]

theorem scE117Cut_roots_ok : scE117CutCell.rootsOK scE117CutRoots = true := by decide +kernel

theorem scE117Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE117CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE117Cut_margin_le (i : Fin 3) : curvatureLoss scE117CutCell scE117CutCaps i ≤ scE117CutMargins i := by
  fin_cases i <;> decide +kernel

def scE118CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨9/40, 19/80⟩, ⟨3/20, 13/80⟩⟩
def scE118CutRoots : Fin 3 → RatBounds := ![⟨500877772418367/281474976710656, 536789820192359/281474976710656⟩, ⟨221576650843111/140737488355328, 237920473336109/140737488355328⟩, ⟨16669290458861/17592186044416, 297183699875277/281474976710656⟩]
def scE118CutCaps : Fin 3 → Fin 3 → ℚ := ![![2695677601/12500000, 3212987609/20000000, 6814874283/100000000], ![254473299/2500000, 5438621547/50000000, 1514680653/50000000], ![519616833/100000000, 517599809/100000000, 256408607/100000000]]
def scE118CutWeightFloor : ℚ := 26496689/20000000
def scE118CutMargins : Fin 3 → ℚ := ![31507783/5000000000, 10726477/2000000000, 19727821/10000000000]

theorem scE118Cut_roots_ok : scE118CutCell.rootsOK scE118CutRoots = true := by decide +kernel

theorem scE118Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE118CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE118Cut_margin_le (i : Fin 3) : curvatureLoss scE118CutCell scE118CutCaps i ≤ scE118CutMargins i := by
  fin_cases i <;> decide +kernel

def scE119CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨9/40, 19/80⟩, ⟨13/80, 1/6⟩⟩
def scE119CutRoots : Fin 3 → RatBounds := ![⟨500608987197871/281474976710656, 535141629409005/281474976710656⟩, ⟨221270813717123/140737488355328, 473816305289765/281474976710656⟩, ⟨133057631257971/140737488355328, 73793866856413/70368744177664⟩]
def scE119CutCaps : Fin 3 → Fin 3 → ℚ := ![![4279667971/20000000, 15939438581/100000000, 6699942353/100000000], ![5063608923/50000000, 10770960047/100000000, 588782073/20000000], ![200442697/50000000, 40126791/10000000, 50931211/25000000]]
def scE119CutWeightFloor : ℚ := 3385593/2500000
def scE119CutMargins : Fin 3 → ℚ := ![61660353/10000000000, 52255829/10000000000, 18879861/10000000000]

theorem scE119Cut_roots_ok : scE119CutCell.rootsOK scE119CutRoots = true := by decide +kernel

theorem scE119Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE119CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE119Cut_margin_le (i : Fin 3) : curvatureLoss scE119CutCell scE119CutCaps i ≤ scE119CutMargins i := by
  fin_cases i <;> decide +kernel

def scE120CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨19/80, 1/4⟩, ⟨1/8, 11/80⟩⟩
def scE120CutRoots : Fin 3 → RatBounds := ![⟨497709834374477/281474976710656, 532598902499043/281474976710656⟩, ⟨438339432797021/281474976710656, 117513280967303/70368744177664⟩, ⟨136481079593597/140737488355328, 18944238545543/17592186044416⟩]
def scE120CutCaps : Fin 3 → Fin 3 → ℚ := ![![2355816383/12500000, 6896143251/50000000, 758311483/12500000], ![1738151963/20000000, 2318364727/25000000, 53707189/2000000], ![276412369/50000000, 543305739/100000000, 279920477/100000000]]
def scE120CutWeightFloor : ℚ := 6441507/5000000
def scE120CutMargins : Fin 3 → ℚ := ![13715877/2500000000, 46111429/10000000000, 882009/500000000]

theorem scE120Cut_roots_ok : scE120CutCell.rootsOK scE120CutRoots = true := by decide +kernel

theorem scE120Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE120CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE120Cut_margin_le (i : Fin 3) : curvatureLoss scE120CutCell scE120CutCaps i ≤ scE120CutMargins i := by
  fin_cases i <;> decide +kernel

def scE121CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨19/80, 1/4⟩, ⟨11/80, 3/20⟩⟩
def scE121CutRoots : Fin 3 → RatBounds := ![⟨248151833561741/140737488355328, 531080666992251/281474976710656⟩, ⟨218183073217715/140737488355328, 116979362539745/70368744177664⟩, ⟨67760950674859/70368744177664, 300961954760019/281474976710656⟩]
def scE121CutCaps : Fin 3 → Fin 3 → ℚ := ![![76826111/400000, 2814097549/20000000, 1544908787/25000000], ![276680397/3125000, 117997147/1250000, 2735348017/100000000], ![265179013/50000000, 104133883/20000000, 26822527/10000000]]
def scE121CutWeightFloor : ℚ := 32790049/25000000
def scE121CutMargins : Fin 3 → ℚ := ![5584113/1000000000, 46935409/10000000000, 8967977/5000000000]

theorem scE121Cut_roots_ok : scE121CutCell.rootsOK scE121CutRoots = true := by decide +kernel

theorem scE121Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE121CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE121Cut_margin_le (i : Fin 3) : curvatureLoss scE121CutCell scE121CutCaps i ≤ scE121CutMargins i := by
  fin_cases i <;> decide +kernel

def scE122CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨19/80, 1/4⟩, ⟨3/20, 13/80⟩⟩
def scE122CutRoots : Fin 3 → RatBounds := ![⟨247472704033803/140737488355328, 264807659714223/140737488355328⟩, ⟨434463179185835/281474976710656, 465859271323309/281474976710656⟩, ⟨67299381823009/70368744177664, 298898248697779/281474976710656⟩]
def scE122CutCaps : Fin 3 → Fin 3 → ℚ := ![![19565952597/100000000, 7173932759/50000000, 629253233/10000000], ![9016386191/100000000, 9605753457/100000000, 1392600947/50000000], ![254610333/50000000, 12485129/2500000, 128619849/50000000]]
def scE122CutWeightFloor : ℚ := 133491347/100000000
def scE122CutMargins : Fin 3 → ℚ := ![56819453/10000000000, 47759813/10000000000, 18232371/10000000000]

theorem scE122Cut_roots_ok : scE122CutCell.rootsOK scE122CutRoots = true := by decide +kernel

theorem scE122Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE122CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE122Cut_margin_le (i : Fin 3) : curvatureLoss scE122CutCell scE122CutCaps i ≤ scE122CutMargins i := by
  fin_cases i <;> decide +kernel

def scE123CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨19/80, 1/4⟩, ⟨13/80, 1/6⟩⟩
def scE123CutRoots : Fin 3 → RatBounds := ![⟨494690276706143/281474976710656, 16499817083701/8796093022208⟩, ⟨216927664994559/140737488355328, 231925200089949/140737488355328⟩, ⟨134302209611761/140737488355328, 37112233168685/35184372088832⟩]
def scE123CutCaps : Fin 3 → Fin 3 → ℚ := ![![1212909893/6250000, 14231115723/100000000, 3090857413/50000000], ![1120761567/12500000, 9504749953/100000000, 2702287551/100000000], ![391868119/100000000, 385817479/100000000, 101776453/50000000]]
def scE123CutWeightFloor : ℚ := 17055653/12500000
def scE123CutMargins : Fin 3 → ℚ := ![444003/80000000, 46442841/10000000000, 17395741/10000000000]

theorem scE123Cut_roots_ok : scE123CutCell.rootsOK scE123CutRoots = true := by decide +kernel

theorem scE123Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE123CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE123Cut_margin_le (i : Fin 3) : curvatureLoss scE123CutCell scE123CutCaps i ≤ scE123CutMargins i := by
  fin_cases i <;> decide +kernel

def scE124CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨1/4, 21/80⟩, ⟨1/8, 11/80⟩⟩
def scE124CutRoots : Fin 3 → RatBounds := ![⟨246122286412943/140737488355328, 526035564698399/281474976710656⟩, ⟨26884251692933/17592186044416, 14397292279295/8796093022208⟩, ⟨268998069533/274877906944, 76225712805539/70368744177664⟩]
def scE124CutCaps : Fin 3 → Fin 3 → ℚ := ![![8613410263/50000000, 6207259647/50000000, 5640216929/100000000], ![7767328333/100000000, 128849557/1562500, 501216957/20000000], ![543037087/100000000, 525307589/100000000, 281248843/100000000]]
def scE124CutWeightFloor : ℚ := 64907289/50000000
def scE124CutMargins : Fin 3 → ℚ := ![49877317/10000000000, 8275859/2000000000, 823003/500000000]

theorem scE124Cut_roots_ok : scE124CutCell.rootsOK scE124CutRoots = true := by decide +kernel

theorem scE124Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE124CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE124Cut_margin_le (i : Fin 3) : curvatureLoss scE124CutCell scE124CutCaps i ≤ scE124CutMargins i := by
  fin_cases i <;> decide +kernel

def scE125CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨1/4, 21/80⟩, ⟨11/80, 3/20⟩⟩
def scE125CutRoots : Fin 3 → RatBounds := ![⟨245432555795605/140737488355328, 262273888132761/140737488355328⟩, ⟨428185937773339/281474976710656, 458591705093883/281474976710656⟩, ⟨34192073134105/35184372088832, 151382597465301/140737488355328⟩]
def scE125CutCaps : Fin 3 → Fin 3 → ℚ := ![![17555043807/100000000, 12665188649/100000000, 5746388703/100000000], ![247281053/3125000, 8394093827/100000000, 2552830143/100000000], ![65110521/12500000, 1258401/250000, 16842349/6250000]]
def scE125CutWeightFloor : ℚ := 132155463/100000000
def scE125CutMargins : Fin 3 → ℚ := ![50759613/10000000000, 42114537/10000000000, 2091967/1250000000]

theorem scE125Cut_roots_ok : scE125CutCell.rootsOK scE125CutRoots = true := by decide +kernel

theorem scE125Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE125CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE125Cut_margin_le (i : Fin 3) : curvatureLoss scE125CutCell scE125CutCaps i ≤ scE125CutMargins i := by
  fin_cases i <;> decide +kernel

def scE126CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨1/4, 21/80⟩, ⟨3/20, 13/80⟩⟩
def scE126CutRoots : Fin 3 → RatBounds := ![⟨61191585574859/35184372088832, 523111872154049/281474976710656⟩, ⟨106573486807381/70368744177664, 228273623335975/140737488355328⟩, ⟨271691158820917/281474976710656, 37588667275331/35184372088832⟩]
def scE126CutCaps : Fin 3 → Fin 3 → ℚ := ![![17882775361/100000000, 807194811/6250000, 5852332933/100000000], ![8058301151/100000000, 8541525743/100000000, 129972639/5000000], ![31252911/6250000, 482746773/100000000, 258421711/100000000]]
def scE126CutWeightFloor : ℚ := 67248747/50000000
def scE126CutMargins : Fin 3 → ℚ := ![51642819/10000000000, 42850371/10000000000, 4253031/2500000000]

theorem scE126Cut_roots_ok : scE126CutCell.rootsOK scE126CutRoots = true := by decide +kernel

theorem scE126Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE126CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE126Cut_margin_le (i : Fin 3) : curvatureLoss scE126CutCell scE126CutCaps i ≤ scE126CutMargins i := by
  fin_cases i <;> decide +kernel

def scE127CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨1/4, 21/80⟩, ⟨13/80, 1/6⟩⟩
def scE127CutRoots : Fin 3 → RatBounds := ![⟨7645158833481/4398046511104, 260757643008837/140737488355328⟩, ⟨425689485542339/281474976710656, 56819035631141/35184372088832⟩, ⟨271098401965339/281474976710656, 298716320677229/281474976710656⟩]
def scE127CutCaps : Fin 3 → Fin 3 → ℚ := ![![2216278911/12500000, 12806103577/100000000, 2872593307/50000000], ![500612743/6250000, 422262351/5000000, 100784869/4000000], ![38394381/10000000, 46470589/12500000, 203712459/100000000]]
def scE127CutWeightFloor : ℚ := 137464741/100000000
def scE127CutMargins : Fin 3 → ℚ := ![12589207/2500000000, 41587223/10000000000, 16186413/10000000000]

theorem scE127Cut_roots_ok : scE127CutCell.rootsOK scE127CutRoots = true := by decide +kernel

theorem scE127Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE127CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE127Cut_margin_le (i : Fin 3) : curvatureLoss scE127CutCell scE127CutCaps i ≤ scE127CutMargins i := by
  fin_cases i <;> decide +kernel

def scE128CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨21/80, 11/40⟩, ⟨1/8, 11/80⟩⟩
def scE128CutRoots : Fin 3 → RatBounds := ![⟨243627494112245/140737488355328, 16252491929829/8796093022208⟩, ⟨52803384076387/35184372088832, 225986490538271/140737488355328⟩, ⟨277957022349363/281474976710656, 153395637444497/140737488355328⟩]
def scE128CutCaps : Fin 3 → Fin 3 → ℚ := ![![15851595811/100000000, 11254614641/100000000, 5278319883/100000000], ![6992677249/100000000, 1844705473/25000000, 1178983541/50000000], ![534372201/100000000, 101746869/20000000, 70728769/25000000]]
def scE128CutWeightFloor : ℚ := 65400479/50000000
def scE128CutMargins : Fin 3 → ℚ := ![45661417/10000000000, 37387053/10000000000, 1933399/1250000000]

theorem scE128Cut_roots_ok : scE128CutCell.rootsOK scE128CutRoots = true := by decide +kernel

theorem scE128Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE128CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE128Cut_margin_le (i : Fin 3) : curvatureLoss scE128CutCell scE128CutCaps i ≤ scE128CutMargins i := by
  fin_cases i <;> decide +kernel

def scE129CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨21/80, 11/40⟩, ⟨11/80, 3/20⟩⟩
def scE129CutRoots : Fin 3 → RatBounds := ![⟨485900059714087/281474976710656, 518619791859751/281474976710656⟩, ⟨420474912887579/281474976710656, 449863640596745/281474976710656⟩, ⟨276040701227567/281474976710656, 76165338873129/70368744177664⟩]
def scE129CutCaps : Fin 3 → Fin 3 → ℚ := ![![16152922959/100000000, 11482073779/100000000, 2689298701/50000000], ![3561898749/50000000, 3755435833/50000000, 150125579/6250000], ![51249541/10000000, 487424607/100000000, 54210873/20000000]]
def scE129CutWeightFloor : ℚ := 133152577/100000000
def scE129CutMargins : Fin 3 → ℚ := ![46463313/10000000000, 19023799/5000000000, 15725901/10000000000]

theorem scE129Cut_roots_ok : scE129CutCell.rootsOK scE129CutRoots = true := by decide +kernel

theorem scE129Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE129CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE129Cut_margin_le (i : Fin 3) : curvatureLoss scE129CutCell scE129CutCaps i ≤ scE129CutMargins i := by
  fin_cases i <;> decide +kernel

def scE130CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨21/80, 11/40⟩, ⟨3/20, 13/80⟩⟩
def scE130CutRoots : Fin 3 → RatBounds := ![⟨484591362214611/281474976710656, 258605404292489/140737488355328⟩, ⟨418592668926715/281474976710656, 223915618531449/140737488355328⟩, ⟨274196313209045/281474976710656, 75653223758875/70368744177664⟩]
def scE130CutCaps : Fin 3 → Fin 3 → ℚ := ![![1028364041/6250000, 5854430499/50000000, 5478663279/100000000], ![1450918881/20000000, 7642665457/100000000, 2445939009/100000000], ![245960867/50000000, 58426581/12500000, 64978893/25000000]]
def scE130CutWeightFloor : ℚ := 135505393/100000000
def scE130CutMargins : Fin 3 → ℚ := ![47266291/10000000000, 19354433/5000000000, 15985387/10000000000]

theorem scE130Cut_roots_ok : scE130CutCell.rootsOK scE130CutRoots = true := by decide +kernel

theorem scE130Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE130CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE130Cut_margin_le (i : Fin 3) : curvatureLoss scE130CutCell scE130CutCaps i ≤ scE130CutMargins i := by
  fin_cases i <;> decide +kernel

def scE131CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨21/80, 11/40⟩, ⟨13/80, 1/6⟩⟩
def scE131CutRoots : Fin 3 → RatBounds := ![⟨121090121941751/70368744177664, 257818307568651/140737488355328⟩, ⟨417991205134221/281474976710656, 55731067403989/35184372088832⟩, ⟨136801983790003/140737488355328, 37578350649177/35184372088832⟩]
def scE131CutCaps : Fin 3 → Fin 3 → ℚ := ![![50960619/312500, 5803357003/50000000, 5374800219/100000000], ![3603870919/50000000, 37752789/500000, 473742799/20000000], ![188488043/50000000, 358930147/100000000, 12761109/6250000]]
def scE131CutWeightFloor : ℚ := 17310733/12500000
def scE131CutMargins : Fin 3 → ℚ := ![46009817/10000000000, 937361/250000000, 15168361/10000000000]

theorem scE131Cut_roots_ok : scE131CutCell.rootsOK scE131CutRoots = true := by decide +kernel

theorem scE131Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE131CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE131Cut_margin_le (i : Fin 3) : curvatureLoss scE131CutCell scE131CutCaps i ≤ scE131CutMargins i := by
  fin_cases i <;> decide +kernel

def scE132CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨11/40, 23/80⟩, ⟨1/8, 11/80⟩⟩
def scE132CutRoots : Fin 3 → RatBounds := ![⟨241349761944907/140737488355328, 514673094476055/281474976710656⟩, ⟨415130643900183/281474976710656, 443769048068109/281474976710656⟩, ⟨140238638657159/140737488355328, 77192527551613/70368744177664⟩]
def scE132CutCaps : Fin 3 → Fin 3 → ℚ := ![![14675301757/100000000, 10270377073/100000000, 4969243937/100000000], ![3169087693/50000000, 3319983171/50000000, 69853881/3125000], ![526681671/100000000, 24670029/5000000, 35610849/12500000]]
def scE132CutWeightFloor : ℚ := 131792247/100000000
def scE132CutMargins : Fin 3 → ℚ := ![42070623/10000000000, 4248961/1250000000, 7313921/5000000000]

theorem scE132Cut_roots_ok : scE132CutCell.rootsOK scE132CutRoots = true := by decide +kernel

theorem scE132Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE132CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE132Cut_margin_le (i : Fin 3) : curvatureLoss scE132CutCell scE132CutCaps i ≤ scE132CutMargins i := by
  fin_cases i <;> decide +kernel

def scE133CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨11/40, 23/80⟩, ⟨11/80, 3/20⟩⟩
def scE133CutRoots : Fin 3 → RatBounds := ![⟨481367121172451/281474976710656, 513238599207893/281474976710656⟩, ⟨413187280410241/281474976710656, 441670486950735/281474976710656⟩, ⟨278562231349141/281474976710656, 19165468668535/17592186044416⟩]
def scE133CutCaps : Fin 3 → Fin 3 → ℚ := ![![14953693203/100000000, 1309763837/12500000, 5064518493/100000000], ![1614252269/25000000, 270347613/4000000, 2277101147/100000000], ![252524261/50000000, 472683367/100000000, 272924553/100000000]]
def scE133CutWeightFloor : ℚ := 134154563/100000000
def scE133CutMargins : Fin 3 → ℚ := ![42804201/10000000000, 34588837/10000000000, 14872157/10000000000]

theorem scE133Cut_roots_ok : scE133CutCell.rootsOK scE133CutRoots = true := by decide +kernel

theorem scE133Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE133CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE133Cut_margin_le (i : Fin 3) : curvatureLoss scE133CutCell scE133CutCaps i ≤ scE133CutMargins i := by
  fin_cases i <;> decide +kernel

def scE134CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨11/40, 23/80⟩, ⟨3/20, 13/80⟩⟩
def scE134CutRoots : Fin 3 → RatBounds := ![⟨240040105787269/140737488355328, 511854231369029/281474976710656⟩, ⟨411313682820235/281474976710656, 439648657154127/281474976710656⟩, ⟨69179757908001/70368744177664, 304606019642793/281474976710656⟩]
def scE134CutCaps : Fin 3 → Fin 3 → ℚ := ![![3807928639/25000000, 10685230857/100000000, 5159595159/100000000], ![3287774239/50000000, 6877187397/100000000, 23187747/1000000], ![484707823/100000000, 453230519/100000000, 261691463/100000000]]
def scE134CutWeightFloor : ℚ := 136518131/100000000
def scE134CutMargins : Fin 3 → ℚ := ![21769503/5000000000, 7037363/2000000000, 3779327/2500000000]

theorem scE134Cut_roots_ok : scE134CutCell.rootsOK scE134CutRoots = true := by decide +kernel

theorem scE134Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE134CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE134Cut_margin_le (i : Fin 3) : curvatureLoss scE134CutCell scE134CutCaps i ≤ scE134CutMargins i := by
  fin_cases i <;> decide +kernel

def scE135CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨11/40, 23/80⟩, ⟨13/80, 1/6⟩⟩
def scE135CutRoots : Fin 3 → RatBounds := ![⟨479860078798415/281474976710656, 510300437253677/281474976710656⟩, ⟨410714868485067/281474976710656, 437676759177045/281474976710656⟩, ⟨138063572442857/140737488355328, 302626455611919/281474976710656⟩]
def scE135CutCaps : Fin 3 → Fin 3 → ℚ := ![![15092973791/100000000, 10589419051/100000000, 50590779/1000000], ![3265129877/50000000, 1357832511/20000000, 2243924557/100000000], ![92706451/25000000, 347144607/100000000, 4098277/2000000]]
def scE135CutWeightFloor : ℚ := 558047/400000
def scE135CutMargins : Fin 3 → ℚ := ![42313353/10000000000, 17008939/5000000000, 7154073/5000000000]

theorem scE135Cut_roots_ok : scE135CutCell.rootsOK scE135CutRoots = true := by decide +kernel

theorem scE135Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE135CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE135Cut_margin_le (i : Fin 3) : curvatureLoss scE135CutCell scE135CutCaps i ≤ scE135CutMargins i := by
  fin_cases i <;> decide +kernel

def scE136CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨23/80, 3/10⟩, ⟨1/8, 11/80⟩⟩
def scE136CutRoots : Fin 3 → RatBounds := ![⟨239271246683121/140737488355328, 509766143071373/281474976710656⟩, ⟨408218877742167/281474976710656, 436047649092539/281474976710656⟩, ⟨35377542431473/35184372088832, 310837364975097/281474976710656⟩]
def scE136CutCaps : Fin 3 → Fin 3 → ℚ := ![![6831343019/50000000, 2357340111/25000000, 4704044267/100000000], ![2891028117/50000000, 750984419/12500000, 2134469207/100000000], ![259921893/50000000, 23957619/5000000, 1435689/500000]]
def scE136CutWeightFloor : ℚ := 2074861/1562500
def scE136CutMargins : Fin 3 → ℚ := ![38993333/10000000000, 3885837/1250000000, 1739661/1250000000]

theorem scE136Cut_roots_ok : scE136CutCell.rootsOK scE136CutRoots = true := by decide +kernel

theorem scE136Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE136CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE136Cut_margin_le (i : Fin 3) : curvatureLoss scE136CutCell scE136CutCaps i ≤ scE136CutMargins i := by
  fin_cases i <;> decide +kernel

def scE137CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨23/80, 3/10⟩, ⟨11/80, 3/20⟩⟩
def scE137CutRoots : Fin 3 → RatBounds := ![⟨119307688214821/70368744177664, 254177454855971/140737488355328⟩, ⟨203141646543265/140737488355328, 433958501540647/281474976710656⟩, ⟨140553345854489/140737488355328, 77180416084429/70368744177664⟩]
def scE137CutCaps : Fin 3 → Fin 3 → ℚ := ![![6960696951/50000000, 9620209697/100000000, 4795061809/100000000], ![5890468839/100000000, 6115273083/100000000, 2174380943/100000000], ![498426033/100000000, 22949419/5000000, 27506303/10000000]]
def scE137CutWeightFloor : ℚ := 67582067/50000000
def scE137CutMargins : Fin 3 → ℚ := ![39668533/10000000000, 31629827/10000000000, 7074713/5000000000]

theorem scE137Cut_roots_ok : scE137CutCell.rootsOK scE137CutRoots = true := by decide +kernel

theorem scE137Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE137CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE137Cut_margin_le (i : Fin 3) : curvatureLoss scE137CutCell scE137CutCaps i ≤ scE137CutMargins i := by
  fin_cases i <;> decide +kernel

def scE138CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨23/80, 3/10⟩, ⟨3/20, 13/80⟩⟩
def scE138CutRoots : Fin 3 → RatBounds := ![⟨475963828288345/281474976710656, 506993036802319/281474976710656⟩, ⟨404417353995247/281474976710656, 215972960664963/140737488355328⟩, ⟨139632398279941/140737488355328, 306686782532245/281474976710656⟩]
def scE138CutCaps : Fin 3 → Fin 3 → ℚ := ![![14179778263/100000000, 4905247667/50000000, 61073667/1250000], ![119972249/2000000, 6222468871/100000000, 69193663/3125000], ![478291399/100000000, 220028699/50000000, 263725279/100000000]]
def scE138CutWeightFloor : ℚ := 137538469/100000000
def scE138CutMargins : Fin 3 → ℚ := ![40345083/10000000000, 32173871/10000000000, 14382453/10000000000]

theorem scE138Cut_roots_ok : scE138CutCell.rootsOK scE138CutRoots = true := by decide +kernel

theorem scE138Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE138CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE138Cut_margin_le (i : Fin 3) : curvatureLoss scE138CutCell scE138CutCaps i ≤ scE138CutMargins i := by
  fin_cases i <;> decide +kernel

def scE139CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨23/80, 3/10⟩, ⟨13/80, 1/6⟩⟩
def scE139CutRoots : Fin 3 → RatBounds := ![⟨475753589575837/281474976710656, 505457819043997/281474976710656⟩, ⟨403820876284103/281474976710656, 107495878523895/70368744177664⟩, ⟨278673405645539/281474976710656, 304713371549031/281474976710656⟩]
def scE139CutCaps : Fin 3 → Fin 3 → ℚ := ![![7024121819/50000000, 1944068853/20000000, 957694753/20000000], ![1488767247/25000000, 1534985837/25000000, 1071030621/50000000], ![91344369/25000000, 168133567/50000000, 51472819/25000000]]
def scE139CutWeightFloor : ℚ := 70272611/50000000
def scE139CutMargins : Fin 3 → ℚ := ![19574131/5000000000, 31050099/10000000000, 13580883/10000000000]

theorem scE139Cut_roots_ok : scE139CutCell.rootsOK scE139CutRoots = true := by decide +kernel

theorem scE139Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE139CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE139Cut_margin_le (i : Fin 3) : curvatureLoss scE139CutCell scE139CutCaps i ≤ scE139CutMargins i := by
  fin_cases i <;> decide +kernel

def scE140CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨3/10, 5/16⟩, ⟨1/8, 11/80⟩⟩
def scE140CutRoots : Fin 3 → RatBounds := ![⟨474753130761453/281474976710656, 505316714235771/281474976710656⟩, ⟨200828485574335/140737488355328, 428762322952859/281474976710656⟩, ⟨142795663815537/140737488355328, 156495938536323/140737488355328⟩]
def scE140CutCaps : Fin 3 → Fin 3 → ℚ := ![![399566981/3125000, 2176576829/25000000, 1118930487/25000000], ![5307206007/100000000, 2732153301/50000000, 1026132397/50000000], ![12843949/2500000, 465860929/100000000, 28964693/10000000]]
def scE140CutWeightFloor : ℚ := 133799951/100000000
def scE140CutMargins : Fin 3 → ℚ := ![36342007/10000000000, 5717373/2000000000, 13315691/10000000000]

theorem scE140Cut_roots_ok : scE140CutCell.rootsOK scE140CutRoots = true := by decide +kernel

theorem scE140Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE140CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE140Cut_margin_le (i : Fin 3) : curvatureLoss scE140CutCell scE140CutCaps i ≤ scE140CutMargins i := by
  fin_cases i <;> decide +kernel

def scE141CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨3/10, 5/16⟩, ⟨11/80, 3/20⟩⟩
def scE141CutRoots : Fin 3 → RatBounds := ![⟨236730156434047/140737488355328, 503926713597213/281474976710656⟩, ⟨399728248797883/281474976710656, 213340681088535/140737488355328⟩, ⟨283679170401441/281474976710656, 155441357963017/140737488355328⟩]
def scE141CutCaps : Fin 3 → Fin 3 → ℚ := ![![6513933451/50000000, 4441306181/50000000, 456311521/10000000], ![5406723981/100000000, 695238577/12500000, 2090611269/100000000], ![246265431/50000000, 44621553/10000000, 55489901/20000000]]
def scE141CutWeightFloor : ℚ := 27236751/20000000
def scE141CutMargins : Fin 3 → ℚ := ![7393407/2000000000, 2908347/1000000000, 6768727/5000000000]

theorem scE141Cut_roots_ok : scE141CutCell.rootsOK scE141CutRoots = true := by decide +kernel

theorem scE141Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE141CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE141Cut_margin_le (i : Fin 3) : curvatureLoss scE141CutCell scE141CutCaps i ≤ scE141CutMargins i := by
  fin_cases i <;> decide +kernel


end HlawkaSchatten.BelowExponent.Vertex
