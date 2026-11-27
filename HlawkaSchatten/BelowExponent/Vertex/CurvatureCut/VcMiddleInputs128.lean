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

def vcM146CutCell : ParameterCell := ⟨⟨7/40, 1/5⟩, ⟨13/40, 7/20⟩, ⟨0, 1/36⟩⟩
def vcM146CutRoots : Fin 3 → RatBounds := ![⟨388633578498453/281474976710656, 27092294320859/17592186044416⟩, ⟨178403587029443/140737488355328, 399774071142553/281474976710656⟩, ⟨320491126202677/281474976710656, 184125146779195/140737488355328⟩]
def vcM146CutCaps : Fin 3 → Fin 3 → ℚ := ![![16845079147/100000000, 13804950879/100000000, 13125776411/100000000], ![3631817537/50000000, 7259423203/100000000, 6392747493/100000000], ![1534655283/100000000, 356546933/25000000, 636970511/50000000]]
def vcM146CutWeightFloor : ℚ := 113573771/100000000
def vcM146CutMargins : Fin 3 → ℚ := ![8126047/400000000, 44580273/2500000000, 41193927/2500000000]

theorem vcM146Cut_roots_ok : vcM146CutCell.rootsOK vcM146CutRoots = true := by decide +kernel

theorem vcM146Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM146CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM146Cut_margin_le (i : Fin 3) : curvatureLoss vcM146CutCell vcM146CutCaps i ≤ vcM146CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM147CutCell : ParameterCell := ⟨⟨7/40, 1/5⟩, ⟨13/40, 7/20⟩, ⟨1/36, 1/18⟩⟩
def vcM147CutRoots : Fin 3 → RatBounds := ![⟨384499876411065/281474976710656, 428593152969139/281474976710656⟩, ⟨176002367582099/140737488355328, 12314997378619/8796093022208⟩, ⟨78864017044717/70368744177664, 181103551354515/140737488355328⟩]
def vcM147CutCaps : Fin 3 → Fin 3 → ℚ := ![![18162677817/100000000, 2967394893/20000000, 442002847/3125000], ![7802078129/100000000, 780895399/10000000, 6865039233/100000000], ![1380644103/100000000, 1278737481/100000000, 285332463/25000000]]
def vcM147CutWeightFloor : ℚ := 58881413/50000000
def vcM147CutMargins : Fin 3 → ℚ := ![108083027/5000000000, 94627409/5000000000, 43785507/2500000000]

theorem vcM147Cut_roots_ok : vcM147CutCell.rootsOK vcM147CutRoots = true := by decide +kernel

theorem vcM147Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM147CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM147Cut_margin_le (i : Fin 3) : curvatureLoss vcM147CutCell vcM147CutCaps i ≤ vcM147CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM148CutCell : ParameterCell := ⟨⟨7/40, 1/5⟩, ⟨7/20, 3/8⟩, ⟨0, 1/36⟩⟩
def vcM148CutRoots : Fin 3 → RatBounds := ![⟨96808587436053/70368744177664, 431965483011209/281474976710656⟩, ⟨349849060497135/281474976710656, 24524233925871/17592186044416⟩, ⟨325760889206711/281474976710656, 93386830754937/70368744177664⟩]
def vcM148CutCaps : Fin 3 → Fin 3 → ℚ := ![![17303047541/100000000, 1749658871/12500000, 6868743903/50000000], ![3154581293/50000000, 6186567001/100000000, 2830626879/50000000], ![760606169/50000000, 1380259119/100000000, 1303482373/100000000]]
def vcM148CutWeightFloor : ℚ := 28837751/25000000
def vcM148CutMargins : Fin 3 → ℚ := ![199142579/10000000000, 170998919/10000000000, 164124837/10000000000]

theorem vcM148Cut_roots_ok : vcM148CutCell.rootsOK vcM148CutRoots = true := by decide +kernel

theorem vcM148Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM148CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM148Cut_margin_le (i : Fin 3) : curvatureLoss vcM148CutCell vcM148CutCaps i ≤ vcM148CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM149CutCell : ParameterCell := ⟨⟨7/40, 1/5⟩, ⟨7/20, 3/8⟩, ⟨1/36, 1/18⟩⟩
def vcM149CutRoots : Fin 3 → RatBounds := ![⟨191564364574601/140737488355328, 427114887787831/281474976710656⟩, ⟨345006008891413/281474976710656, 96659284720621/70368744177664⟩, ⟨20048229509727/17592186044416, 183787740172805/140737488355328⟩]
def vcM149CutCaps : Fin 3 → Fin 3 → ℚ := ![![18656177717/100000000, 3759346719/25000000, 7406469043/50000000], ![6774658227/100000000, 1663502411/25000000, 6084963947/100000000], ![684238587/50000000, 618573469/50000000, 1167922397/100000000]]
def vcM149CutWeightFloor : ℚ := 11956819/10000000
def vcM149CutMargins : Fin 3 → ℚ := ![211877453/10000000000, 90698197/5000000000, 21816193/1250000000]

theorem vcM149Cut_roots_ok : vcM149CutCell.rootsOK vcM149CutRoots = true := by decide +kernel

theorem vcM149Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM149CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM149Cut_margin_le (i : Fin 3) : curvatureLoss vcM149CutCell vcM149CutCaps i ≤ vcM149CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM150CutCell : ParameterCell := ⟨⟨7/40, 1/5⟩, ⟨3/8, 2/5⟩, ⟨0, 1/36⟩⟩
def vcM150CutRoots : Fin 3 → RatBounds := ![⟨386403224440649/281474976710656, 431218569518907/281474976710656⟩, ⟨343307170357829/281474976710656, 24099630504867/17592186044416⟩, ⟨331299444542087/281474976710656, 189653245299891/140737488355328⟩]
def vcM150CutCaps : Fin 3 → Fin 3 → ℚ := ![![4617493547/25000000, 7377021659/50000000, 14981442009/100000000], ![5984188203/100000000, 89350359/1562500, 5492455233/100000000], ![151634149/10000000, 66997501/5000000, 133780751/10000000]]
def vcM150CutWeightFloor : ℚ := 7325229/6250000
def vcM150CutMargins : Fin 3 → ℚ := ![205673351/10000000000, 43216261/2500000000, 172855559/10000000000]

theorem vcM150Cut_roots_ok : vcM150CutCell.rootsOK vcM150CutRoots = true := by decide +kernel

theorem vcM150Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM150CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM150Cut_margin_le (i : Fin 3) : curvatureLoss vcM150CutCell vcM150CutCaps i ≤ vcM150CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM151CutCell : ParameterCell := ⟨⟨7/40, 1/5⟩, ⟨3/8, 2/5⟩, ⟨1/36, 1/18⟩⟩
def vcM151CutRoots : Fin 3 → RatBounds := ![⟨382313000660519/281474976710656, 213192952136747/140737488355328⟩, ⟨338422065225887/281474976710656, 189891777968479/140737488355328⟩, ⟨163177540714815/140737488355328, 373402284577087/281474976710656⟩]
def vcM151CutCaps : Fin 3 → Fin 3 → ℚ := ![![99564681/500000, 15842094707/100000000, 1615978767/10000000], ![6425134181/100000000, 614871773/10000000, 738345687/12500000], ![1364109103/100000000, 600365923/50000000, 239779967/20000000]]
def vcM151CutWeightFloor : ℚ := 24286887/20000000
def vcM151CutMargins : Fin 3 → ℚ := ![54730773/2500000000, 36676871/2000000000, 18395841/1000000000]

theorem vcM151Cut_roots_ok : vcM151CutCell.rootsOK vcM151CutRoots = true := by decide +kernel

theorem vcM151Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM151CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM151Cut_margin_le (i : Fin 3) : curvatureLoss vcM151CutCell vcM151CutCaps i ≤ vcM151CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM152CutCell : ParameterCell := ⟨⟨7/40, 1/5⟩, ⟨2/5, 17/40⟩, ⟨0, 1/36⟩⟩
def vcM152CutRoots : Fin 3 → RatBounds := ![⟨193063783324121/140737488355328, 431221988611875/281474976710656⟩, ⟨168568440586295/140737488355328, 189669822294051/140737488355328⟩, ⟨168568440586295/140737488355328, 96390434386243/70368744177664⟩]
def vcM152CutCaps : Fin 3 → Fin 3 → ℚ := ![![256048461/1250000, 8076345359/50000000, 4252515327/25000000], ![6111475753/100000000, 2841213513/50000000, 1155209253/20000000], ![75992931/5000000, 52188989/4000000, 1377390691/100000000]]
def vcM152CutWeightFloor : ℚ := 119141499/100000000
def vcM152CutMargins : Fin 3 → ℚ := ![222435323/10000000000, 2862047/156250000, 47825371/2500000000]

theorem vcM152Cut_roots_ok : vcM152CutCell.rootsOK vcM152CutRoots = true := by decide +kernel

theorem vcM152Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM152CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM152Cut_margin_le (i : Fin 3) : curvatureLoss vcM152CutCell vcM152CutCaps i ≤ vcM152CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM153CutCell : ParameterCell := ⟨⟨7/40, 1/5⟩, ⟨2/5, 17/40⟩, ⟨1/36, 1/18⟩⟩
def vcM153CutRoots : Fin 3 → RatBounds := ![⟨191020130404875/140737488355328, 213196232840525/140737488355328⟩, ⟨332208415114239/281474976710656, 186732878773005/140737488355328⟩, ⟨332236332541937/281474976710656, 379721598772325/281474976710656⟩]
def vcM153CutCaps : Fin 3 → Fin 3 → ℚ := ![![5520275061/25000000, 3466594741/20000000, 18348885901/100000000], ![3281587839/50000000, 6108907751/100000000, 1553458081/25000000], ![68368771/5000000, 233798851/20000000, 154337633/12500000]]
def vcM153CutWeightFloor : ℚ := 123371/100000
def vcM153CutMargins : Fin 3 → ℚ := ![118485913/5000000000, 194414721/10000000000, 40761001/2000000000]

theorem vcM153Cut_roots_ok : vcM153CutCell.rootsOK vcM153CutRoots = true := by decide +kernel

theorem vcM153Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM153CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM153Cut_margin_le (i : Fin 3) : curvatureLoss vcM153CutCell vcM153CutCaps i ≤ vcM153CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM154CutCell : ParameterCell := ⟨⟨1/5, 9/40⟩, ⟨1/5, 9/40⟩, ⟨0, 1/36⟩⟩
def vcM154CutRoots : Fin 3 → RatBounds := ![⟨394985630811383/281474976710656, 442034517497801/281474976710656⟩, ⟨394985630811383/281474976710656, 442034517497801/281474976710656⟩, ⟨301359502160265/281474976710656, 175476514269297/140737488355328⟩]
def vcM154CutCaps : Fin 3 → Fin 3 → ℚ := ![![13356311833/50000000, 1204825139/5000000, 20595171521/100000000], ![40947916383/100000000, 42410168493/100000000, 16352849897/50000000], ![1774083261/100000000, 1804962047/100000000, 156557939/12500000]]
def vcM154CutWeightFloor : ℚ := 106692371/100000000
def vcM154CutMargins : Fin 3 → ℚ := ![68213639/1250000000, 26849617/500000000, 214246573/5000000000]

theorem vcM154Cut_roots_ok : vcM154CutCell.rootsOK vcM154CutRoots = true := by decide +kernel

theorem vcM154Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM154CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM154Cut_margin_le (i : Fin 3) : curvatureLoss vcM154CutCell vcM154CutCaps i ≤ vcM154CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM155CutCell : ParameterCell := ⟨⟨1/5, 9/40⟩, ⟨1/5, 9/40⟩, ⟨1/36, 1/18⟩⟩
def vcM155CutRoots : Fin 3 → RatBounds := ![⟨97616794189059/70368744177664, 436694270587641/281474976710656⟩, ⟨97616794189059/70368744177664, 436694270587641/281474976710656⟩, ⟨296140541075739/281474976710656, 86147829087197/70368744177664⟩]
def vcM155CutCaps : Fin 3 → Fin 3 → ℚ := ![![190109421/1250000, 3407800079/25000000, 10504156163/100000000], ![22612088489/100000000, 24112413807/100000000, 2160449981/12500000], ![132739343/12500000, 538054007/50000000, 74832177/10000000]]
def vcM155CutWeightFloor : ℚ := 114510393/100000000
def vcM155CutMargins : Fin 3 → ℚ := ![305717563/10000000000, 152625557/5000000000, 112154727/5000000000]

theorem vcM155Cut_roots_ok : vcM155CutCell.rootsOK vcM155CutRoots = true := by decide +kernel

theorem vcM155Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM155CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM155Cut_margin_le (i : Fin 3) : curvatureLoss vcM155CutCell vcM155CutCaps i ≤ vcM155CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM156CutCell : ParameterCell := ⟨⟨1/5, 9/40⟩, ⟨9/40, 1/4⟩, ⟨0, 1/36⟩⟩
def vcM156CutRoots : Fin 3 → RatBounds := ![⟨390754507677719/281474976710656, 218338527122777/140737488355328⟩, ⟨385509700685093/281474976710656, 215554468870391/140737488355328⟩, ⟨305571811846235/281474976710656, 88565146040969/70368744177664⟩]
def vcM156CutCaps : Fin 3 → Fin 3 → ℚ := ![![22689768259/100000000, 20227036433/100000000, 17667128949/100000000], ![5235140137/20000000, 27065604157/100000000, 10776039351/50000000], ![422857901/25000000, 1701028791/100000000, 628026131/50000000]]
def vcM156CutWeightFloor : ℚ := 108223439/100000000
def vcM156CutMargins : Fin 3 → ℚ := ![398075439/10000000000, 385880283/10000000000, 159257381/5000000000]

theorem vcM156Cut_roots_ok : vcM156CutCell.rootsOK vcM156CutRoots = true := by decide +kernel

theorem vcM156Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM156CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM156Cut_margin_le (i : Fin 3) : curvatureLoss vcM156CutCell vcM156CutCaps i ≤ vcM156CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM157CutCell : ParameterCell := ⟨⟨1/5, 9/40⟩, ⟨9/40, 1/4⟩, ⟨1/36, 1/18⟩⟩
def vcM157CutRoots : Fin 3 → RatBounds := ![⟨193164574379389/140737488355328, 431448152653151/281474976710656⟩, ⟨380953654158093/281474976710656, 425724016823737/281474976710656⟩, ⟨150205539668451/140737488355328, 173999334453037/140737488355328⟩]
def vcM157CutCaps : Fin 3 → Fin 3 → ℚ := ![![61117189/250000, 10879573277/50000000, 18927574241/100000000], ![28113354021/100000000, 29118504341/100000000, 23031277769/100000000], ![1521861883/100000000, 1528554071/100000000, 562822839/50000000]]
def vcM157CutWeightFloor : ℚ := 28005673/25000000
def vcM157CutMargins : Fin 3 → ℚ := ![212652623/5000000000, 206112323/5000000000, 169330227/5000000000]

theorem vcM157Cut_roots_ok : vcM157CutCell.rootsOK vcM157CutRoots = true := by decide +kernel

theorem vcM157Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM157CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM157Cut_margin_le (i : Fin 3) : curvatureLoss vcM157CutCell vcM157CutCaps i ≤ vcM157CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM158CutCell : ParameterCell := ⟨⟨1/5, 9/40⟩, ⟨1/4, 11/40⟩, ⟨0, 1/36⟩⟩
def vcM158CutRoots : Fin 3 → RatBounds := ![⟨96812792079345/70368744177664, 216159772024165/140737488355328⟩, ⟨23547355522271/17592186044416, 210597830082315/140737488355328⟩, ⟨154979935187805/140737488355328, 357980625550585/281474976710656⟩]
def vcM158CutCaps : Fin 3 → Fin 3 → ℚ := ![![20303957291/100000000, 8918907327/50000000, 15983405387/100000000], ![3579176499/20000000, 9220508573/50000000, 15157060897/100000000], ![1628855003/100000000, 1616595783/100000000, 253249327/20000000]]
def vcM158CutWeightFloor : ℚ := 27444709/25000000
def vcM158CutMargins : Fin 3 → ℚ := ![9817083/312500000, 14951027/500000000, 798431/31250000]

theorem vcM158Cut_roots_ok : vcM158CutCell.rootsOK vcM158CutRoots = true := by decide +kernel

theorem vcM158Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM158CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM158Cut_margin_le (i : Fin 3) : curvatureLoss vcM158CutCell vcM158CutCaps i ≤ vcM158CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM159CutCell : ParameterCell := ⟨⟨1/5, 9/40⟩, ⟨1/4, 11/40⟩, ⟨1/36, 1/18⟩⟩
def vcM159CutRoots : Fin 3 → RatBounds := ![⟨191451478708829/140737488355328, 213591178042537/140737488355328⟩, ⟨186080821445523/140737488355328, 51970178053177/35184372088832⟩, ⟨304855722836343/281474976710656, 351812289817307/281474976710656⟩]
def vcM159CutCaps : Fin 3 → Fin 3 → ℚ := ![![2188601039/10000000, 19189325147/100000000, 171525709/1000000], ![961575637/5000000, 496320589/2500000, 8116136261/50000000], ![366428709/25000000, 726013141/50000000, 283696837/25000000]]
def vcM159CutWeightFloor : ℚ := 113681427/100000000
def vcM159CutMargins : Fin 3 → ℚ := ![8384189/250000000, 31902167/1000000000, 33970523/1250000000]

theorem vcM159Cut_roots_ok : vcM159CutCell.rootsOK vcM159CutRoots = true := by decide +kernel

theorem vcM159Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM159CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM159Cut_margin_le (i : Fin 3) : curvatureLoss vcM159CutCell vcM159CutCaps i ≤ vcM159CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM160CutCell : ParameterCell := ⟨⟨1/5, 9/40⟩, ⟨11/40, 3/10⟩, ⟨0, 1/36⟩⟩
def vcM160CutRoots : Fin 3 → RatBounds := ![⟨96103524139557/70368744177664, 13402103259719/8796093022208⟩, ⟨184318942742937/140737488355328, 103040441342869/70368744177664⟩, ⟨78635450211755/70368744177664, 45263669365763/35184372088832⟩]
def vcM160CutCaps : Fin 3 → Fin 3 → ℚ := ![![9495204673/50000000, 16459762893/100000000, 15122282623/100000000], ![13027622449/100000000, 13337496141/100000000, 5651683877/50000000], ![158724133/10000000, 1550150799/100000000, 256646127/20000000]]
def vcM160CutWeightFloor : ℚ := 111371893/100000000
def vcM160CutMargins : Fin 3 → ℚ := ![53089983/2000000000, 247742387/10000000000, 218827233/10000000000]

theorem vcM160Cut_roots_ok : vcM160CutCell.rootsOK vcM160CutRoots = true := by decide +kernel

theorem vcM160Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM160CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM160Cut_margin_le (i : Fin 3) : curvatureLoss vcM160CutCell vcM160CutCaps i ≤ vcM160CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM161CutCell : ParameterCell := ⟨⟨1/5, 9/40⟩, ⟨11/40, 3/10⟩, ⟨1/36, 1/18⟩⟩
def vcM161CutRoots : Fin 3 → RatBounds := ![⟨380128171772027/281474976710656, 423803803090541/281474976710656⟩, ⟨181999878393155/140737488355328, 101668520804051/70368744177664⟩, ⟨309492776781539/281474976710656, 178014614450833/140737488355328⟩]
def vcM161CutCaps : Fin 3 → Fin 3 → ℚ := ![![20479600271/100000000, 17704784187/100000000, 16258734471/100000000], ![875243091/6250000, 7182976557/50000000, 1516135201/12500000], ![714108197/50000000, 1391691119/100000000, 1150069301/100000000]]
def vcM161CutWeightFloor : ℚ := 4614033/4000000
def vcM161CutMargins : Fin 3 → ℚ := ![283177499/10000000000, 131987791/5000000000, 232872303/10000000000]

theorem vcM161Cut_roots_ok : vcM161CutCell.rootsOK vcM161CutRoots = true := by decide +kernel

theorem vcM161Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM161CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM161Cut_margin_le (i : Fin 3) : curvatureLoss vcM161CutCell vcM161CutCaps i ≤ vcM161CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM162CutCell : ParameterCell := ⟨⟨1/5, 9/40⟩, ⟨3/10, 13/40⟩, ⟨0, 1/36⟩⟩
def vcM162CutRoots : Fin 3 → RatBounds := ![⟨382196023932149/281474976710656, 106562393953313/70368744177664⟩, ⟨180537020145833/140737488355328, 25243771513551/17592186044416⟩, ⟨319337236204303/281474976710656, 366651669908839/281474976710656⟩]
def vcM162CutCaps : Fin 3 → Fin 3 → ℚ := ![![18554249097/100000000, 15879147079/100000000, 7488449723/50000000], ![315529927/3125000, 2556770913/25000000, 2236142211/25000000], ![1558143083/100000000, 373364501/25000000, 1305326083/100000000]]
def vcM162CutWeightFloor : ℚ := 2260277/2000000
def vcM162CutMargins : Fin 3 → ℚ := ![11943297/500000000, 218359423/10000000000, 99738211/5000000000]

theorem vcM162Cut_roots_ok : vcM162CutCell.rootsOK vcM162CutRoots = true := by decide +kernel

theorem vcM162Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM162CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM162Cut_margin_le (i : Fin 3) : curvatureLoss vcM162CutCell vcM162CutCaps i ≤ vcM162CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM163CutCell : ParameterCell := ⟨⟨1/5, 9/40⟩, ⟨3/10, 13/40⟩, ⟨1/36, 1/18⟩⟩
def vcM163CutRoots : Fin 3 → RatBounds := ![⟨94489589483237/70368744177664, 210621470482587/140737488355328⟩, ⟨89097998673541/70368744177664, 99588861347155/70368744177664⟩, ⟨78585501035815/70368744177664, 360655027936577/281474976710656⟩]
def vcM163CutCaps : Fin 3 → Fin 3 → ℚ := ![![20019213651/100000000, 3415206437/20000000, 1008346099/6250000], ![1085418597/10000000, 11019398273/100000000, 600859021/6250000], ![1402005609/100000000, 268051799/20000000, 1169998043/100000000]]
def vcM163CutWeightFloor : ℚ := 58523347/50000000
def vcM163CutMargins : Fin 3 → ℚ := ![127360433/5000000000, 7263201/312500000, 13277209/625000000]

theorem vcM163Cut_roots_ok : vcM163CutCell.rootsOK vcM163CutRoots = true := by decide +kernel

theorem vcM163Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM163CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM163Cut_margin_le (i : Fin 3) : curvatureLoss vcM163CutCell vcM163CutCaps i ≤ vcM163CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM164CutCell : ParameterCell := ⟨⟨1/5, 9/40⟩, ⟨13/40, 7/20⟩, ⟨0, 1/36⟩⟩
def vcM164CutRoots : Fin 3 → RatBounds := ![⟨380561530324323/281474976710656, 106103778293449/70368744177664⟩, ⟨88500527575931/70368744177664, 396324795546943/281474976710656⟩, ⟨324367745223657/281474976710656, 371620383084919/281474976710656⟩]
def vcM164CutCaps : Fin 3 → Fin 3 → ℚ := ![![18924276871/100000000, 15997083931/100000000, 15530464629/100000000], ![2081377273/25000000, 8310067453/100000000, 1878289439/25000000], ![1539672169/100000000, 1444710747/100000000, 333122617/25000000]]
def vcM164CutWeightFloor : ℚ := 114714757/100000000
def vcM164CutMargins : Fin 3 → ℚ := ![113869593/5000000000, 40766789/2000000000, 192880253/10000000000]

theorem vcM164Cut_roots_ok : vcM164CutCell.rootsOK vcM164CutRoots = true := by decide +kernel

theorem vcM164Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM164CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM164Cut_margin_le (i : Fin 3) : curvatureLoss vcM164CutCell vcM164CutCaps i ≤ vcM164CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM165CutCell : ParameterCell := ⟨⟨1/5, 9/40⟩, ⟨13/40, 7/20⟩, ⟨1/36, 1/18⟩⟩
def vcM165CutRoots : Fin 3 → RatBounds := ![⟨376358720251777/281474976710656, 419449404372947/281474976710656⟩, ⟨174637253516585/140737488355328, 390719150171975/281474976710656⟩, ⟨159712530517059/140737488355328, 91425745858105/70368744177664⟩]
def vcM165CutCaps : Fin 3 → Fin 3 → ℚ := ![![1276159341/6250000, 17196478643/100000000, 1674301501/10000000], ![2237170149/25000000, 4476471143/50000000, 8084890117/100000000], ![692698821/50000000, 51843409/4000000, 1194538183/100000000]]
def vcM165CutWeightFloor : ℚ := 5939093/5000000
def vcM165CutMargins : Fin 3 → ℚ := ![242793731/10000000000, 108396587/5000000000, 51372351/2500000000]

theorem vcM165Cut_roots_ok : vcM165CutCell.rootsOK vcM165CutRoots = true := by decide +kernel

theorem vcM165Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM165CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM165Cut_margin_le (i : Fin 3) : curvatureLoss vcM165CutCell vcM165CutCaps i ≤ vcM165CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM166CutCell : ParameterCell := ⟨⟨1/5, 9/40⟩, ⟨7/20, 3/8⟩, ⟨0, 1/36⟩⟩
def vcM166CutRoots : Fin 3 → RatBounds := ![⟨189742676984509/140737488355328, 52916150033009/35184372088832⟩, ⟨347367806688781/281474976710656, 389364705827299/281474976710656⟩, ⟨329657298249841/281474976710656, 377035962733989/281474976710656⟩]
def vcM166CutCaps : Fin 3 → Fin 3 → ℚ := ![![5031028031/25000000, 3361260077/20000000, 2104268863/12500000], ![3677653759/50000000, 7197278029/100000000, 6754081633/100000000], ![1530930919/100000000, 1402707551/100000000, 1364931621/100000000]]
def vcM166CutWeightFloor : ℚ := 116484011/100000000
def vcM166CutMargins : Fin 3 → ℚ := ![22944889/1000000000, 100528579/5000000000, 197447917/10000000000]

theorem vcM166Cut_roots_ok : vcM166CutCell.rootsOK vcM166CutRoots = true := by decide +kernel

theorem vcM166Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM166CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM166Cut_margin_le (i : Fin 3) : curvatureLoss vcM166CutCell vcM166CutCaps i ≤ vcM166CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM167CutCell : ParameterCell := ⟨⟨1/5, 9/40⟩, ⟨7/20, 3/8⟩, ⟨1/36, 1/18⟩⟩
def vcM167CutRoots : Fin 3 → RatBounds := ![⟨375304439861139/281474976710656, 104597269893823/70368744177664⟩, ⟨342593149967779/281474976710656, 191847460478689/140737488355328⟩, ⟨162382984321923/140737488355328, 371193917033651/281474976710656⟩]
def vcM167CutCaps : Fin 3 → Fin 3 → ℚ := ![![21710804829/100000000, 4514371701/25000000, 18156377943/100000000], ![3952105403/50000000, 7753869493/100000000, 363776883/5000000], ![1377587689/100000000, 1258076337/100000000, 1223884903/100000000]]
def vcM167CutWeightFloor : ℚ := 60283543/50000000
def vcM167CutMargins : Fin 3 → ℚ := ![61163557/2500000000, 42757089/2000000000, 210491287/10000000000]

theorem vcM167Cut_roots_ok : vcM167CutCell.rootsOK vcM167CutRoots = true := by decide +kernel

theorem vcM167Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM167CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM167Cut_margin_le (i : Fin 3) : curvatureLoss vcM167CutCell vcM167CutCaps i ≤ vcM167CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM168CutCell : ParameterCell := ⟨⟨1/5, 9/40⟩, ⟨3/8, 2/5⟩, ⟨0, 1/36⟩⟩
def vcM168CutRoots : Fin 3 → RatBounds := ![⟨189475621612879/140737488355328, 211485864537685/140737488355328⟩, ⟨341124709233141/281474976710656, 11967589133927/8796093022208⟩, ⟨335232798719707/281474976710656, 382926714528593/281474976710656⟩]
def vcM168CutCaps : Fin 3 → Fin 3 → ℚ := ![![2229609193/10000000, 18388784589/100000000, 9525986099/50000000], ![7276103697/100000000, 1736406571/25000000, 3429657347/50000000], ![306307091/20000000, 683334897/50000000, 280621729/20000000]]
def vcM168CutWeightFloor : ℚ := 118330703/100000000
def vcM168CutMargins : Fin 3 → ℚ := ![245804533/10000000000, 2111067/100000000, 215964999/10000000000]

theorem vcM168Cut_roots_ok : vcM168CutCell.rootsOK vcM168CutRoots = true := by decide +kernel

theorem vcM168Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM168CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM168Cut_margin_le (i : Fin 3) : curvatureLoss vcM168CutCell vcM168CutCaps i ≤ vcM168CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM169CutCell : ParameterCell := ⟨⟨1/5, 9/40⟩, ⟨3/8, 2/5⟩, ⟨1/36, 1/18⟩⟩
def vcM169CutRoots : Fin 3 → RatBounds := ![⟨187389772900453/140737488355328, 209021107455999/140737488355328⟩, ⟨336301607295363/281474976710656, 377225578793115/281474976710656⟩, ⟨330391648570041/281474976710656, 47144547142783/35184372088832⟩]
def vcM169CutCaps : Fin 3 → Fin 3 → ℚ := ![![12024435969/50000000, 19745690163/100000000, 822025303/4000000], ![3910056029/50000000, 3740373161/50000000, 3696056949/50000000], ![1378234137/100000000, 306380289/25000000, 1258461489/100000000]]
def vcM169CutWeightFloor : ℚ := 122411573/100000000
def vcM169CutMargins : Fin 3 → ℚ := ![262269591/10000000000, 224526763/10000000000, 115220323/5000000000]

theorem vcM169Cut_roots_ok : vcM169CutCell.rootsOK vcM169CutRoots = true := by decide +kernel

theorem vcM169Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM169CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM169Cut_margin_le (i : Fin 3) : curvatureLoss vcM169CutCell vcM169CutCaps i ≤ vcM169CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM170CutCell : ParameterCell := ⟨⟨9/40, 1/4⟩, ⟨9/40, 1/4⟩, ⟨0, 1/36⟩⟩
def vcM170CutRoots : Fin 3 → RatBounds := ![⟨381770224156339/281474976710656, 213212284352677/140737488355328⟩, ⟨381770224156339/281474976710656, 213212284352677/140737488355328⟩, ⟨309730142789993/281474976710656, 357660396093593/281474976710656⟩]
def vcM170CutCaps : Fin 3 → Fin 3 → ℚ := ![![1411739/6250, 20489425899/100000000, 3678396927/20000000], ![28831185229/100000000, 3012106277/10000000, 1228077649/5000000], ![335329187/20000000, 1705048331/100000000, 1305981579/100000000]]
def vcM170CutWeightFloor : ℚ := 54750437/50000000
def vcM170CutMargins : Fin 3 → ℚ := ![104470591/2500000000, 20591987/500000000, 174085393/5000000000]

theorem vcM170Cut_roots_ok : vcM170CutCell.rootsOK vcM170CutRoots = true := by decide +kernel

theorem vcM170Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM170CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM170Cut_margin_le (i : Fin 3) : curvatureLoss vcM170CutCell vcM170CutCaps i ≤ vcM170CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM171CutCell : ParameterCell := ⟨⟨9/40, 1/4⟩, ⟨9/40, 1/4⟩, ⟨1/36, 1/18⟩⟩
def vcM171CutRoots : Fin 3 → RatBounds := ![⟨377300008214301/281474976710656, 3290170210187/2199023255552⟩, ⟨377300008214301/281474976710656, 3290170210187/2199023255552⟩, ⟨304634451819031/281474976710656, 351501936018731/281474976710656⟩]
def vcM171CutCaps : Fin 3 → Fin 3 → ℚ := ![![6087249971/25000000, 22052554357/100000000, 1232990207/6250000], ![1238676929/4000000, 32425496449/100000000, 26286357399/100000000], ![94284727/6250000, 766566573/50000000, 585568421/50000000]]
def vcM171CutWeightFloor : ℚ := 56605021/50000000
def vcM171CutMargins : Fin 3 → ℚ := ![223352881/5000000000, 55049617/1250000000, 370781631/10000000000]

theorem vcM171Cut_roots_ok : vcM171CutCell.rootsOK vcM171CutRoots = true := by decide +kernel

theorem vcM171Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM171CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM171Cut_margin_le (i : Fin 3) : curvatureLoss vcM171CutCell vcM171CutCaps i ≤ vcM171CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM172CutCell : ParameterCell := ⟨⟨9/40, 1/4⟩, ⟨1/4, 11/40⟩, ⟨0, 1/36⟩⟩
def vcM172CutRoots : Fin 3 → RatBounds := ![⟨94675787456781/70368744177664, 422656350350611/281474976710656⟩, ⟨93363473052237/70368744177664, 208549838333483/140737488355328⟩, ⟨314084617574081/281474976710656, 361475204372345/281474976710656⟩]
def vcM172CutCaps : Fin 3 → Fin 3 → ℚ := ![![20768675611/100000000, 3733388119/20000000, 8546611841/50000000], ![19832835841/100000000, 20611075147/100000000, 8670399751/50000000], ![202678363/12500000, 203135639/12500000, 1318325261/100000000]]
def vcM172CutWeightFloor : ℚ := 111036749/100000000
def vcM172CutMargins : Fin 3 → ℚ := ![332838071/10000000000, 64506709/2000000000, 56346227/2000000000]

theorem vcM172Cut_roots_ok : vcM172CutCell.rootsOK vcM172CutRoots = true := by decide +kernel

theorem vcM172Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM172CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM172Cut_margin_le (i : Fin 3) : curvatureLoss vcM172CutCell vcM172CutCaps i ≤ vcM172CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM173CutCell : ParameterCell := ⟨⟨9/40, 1/4⟩, ⟨1/4, 11/40⟩, ⟨1/36, 1/18⟩⟩
def vcM173CutRoots : Fin 3 → RatBounds := ![⟨5848488436887/4398046511104, 417456816732861/281474976710656⟩, ⟨184468379954207/140737488355328, 102939745139821/70368744177664⟩, ⟨309051914517927/281474976710656, 355414115715081/281474976710656⟩]
def vcM173CutCaps : Fin 3 → Fin 3 → ℚ := ![![4479163457/20000000, 20086977447/100000000, 367200641/2000000], ![21315702927/100000000, 22199231049/100000000, 3717885939/20000000], ![1459136477/100000000, 365182569/25000000, 147791901/12500000]]
def vcM173CutWeightFloor : ℚ := 7177709/6250000
def vcM173CutMargins : Fin 3 → ℚ := ![177784857/5000000000, 172224919/5000000000, 150035683/5000000000]

theorem vcM173Cut_roots_ok : vcM173CutCell.rootsOK vcM173CutRoots = true := by decide +kernel

theorem vcM173Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM173CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM173Cut_margin_le (i : Fin 3) : curvatureLoss vcM173CutCell vcM173CutCaps i ≤ vcM173CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM174CutCell : ParameterCell := ⟨⟨9/40, 1/4⟩, ⟨11/40, 3/10⟩, ⟨0, 1/36⟩⟩
def vcM174CutRoots : Fin 3 → RatBounds := ![⟨188128395019571/140737488355328, 419726081185605/281474976710656⟩, ⟨182862097760057/140737488355328, 102146698093389/70368744177664⟩, ⟨2489467493869/2199023255552, 91426073528817/70368744177664⟩]
def vcM174CutCaps : Fin 3 → Fin 3 → ℚ := ![![4009540759/20000000, 17838932373/100000000, 133646833/800000], ![7259263353/50000000, 14963834411/100000000, 6486999869/50000000], ![1582075887/100000000, 1560948751/100000000, 668565149/50000000]]
def vcM174CutWeightFloor : ℚ := 22522979/20000000
def vcM174CutMargins : Fin 3 → ℚ := ![35663487/1250000000, 271327063/10000000000, 244770563/10000000000]

theorem vcM174Cut_roots_ok : vcM174CutCell.rootsOK vcM174CutRoots = true := by decide +kernel

theorem vcM174Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM174CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM174Cut_margin_le (i : Fin 3) : curvatureLoss vcM174CutCell vcM174CutCaps i ≤ vcM174CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM175CutCell : ParameterCell := ⟨⟨9/40, 1/4⟩, ⟨11/40, 3/10⟩, ⟨1/36, 1/18⟩⟩
def vcM175CutRoots : Fin 3 → RatBounds := ![⟨185956336009821/140737488355328, 414592289502585/281474976710656⟩, ⟨11286197383719/8796093022208, 201592250409009/140737488355328⟩, ⟨156840159079939/140737488355328, 179867650073815/140737488355328⟩]
def vcM175CutCaps : Fin 3 → Fin 3 → ℚ := ![![10815697829/50000000, 479781133/2500000, 17979951179/100000000], ![3121924513/20000000, 16127435997/100000000, 13937547877/100000000], ![1423933777/100000000, 87659923/6250000, 1199365727/100000000]]
def vcM175CutWeightFloor : ℚ := 23298041/20000000
def vcM175CutMargins : Fin 3 → ℚ := ![60935877/2000000000, 72363741/2500000000, 130461709/5000000000]

theorem vcM175Cut_roots_ok : vcM175CutCell.rootsOK vcM175CutRoots = true := by decide +kernel

theorem vcM175Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM175CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM175Cut_margin_le (i : Fin 3) : curvatureLoss vcM175CutCell vcM175CutCaps i ≤ vcM175CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM176CutCell : ParameterCell := ⟨⟨9/40, 1/4⟩, ⟨3/10, 13/40⟩, ⟨0, 1/36⟩⟩
def vcM176CutRoots : Fin 3 → RatBounds := ![⟨187195902220573/140737488355328, 104393998564249/70368744177664⟩, ⟨358513174939339/281474976710656, 400792531080887/281474976710656⟩, ⟨161725238632803/140737488355328, 370355261894235/281474976710656⟩]
def vcM176CutCaps : Fin 3 → Fin 3 → ℚ := ![![20286400827/100000000, 17857926979/100000000, 8579978709/50000000], ![567310899/5000000, 2887475453/25000000, 206531277/2000000], ![778211087/50000000, 94331693/6250000, 681074683/50000000]]
def vcM176CutWeightFloor : ℚ := 57122841/50000000
def vcM176CutMargins : Fin 3 → ℚ := ![262141623/10000000000, 244306023/10000000000, 227876463/10000000000]

theorem vcM176Cut_roots_ok : vcM176CutCell.rootsOK vcM176CutRoots = true := by decide +kernel

theorem vcM176Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM176CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM176Cut_margin_le (i : Fin 3) : curvatureLoss vcM176CutCell vcM176CutCaps i ≤ vcM176CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM177CutCell : ParameterCell := ⟨⟨9/40, 1/4⟩, ⟨3/10, 13/40⟩, ⟨1/36, 1/18⟩⟩
def vcM177CutRoots : Fin 3 → RatBounds := ![⟨185044813579977/140737488355328, 103122866929655/70368744177664⟩, ⟨176948444021609/140737488355328, 197662597036333/140737488355328⟩, ⟨318538518532719/281474976710656, 182236852949833/140737488355328⟩]
def vcM177CutCaps : Fin 3 → Fin 3 → ℚ := ![![2736860677/12500000, 9602694519/50000000, 924641887/5000000], ![6100203793/50000000, 6227473479/50000000, 11115042341/100000000], ![1401006973/100000000, 677821593/50000000, 1222015867/100000000]]
def vcM177CutWeightFloor : ℚ := 118165049/100000000
def vcM177CutMargins : Fin 3 → ℚ := ![69970569/2500000000, 130210819/5000000000, 121548991/5000000000]

theorem vcM177Cut_roots_ok : vcM177CutCell.rootsOK vcM177CutRoots = true := by decide +kernel

theorem vcM177Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM177CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM177Cut_margin_le (i : Fin 3) : curvatureLoss vcM177CutCell vcM177CutCaps i ≤ vcM177CutMargins i := by
  fin_cases i <;> decide +kernel


end HlawkaSchatten.BelowExponent.Vertex
