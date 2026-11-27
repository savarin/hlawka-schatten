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

def vcM1Child2CutCell : ParameterCell := ⟨⟨1/20, 1/16⟩, ⟨11/80, 3/20⟩, ⟨1/36, 1/24⟩⟩
def vcM1Child2CutRoots : Fin 3 → RatBounds := ![⟨266838023511557/140737488355328, 288267031603253/140737488355328⟩, ⟨127934617344231/70368744177664, 553303116888373/281474976710656⟩, ⟨68803394041897/70368744177664, 39075066561097/35184372088832⟩]
def vcM1Child2CutCaps : Fin 3 → Fin 3 → ℚ := ![![39505944237/100000000, 4278732259/12500000, 15709344549/100000000], ![26909638819/100000000, 14301155737/50000000, 11008945359/100000000], ![1018988569/100000000, 1088592103/100000000, 13775729/3125000]]
def vcM1Child2CutWeightFloor : ℚ := 104849519/100000000
def vcM1Child2CutMargins : Fin 3 → ℚ := ![33043747/2500000000, 62671983/5000000000, 53247103/10000000000]

theorem vcM1Child2Cut_roots_ok : vcM1Child2CutCell.rootsOK vcM1Child2CutRoots = true := by decide +kernel

theorem vcM1Child2Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM1Child2CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM1Child2Cut_margin_le (i : Fin 3) : curvatureLoss vcM1Child2CutCell vcM1Child2CutCaps i ≤ vcM1Child2CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM1Child3CutCell : ParameterCell := ⟨⟨1/20, 1/16⟩, ⟨11/80, 3/20⟩, ⟨1/24, 1/18⟩⟩
def vcM1Child3CutRoots : Fin 3 → RatBounds := ![⟨531195292437601/281474976710656, 286901498276241/140737488355328⟩, ⟨31804036531199/17592186044416, 550139596920291/281474976710656⟩, ⟨272346682857851/281474976710656, 77319159095179/70368744177664⟩]
def vcM1Child3CutCaps : Fin 3 → Fin 3 → ℚ := ![![20338037699/50000000, 35259700147/100000000, 16095467039/100000000], ![13848474017/50000000, 14710682773/50000000, 2819354741/25000000], ![242112773/25000000, 1032503873/100000000, 83485539/20000000]]
def vcM1Child3CutWeightFloor : ℚ := 107288393/100000000
def vcM1Child3CutMargins : Fin 3 → ℚ := ![27175251/2000000000, 16102481/1250000000, 54469197/10000000000]

theorem vcM1Child3Cut_roots_ok : vcM1Child3CutCell.rootsOK vcM1Child3CutRoots = true := by decide +kernel

theorem vcM1Child3Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM1Child3CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM1Child3Cut_margin_le (i : Fin 3) : curvatureLoss vcM1Child3CutCell vcM1Child3CutCaps i ≤ vcM1Child3CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM1Child4CutCell : ParameterCell := ⟨⟨1/16, 3/40⟩, ⟨1/8, 11/80⟩, ⟨1/36, 1/24⟩⟩
def vcM1Child4CutRoots : Fin 3 → RatBounds := ![⟨264761514191349/140737488355328, 142976675140973/70368744177664⟩, ⟨256944144592615/140737488355328, 138839068886377/70368744177664⟩, ⟨274663665894011/281474976710656, 311866851773767/281474976710656⟩]
def vcM1Child4CutCaps : Fin 3 → Fin 3 → ℚ := ![![6210737009/12500000, 10978310133/25000000, 21289984621/100000000], ![42102101207/100000000, 21928042703/50000000, 19039234739/100000000], ![541494079/50000000, 227913887/20000000, 455346621/100000000]]
def vcM1Child4CutWeightFloor : ℚ := 104549973/100000000
def vcM1Child4CutMargins : Fin 3 → ℚ := ![36376961/2000000000, 17417227/1000000000, 79865969/10000000000]

theorem vcM1Child4Cut_roots_ok : vcM1Child4CutCell.rootsOK vcM1Child4CutRoots = true := by decide +kernel

theorem vcM1Child4Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM1Child4CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM1Child4Cut_margin_le (i : Fin 3) : curvatureLoss vcM1Child4CutCell vcM1Child4CutCaps i ≤ vcM1Child4CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM1Child5CutCell : ParameterCell := ⟨⟨1/16, 3/40⟩, ⟨1/8, 11/80⟩, ⟨1/24, 1/18⟩⟩
def vcM1Child5CutRoots : Fin 3 → RatBounds := ![⟨131747692077343/70368744177664, 569119849979933/281474976710656⟩, ⟨255537912735951/140737488355328, 552261300336057/281474976710656⟩, ⟨135904806428123/140737488355328, 308557533947325/281474976710656⟩]
def vcM1Child5CutCaps : Fin 3 → Fin 3 → ℚ := ![![25603256481/50000000, 22638446673/50000000, 21815861011/100000000], ![8678609977/20000000, 45189071529/100000000, 19498856933/100000000], ![1029699851/100000000, 540882163/50000000, 26961351/6250000]]
def vcM1Child5CutWeightFloor : ℚ := 26735519/25000000
def vcM1Child5CutMargins : Fin 3 → ℚ := ![187247651/10000000000, 179299759/10000000000, 16346597/2000000000]

theorem vcM1Child5Cut_roots_ok : vcM1Child5CutCell.rootsOK vcM1Child5CutRoots = true := by decide +kernel

theorem vcM1Child5Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM1Child5CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM1Child5Cut_margin_le (i : Fin 3) : curvatureLoss vcM1Child5CutCell vcM1Child5CutCaps i ≤ vcM1Child5CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM1Child6CutCell : ParameterCell := ⟨⟨1/16, 3/40⟩, ⟨11/80, 3/20⟩, ⟨1/36, 1/24⟩⟩
def vcM1Child6CutRoots : Fin 3 → RatBounds := ![⟨260139728282237/140737488355328, 140112239045771/70368744177664⟩, ⟨501783628174799/281474976710656, 540923836098703/281474976710656⟩, ⟨276986346812245/281474976710656, 78178404852425/70368744177664⟩]
def vcM1Child6CutCaps : Fin 3 → Fin 3 → ℚ := ![![39314154097/100000000, 34163931537/100000000, 16830797199/100000000], ![15075217549/50000000, 31702943151/100000000, 2741833121/20000000], ![102039221/10000000, 1342921/125000, 112200171/25000000]]
def vcM1Child6CutWeightFloor : ℚ := 26359229/25000000
def vcM1Child6CutMargins : Fin 3 → ℚ := ![138133463/10000000000, 131236751/10000000000, 60730543/10000000000]

theorem vcM1Child6Cut_roots_ok : vcM1Child6CutCell.rootsOK vcM1Child6CutRoots = true := by decide +kernel

theorem vcM1Child6Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM1Child6CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM1Child6Cut_margin_le (i : Fin 3) : curvatureLoss vcM1Child6CutCell vcM1Child6CutCaps i ≤ vcM1Child6CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM1Child7CutCell : ParameterCell := ⟨⟨1/16, 3/40⟩, ⟨11/80, 3/20⟩, ⟨1/24, 1/18⟩⟩
def vcM1Child7CutRoots : Fin 3 → RatBounds := ![⟨517815086862883/281474976710656, 278871146517041/140737488355328⟩, ⟨498993465222267/281474976710656, 134464916973319/70368744177664⟩, ⟨274135535627813/281474976710656, 154713624641903/140737488355328⟩]
def vcM1Child7CutCaps : Fin 3 → Fin 3 → ℚ := ![![20254423963/50000000, 7044363997/20000000, 17255530853/100000000], ![15533558611/50000000, 32653925033/100000000, 7024460277/50000000], ![969907269/100000000, 254850693/25000000, 85018533/20000000]]
def vcM1Child7CutWeightFloor : ℚ := 26965237/25000000
def vcM1Child7CutMargins : Fin 3 → ℚ := ![142135511/10000000000, 67513933/5000000000, 31083259/5000000000]

theorem vcM1Child7Cut_roots_ok : vcM1Child7CutCell.rootsOK vcM1Child7CutRoots = true := by decide +kernel

theorem vcM1Child7Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM1Child7CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM1Child7Cut_margin_le (i : Fin 3) : curvatureLoss vcM1Child7CutCell vcM1Child7CutCaps i ≤ vcM1Child7CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM28Child0CutCell : ParameterCell := ⟨⟨3/40, 7/80⟩, ⟨1/10, 9/80⟩, ⟨0, 1/72⟩⟩
def vcM28Child0CutRoots : Fin 3 → RatBounds := ![⟨135438166012815/70368744177664, 586968863489937/281474976710656⟩, ⟨535657388028775/281474976710656, 580507957891379/281474976710656⟩, ⟨69542458174107/70368744177664, 9938034685035/8796093022208⟩]
def vcM28Child0CutCaps : Fin 3 → Fin 3 → ℚ := ![![80769399001/100000000, 18447341551/25000000, 2310739419/6250000], ![11168975579/10000000, 112932463619/100000000, 1308379899/2500000], ![695831701/50000000, 1432563881/100000000, 269828577/50000000]]
def vcM28Child0CutWeightFloor : ℚ := 6176611/6250000
def vcM28Child0CutMargins : Fin 3 → ℚ := ![379252457/10000000000, 184072683/5000000000, 43932261/2500000000]

theorem vcM28Child0Cut_roots_ok : vcM28Child0CutCell.rootsOK vcM28Child0CutRoots = true := by decide +kernel

theorem vcM28Child0Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM28Child0CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM28Child0Cut_margin_le (i : Fin 3) : curvatureLoss vcM28Child0CutCell vcM28Child0CutCaps i ≤ vcM28Child0CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM28Child1CutCell : ParameterCell := ⟨⟨3/40, 7/80⟩, ⟨1/10, 9/80⟩, ⟨1/72, 1/36⟩⟩
def vcM28Child1CutRoots : Fin 3 → RatBounds := ![⟨134707165330487/70368744177664, 583735707126573/281474976710656⟩, ⟨532604306743985/281474976710656, 9017692061171/4398046511104⟩, ⟨275008389553253/281474976710656, 314316364162343/281474976710656⟩]
def vcM28Child1CutCaps : Fin 3 → Fin 3 → ℚ := ![![24827145377/50000000, 44813944837/100000000, 18783646111/100000000], ![8171493041/12500000, 1350574167/2000000, 27863051119/100000000], ![855424677/100000000, 882613617/100000000, 16441227/5000000]]
def vcM28Child1CutWeightFloor : ℚ := 4162883/4000000
def vcM28Child1CutMargins : Fin 3 → ℚ := ![28340409/1250000000, 221547461/10000000000, 45949857/5000000000]

theorem vcM28Child1Cut_roots_ok : vcM28Child1CutCell.rootsOK vcM28Child1CutRoots = true := by decide +kernel

theorem vcM28Child1Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM28Child1CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM28Child1Cut_margin_le (i : Fin 3) : curvatureLoss vcM28Child1CutCell vcM28Child1CutCaps i ≤ vcM28Child1CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM28Child2CutCell : ParameterCell := ⟨⟨3/40, 7/80⟩, ⟨9/80, 1/8⟩, ⟨0, 1/72⟩⟩
def vcM28Child2CutRoots : Fin 3 → RatBounds := ![⟨132818310720623/70368744177664, 286925961645703/140737488355328⟩, ⟨261135418902403/140737488355328, 282170030096579/140737488355328⟩, ⟨280450820806433/281474976710656, 318529710636451/281474976710656⟩]
def vcM28Child2CutCaps : Fin 3 → Fin 3 → ℚ := ![![60003519913/100000000, 54127277971/100000000, 13837019323/50000000], ![13915844663/20000000, 71067599193/100000000, 6703752977/20000000], ![643735707/50000000, 666917357/50000000, 263967483/50000000]]
def vcM28Child2CutWeightFloor : ℚ := 49818073/50000000
def vcM28Child2CutMargins : Fin 3 → ℚ := ![256195731/10000000000, 123868737/5000000000, 60395093/5000000000]

theorem vcM28Child2Cut_roots_ok : vcM28Child2CutCell.rootsOK vcM28Child2CutRoots = true := by decide +kernel

theorem vcM28Child2Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM28Child2CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM28Child2Cut_margin_le (i : Fin 3) : curvatureLoss vcM28Child2CutCell vcM28Child2CutCaps i ≤ vcM28Child2CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM28Child3CutCell : ParameterCell := ⟨⟨3/40, 7/80⟩, ⟨9/80, 1/8⟩, ⟨1/72, 1/36⟩⟩
def vcM28Child3CutRoots : Fin 3 → RatBounds := ![⟨528433392706839/281474976710656, 285359661177881/140737488355328⟩, ⟨259621828061857/140737488355328, 561001165607763/281474976710656⟩, ⟨277294264587863/281474976710656, 157429490292655/140737488355328⟩]
def vcM28Child3CutCaps : Fin 3 → Fin 3 → ℚ := ![![775470807/1250000, 55990354709/100000000, 28399216387/100000000], ![71948702817/100000000, 14700470489/20000000, 17182324413/50000000], ![1221580959/100000000, 632019383/50000000, 498959859/100000000]]
def vcM28Child3CutWeightFloor : ℚ := 5098087/5000000
def vcM28Child3CutMargins : Fin 3 → ℚ := ![3307971/125000000, 255963377/10000000000, 123788799/10000000000]

theorem vcM28Child3Cut_roots_ok : vcM28Child3CutCell.rootsOK vcM28Child3CutRoots = true := by decide +kernel

theorem vcM28Child3Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM28Child3CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM28Child3Cut_margin_le (i : Fin 3) : curvatureLoss vcM28Child3CutCell vcM28Child3CutCaps i ≤ vcM28Child3CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM28Child4CutCell : ParameterCell := ⟨⟨7/80, 1/10⟩, ⟨1/10, 9/80⟩, ⟨0, 1/72⟩⟩
def vcM28Child4CutRoots : Fin 3 → RatBounds := ![⟨263968613808171/140737488355328, 570251316343381/281474976710656⟩, ⟨262469324227247/140737488355328, 567083427449703/281474976710656⟩, ⟨70065025691651/70368744177664, 318277516919677/281474976710656⟩]
def vcM28Child4CutCaps : Fin 3 → Fin 3 → ℚ := ![![38673200677/50000000, 8902765599/12500000, 37337456283/100000000], ![26318724979/20000000, 1328055329/1000000, 64369557803/100000000], ![138463659/10000000, 1412753559/100000000, 548349687/100000000]]
def vcM28Child4CutWeightFloor : ℚ := 9956839/10000000
def vcM28Child4CutMargins : Fin 3 → ℚ := ![102856179/2500000000, 401898043/10000000000, 199968729/10000000000]

theorem vcM28Child4Cut_roots_ok : vcM28Child4CutCell.rootsOK vcM28Child4CutRoots = true := by decide +kernel

theorem vcM28Child4Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM28Child4CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM28Child4Cut_margin_le (i : Fin 3) : curvatureLoss vcM28Child4CutCell vcM28Child4CutCaps i ≤ vcM28Child4CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM28Child5CutCell : ParameterCell := ⟨⟨7/80, 1/10⟩, ⟨1/10, 9/80⟩, ⟨1/72, 1/36⟩⟩
def vcM28Child5CutRoots : Fin 3 → RatBounds := ![⟨262518344358727/140737488355328, 283526105460087/140737488355328⟩, ⟨521975710079943/281474976710656, 281907807060561/140737488355328⟩, ⟨277108255436689/281474976710656, 157306062005855/140737488355328⟩]
def vcM28Child5CutCaps : Fin 3 → Fin 3 → ℚ := ![![46729063907/100000000, 42689001247/100000000, 2354962049/12500000], ![9232246443/12500000, 3051569911/4000000, 16687330397/50000000], ![106041459/12500000, 864826717/100000000, 167317321/50000000]]
def vcM28Child5CutWeightFloor : ℚ := 104667723/100000000
def vcM28Child5CutMargins : Fin 3 → ℚ := ![237567107/10000000000, 2930809/125000000, 5139403/500000000]

theorem vcM28Child5Cut_roots_ok : vcM28Child5CutCell.rootsOK vcM28Child5CutRoots = true := by decide +kernel

theorem vcM28Child5Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM28Child5CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM28Child5Cut_margin_le (i : Fin 3) : curvatureLoss vcM28Child5CutCell vcM28Child5CutCaps i ≤ vcM28Child5CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM28Child6CutCell : ParameterCell := ⟨⟨7/80, 1/10⟩, ⟨9/80, 1/8⟩, ⟨0, 1/72⟩⟩
def vcM28Child6CutRoots : Fin 3 → RatBounds := ![⟨129595105071545/70368744177664, 558420072864423/281474976710656⟩, ⟨512467868117865/281474976710656, 552191379708269/281474976710656⟩, ⟨282412275148021/281474976710656, 318870376595427/281474976710656⟩]
def vcM28Child6CutCaps : Fin 3 → Fin 3 → ℚ := ![![29171037813/50000000, 53010252639/100000000, 28410286213/100000000], ![40811437723/50000000, 41507930883/50000000, 20552836471/50000000], ![1283462833/100000000, 1315435569/100000000, 2685959/500000]]
def vcM28Child6CutWeightFloor : ℚ := 20066599/20000000
def vcM28Child6CutMargins : Fin 3 → ℚ := ![55292763/2000000000, 26884787/1000000000, 13706867/1000000000]

theorem vcM28Child6Cut_roots_ok : vcM28Child6CutCell.rootsOK vcM28Child6CutRoots = true := by decide +kernel

theorem vcM28Child6Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM28Child6CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM28Child6Cut_margin_le (i : Fin 3) : curvatureLoss vcM28Child6CutCell vcM28Child6CutCaps i ≤ vcM28Child6CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM28Child7CutCell : ParameterCell := ⟨⟨7/80, 1/10⟩, ⟨9/80, 1/8⟩, ⟨1/72, 1/36⟩⟩
def vcM28Child7CutRoots : Fin 3 → RatBounds := ![⟨515559184867243/281474976710656, 555314759966895/281474976710656⟩, ⟨127381440854293/70368744177664, 548953267307419/281474976710656⟩, ⟨279267873887277/281474976710656, 39404346764565/35184372088832⟩]
def vcM28Child7CutCaps : Fin 3 → Fin 3 → ℚ := ![![60378056599/100000000, 428606429/781250, 29168621969/100000000], ![84434078429/100000000, 85911623639/100000000, 21077655913/50000000], ![1217889937/100000000, 1948661/156250, 2539327/500000]]
def vcM28Child7CutWeightFloor : ℚ := 102636559/100000000
def vcM28Child7CutMargins : Fin 3 → ℚ := ![142886429/5000000000, 277954941/10000000000, 140529157/10000000000]

theorem vcM28Child7Cut_roots_ok : vcM28Child7CutCell.rootsOK vcM28Child7CutRoots = true := by decide +kernel

theorem vcM28Child7Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM28Child7CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM28Child7Cut_margin_le (i : Fin 3) : curvatureLoss vcM28Child7CutCell vcM28Child7CutCaps i ≤ vcM28Child7CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM29Child0CutCell : ParameterCell := ⟨⟨3/40, 7/80⟩, ⟨1/10, 9/80⟩, ⟨1/36, 1/24⟩⟩
def vcM29Child0CutRoots : Fin 3 → RatBounds := ![⟨268020163776971/140737488355328, 290328244827367/140737488355328⟩, ⟨66211732710851/35184372088832, 573918373727623/281474976710656⟩, ⟨68002199164097/70368744177664, 155405096050273/140737488355328⟩]
def vcM29Child0CutCaps : Fin 3 → Fin 3 → ℚ := ![![51198857773/100000000, 23110828533/50000000, 3852585039/20000000], ![1349079403/2000000, 69687266217/100000000, 28549673379/100000000], ![101393411/12500000, 104524503/12500000, 310627137/100000000]]
def vcM29Child0CutWeightFloor : ℚ := 21324781/20000000
def vcM29Child0CutMargins : Fin 3 → ℚ := ![14606231/625000000, 228400907/10000000000, 94132987/10000000000]

theorem vcM29Child0Cut_roots_ok : vcM29Child0CutCell.rootsOK vcM29Child0CutRoots = true := by decide +kernel

theorem vcM29Child0Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM29Child0CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM29Child0Cut_margin_le (i : Fin 3) : curvatureLoss vcM29Child0CutCell vcM29Child0CutCaps i ≤ vcM29Child0CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM29Child1CutCell : ParameterCell := ⟨⟨3/40, 7/80⟩, ⟨1/10, 9/80⟩, ⟨1/24, 1/18⟩⟩
def vcM29Child1CutRoots : Fin 3 → RatBounds := ![⟨533378276526115/281474976710656, 577720288336301/281474976710656⟩, ⟨263458056925105/140737488355328, 285427324739127/140737488355328⟩, ⟨134579464757537/140737488355328, 38435454056951/35184372088832⟩]
def vcM29Child1CutCaps : Fin 3 → Fin 3 → ℚ := ![![52732778689/100000000, 47619074469/100000000, 19739091353/100000000], ![34759817013/50000000, 35914574507/50000000, 913495933/3125000], ![770106187/100000000, 396617271/50000000, 58771821/20000000]]
def vcM29Child1CutWeightFloor : ℚ := 109177407/100000000
def vcM29Child1CutMargins : Fin 3 → ℚ := ![9625247/400000000, 235210011/10000000000, 96354981/10000000000]

theorem vcM29Child1Cut_roots_ok : vcM29Child1CutCell.rootsOK vcM29Child1CutRoots = true := by decide +kernel

theorem vcM29Child1Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM29Child1CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM29Child1Cut_margin_le (i : Fin 3) : curvatureLoss vcM29Child1CutCell vcM29Child1CutCaps i ≤ vcM29Child1CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM29Child2CutCell : ParameterCell := ⟨⟨3/40, 7/80⟩, ⟨9/80, 1/8⟩, ⟨1/36, 1/24⟩⟩
def vcM29Child2CutRoots : Fin 3 → RatBounds := ![⟨525725466202183/281474976710656, 17741753918535/8796093022208⟩, ⟨32272407794349/17592186044416, 34863937193553/17592186044416⟩, ⟨274299270611153/281474976710656, 155690602823159/140737488355328⟩]
def vcM29Child2CutCaps : Fin 3 → Fin 3 → ℚ := ![![64056792577/100000000, 14459578397/25000000, 454999441/1562500], ![37149397679/50000000, 75917514151/100000000, 35205492331/100000000], ![290134387/25000000, 119950979/10000000, 472282713/100000000]]
def vcM29Child2CutWeightFloor : ℚ := 52145031/50000000
def vcM29Child2CutMargins : Fin 3 → ℚ := ![136512061/5000000000, 66033547/2500000000, 126774457/10000000000]

theorem vcM29Child2Cut_roots_ok : vcM29Child2CutCell.rootsOK vcM29Child2CutRoots = true := by decide +kernel

theorem vcM29Child2Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM29Child2CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM29Child2Cut_margin_le (i : Fin 3) : curvatureLoss vcM29Child2CutCell vcM29Child2CutCaps i ≤ vcM29Child2CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM29Child3CutCell : ParameterCell := ⟨⟨3/40, 7/80⟩, ⟨9/80, 1/8⟩, ⟨1/24, 1/18⟩⟩
def vcM29Child3CutRoots : Fin 3 → RatBounds := ![⟨523140329234061/281474976710656, 35305732400493/17592186044416⟩, ⟨513605505595697/281474976710656, 277397009704401/140737488355328⟩, ⟨271453737758001/281474976710656, 154040775355573/140737488355328⟩]
def vcM29Child3CutCaps : Fin 3 → Fin 3 → ℚ := ![![66062004211/100000000, 466189709/781250, 5967323591/20000000], ![9579511359/12500000, 7831733393/10000000, 7211065571/20000000], ![1103885093/100000000, 1139737129/100000000, 447668587/100000000]]
def vcM29Child3CutWeightFloor : ℚ := 13327613/12500000
def vcM29Child3CutMargins : Fin 3 → ℚ := ![281368977/10000000000, 272259179/10000000000, 25954931/2000000000]

theorem vcM29Child3Cut_roots_ok : vcM29Child3CutCell.rootsOK vcM29Child3CutRoots = true := by decide +kernel

theorem vcM29Child3Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM29Child3CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM29Child3Cut_margin_le (i : Fin 3) : curvatureLoss vcM29Child3CutCell vcM29Child3CutCaps i ≤ vcM29Child3CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM29Child4CutCell : ParameterCell := ⟨⟨7/80, 1/10⟩, ⟨1/10, 9/80⟩, ⟨1/36, 1/24⟩⟩
def vcM29Child4CutRoots : Fin 3 → RatBounds := ![⟨522271377093477/281474976710656, 564006187790531/281474976710656⟩, ⟨519151372170627/281474976710656, 280352326702941/140737488355328⟩, ⟨274117731012227/281474976710656, 4861553357165/4398046511104⟩]
def vcM29Child4CutCaps : Fin 3 → Fin 3 → ℚ := ![![1928517673/4000000, 22023377783/50000000, 9661879943/50000000], ![19061448337/25000000, 19692435571/25000000, 34207633251/100000000], ![804448661/100000000, 409829269/50000000, 63235499/20000000]]
def vcM29Child4CutWeightFloor : ℚ := 21442451/20000000
def vcM29Child4CutMargins : Fin 3 → ℚ := ![245023207/10000000000, 241852387/10000000000, 105315891/10000000000]

theorem vcM29Child4Cut_roots_ok : vcM29Child4CutCell.rootsOK vcM29Child4CutRoots = true := by decide +kernel

theorem vcM29Child4Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM29Child4CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM29Child4Cut_margin_le (i : Fin 3) : curvatureLoss vcM29Child4CutCell vcM29Child4CutCaps i ≤ vcM29Child4CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM29Child5CutCell : ParameterCell := ⟨⟨7/80, 1/10⟩, ⟨1/10, 9/80⟩, ⟨1/24, 1/18⟩⟩
def vcM29Child5CutRoots : Fin 3 → RatBounds := ![⟨64953986880655/35184372088832, 561102333763385/281474976710656⟩, ⟨64556996158755/35184372088832, 557739327275241/281474976710656⟩, ⟨271276446344571/281474976710656, 307844574733745/281474976710656⟩]
def vcM29Child5CutCaps : Fin 3 → Fin 3 → ℚ := ![![49686317513/100000000, 4539455201/10000000, 4951170781/25000000], ![7861668229/10000000, 20307860461/25000000, 35039523209/100000000], ![9547187/1250000, 97228871/12500000, 299166133/100000000]]
def vcM29Child5CutWeightFloor : ℚ := 5487927/5000000
def vcM29Child5CutMargins : Fin 3 → ℚ := ![252433461/10000000000, 15574497/625000000, 1347987/125000000]

theorem vcM29Child5Cut_roots_ok : vcM29Child5CutCell.rootsOK vcM29Child5CutRoots = true := by decide +kernel

theorem vcM29Child5Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM29Child5CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM29Child5Cut_margin_le (i : Fin 3) : curvatureLoss vcM29Child5CutCell vcM29Child5CutCaps i ≤ vcM29Child5CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM29Child6CutCell : ParameterCell := ⟨⟨7/80, 1/10⟩, ⟨9/80, 1/8⟩, ⟨1/36, 1/24⟩⟩
def vcM29Child6CutRoots : Fin 3 → RatBounds := ![⟨256434817696989/140737488355328, 552358287571705/281474976710656⟩, ⟨63340236045665/35184372088832, 545871293197497/281474976710656⟩, ⟨276284374570465/281474976710656, 311790248476249/281474976710656⟩]
def vcM29Child6CutCaps : Fin 3 → Fin 3 → ℚ := ![![12479829581/20000000, 56698515389/100000000, 14961189679/50000000], ![43614530501/50000000, 88788338431/100000000, 21608990687/50000000], ![14464227/1250000, 1183964979/100000000, 96171013/20000000]]
def vcM29Child6CutWeightFloor : ℚ := 104943121/100000000
def vcM29Child6CutMargins : Fin 3 → ℚ := ![295032763/10000000000, 143504433/5000000000, 144011737/10000000000]

theorem vcM29Child6Cut_roots_ok : vcM29Child6CutCell.rootsOK vcM29Child6CutRoots = true := by decide +kernel

theorem vcM29Child6Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM29Child6CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM29Child6Cut_margin_le (i : Fin 3) : curvatureLoss vcM29Child6CutCell vcM29Child6CutCaps i ≤ vcM29Child6CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM29Child7CutCell : ParameterCell := ⟨⟨7/80, 1/10⟩, ⟨9/80, 1/8⟩, ⟨1/24, 1/18⟩⟩
def vcM29Child7CutRoots : Fin 3 → RatBounds := ![⟨510302613396623/281474976710656, 274770016101793/140737488355328⟩, ⟨504046564811923/281474976710656, 135733560904187/70368744177664⟩, ⟨68362431877305/70368744177664, 154261055117947/140737488355328⟩]
def vcM29Child7CutCaps : Fin 3 → Fin 3 → ℚ := ![![32203218513/50000000, 14630502879/25000000, 30671904671/100000000], ![45005040391/50000000, 22912399051/25000000, 8859663407/20000000], ![550376843/50000000, 1125409401/100000000, 455924847/100000000]]
def vcM29Child7CutWeightFloor : ℚ := 3351639/3125000
def vcM29Child7CutMargins : Fin 3 → ℚ := ![304248971/10000000000, 296017583/10000000000, 147525571/10000000000]

theorem vcM29Child7Cut_roots_ok : vcM29Child7CutCell.rootsOK vcM29Child7CutRoots = true := by decide +kernel

theorem vcM29Child7Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM29Child7CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM29Child7Cut_margin_le (i : Fin 3) : curvatureLoss vcM29Child7CutCell vcM29Child7CutCaps i ≤ vcM29Child7CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM31Child0CutCell : ParameterCell := ⟨⟨3/40, 7/80⟩, ⟨1/8, 11/80⟩, ⟨1/36, 1/24⟩⟩
def vcM31Child0CutRoots : Fin 3 → RatBounds := ![⟨516412131669149/281474976710656, 139049281452329/70368744177664⟩, ⟨504103527414795/281474976710656, 271603577522511/140737488355328⟩, ⟨138273427973683/140737488355328, 156067673065345/140737488355328⟩]
def vcM31Child0CutCaps : Fin 3 → Fin 3 → ℚ := ![![49284275309/100000000, 10957466519/25000000, 899748389/4000000], ![49326969209/100000000, 50874624231/100000000, 23854485867/100000000], ![1734299/160000, 70305927/6250000, 115979349/25000000]]
def vcM31Child0CutWeightFloor : ℚ := 2629259/2500000
def vcM31Child0CutMargins : Fin 3 → ℚ := ![195213747/10000000000, 11730133/625000000, 5727653/625000000]

theorem vcM31Child0Cut_roots_ok : vcM31Child0CutCell.rootsOK vcM31Child0CutRoots = true := by decide +kernel

theorem vcM31Child0Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM31Child0CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM31Child0Cut_margin_le (i : Fin 3) : curvatureLoss vcM31Child0CutCell vcM31Child0CutCaps i ≤ vcM31Child0CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM31Child1CutCell : ParameterCell := ⟨⟨3/40, 7/80⟩, ⟨1/8, 11/80⟩, ⟨1/24, 1/18⟩⟩
def vcM31Child1CutRoots : Fin 3 → RatBounds := ![⟨64237136655021/35184372088832, 553435506665053/281474976710656⟩, ⟨501371664364903/281474976710656, 270103833904035/140737488355328⟩, ⟨17106635053827/17592186044416, 77215097392679/70368744177664⟩]
def vcM31Child1CutCaps : Fin 3 → Fin 3 → ℚ := ![![50844119133/100000000, 45219129763/100000000, 461240863/2000000], ![10174735609/20000000, 52469947297/100000000, 2443776503/10000000], ![515356913/50000000, 1068291321/100000000, 439625313/100000000]]
def vcM31Child1CutWeightFloor : ℚ := 107543563/100000000
def vcM31Child1CutMargins : Fin 3 → ℚ := ![100576449/5000000000, 193374913/10000000000, 93833117/10000000000]

theorem vcM31Child1Cut_roots_ok : vcM31Child1CutCell.rootsOK vcM31Child1CutRoots = true := by decide +kernel

theorem vcM31Child1Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM31Child1CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM31Child1Cut_margin_le (i : Fin 3) : curvatureLoss vcM31Child1CutCell vcM31Child1CutCaps i ≤ vcM31Child1CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM31Child2CutCell : ParameterCell := ⟨⟨3/40, 7/80⟩, ⟨11/80, 3/20⟩, ⟨1/36, 1/24⟩⟩
def vcM31Child2CutRoots : Fin 3 → RatBounds := ![⟨507971014677747/281474976710656, 545839315540001/281474976710656⟩, ⟨492785887222271/281474976710656, 529852803276813/281474976710656⟩, ⟨278765150377999/281474976710656, 9782756659367/8796093022208⟩]
def vcM31Child2CutCaps : Fin 3 → Fin 3 → ℚ := ![![3909458263/10000000, 4271156847/12500000, 4459109901/25000000], ![17281016349/50000000, 7192115179/20000000, 16936327417/100000000], ![255295363/25000000, 530822471/50000000, 36601/8000]]
def vcM31Child2CutWeightFloor : ℚ := 26506201/25000000
def vcM31Child2CutMargins : Fin 3 → ℚ := ![146322917/10000000000, 69766117/5000000000, 13803749/2000000000]

theorem vcM31Child2Cut_roots_ok : vcM31Child2CutCell.rootsOK vcM31Child2CutRoots = true := by decide +kernel

theorem vcM31Child2Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM31Child2CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM31Child2Cut_margin_le (i : Fin 3) : curvatureLoss vcM31Child2CutCell vcM31Child2CutCaps i ≤ vcM31Child2CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM31Child3CutCell : ParameterCell := ⟨⟨3/40, 7/80⟩, ⟨11/80, 3/20⟩, ⟨1/24, 1/18⟩⟩
def vcM31Child3CutRoots : Fin 3 → RatBounds := ![⟨252760038261851/140737488355328, 543152710121375/281474976710656⟩, ⟨30629507148009/17592186044416, 263439182029545/140737488355328⟩, ⟨137964851703741/140737488355328, 2420282169171/2199023255552⟩]
def vcM31Child3CutCaps : Fin 3 → Fin 3 → ℚ := ![![40325844233/100000000, 2203205467/6250000, 18297494409/100000000], ![1782062399/5000000, 37078087399/100000000, 17361536193/100000000], ![970774333/100000000, 503886163/50000000, 216729917/50000000]]
def vcM31Child3CutWeightFloor : ℚ := 4337317/4000000
def vcM31Child3CutMargins : Fin 3 → ℚ := ![75357011/5000000000, 143698317/10000000000, 70691731/10000000000]

theorem vcM31Child3Cut_roots_ok : vcM31Child3CutCell.rootsOK vcM31Child3CutRoots = true := by decide +kernel

theorem vcM31Child3Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM31Child3CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM31Child3Cut_margin_le (i : Fin 3) : curvatureLoss vcM31Child3CutCell vcM31Child3CutCaps i ≤ vcM31Child3CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM31Child4CutCell : ParameterCell := ⟨⟨7/80, 1/10⟩, ⟨1/8, 11/80⟩, ⟨1/36, 1/24⟩⟩
def vcM31Child4CutRoots : Fin 3 → RatBounds := ![⟨252175462734203/140737488355328, 541907055999037/281474976710656⟩, ⟨247626158700897/140737488355328, 532330218285223/281474976710656⟩, ⟨278426677548817/281474976710656, 312608227143631/281474976710656⟩]
def vcM31Child4CutCaps : Fin 3 → Fin 3 → ℚ := ![![9685479887/20000000, 8667473453/20000000, 2915748657/12500000], ![28706531811/50000000, 735984281/1250000, 29183556549/100000000], ![270537923/25000000, 555559957/50000000, 94560187/20000000]]
def vcM31Child4CutWeightFloor : ℚ := 26447561/25000000
def vcM31Child4CutMargins : Fin 3 → ℚ := ![20932901/1000000000, 40464009/2000000000, 25924439/2500000000]

theorem vcM31Child4Cut_roots_ok : vcM31Child4CutCell.rootsOK vcM31Child4CutRoots = true := by decide +kernel

theorem vcM31Child4Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM31Child4CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM31Child4Cut_margin_le (i : Fin 3) : curvatureLoss vcM31Child4CutCell vcM31Child4CutCaps i ≤ vcM31Child4CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM31Child5CutCell : ParameterCell := ⟨⟨7/80, 1/10⟩, ⟨1/8, 11/80⟩, ⟨1/24, 1/18⟩⟩
def vcM31Child5CutRoots : Fin 3 → RatBounds := ![⟨501850150034933/281474976710656, 67395791837601/35184372088832⟩, ⟨246297023596987/140737488355328, 132354263694557/70368744177664⟩, ⟨137799456012131/140737488355328, 77341187929407/70368744177664⟩]
def vcM31Child5CutCaps : Fin 3 → Fin 3 → ℚ := ![![24992242193/50000000, 22365926927/50000000, 5981583167/25000000], ![59244038059/100000000, 60767183819/100000000, 29917585481/100000000], ![514557083/50000000, 1055627833/100000000, 89632909/20000000]]
def vcM31Child5CutWeightFloor : ℚ := 6759047/6250000
def vcM31Child5CutMargins : Fin 3 → ℚ := ![107909213/5000000000, 208598207/10000000000, 106244547/10000000000]

theorem vcM31Child5Cut_roots_ok : vcM31Child5CutCell.rootsOK vcM31Child5CutRoots = true := by decide +kernel

theorem vcM31Child5Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM31Child5CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM31Child5Cut_margin_le (i : Fin 3) : curvatureLoss vcM31Child5CutCell vcM31Child5CutCaps i ≤ vcM31Child5CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM31Child6CutCell : ParameterCell := ⟨⟨7/80, 1/10⟩, ⟨11/80, 3/20⟩, ⟨1/36, 1/24⟩⟩
def vcM31Child6CutRoots : Fin 3 → RatBounds := ![⟨248303385363469/140737488355328, 532488393602973/281474976710656⟩, ⟨121155306353435/70368744177664, 519900507101667/281474976710656⟩, ⟨280554737970617/281474976710656, 313572909389663/281474976710656⟩]
def vcM31Child6CutCaps : Fin 3 → Fin 3 → ℚ := ![![1930569933/5000000, 16990124627/50000000, 465427333/2500000], ![39715251181/100000000, 10257655889/25000000, 20572549297/100000000], ![10202013/1000000, 524934421/50000000, 116648037/25000000]]
def vcM31Child6CutWeightFloor : ℚ := 21323277/20000000
def vcM31Child6CutMargins : Fin 3 → ℚ := ![31088343/2000000000, 37259281/2500000000, 77667349/10000000000]

theorem vcM31Child6Cut_roots_ok : vcM31Child6CutCell.rootsOK vcM31Child6CutRoots = true := by decide +kernel

theorem vcM31Child6Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM31Child6CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM31Child6Cut_margin_le (i : Fin 3) : curvatureLoss vcM31Child6CutCell vcM31Child6CutCaps i ≤ vcM31Child6CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM31Child7CutCell : ParameterCell := ⟨⟨7/80, 1/10⟩, ⟨11/80, 3/20⟩, ⟨1/24, 1/18⟩⟩
def vcM31Child7CutRoots : Fin 3 → RatBounds := ![⟨123541683403013/70368744177664, 132454545300255/70368744177664⟩, ⟨30123587209461/17592186044416, 64625936534035/35184372088832⟩, ⟨277734050971145/281474976710656, 155176190665683/140737488355328⟩]
def vcM31Child7CutCaps : Fin 3 → Fin 3 → ℚ := ![![39849371979/100000000, 17536988521/50000000, 4776931243/25000000], ![40978297179/100000000, 42338390557/100000000, 21095364841/100000000], ![3879789/400000, 7975849/800000, 221088493/50000000]]
def vcM31Child7CutWeightFloor : ℚ := 27252081/25000000
def vcM31Child7CutMargins : Fin 3 → ℚ := ![80102671/5000000000, 153600017/10000000000, 39793933/5000000000]

theorem vcM31Child7Cut_roots_ok : vcM31Child7CutCell.rootsOK vcM31Child7CutRoots = true := by decide +kernel

theorem vcM31Child7Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM31Child7CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM31Child7Cut_margin_le (i : Fin 3) : curvatureLoss vcM31Child7CutCell vcM31Child7CutCaps i ≤ vcM31Child7CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM59Child0CutCell : ParameterCell := ⟨⟨1/10, 9/80⟩, ⟨1/10, 9/80⟩, ⟨1/36, 1/24⟩⟩
def vcM59Child0CutRoots : Fin 3 → RatBounds := ![⟨509642097210027/281474976710656, 137229884316629/70368744177664⟩, ⟨509642097210027/281474976710656, 137229884316629/70368744177664⟩, ⟨276197081784741/281474976710656, 155837762424955/140737488355328⟩]
def vcM59Child0CutCaps : Fin 3 → Fin 3 → ℚ := ![![2802190371/6250000, 20706475497/50000000, 9567673619/50000000], ![42154296707/50000000, 136502139/156250, 39715874849/100000000], ![797437199/100000000, 806142231/100000000, 321850367/100000000]]
def vcM59Child0CutWeightFloor : ℚ := 5390441/5000000
def vcM59Child0CutMargins : Fin 3 → ℚ := ![31769563/1250000000, 253456167/10000000000, 5785993/500000000]

theorem vcM59Child0Cut_roots_ok : vcM59Child0CutCell.rootsOK vcM59Child0CutRoots = true := by decide +kernel

theorem vcM59Child0Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM59Child0CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM59Child0Cut_margin_le (i : Fin 3) : curvatureLoss vcM59Child0CutCell vcM59Child0CutCaps i ≤ vcM59Child0CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM59Child1CutCell : ParameterCell := ⟨⟨1/10, 9/80⟩, ⟨1/10, 9/80⟩, ⟨1/24, 1/18⟩⟩
def vcM59Child1CutRoots : Fin 3 → RatBounds := ![⟨63377710233629/35184372088832, 273021424460327/140737488355328⟩, ⟨63377710233629/35184372088832, 273021424460327/140737488355328⟩, ⟨273364447145947/281474976710656, 308409654445091/281474976710656⟩]
def vcM59Child1CutCaps : Fin 3 → Fin 3 → ℚ := ![![2311334657/5000000, 10672990463/25000000, 19617465037/100000000], ![17391965531/20000000, 90126297379/100000000, 8141280483/20000000], ![378549259/50000000, 382608333/50000000, 30458509/10000000]]
def vcM59Child1CutWeightFloor : ℚ := 22069719/20000000
def vcM59Child1CutMargins : Fin 3 → ℚ := ![261955489/10000000000, 65313951/2500000000, 11855449/1000000000]

theorem vcM59Child1Cut_roots_ok : vcM59Child1CutCell.rootsOK vcM59Child1CutRoots = true := by decide +kernel

theorem vcM59Child1Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM59Child1CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM59Child1Cut_margin_le (i : Fin 3) : curvatureLoss vcM59Child1CutCell vcM59Child1CutCaps i ≤ vcM59Child1CutMargins i := by
  fin_cases i <;> decide +kernel


end HlawkaSchatten.BelowExponent.Vertex
