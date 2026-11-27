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

def vcM59Child2CutCell : ParameterCell := ⟨⟨1/10, 9/80⟩, ⟨9/80, 1/8⟩, ⟨1/36, 1/24⟩⟩
def vcM59Child2CutRoots : Fin 3 → RatBounds := ![⟨7828587025991/4398046511104, 134587805754471/70368744177664⟩, ⟨497998771739767/281474976710656, 133790361518805/70368744177664⟩, ⟨69564499967153/70368744177664, 78097269539217/70368744177664⟩]
def vcM59Child2CutCaps : Fin 3 → Fin 3 → ℚ := ![![59869157689/100000000, 54755337273/100000000, 30084009033/100000000], ![25031910959/25000000, 12737254763/12500000, 6448257907/12500000], ![115013887/10000000, 234116073/20000000, 61185049/12500000]]
def vcM59Child2CutWeightFloor : ℚ := 52797727/50000000
def vcM59Child2CutMargins : Fin 3 → ℚ := ![78816761/2500000000, 77196551/2500000000, 5021629/312500000]

theorem vcM59Child2Cut_roots_ok : vcM59Child2CutCell.rootsOK vcM59Child2CutRoots = true := by decide +kernel

theorem vcM59Child2Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM59Child2CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM59Child2Cut_margin_le (i : Fin 3) : curvatureLoss vcM59Child2CutCell vcM59Child2CutCaps i ≤ vcM59Child2CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM59Child3CutCell : ParameterCell := ⟨⟨1/10, 9/80⟩, ⟨9/80, 1/8⟩, ⟨1/24, 1/18⟩⟩
def vcM59Child3CutRoots : Fin 3 → RatBounds := ![⟨124619422524535/70368744177664, 535554782117607/281474976710656⟩, ⟨123848607036041/70368744177664, 133076891821635/70368744177664⟩, ⟨68858516310009/70368744177664, 19321868710657/17592186044416⟩]
def vcM59Child3CutCaps : Fin 3 → Fin 3 → ℚ := ![![61818618959/100000000, 1130751417/2000000, 1928666167/6250000], ![51677036637/50000000, 105220117313/100000000, 52908804519/100000000], ![218838821/20000000, 556526309/50000000, 232115167/50000000]]
def vcM59Child3CutWeightFloor : ℚ := 13485611/12500000
def vcM59Child3CutMargins : Fin 3 → ℚ := ![325241307/10000000000, 6372337/200000000, 16472771/1000000000]

theorem vcM59Child3Cut_roots_ok : vcM59Child3CutCell.rootsOK vcM59Child3CutRoots = true := by decide +kernel

theorem vcM59Child3Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM59Child3CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM59Child3Cut_margin_le (i : Fin 3) : curvatureLoss vcM59Child3CutCell vcM59Child3CutCaps i ≤ vcM59Child3CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM59Child4CutCell : ParameterCell := ⟨⟨9/80, 1/8⟩, ⟨1/10, 9/80⟩, ⟨1/36, 1/24⟩⟩
def vcM59Child4CutRoots : Fin 3 → RatBounds := ![⟨497998771739767/281474976710656, 133790361518805/70368744177664⟩, ⟨7828587025991/4398046511104, 134587805754471/70368744177664⟩, ⟨69564499967153/70368744177664, 78097269539217/70368744177664⟩]
def vcM59Child4CutCaps : Fin 3 → Fin 3 → ℚ := ![![160972371/390625, 38412852019/100000000, 18574756033/100000000], ![5708688437/6250000, 29725593/31250, 8984386493/20000000], ![790388143/100000000, 79368463/10000000, 65481619/20000000]]
def vcM59Child4CutWeightFloor : ℚ := 1084151/1000000
def vcM59Child4CutMargins : Fin 3 → ℚ := ![52157707/2000000000, 262723843/10000000000, 62403219/5000000000]

theorem vcM59Child4Cut_roots_ok : vcM59Child4CutCell.rootsOK vcM59Child4CutRoots = true := by decide +kernel

theorem vcM59Child4Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM59Child4CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM59Child4Cut_margin_le (i : Fin 3) : curvatureLoss vcM59Child4CutCell vcM59Child4CutCaps i ≤ vcM59Child4CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM59Child5CutCell : ParameterCell := ⟨⟨9/80, 1/8⟩, ⟨1/10, 9/80⟩, ⟨1/24, 1/18⟩⟩
def vcM59Child5CutRoots : Fin 3 → RatBounds := ![⟨123848607036041/70368744177664, 133076891821635/70368744177664⟩, ⟨124619422524535/70368744177664, 535554782117607/281474976710656⟩, ⟨68858516310009/70368744177664, 19321868710657/17592186044416⟩]
def vcM59Child5CutCaps : Fin 3 → Fin 3 → ℚ := ![![42503406301/100000000, 4951073043/12500000, 9524243961/50000000], ![4711548857/5000000, 1533665181/1562500, 5756647517/12500000], ![187582627/25000000, 376784133/50000000, 77474039/25000000]]
def vcM59Child5CutWeightFloor : ℚ := 110949263/100000000
def vcM59Child5CutMargins : Fin 3 → ℚ := ![268868589/10000000000, 135442859/5000000000, 63949469/5000000000]

theorem vcM59Child5Cut_roots_ok : vcM59Child5CutCell.rootsOK vcM59Child5CutRoots = true := by decide +kernel

theorem vcM59Child5Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM59Child5CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM59Child5Cut_margin_le (i : Fin 3) : curvatureLoss vcM59Child5CutCell vcM59Child5CutCaps i ≤ vcM59Child5CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM59Child6CutCell : ParameterCell := ⟨⟨9/80, 1/8⟩, ⟨9/80, 1/8⟩, ⟨1/36, 1/24⟩⟩
def vcM59Child6CutRoots : Fin 3 → RatBounds := ![⟨490074164568427/281474976710656, 262759435290497/140737488355328⟩, ⟨490074164568427/281474976710656, 262759435290497/140737488355328⟩, ⟨280227955415567/281474976710656, 313152659843743/281474976710656⟩]
def vcM59Child6CutCaps : Fin 3 → Fin 3 → ℚ := ![![56682168777/100000000, 52187804669/100000000, 14854357581/50000000], ![112346142573/100000000, 3582269847/3125000, 30010105477/50000000], ![285682633/25000000, 1158208839/100000000, 249111953/50000000]]
def vcM59Child6CutWeightFloor : ℚ := 106250541/100000000
def vcM59Child6CutMargins : Fin 3 → ℚ := ![20805553/625000000, 328613921/10000000000, 176453159/10000000000]

theorem vcM59Child6Cut_roots_ok : vcM59Child6CutCell.rootsOK vcM59Child6CutRoots = true := by decide +kernel

theorem vcM59Child6Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM59Child6CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM59Child6Cut_margin_le (i : Fin 3) : curvatureLoss vcM59Child6CutCell vcM59Child6CutCaps i ≤ vcM59Child6CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM59Child7CutCell : ParameterCell := ⟨⟨9/80, 1/8⟩, ⟨9/80, 1/8⟩, ⟨1/24, 1/18⟩⟩
def vcM59Child7CutRoots : Fin 3 → RatBounds := ![⟨121883717352763/70368744177664, 522740567530327/281474976710656⟩, ⟨121883717352763/70368744177664, 522740567530327/281474976710656⟩, ⟨138707291063567/140737488355328, 38742537527019/35184372088832⟩]
def vcM59Child7CutCaps : Fin 3 → Fin 3 → ℚ := ![![5854664327/10000000, 5390667179/10000000, 15249702307/50000000], ![28996915807/25000000, 59201959371/50000000, 61580436557/100000000], ![543565313/50000000, 1101572679/100000000, 472633303/100000000]]
def vcM59Child7CutWeightFloor : ℚ := 54261031/50000000
def vcM59Child7CutMargins : Fin 3 → ℚ := ![171754339/5000000000, 339200307/10000000000, 36196617/2000000000]

theorem vcM59Child7Cut_roots_ok : vcM59Child7CutCell.rootsOK vcM59Child7CutRoots = true := by decide +kernel

theorem vcM59Child7Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM59Child7CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM59Child7Cut_margin_le (i : Fin 3) : curvatureLoss vcM59Child7CutCell vcM59Child7CutCaps i ≤ vcM59Child7CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM61Child0CutCell : ParameterCell := ⟨⟨1/10, 9/80⟩, ⟨1/8, 11/80⟩, ⟨1/36, 1/24⟩⟩
def vcM61Child0CutRoots : Fin 3 → RatBounds := ![⟨493202326818377/281474976710656, 528830869399295/281474976710656⟩, ⟨243607742675899/140737488355328, 522544036094375/281474976710656⟩, ⟨140154760757357/140737488355328, 9789297802229/8796093022208⟩]
def vcM61Child0CutCaps : Fin 3 → Fin 3 → ℚ := ![![5877329053/12500000, 42385905033/100000000, 23778926391/100000000], ![32895425099/50000000, 16832835449/25000000, 8707301189/25000000], ![269320173/25000000, 549283279/50000000, 481753841/100000000]]
def vcM61Child0CutWeightFloor : ℚ := 106413227/100000000
def vcM61Child0CutMargins : Fin 3 → ℚ := ![222928631/10000000000, 108470217/5000000000, 115630643/10000000000]

theorem vcM61Child0Cut_roots_ok : vcM61Child0CutCell.rootsOK vcM61Child0CutRoots = true := by decide +kernel

theorem vcM61Child0Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM61Child0CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM61Child0Cut_margin_le (i : Fin 3) : curvatureLoss vcM61Child0CutCell vcM61Child0CutCaps i ≤ vcM61Child0CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM61Child1CutCell : ParameterCell := ⟨⟨1/10, 9/80⟩, ⟨1/8, 11/80⟩, ⟨1/24, 1/18⟩⟩
def vcM61Child1CutRoots : Fin 3 → RatBounds := ![⟨490713273543885/281474976710656, 263053690711669/140737488355328⟩, ⟨121156157849777/70368744177664, 259854632991311/140737488355328⟩, ⟨277494322045865/281474976710656, 310043130959189/281474976710656⟩]
def vcM61Child1CutCaps : Fin 3 → Fin 3 → ℚ := ![![48550290991/100000000, 43765447123/100000000, 24400410751/100000000], ![33960122499/50000000, 69526993893/100000000, 35742745731/100000000], ![102457369/10000000, 522033303/50000000, 456767893/100000000]]
def vcM61Child1CutWeightFloor : ℚ := 108749931/100000000
def vcM61Child1CutMargins : Fin 3 → ℚ := ![45990407/2000000000, 223791821/10000000000, 29642123/2500000000]

theorem vcM61Child1Cut_roots_ok : vcM61Child1CutCell.rootsOK vcM61Child1CutRoots = true := by decide +kernel

theorem vcM61Child1Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM61Child1CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM61Child1Cut_margin_le (i : Fin 3) : curvatureLoss vcM61Child1CutCell vcM61Child1CutCaps i ≤ vcM61Child1CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM61Child2CutCell : ParameterCell := ⟨⟨1/10, 9/80⟩, ⟨11/80, 3/20⟩, ⟨1/36, 1/24⟩⟩
def vcM61Child2CutRoots : Fin 3 → RatBounds := ![⟨486068347754943/281474976710656, 260111022785995/140737488355328⟩, ⟨7456061592545/4398046511104, 63864382492457/35184372088832⟩, ⟨141179559856307/140737488355328, 314263427076237/281474976710656⟩]
def vcM61Child2CutCaps : Fin 3 → Fin 3 → ℚ := ![![37759711717/100000000, 33499473927/100000000, 19132570309/100000000], ![45269818587/100000000, 9319557317/20000000, 24511405689/100000000], ![508456703/50000000, 1038644337/100000000, 475795121/100000000]]
def vcM61Child2CutWeightFloor : ℚ := 53607143/50000000
def vcM61Child2CutMargins : Fin 3 → ℚ := ![1646191/100000000, 15894441/1000000000, 86389409/10000000000]

theorem vcM61Child2Cut_roots_ok : vcM61Child2CutCell.rootsOK vcM61Child2CutRoots = true := by decide +kernel

theorem vcM61Child2Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM61Child2CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM61Child2Cut_margin_le (i : Fin 3) : curvatureLoss vcM61Child2CutCell vcM61Child2CutCaps i ≤ vcM61Child2CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM61Child3CutCell : ParameterCell := ⟨⟨1/10, 9/80⟩, ⟨11/80, 3/20⟩, ⟨1/24, 1/18⟩⟩
def vcM61Child3CutRoots : Fin 3 → RatBounds := ![⟨241818513134339/140737488355328, 258782552227269/140737488355328⟩, ⟨474608335246873/281474976710656, 508096224946871/281474976710656⟩, ⟨279552677832273/281474976710656, 311072185857317/281474976710656⟩]
def vcM61Child3CutCaps : Fin 3 → Fin 3 → ℚ := ![![38988664501/100000000, 17295965947/50000000, 19646748487/100000000], ![46737754331/100000000, 6013970253/12500000, 12581199219/50000000], ![120863873/12500000, 986674407/100000000, 451008921/100000000]]
def vcM61Child3CutWeightFloor : ℚ := 54795199/50000000
def vcM61Child3CutMargins : Fin 3 → ℚ := ![169765891/10000000000, 163909787/10000000000, 11075671/1250000000]

theorem vcM61Child3Cut_roots_ok : vcM61Child3CutCell.rootsOK vcM61Child3CutRoots = true := by decide +kernel

theorem vcM61Child3Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM61Child3CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM61Child3Cut_margin_le (i : Fin 3) : curvatureLoss vcM61Child3CutCell vcM61Child3CutCaps i ≤ vcM61Child3CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM61Child4CutCell : ParameterCell := ⟨⟨9/80, 1/8⟩, ⟨1/8, 11/80⟩, ⟨1/36, 1/24⟩⟩
def vcM61Child4CutRoots : Fin 3 → RatBounds := ![⟨241426652587417/140737488355328, 516802831110457/281474976710656⟩, ⟨479895059080339/281474976710656, 513702750808081/281474976710656⟩, ⟨282200716003143/281474976710656, 314061610576241/281474976710656⟩]
def vcM61Child4CutCaps : Fin 3 → Fin 3 → ℚ := ![![45102662871/100000000, 40969006389/100000000, 23834583647/100000000], ![3699581037/5000000, 1894724557/2500000, 4058695933/10000000], ![534972267/50000000, 135970937/12500000, 98137543/20000000]]
def vcM61Child4CutWeightFloor : ℚ := 26760511/25000000
def vcM61Child4CutMargins : Fin 3 → ℚ := ![235185943/10000000000, 230665843/10000000000, 25401301/2000000000]

theorem vcM61Child4Cut_roots_ok : vcM61Child4CutCell.rootsOK vcM61Child4CutRoots = true := by decide +kernel

theorem vcM61Child4Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM61Child4CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM61Child4Cut_margin_le (i : Fin 3) : curvatureLoss vcM61Child4CutCell vcM61Child4CutCaps i ≤ vcM61Child4CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM61Child5CutCell : ParameterCell := ⟨⟨9/80, 1/8⟩, ⟨1/8, 11/80⟩, ⟨1/24, 1/18⟩⟩
def vcM61Child5CutRoots : Fin 3 → RatBounds := ![⟨480373775253921/281474976710656, 514093447215187/281474976710656⟩, ⟨477366130565477/281474976710656, 510939439091301/281474976710656⟩, ⟨34924721228241/35184372088832, 155437129042157/140737488355328⟩]
def vcM61Child5CutCaps : Fin 3 → Fin 3 → ℚ := ![![46588037821/100000000, 42322029759/100000000, 382502751/1562500], ![76403183703/100000000, 1565682299/2000000, 8332681259/20000000], ![40707149/4000000, 129263453/12500000, 465352129/100000000]]
def vcM61Child5CutWeightFloor : ℚ := 27340569/25000000
def vcM61Child5CutMargins : Fin 3 → ℚ := ![60667781/2500000000, 47610477/2000000000, 32577193/2500000000]

theorem vcM61Child5Cut_roots_ok : vcM61Child5CutCell.rootsOK vcM61Child5CutRoots = true := by decide +kernel

theorem vcM61Child5Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM61Child5CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM61Child5Cut_margin_le (i : Fin 3) : curvatureLoss vcM61Child5CutCell vcM61Child5CutCaps i ≤ vcM61Child5CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM61Child6CutCell : ParameterCell := ⟨⟨9/80, 1/8⟩, ⟨11/80, 3/20⟩, ⟨1/36, 1/24⟩⟩
def vcM61Child6CutRoots : Fin 3 → RatBounds := ![⟨476257352729457/281474976710656, 15903077785443/8796093022208⟩, ⟨470401774934031/281474976710656, 502773144912903/281474976710656⟩, ⟨284181761322803/281474976710656, 157550393632445/140737488355328⟩]
def vcM61Child6CutCaps : Fin 3 → Fin 3 → ℚ := ![![36589033043/100000000, 16373378431/50000000, 19416799863/100000000], ![1590753347/3125000, 3272326581/6250000, 28620112003/100000000], ![505606453/50000000, 1028379953/100000000, 30311449/6250000]]
def vcM61Child6CutWeightFloor : ℚ := 107820597/100000000
def vcM61Child6CutMargins : Fin 3 → ℚ := ![173323343/10000000000, 168698413/10000000000, 94991517/10000000000]

theorem vcM61Child6Cut_roots_ok : vcM61Child6CutCell.rootsOK vcM61Child6CutRoots = true := by decide +kernel

theorem vcM61Child6Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM61Child6CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM61Child6Cut_margin_le (i : Fin 3) : curvatureLoss vcM61Child6CutCell vcM61Child6CutCaps i ≤ vcM61Child6CutMargins i := by
  fin_cases i <;> decide +kernel

def vcM61Child7CutCell : ParameterCell := ⟨⟨9/80, 1/8⟩, ⟨11/80, 3/20⟩, ⟨1/24, 1/18⟩⟩
def vcM61Child7CutRoots : Fin 3 → RatBounds := ![⟨473832846116017/281474976710656, 506252136160341/281474976710656⟩, ⟨467881277437067/281474976710656, 62502763593087/35184372088832⟩, ⟨281389120836699/281474976710656, 311936891684723/281474976710656⟩]
def vcM61Child7CutCaps : Fin 3 → Fin 3 → ℚ := ![![37794944881/100000000, 33829682141/100000000, 3990784799/20000000], ![5257003499/10000000, 54083519891/100000000, 14698099647/50000000], ![7512311/781250, 97723403/10000000, 114956047/25000000]]
def vcM61Child7CutWeightFloor : ℚ := 1721589/1562500
def vcM61Child7CutMargins : Fin 3 → ℚ := ![44703179/2500000000, 43515461/2500000000, 48747859/5000000000]

theorem vcM61Child7Cut_roots_ok : vcM61Child7CutCell.rootsOK vcM61Child7CutRoots = true := by decide +kernel

theorem vcM61Child7Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcM61Child7CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM61Child7Cut_margin_le (i : Fin 3) : curvatureLoss vcM61Child7CutCell vcM61Child7CutCaps i ≤ vcM61Child7CutMargins i := by
  fin_cases i <;> decide +kernel


end HlawkaSchatten.BelowExponent.Vertex
