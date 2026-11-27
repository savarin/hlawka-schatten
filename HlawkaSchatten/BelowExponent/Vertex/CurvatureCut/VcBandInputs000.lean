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

def vcS10CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨13/80, 7/40⟩, ⟨0, 1/40⟩⟩
def vcS10CutRoots : Fin 3 → RatBounds := ![⟨272896382520499/140737488355328, 296618396030061/140737488355328⟩, ⟨512146036187775/281474976710656, 557658627870571/281474976710656⟩, ⟨280550104355227/281474976710656, 80544401482241/70368744177664⟩]
def vcS10CutCaps : Fin 3 → Fin 3 → ℚ := ![![7539752643/25000000, 24427517263/100000000, 10082875349/100000000], ![8115322999/50000000, 565137/3200, 4962832487/100000000], ![658031661/50000000, 354881807/25000000, 290048453/50000000]]
def vcS10CutWeightFloor : ℚ := 99671419/100000000
def vcS10CutMargins : Fin 3 → ℚ := ![100886543/10000000000, 93293277/10000000000, 8479539/2500000000]

theorem vcS10Cut_roots_ok : vcS10CutCell.rootsOK vcS10CutRoots = true := by decide +kernel

theorem vcS10Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS10CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS10Cut_margin_le (i : Fin 3) : curvatureLoss vcS10CutCell vcS10CutCaps i ≤ vcS10CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS11CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨13/80, 7/40⟩, ⟨1/40, 1/20⟩⟩
def vcS11CutRoots : Fin 3 → RatBounds := ![⟨541372215645815/281474976710656, 147028070295303/70368744177664⟩, ⟨506534411897335/281474976710656, 551208278702895/281474976710656⟩, ⟨68775484195433/70368744177664, 78893082257455/70368744177664⟩]
def vcS11CutCaps : Fin 3 → Fin 3 → ℚ := ![![31669427331/100000000, 25710663873/100000000, 2630696407/25000000], ![3402897267/20000000, 18478827159/100000000, 5183734261/100000000], ![1187949973/100000000, 318791969/25000000, 20801117/4000000]]
def vcS11CutWeightFloor : ℚ := 52094443/50000000
def vcS11CutMargins : Fin 3 → ℚ := ![104366629/10000000000, 96269849/10000000000, 6947903/2000000000]

theorem vcS11Cut_roots_ok : vcS11CutCell.rootsOK vcS11CutRoots = true := by decide +kernel

theorem vcS11Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS11CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS11Cut_margin_le (i : Fin 3) : curvatureLoss vcS11CutCell vcS11CutCaps i ≤ vcS11CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS12CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨13/80, 7/40⟩, ⟨1/20, 3/40⟩⟩
def vcS12CutRoots : Fin 3 → RatBounds := ![⟨268647236327147/140737488355328, 583405636511753/281474976710656⟩, ⟨250687475262365/140737488355328, 545300713823153/281474976710656⟩, ⟨270126428472723/281474976710656, 309566507456463/281474976710656⟩]
def vcS12CutCaps : Fin 3 → Fin 3 → ℚ := ![![33167417207/100000000, 13490043903/50000000, 10958911673/100000000], ![8895685513/50000000, 4822590327/25000000, 2701173997/50000000], ![269265553/25000000, 4496732/390625, 234294447/50000000]]
def vcS12CutWeightFloor : ℚ := 108710579/100000000
def vcS12CutMargins : Fin 3 → ℚ := ![13492929/1250000000, 19873087/2000000000, 35616437/10000000000]

theorem vcS12Cut_roots_ok : vcS12CutCell.rootsOK vcS12CutRoots = true := by decide +kernel

theorem vcS12Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS12CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS12Cut_margin_le (i : Fin 3) : curvatureLoss vcS12CutCell vcS12CutCaps i ≤ vcS12CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS13CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨13/80, 7/40⟩, ⟨3/40, 1/10⟩⟩
def vcS13CutRoots : Fin 3 → RatBounds := ![⟨133380158075667/70368744177664, 579067077701407/281474976710656⟩, ⟨496614276983849/281474976710656, 33741819216181/17592186044416⟩, ⟨66391146570589/70368744177664, 76020503388573/70368744177664⟩]
def vcS13CutCaps : Fin 3 → Fin 3 → ℚ := ![![135368568/390625, 28237374363/100000000, 5695854337/50000000], ![9281030331/50000000, 20097309063/100000000, 5619777059/100000000], ![980518897/100000000, 1043926999/100000000, 424229543/100000000]]
def vcS13CutWeightFloor : ℚ := 11323581/10000000
def vcS13CutMargins : Fin 3 → ℚ := ![111598613/10000000000, 102559359/10000000000, 9134963/2500000000]

theorem vcS13Cut_roots_ok : vcS13CutCell.rootsOK vcS13CutRoots = true := by decide +kernel

theorem vcS13Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS13CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS13Cut_margin_le (i : Fin 3) : curvatureLoss vcS13CutCell vcS13CutCaps i ≤ vcS13CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS14CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨7/40, 3/16⟩, ⟨0, 1/40⟩⟩
def vcS14CutRoots : Fin 3 → RatBounds := ![⟨67069565745103/35184372088832, 581712940960579/281474976710656⟩, ⟨125081019152907/70368744177664, 543505110590905/281474976710656⟩, ⟨141533323785743/140737488355328, 161600957838313/140737488355328⟩]
def vcS14CutCaps : Fin 3 → Fin 3 → ℚ := ![![1627453929/6250000, 20627008463/100000000, 1093719473/12500000], ![13612943799/100000000, 593607863/4000000, 847337717/20000000], ![1277800123/100000000, 1362485699/100000000, 580470177/100000000]]
def vcS14CutWeightFloor : ℚ := 4022619/4000000
def vcS14CutMargins : Fin 3 → ℚ := ![8742853/1000000000, 15983261/2000000000, 29899073/10000000000]

theorem vcS14Cut_roots_ok : vcS14CutCell.rootsOK vcS14CutRoots = true := by decide +kernel

theorem vcS14Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS14CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS14Cut_margin_le (i : Fin 3) : curvatureLoss vcS14CutCell vcS14CutCaps i ≤ vcS14CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS15CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨7/40, 3/16⟩, ⟨1/40, 1/20⟩⟩
def vcS15CutRoots : Fin 3 → RatBounds := ![⟨16632902520173/8796093022208, 576729594237999/281474976710656⟩, ⟨247380278509165/140737488355328, 268561039992637/140737488355328⟩, ⟨138808940124231/140737488355328, 79158575919311/70368744177664⟩]
def vcS15CutCaps : Fin 3 → Fin 3 → ℚ := ![![1366563937/5000000, 21712250617/100000000, 9137302099/100000000], ![7133520083/50000000, 7761473419/50000000, 4427525467/100000000], ![575189369/50000000, 1221567977/100000000, 259830681/50000000]]
def vcS15CutWeightFloor : ℚ := 52554977/50000000
def vcS15CutMargins : Fin 3 → ℚ := ![90234051/10000000000, 16453699/2000000000, 30553659/10000000000]

theorem vcS15Cut_roots_ok : vcS15CutCell.rootsOK vcS15CutRoots = true := by decide +kernel

theorem vcS15Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS15CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS15Cut_margin_le (i : Fin 3) : curvatureLoss vcS15CutCell vcS15CutCaps i ≤ vcS15CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS16CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨7/40, 3/16⟩, ⟨1/20, 3/40⟩⟩
def vcS16CutRoots : Fin 3 → RatBounds := ![⟨528283235165281/281474976710656, 572153269106637/281474976710656⟩, ⟨489646880894229/281474976710656, 132819533668759/70368744177664⟩, ⟨136320839380983/140737488355328, 310662537106411/281474976710656⟩]
def vcS16CutCaps : Fin 3 → Fin 3 → ℚ := ![![28613298847/100000000, 22785961707/100000000, 9521495009/100000000], ![7457739677/50000000, 16200181399/100000000, 4616355771/100000000], ![1042490989/100000000, 1102256597/100000000, 9362703/2000000]]
def vcS16CutWeightFloor : ℚ := 10965899/10000000
def vcS16CutMargins : Fin 3 → ℚ := ![46580803/5000000000, 84756191/10000000000, 3908787/1250000000]

theorem vcS16Cut_roots_ok : vcS16CutCell.rootsOK vcS16CutRoots = true := by decide +kernel

theorem vcS16Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS16CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS16Cut_margin_le (i : Fin 3) : curvatureLoss vcS16CutCell vcS16CutCaps i ≤ vcS16CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS17CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨7/40, 3/16⟩, ⟨3/40, 1/10⟩⟩
def vcS17CutRoots : Fin 3 → RatBounds := ![⟨524609668986651/281474976710656, 567935416391529/281474976710656⟩, ⟨242464894687529/140737488355328, 131476674153299/70368744177664⟩, ⟨268079072469301/281474976710656, 305208973385053/281474976710656⟩]
def vcS17CutCaps : Fin 3 → Fin 3 → ℚ := ![![14943205751/50000000, 23849470727/100000000, 9902739999/100000000], ![15558869103/100000000, 2109061517/12500000, 4803406337/100000000], ![118576779/12500000, 999134693/100000000, 423711947/100000000]]
def vcS17CutWeightFloor : ℚ := 114211829/100000000
def vcS17CutMargins : Fin 3 → ℚ := ![96171363/10000000000, 10917603/1250000000, 4004149/1250000000]

theorem vcS17Cut_roots_ok : vcS17CutCell.rootsOK vcS17CutRoots = true := by decide +kernel

theorem vcS17Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS17CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS17Cut_margin_le (i : Fin 3) : curvatureLoss vcS17CutCell vcS17CutCaps i ≤ vcS17CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS18CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨3/16, 1/5⟩, ⟨0, 1/40⟩⟩
def vcS18CutRoots : Fin 3 → RatBounds := ![⟨528184194337083/281474976710656, 571366434492715/281474976710656⟩, ⟨244692163781941/140737488355328, 530549157535409/281474976710656⟩, ⟨142770752108249/140737488355328, 324371004021685/281474976710656⟩]
def vcS18CutCaps : Fin 3 → Fin 3 → ℚ := ![![5698432603/25000000, 1104953421/6250000, 12322881/160000], ![11585293573/100000000, 12646620729/100000000, 3684550803/100000000], ![1246019741/100000000, 1312160759/100000000, 291140349/50000000]]
def vcS18CutWeightFloor : ℚ := 1268059/1250000
def vcS18CutMargins : Fin 3 → ℚ := ![76881061/10000000000, 34740741/5000000000, 6697009/2500000000]

theorem vcS18Cut_roots_ok : vcS18CutCell.rootsOK vcS18CutRoots = true := by decide +kernel

theorem vcS18Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS18CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS18Cut_margin_le (i : Fin 3) : curvatureLoss vcS18CutCell vcS18CutCaps i ≤ vcS18CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS19CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨3/16, 1/5⟩, ⟨1/40, 1/20⟩⟩
def vcS19CutRoots : Fin 3 → RatBounds := ![⟨523987446250967/281474976710656, 17703467105375/8796093022208⟩, ⟨30241421766007/17592186044416, 65528021918469/35184372088832⟩, ⟨280093687791171/281474976710656, 317838394732387/281474976710656⟩]
def vcS19CutCaps : Fin 3 → Fin 3 → ℚ := ![![11957342027/50000000, 9304162539/50000000, 2011893001/25000000], ![6069950619/50000000, 13224993747/100000000, 3851839301/100000000], ![1120955097/100000000, 1175690643/100000000, 521074351/100000000]]
def vcS19CutWeightFloor : ℚ := 106013981/100000000
def vcS19CutMargins : Fin 3 → ℚ := ![39588287/5000000000, 35679767/5000000000, 6827983/2500000000]

theorem vcS19Cut_roots_ok : vcS19CutCell.rootsOK vcS19CutRoots = true := by decide +kernel

theorem vcS19Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS19CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS19Cut_margin_le (i : Fin 3) : curvatureLoss vcS19CutCell vcS19CutCaps i ≤ vcS19CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS110CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨3/16, 1/5⟩, ⟨1/20, 3/40⟩⟩
def vcS110CutRoots : Fin 3 → RatBounds := ![⟨520116640518341/281474976710656, 562052664290467/281474976710656⟩, ⟨478789107438887/281474976710656, 518435246523551/281474976710656⟩, ⟨4298721831139/4398046511104, 311898248290505/281474976710656⟩]
def vcS110CutCaps : Fin 3 → Fin 3 → ℚ := ![![12513703043/50000000, 19527578283/100000000, 4195183067/50000000], ![6344897027/50000000, 13798769763/100000000, 502169929/12500000], ![1013272469/100000000, 1058893619/100000000, 468787207/100000000]]
def vcS110CutWeightFloor : ℚ := 27647043/25000000
def vcS110CutMargins : Fin 3 → ℚ := ![40791299/5000000000, 7336313/1000000000, 348703/125000000]

theorem vcS110Cut_roots_ok : vcS110CutCell.rootsOK vcS110CutRoots = true := by decide +kernel

theorem vcS110Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS110CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS110Cut_margin_le (i : Fin 3) : curvatureLoss vcS110CutCell vcS110CutCaps i ≤ vcS110CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS111CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨3/16, 1/5⟩, ⟨3/40, 1/10⟩⟩
def vcS111CutRoots : Fin 3 → RatBounds := ![⟨516534756567941/281474976710656, 557944149831935/281474976710656⟩, ⟨29631888898419/17592186044416, 513115971239953/281474976710656⟩, ⟨67639025882057/70368744177664, 4788646543569/4398046511104⟩]
def vcS111CutCaps : Fin 3 → Fin 3 → ℚ := ![![6533198897/25000000, 20438143453/100000000, 8730555243/100000000], ![264709409/2000000, 7184218061/50000000, 16333238/390625], ![460539491/50000000, 14985029/1562500, 424068299/100000000]]
def vcS111CutWeightFloor : ℚ := 57583237/50000000
def vcS111CutMargins : Fin 3 → ℚ := ![3363483/400000000, 18868529/2500000000, 28531519/10000000000]

theorem vcS111Cut_roots_ok : vcS111CutCell.rootsOK vcS111CutRoots = true := by decide +kernel

theorem vcS111Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS111CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS111Cut_margin_le (i : Fin 3) : curvatureLoss vcS111CutCell vcS111CutCaps i ≤ vcS111CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS112CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨1/5, 17/80⟩, ⟨0, 1/40⟩⟩
def vcS112CutRoots : Fin 3 → RatBounds := ![⟨520574205139577/281474976710656, 562042229514179/281474976710656⟩, ⟨479218522243577/281474976710656, 518628112892297/281474976710656⟩, ⟨287988365313799/281474976710656, 325669928962017/281474976710656⟩]
def vcS112CutCaps : Fin 3 → Fin 3 → ℚ := ![![4037910809/20000000, 15343109203/100000000, 6862232597/100000000], ![2495785397/25000000, 2181253691/20000000, 16250973/500000], ![1218574027/100000000, 633357749/50000000, 292547761/50000000]]
def vcS112CutWeightFloor : ℚ := 5115701/5000000
def vcS112CutMargins : Fin 3 → ℚ := ![17112789/2500000000, 61164531/10000000000, 12160947/5000000000]

theorem vcS112Cut_roots_ok : vcS112CutCell.rootsOK vcS112CutRoots = true := by decide +kernel

theorem vcS112Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS112CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS112Cut_margin_le (i : Fin 3) : curvatureLoss vcS112CutCell vcS112CutCaps i ≤ vcS112CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS113CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨1/5, 17/80⟩, ⟨1/40, 1/20⟩⟩
def vcS113CutRoots : Fin 3 → RatBounds := ![⟨516475423353037/281474976710656, 557302939404623/281474976710656⟩, ⟨473733530701647/281474976710656, 256176620281227/140737488355328⟩, ⟨282542779103965/281474976710656, 319170052586501/281474976710656⟩]
def vcS113CutCaps : Fin 3 → Fin 3 → ℚ := ![![21175037603/100000000, 8075313367/50000000, 7174651447/100000000], ![522986009/5000000, 5701273081/50000000, 3398828579/100000000], ![1095675039/100000000, 567201939/50000000, 130858657/25000000]]
def vcS113CutWeightFloor : ℚ := 53453181/50000000
def vcS113CutMargins : Fin 3 → ℚ := ![35173299/5000000000, 31338661/5000000000, 12370331/5000000000]

theorem vcS113Cut_roots_ok : vcS113CutCell.rootsOK vcS113CutRoots = true := by decide +kernel

theorem vcS113Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS113CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS113Cut_margin_le (i : Fin 3) : curvatureLoss vcS113CutCell vcS113CutCaps i ≤ vcS113CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS114CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨1/5, 17/80⟩, ⟨1/20, 3/40⟩⟩
def vcS114CutRoots : Fin 3 → RatBounds := ![⟨128173798763409/70368744177664, 276475967555917/140737488355328⟩, ⟨29293433111731/17592186044416, 15831623661903/8796093022208⟩, ⟨34696144430573/35184372088832, 313259447863345/281474976710656⟩]
def vcS114CutCaps : Fin 3 → Fin 3 → ℚ := ![![5538425107/25000000, 16949639907/100000000, 467773333/6250000], ![5466148761/50000000, 1189493139/10000000, 354588513/10000000], ![494962319/50000000, 255307849/25000000, 7355869/1562500]]
def vcS114CutWeightFloor : ℚ := 111504047/100000000
def vcS114CutMargins : Fin 3 → ℚ := ![18088719/2500000000, 2009857/312500000, 25221409/10000000000]

theorem vcS114Cut_roots_ok : vcS114CutCell.rootsOK vcS114CutRoots = true := by decide +kernel

theorem vcS114Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS114CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS114Cut_margin_le (i : Fin 3) : curvatureLoss vcS114CutCell vcS114CutCaps i ≤ vcS114CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS115CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨1/5, 17/80⟩, ⟨3/40, 1/10⟩⟩
def vcS115CutRoots : Fin 3 → RatBounds := ![⟨509197325306995/281474976710656, 274471396140039/140737488355328⟩, ⟨116012394676557/70368744177664, 125334495629485/70368744177664⟩, ⟨273008623557925/281474976710656, 153930680935537/140737488355328⟩]
def vcS115CutCaps : Fin 3 → Fin 3 → ℚ := ![![2890781473/12500000, 1774111913/10000000, 7791716423/100000000], ![5700645007/50000000, 619191569/5000000, 1845769219/50000000], ![898341133/100000000, 923742369/100000000, 212738841/50000000]]
def vcS115CutWeightFloor : ℚ := 5805309/5000000
def vcS115CutMargins : Fin 3 → ℚ := ![4653431/625000000, 16513633/2500000000, 25752277/10000000000]

theorem vcS115Cut_roots_ok : vcS115CutCell.rootsOK vcS115CutRoots = true := by decide +kernel

theorem vcS115Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS115CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS115Cut_margin_le (i : Fin 3) : curvatureLoss vcS115CutCell vcS115CutCaps i ≤ vcS115CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS116CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨17/80, 9/40⟩, ⟨0, 1/40⟩⟩
def vcS116CutRoots : Fin 3 → RatBounds := ![⟨64205265812145/35184372088832, 138403516162419/70368744177664⟩, ⟨117434064450991/70368744177664, 507609018076731/281474976710656⟩, ⟨145209280831801/140737488355328, 81771810964023/70368744177664⟩]
def vcS116CutCaps : Fin 3 → Fin 3 → ℚ := ![![9034232467/50000000, 3368193397/25000000, 6197258049/100000000], ![8695982749/100000000, 1187774297/12500000, 1451208393/50000000], ![18667103/1562500, 612675899/50000000, 117754131/20000000]]
def vcS116CutWeightFloor : ℚ := 103177399/100000000
def vcS116CutMargins : Fin 3 → ℚ := ![7700983/1250000000, 27223023/5000000000, 11186287/5000000000]

theorem vcS116Cut_roots_ok : vcS116CutCell.rootsOK vcS116CutRoots = true := by decide +kernel

theorem vcS116Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS116CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS116Cut_margin_le (i : Fin 3) : curvatureLoss vcS116CutCell vcS116CutCaps i ≤ vcS116CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS117CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨17/80, 9/40⟩, ⟨1/40, 1/20⟩⟩
def vcS117CutRoots : Fin 3 → RatBounds := ![⟨254816638811009/140737488355328, 548980650372941/281474976710656⟩, ⟨232141588014829/140737488355328, 250688699655835/140737488355328⟩, ⟨71244066302401/70368744177664, 320618139842775/281474976710656⟩]
def vcS117CutCaps : Fin 3 → Fin 3 → ℚ := ![![3788884969/20000000, 7091048737/50000000, 405117541/6250000], ![18220547/200000, 9932745731/100000000, 75900451/2500000], ![536834137/50000000, 137106937/12500000, 263286647/50000000]]
def vcS117CutWeightFloor : ℚ := 10779153/10000000
def vcS117CutMargins : Fin 3 → ℚ := ![63182367/10000000000, 55668487/10000000000, 45407/20000000]

theorem vcS117Cut_roots_ok : vcS117CutCell.rootsOK vcS117CutRoots = true := by decide +kernel

theorem vcS117Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS117CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS117Cut_margin_le (i : Fin 3) : curvatureLoss vcS117CutCell vcS117CutCaps i ≤ vcS117CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS118CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨17/80, 9/40⟩, ⟨1/20, 3/40⟩⟩
def vcS118CutRoots : Fin 3 → RatBounds := ![⟨63242024366855/35184372088832, 272363699395517/140737488355328⟩, ⟨459275246611201/281474976710656, 123919347978463/70368744177664⟩, ⟨280005463594733/281474976710656, 314735279278865/281474976710656⟩]
def vcS118CutCaps : Fin 3 → Fin 3 → ℚ := ![![19814657067/100000000, 14884113489/100000000, 6764290081/100000000], ![1904223077/20000000, 10359956643/100000000, 3168197359/100000000], ![484795461/50000000, 246751209/25000000, 94694337/20000000]]
def vcS118CutWeightFloor : ℚ := 22482289/20000000
def vcS118CutMargins : Fin 3 → ℚ := ![202723/31250000, 285079/50000000, 5774597/2500000000]

theorem vcS118Cut_roots_ok : vcS118CutCell.rootsOK vcS118CutRoots = true := by decide +kernel

theorem vcS118Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS118CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS118Cut_margin_le (i : Fin 3) : curvatureLoss vcS118CutCell vcS118CutCaps i ≤ vcS118CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS119CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨17/80, 9/40⟩, ⟨3/40, 1/10⟩⟩
def vcS119CutRoots : Fin 3 → RatBounds := ![⟨502515442257363/281474976710656, 540808805910457/281474976710656⟩, ⟨454659341391167/281474976710656, 490442785396223/281474976710656⟩, ⟨275447358203727/281474976710656, 154681161141039/140737488355328⟩]
def vcS119CutCaps : Fin 3 → Fin 3 → ℚ := ![![20679747811/100000000, 1947457053/12500000, 3522377161/50000000], ![2482215471/25000000, 1348021491/12500000, 3299109739/100000000], ![175901227/20000000, 446212191/50000000, 106951451/25000000]]
def vcS119CutWeightFloor : ℚ := 7314761/6250000
def vcS119CutMargins : Fin 3 → ℚ := ![66653583/10000000000, 29231959/5000000000, 23545093/10000000000]

theorem vcS119Cut_roots_ok : vcS119CutCell.rootsOK vcS119CutRoots = true := by decide +kernel

theorem vcS119Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS119CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS119Cut_margin_le (i : Fin 3) : curvatureLoss vcS119CutCell vcS119CutCaps i ≤ vcS119CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS120CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨9/40, 19/80⟩, ⟨0, 1/40⟩⟩
def vcS120CutRoots : Fin 3 → RatBounds := ![⟨126829293768289/70368744177664, 545978018177655/281474976710656⟩, ⟨230430676259047/140737488355328, 497381957913367/281474976710656⟩, ⟨146420820838215/140737488355328, 328614172644081/281474976710656⟩]
def vcS120CutCaps : Fin 3 → Fin 3 → ℚ := ![![2039804049/12500000, 11949510457/100000000, 706775247/12500000], ![3824011351/50000000, 4176545379/50000000, 2621240973/100000000], ![1173789111/100000000, 593720401/50000000, 593193237/100000000]]
def vcS120CutWeightFloor : ℚ := 416153/400000
def vcS120CutMargins : Fin 3 → ℚ := ![55979711/10000000000, 61163/12500000, 20797297/10000000000]

theorem vcS120Cut_roots_ok : vcS120CutCell.rootsOK vcS120CutRoots = true := by decide +kernel

theorem vcS120Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS120CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS120Cut_margin_le (i : Fin 3) : curvatureLoss vcS120CutCell vcS120CutCaps i ≤ vcS120CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS121CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨9/40, 19/80⟩, ⟨1/40, 1/20⟩⟩
def vcS121CutRoots : Fin 3 → RatBounds := ![⟨503390980741259/281474976710656, 135360316525847/70368744177664⟩, ⟨227718034047953/140737488355328, 122796906481639/70368744177664⟩, ⟨287403514027309/281474976710656, 161087063308565/140737488355328⟩]
def vcS121CutCaps : Fin 3 → Fin 3 → ℚ := ![![17104661333/100000000, 12579171159/100000000, 2958358463/50000000], ![2003188791/25000000, 8730215471/100000000, 548823719/20000000], ![1054392179/100000000, 132808593/12500000, 265194063/50000000]]
def vcS121CutWeightFloor : ℚ := 21734639/20000000
def vcS121CutMargins : Fin 3 → ℚ := ![57294893/10000000000, 49920433/10000000000, 2632419/1250000000]

theorem vcS121Cut_roots_ok : vcS121CutCell.rootsOK vcS121CutRoots = true := by decide +kernel

theorem vcS121Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS121CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS121Cut_margin_le (i : Fin 3) : curvatureLoss vcS121CutCell vcS121CutCaps i ≤ vcS121CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS122CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨9/40, 19/80⟩, ⟨1/20, 3/40⟩⟩
def vcS122CutRoots : Fin 3 → RatBounds := ![⟨499770310533803/281474976710656, 33579828921869/17592186044416⟩, ⟨3519179434393/2199023255552, 485523348435871/281474976710656⟩, ⟨282436324484845/281474976710656, 158158718073213/140737488355328⟩]
def vcS122CutCaps : Fin 3 → Fin 3 → ℚ := ![![4471508313/25000000, 6601188107/50000000, 3088609179/50000000], ![8374432561/100000000, 182088811/2000000, 1432815549/50000000], ![951772469/100000000, 955683211/100000000, 476782389/100000000]]
def vcS122CutWeightFloor : ℚ := 113314393/100000000
def vcS122CutMargins : Fin 3 → ℚ := ![11745139/2000000000, 51034277/10000000000, 10693339/5000000000]

theorem vcS122Cut_roots_ok : vcS122CutCell.rootsOK vcS122CutRoots = true := by decide +kernel

theorem vcS122Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS122CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS122Cut_margin_le (i : Fin 3) : curvatureLoss vcS122CutCell vcS122CutCaps i ≤ vcS122CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS123CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨9/40, 19/80⟩, ⟨3/40, 1/10⟩⟩
def vcS123CutRoots : Fin 3 → RatBounds := ![⟨31026276649795/17592186044416, 533441343675615/281474976710656⟩, ⟨222932455140801/140737488355328, 480322942016731/281474976710656⟩, ⟨138940679375357/140737488355328, 310968157437633/281474976710656⟩]
def vcS123CutCaps : Fin 3 → Fin 3 → ℚ := ![![4665758519/25000000, 6909930681/50000000, 1287189891/20000000], ![4366682389/50000000, 9476061229/100000000, 2985927183/100000000], ![431497449/50000000, 863783939/100000000, 215347539/50000000]]
def vcS123CutWeightFloor : ℚ := 58980397/50000000
def vcS123CutMargins : Fin 3 → ℚ := ![3012537/500000000, 52248161/10000000000, 21766909/10000000000]

theorem vcS123Cut_roots_ok : vcS123CutCell.rootsOK vcS123CutRoots = true := by decide +kernel

theorem vcS123Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS123CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS123Cut_margin_le (i : Fin 3) : curvatureLoss vcS123CutCell vcS123CutCaps i ≤ vcS123CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS124CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨19/80, 1/4⟩, ⟨0, 1/40⟩⟩
def vcS124CutRoots : Fin 3 → RatBounds := ![⟨250769783968385/140737488355328, 539047757242551/281474976710656⟩, ⟨226264536999503/140737488355328, 243927574274811/140737488355328⟩, ⟨295265795016077/281474976710656, 330244018127845/281474976710656⟩]
def vcS124CutCaps : Fin 3 → Fin 3 → ℚ := ![![2971668173/20000000, 10692777761/100000000, 5203171129/100000000], ![6797922987/100000000, 1850221123/25000000, 603561733/25000000], ![288848451/25000000, 576239969/50000000, 299136979/50000000]]
def vcS124CutWeightFloor : ℚ := 52449741/50000000
def vcS124CutMargins : Fin 3 → ℚ := ![10264781/2000000000, 22171467/5000000000, 3910357/2000000000]

theorem vcS124Cut_roots_ok : vcS124CutCell.rootsOK vcS124CutRoots = true := by decide +kernel

theorem vcS124Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS124CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS124Cut_margin_le (i : Fin 3) : curvatureLoss vcS124CutCell vcS124CutCaps i ≤ vcS124CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS125CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨19/80, 1/4⟩, ⟨1/40, 1/20⟩⟩
def vcS125CutRoots : Fin 3 → RatBounds := ![⟨497689389583731/281474976710656, 534599376689035/281474976710656⟩, ⟨447127952731221/281474976710656, 120423218732645/70368744177664⟩, ⟨289832565045045/281474976710656, 20239469579473/17592186044416⟩]
def vcS125CutCaps : Fin 3 → Fin 3 → ℚ := ![![15570206073/100000000, 5628341853/50000000, 5447363507/100000000], ![3560838997/50000000, 7734003751/100000000, 1263868129/50000000], ![1037421877/100000000, 1030782911/100000000, 534798279/100000000]]
def vcS125CutWeightFloor : ℚ := 109554521/100000000
def vcS125CutMargins : Fin 3 → ℚ := ![10484989/2000000000, 22572089/5000000000, 19754479/10000000000]

theorem vcS125Cut_roots_ok : vcS125CutCell.rootsOK vcS125CutRoots = true := by decide +kernel

theorem vcS125Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS125CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS125Cut_margin_le (i : Fin 3) : curvatureLoss vcS125CutCell vcS125CutCaps i ≤ vcS125CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS126CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨19/80, 1/4⟩, ⟨1/20, 3/40⟩⟩
def vcS126CutRoots : Fin 3 → RatBounds := ![⟨494138990851429/281474976710656, 265258484245829/140737488355328⟩, ⟨442170283291975/281474976710656, 238029732458761/140737488355328⟩, ⟨284869640199145/281474976710656, 79499899525985/70368744177664⟩]
def vcS126CutCaps : Fin 3 → Fin 3 → ℚ := ![![16277914513/100000000, 5907415897/50000000, 2844853857/50000000], ![3721366399/50000000, 8064581141/100000000, 2639977443/100000000], ![936078669/100000000, 926842747/100000000, 480634199/100000000]]
def vcS126CutWeightFloor : ℚ := 57108151/50000000
def vcS126CutMargins : Fin 3 → ℚ := ![6705313/1250000000, 23033969/5000000000, 312873/156250000]

theorem vcS126Cut_roots_ok : vcS126CutCell.rootsOK vcS126CutRoots = true := by decide +kernel

theorem vcS126Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS126CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS126Cut_margin_le (i : Fin 3) : curvatureLoss vcS126CutCell vcS126CutCaps i ≤ vcS126CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS127CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨19/80, 1/4⟩, ⟨3/40, 1/10⟩⟩
def vcS127CutRoots : Fin 3 → RatBounds := ![⟨490854276461713/281474976710656, 526756635173319/281474976710656⟩, ⟨218801445254511/140737488355328, 470888725380767/281474976710656⟩, ⟨70079600272437/70368744177664, 312672710391713/281474976710656⟩]
def vcS127CutCaps : Fin 3 → Fin 3 → ℚ := ![![2122734019/12500000, 6183938469/50000000, 5930426501/100000000], ![1552271467/20000000, 8392871857/100000000, 2751104453/100000000], ![424223569/50000000, 837430019/100000000, 217039171/50000000]]
def vcS127CutWeightFloor : ℚ := 118883693/100000000
def vcS127CutMargins : Fin 3 → ℚ := ![27477557/5000000000, 1177269/250000000, 20347353/10000000000]

theorem vcS127Cut_roots_ok : vcS127CutCell.rootsOK vcS127CutRoots = true := by decide +kernel

theorem vcS127Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS127CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS127Cut_margin_le (i : Fin 3) : curvatureLoss vcS127CutCell vcS127CutCaps i ≤ vcS127CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS128CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨1/4, 21/80⟩, ⟨0, 1/40⟩⟩
def vcS128CutRoots : Fin 3 → RatBounds := ![⟨496258483713529/281474976710656, 532750977554347/281474976710656⟩, ⟨444684002019383/281474976710656, 478951251743459/281474976710656⟩, ⟨297698168727841/281474976710656, 165985865448527/140737488355328⟩]
def vcS128CutCaps : Fin 3 → Fin 3 → ℚ := ![![6814151323/50000000, 4822631841/50000000, 7539131/156250], ![6091254331/100000000, 6603243557/100000000, 561339763/25000000], ![1139140553/100000000, 280015621/25000000, 301970807/50000000]]
def vcS128CutWeightFloor : ℚ := 21152727/20000000
def vcS128CutMargins : Fin 3 → ℚ := ![5926787/1250000000, 20242927/5000000000, 741107/400000000]

theorem vcS128Cut_roots_ok : vcS128CutCell.rootsOK vcS128CutRoots = true := by decide +kernel

theorem vcS128Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS128CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS128Cut_margin_le (i : Fin 3) : curvatureLoss vcS128CutCell vcS128CutCaps i ≤ vcS128CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS129CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨1/4, 21/80⟩, ⟨1/40, 1/20⟩⟩
def vcS129CutRoots : Fin 3 → RatBounds := ![⟨61559778553405/35184372088832, 66047931646703/35184372088832⟩, ⟨439303817150355/281474976710656, 472816426471911/281474976710656⟩, ⟨292270438778369/281474976710656, 325585409917891/281474976710656⟩]
def vcS129CutCaps : Fin 3 → Fin 3 → ℚ := ![![2855584327/20000000, 5077159481/50000000, 5053937437/100000000], ![1276212843/20000000, 43123121/625000, 587778793/25000000], ![25560503/2500000, 1001425291/100000000, 539739349/100000000]]
def vcS129CutWeightFloor : ℚ := 110438253/100000000
def vcS129CutMargins : Fin 3 → ℚ := ![48337239/10000000000, 8226453/2000000000, 4669927/2500000000]

theorem vcS129Cut_roots_ok : vcS129CutCell.rootsOK vcS129CutRoots = true := by decide +kernel

theorem vcS129Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS129CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS129Cut_margin_le (i : Fin 3) : curvatureLoss vcS129CutCell vcS129CutCaps i ≤ vcS129CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS130CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨1/4, 21/80⟩, ⟨1/20, 3/40⟩⟩
def vcS130CutRoots : Fin 3 → RatBounds := ![⟨244496232604233/140737488355328, 262187851185561/140737488355328⟩, ⟨434366559855253/281474976710656, 233604797100047/140737488355328⟩, ⟨287312315431737/281474976710656, 39972127492189/35184372088832⟩]
def vcS130CutCaps : Fin 3 → Fin 3 → ℚ := ![![14924353899/100000000, 2664646293/25000000, 5281475993/100000000], ![6668462817/100000000, 1798476937/25000000, 1227861227/50000000], ![922199463/100000000, 900140751/100000000, 19398743/4000000]]
def vcS130CutWeightFloor : ℚ := 115120123/100000000
def vcS130CutMargins : Fin 3 → ℚ := ![24689077/5000000000, 83801/20000000, 18900533/10000000000]

theorem vcS130Cut_roots_ok : vcS130CutCell.rootsOK vcS130CutRoots = true := by decide +kernel

theorem vcS130Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS130CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS130Cut_margin_le (i : Fin 3) : curvatureLoss vcS130CutCell vcS130CutCaps i ≤ vcS130CutMargins i := by
  fin_cases i <;> decide +kernel

def vcS131CutCell : ParameterCell := ⟨⟨1/40, 3/80⟩, ⟨1/4, 21/80⟩, ⟨3/40, 1/10⟩⟩
def vcS131CutRoots : Fin 3 → RatBounds := ![⟨485767690702815/281474976710656, 520684528940243/281474976710656⟩, ⟨429819001620943/281474976710656, 231032260121627/140737488355328⟩, ⟨141382641749327/140737488355328, 314471367735341/281474976710656⟩]
def vcS131CutCaps : Fin 3 → Fin 3 → ℚ := ![![7783900749/50000000, 5579254197/50000000, 220308519/4000000], ![86921097/1250000, 233940347/3125000, 639825571/25000000], ![835576867/100000000, 162609303/20000000, 54737769/12500000]]
def vcS131CutWeightFloor : ℚ := 119808023/100000000
def vcS131CutMargins : Fin 3 → ℚ := ![12628807/2500000000, 1069179/250000000, 19177/10000000]

theorem vcS131Cut_roots_ok : vcS131CutCell.rootsOK vcS131CutRoots = true := by decide +kernel

theorem vcS131Cut_caps_nonneg (k i : Fin 3) : 0 ≤ vcS131CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcS131Cut_margin_le (i : Fin 3) : curvatureLoss vcS131CutCell vcS131CutCaps i ≤ vcS131CutMargins i := by
  fin_cases i <;> decide +kernel


end HlawkaSchatten.BelowExponent.Vertex
