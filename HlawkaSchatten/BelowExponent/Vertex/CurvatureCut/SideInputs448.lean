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

def scE142CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨3/10, 5/16⟩, ⟨3/20, 13/80⟩⟩
def scE142CutRoots : Fin 3 → RatBounds := ![⟨118052922608363/70368744177664, 125646343314575/70368744177664⟩, ⟨198934539030903/140737488355328, 424676841958343/281474976710656⟩, ⟨281838666429479/281474976710656, 308854071806071/281474976710656⟩]
def scE142CutCaps : Fin 3 → Fin 3 → ℚ := ![![1658918861/12500000, 9058587383/100000000, 29067331/625000], ![5505993687/100000000, 113186603/2000000, 2128869253/100000000], ![236289353/50000000, 427773617/100000000, 265997553/100000000]]
def scE142CutWeightFloor : ℚ := 3464223/2500000
def scE142CutMargins : Fin 3 → ℚ := ![37597507/10000000000, 29581429/10000000000, 1720127/1250000000]

theorem scE142Cut_roots_ok : scE142CutCell.rootsOK scE142CutRoots = true := by decide +kernel

theorem scE142Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE142CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE142Cut_margin_le (i : Fin 3) : curvatureLoss scE142CutCell scE142CutCaps i ≤ scE142CutMargins i := by
  fin_cases i <;> decide +kernel

def scE143CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨3/10, 5/16⟩, ⟨13/80, 1/6⟩⟩
def scE143CutRoots : Fin 3 → RatBounds := ![⟨118002636601591/70368744177664, 250533527164925/140737488355328⟩, ⟨397274655110987/281474976710656, 422722749075663/281474976710656⟩, ⟨281247798902411/281474976710656, 153443232178585/140737488355328⟩]
def scE143CutCaps : Fin 3 → Fin 3 → ℚ := ![![13143915557/100000000, 2243315321/25000000, 2277833703/50000000], ![2731820361/50000000, 697409881/12500000, 1029152907/50000000], ![360545327/100000000, 326187311/100000000, 207090653/100000000]]
def scE143CutWeightFloor : ℚ := 141588847/100000000
def scE143CutMargins : Fin 3 → ℚ := ![36421127/10000000000, 14246859/5000000000, 6481429/5000000000]

theorem scE143Cut_roots_ok : scE143CutCell.rootsOK scE143CutRoots = true := by decide +kernel

theorem scE143Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE143CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE143Cut_margin_le (i : Fin 3) : curvatureLoss scE143CutCell scE143CutCaps i ≤ scE143CutMargins i := by
  fin_cases i <;> decide +kernel

def scE144CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨5/16, 13/40⟩, ⟨1/8, 11/80⟩⟩
def scE144CutRoots : Fin 3 → RatBounds := ![⟨471304829365477/281474976710656, 501288719001037/281474976710656⟩, ⟨395414374823115/281474976710656, 52734097428631/35184372088832⟩, ⟨288195037577813/281474976710656, 157616598983217/140737488355328⟩]
def scE144CutCaps : Fin 3 → Fin 3 → ℚ := ![![12023826841/100000000, 808133767/10000000, 4278750179/100000000], ![4899755317/100000000, 199676053/4000000, 992603463/50000000], ![20333751/4000000, 113355139/25000000, 58479979/20000000]]
def scE144CutWeightFloor : ℚ := 134821031/100000000
def scE144CutMargins : Fin 3 → ℚ := ![34046731/10000000000, 26419257/10000000000, 2561077/2000000000]

theorem scE144Cut_roots_ok : scE144CutCell.rootsOK scE144CutRoots = true := by decide +kernel

theorem scE144Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE144CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE144Cut_margin_le (i : Fin 3) : curvatureLoss scE144CutCell scE144CutCaps i ≤ scE144CutMargins i := by
  fin_cases i <;> decide +kernel

def scE145CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨5/16, 13/40⟩, ⟨11/80, 3/20⟩⟩
def scE145CutRoots : Fin 3 → RatBounds := ![⟨470029302043907/281474976710656, 499918062309981/281474976710656⟩, ⟨393491686485343/281474976710656, 419798898466609/281474976710656⟩, ⟨286284435815507/281474976710656, 78282556321251/70368744177664⟩]
def scE145CutCaps : Fin 3 → Fin 3 → ℚ := ![![6126304343/50000000, 8245198901/100000000, 545432731/12500000], ![623954229/12500000, 635127703/12500000, 101113193/5000000], ![60910737/12500000, 217131723/50000000, 28007071/10000000]]
def scE145CutWeightFloor : ℚ := 137215709/100000000
def scE145CutMargins : Fin 3 → ℚ := ![8657973/2500000000, 13437973/5000000000, 6509567/5000000000]

theorem scE145Cut_roots_ok : scE145CutCell.rootsOK scE145CutRoots = true := by decide +kernel

theorem scE145Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE145CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE145Cut_margin_le (i : Fin 3) : curvatureLoss scE145CutCell scE145CutCaps i ≤ scE145CutMargins i := by
  fin_cases i <;> decide +kernel

def scE146CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨5/16, 13/40⟩, ⟨3/20, 13/80⟩⟩
def scE146CutRoots : Fin 3 → RatBounds := ![⟨468797402941899/281474976710656, 249297713990873/140737488355328⟩, ⟨391638479455315/281474976710656, 417801364645909/281474976710656⟩, ⟨284445383278181/281474976710656, 38888434850405/35184372088832⟩]
def scE146CutCaps : Fin 3 → Fin 3 → ℚ := ![![2496270277/20000000, 8408591769/100000000, 4448055107/100000000], ![5083281863/100000000, 2584989659/50000000, 411847621/20000000], ![1869983/400000, 1626101/390625, 268495949/100000000]]
def scE146CutWeightFloor : ℚ := 34902951/25000000
def scE146CutMargins : Fin 3 → ℚ := ![17609501/5000000000, 13666849/5000000000, 3308491/2500000000]

theorem scE146Cut_roots_ok : scE146CutCell.rootsOK scE146CutRoots = true := by decide +kernel

theorem scE146Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE146CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE146Cut_margin_le (i : Fin 3) : curvatureLoss scE146CutCell scE146CutCaps i ≤ scE146CutMargins i := by
  fin_cases i <;> decide +kernel

def scE147CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨5/16, 13/40⟩, ⟨13/80, 1/6⟩⟩
def scE147CutRoots : Fin 3 → RatBounds := ![⟨468604596224935/281474976710656, 15534139219069/8796093022208⟩, ⟨195522928245211/140737488355328, 207927262081173/140737488355328⟩, ⟨283855058347623/281474976710656, 309145343763219/281474976710656⟩]
def scE147CutCaps : Fin 3 → Fin 3 → ℚ := ![![247149313/2000000, 4163799321/50000000, 2177497289/50000000], ![5042021823/100000000, 2546069209/50000000, 1990047701/100000000], ![178129071/50000000, 316812247/100000000, 104248123/50000000]]
def scE147CutWeightFloor : ℚ := 35661249/25000000
def scE147CutMargins : Fin 3 → ℚ := ![34060687/10000000000, 26279177/10000000000, 3109477/2500000000]

theorem scE147Cut_roots_ok : scE147CutCell.rootsOK scE147CutRoots = true := by decide +kernel

theorem scE147Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE147CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE147Cut_margin_le (i : Fin 3) : curvatureLoss scE147CutCell scE147CutCaps i ≤ scE147CutMargins i := by
  fin_cases i <;> decide +kernel

def scE148CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨13/40, 27/80⟩, ⟨1/8, 11/80⟩⟩
def scE148CutRoots : Fin 3 → RatBounds := ![⟨468174526644067/281474976710656, 497651182220213/281474976710656⟩, ⟨48683017304191/35184372088832, 207671942217199/140737488355328⟩, ⟨145418015405053/140737488355328, 158780752770335/140737488355328⟩]
def scE148CutCaps : Fin 3 → Fin 3 → ℚ := ![![11359608393/100000000, 7538754971/100000000, 2054520079/50000000], ![4549027551/100000000, 2289732987/50000000, 1931384109/100000000], ![503528631/100000000, 44173663/10000000, 295380893/100000000]]
def scE148CutWeightFloor : ℚ := 2717129/2000000
def scE148CutMargins : Fin 3 → ℚ := ![32055009/10000000000, 766599/312500000, 618731/500000000]

theorem scE148Cut_roots_ok : scE148CutCell.rootsOK scE148CutRoots = true := by decide +kernel

theorem scE148Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE148CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE148Cut_margin_le (i : Fin 3) : curvatureLoss scE148CutCell scE148CutCaps i ≤ scE148CutMargins i := by
  fin_cases i <;> decide +kernel

def scE149CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨13/40, 27/80⟩, ⟨11/80, 3/20⟩⟩
def scE149CutRoots : Fin 3 → RatBounds := ![⟨466914751349673/281474976710656, 124074525405283/70368744177664⟩, ⟨387546733411521/281474976710656, 413276080161289/281474976710656⟩, ⟨9028969527413/8796093022208, 315464386216521/281474976710656⟩]
def scE149CutCaps : Fin 3 → Fin 3 → ℚ := ![![11575700379/100000000, 1922911453/25000000, 261949163/6250000], ![579290767/12500000, 582647203/12500000, 1967373653/100000000], ![482620019/100000000, 423040011/100000000, 282910649/100000000]]
def scE149CutWeightFloor : ℚ := 6913107/5000000
def scE149CutMargins : Fin 3 → ℚ := ![16301413/5000000000, 24952859/10000000000, 6290499/5000000000]

theorem scE149Cut_roots_ok : scE149CutCell.rootsOK scE149CutRoots = true := by decide +kernel

theorem scE149Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE149CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE149Cut_margin_le (i : Fin 3) : curvatureLoss scE149CutCell scE149CutCaps i ≤ scE149CutMargins i := by
  fin_cases i <;> decide +kernel

def scE150CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨13/40, 27/80⟩, ⟨3/20, 13/80⟩⟩
def scE150CutRoots : Fin 3 → RatBounds := ![⟨232849043631047/140737488355328, 247496231845335/140737488355328⟩, ⟨385698760624393/281474976710656, 6426321244933/4398046511104⟩, ⟨4485772817479/4398046511104, 313447212569679/281474976710656⟩]
def scE150CutCaps : Fin 3 → Fin 3 → ℚ := ![![11791576299/100000000, 7844081033/100000000, 4273176051/100000000], ![1179852423/25000000, 4742742833/100000000, 400657183/20000000], ![231486433/50000000, 50686553/12500000, 135602169/50000000]]
def scE150CutWeightFloor : ℚ := 70334651/50000000
def scE150CutMargins : Fin 3 → ℚ := ![4144033/1250000000, 12687809/5000000000, 12788411/10000000000]

theorem scE150Cut_roots_ok : scE150CutCell.rootsOK scE150CutRoots = true := by decide +kernel

theorem scE150Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE150CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE150Cut_margin_le (i : Fin 3) : curvatureLoss scE150CutCell scE150CutCaps i ≤ scE150CutMargins i := by
  fin_cases i <;> decide +kernel

def scE151CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨13/40, 27/80⟩, ⟨13/80, 1/6⟩⟩
def scE151CutRoots : Fin 3 → RatBounds := ![⟨465512897126741/281474976710656, 493503390953041/281474976710656⟩, ⟨192553853345503/140737488355328, 204672004418679/140737488355328⟩, ⟨286499689684009/281474976710656, 311490233106657/281474976710656⟩]
def scE151CutCaps : Fin 3 → Fin 3 → ℚ := ![![11670895131/100000000, 3883502231/50000000, 2090974407/50000000], ![2339589979/50000000, 4667010803/100000000, 967614981/50000000], ![70491293/20000000, 154031631/50000000, 42019071/20000000]]
def scE151CutWeightFloor : ℚ := 143715891/100000000
def scE151CutMargins : Fin 3 → ℚ := ![32010229/10000000000, 24352041/10000000000, 11993209/10000000000]

theorem scE151Cut_roots_ok : scE151CutCell.rootsOK scE151CutRoots = true := by decide +kernel

theorem scE151Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE151CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE151Cut_margin_le (i : Fin 3) : curvatureLoss scE151CutCell scE151CutCaps i ≤ scE151CutMargins i := by
  fin_cases i <;> decide +kernel

def scE152CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨27/80, 7/20⟩, ⟨1/8, 11/80⟩⟩
def scE152CutRoots : Fin 3 → RatBounds := ![⟨465342204211999/281474976710656, 494377465805037/281474976710656⟩, ⟨383782374897893/281474976710656, 6392888178077/4398046511104⟩, ⟨146759354180813/140737488355328, 79994384876103/70368744177664⟩]
def scE152CutCaps : Fin 3 → Fin 3 → ℚ := ![![10781328967/100000000, 1766437629/25000000, 1984223281/50000000], ![1061618477/25000000, 1054423121/25000000, 1889223669/100000000], ![249626297/50000000, 430729301/100000000, 149289129/50000000]]
def scE152CutWeightFloor : ℚ := 68454109/50000000
def scE152CutMargins : Fin 3 → ℚ := ![30326281/10000000000, 22879243/10000000000, 12023923/10000000000]

theorem scE152Cut_roots_ok : scE152CutCell.rootsOK scE152CutRoots = true := by decide +kernel

theorem scE152Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE152CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE152Cut_margin_le (i : Fin 3) : curvatureLoss scE152CutCell scE152CutCaps i ≤ scE152CutMargins i := by
  fin_cases i <;> decide +kernel

def scE153CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨27/80, 7/20⟩, ⟨11/80, 3/20⟩⟩
def scE153CutRoots : Fin 3 → RatBounds := ![⟨29006045235793/17592186044416, 493040297765821/281474976710656⟩, ⟨381869571070569/281474976710656, 203541101550691/140737488355328⟩, ⟨145805658106303/140737488355328, 317885950557917/281474976710656⟩]
def scE153CutCaps : Fin 3 → Fin 3 → ℚ := ![![2197394201/20000000, 7209034873/100000000, 1012441769/25000000], ![2163044851/50000000, 2146425021/50000000, 384864203/20000000], ![47847591/10000000, 41246877/10000000, 285958611/100000000]]
def scE153CutWeightFloor : ℚ := 13932509/10000000
def scE153CutMargins : Fin 3 → ℚ := ![6168569/2000000000, 23270223/10000000000, 6113327/5000000000]

theorem scE153Cut_roots_ok : scE153CutCell.rootsOK scE153CutRoots = true := by decide +kernel

theorem scE153Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE153CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE153Cut_margin_le (i : Fin 3) : curvatureLoss scE153CutCell scE153CutCaps i ≤ scE153CutMargins i := by
  fin_cases i <;> decide +kernel

def scE154CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨27/80, 7/20⟩, ⟨3/20, 13/80⟩⟩
def scE154CutRoots : Fin 3 → RatBounds := ![⟨462893885135107/281474976710656, 491750047521513/281474976710656⟩, ⟨380026169513873/281474976710656, 405095810428027/281474976710656⟩, ⟨144887627281277/140737488355328, 78968509134777/70368744177664⟩]
def scE154CutCaps : Fin 3 → Fin 3 → ℚ := ![![1119240497/10000000, 1837972609/25000000, 2065454617/50000000], ![13767199/312500, 1091968913/25000000, 1959346007/100000000], ![229477597/50000000, 79066411/20000000, 137056439/50000000]]
def scE154CutWeightFloor : ℚ := 14174349/10000000
def scE154CutMargins : Fin 3 → ℚ := ![31361063/10000000000, 11831151/5000000000, 12430407/10000000000]

theorem scE154Cut_roots_ok : scE154CutCell.rootsOK scE154CutRoots = true := by decide +kernel

theorem scE154Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE154CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE154Cut_margin_le (i : Fin 3) : curvatureLoss scE154CutCell scE154CutCaps i ≤ scE154CutMargins i := by
  fin_cases i <;> decide +kernel

def scE155CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨27/80, 7/20⟩, ⟨13/80, 1/6⟩⟩
def scE155CutRoots : Fin 3 → RatBounds := ![⟨231357811427343/140737488355328, 61284190196967/35184372088832⟩, ⟨23714779669201/17592186044416, 201580336440047/140737488355328⟩, ⟨9037063846213/8796093022208, 313921906614855/281474976710656⟩]
def scE155CutCaps : Fin 3 → Fin 3 → ℚ := ![![553665177/5000000, 454897751/6250000, 4039080219/100000000], ![873235669/20000000, 134186989/3125000, 946192591/50000000], ![349090449/100000000, 74968327/25000000, 2648473/1250000]]
def scE155CutWeightFloor : ℚ := 144803649/100000000
def scE155CutMargins : Fin 3 → ℚ := ![7557749/2500000000, 22667319/10000000000, 5815437/5000000000]

theorem scE155Cut_roots_ok : scE155CutCell.rootsOK scE155CutRoots = true := by decide +kernel

theorem scE155Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE155CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE155Cut_margin_le (i : Fin 3) : curvatureLoss scE155CutCell scE155CutCaps i ≤ scE155CutMargins i := by
  fin_cases i <;> decide +kernel

def scE156CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨7/20, 29/80⟩, ⟨1/8, 11/80⟩⟩
def scE156CutRoots : Fin 3 → RatBounds := ![⟨462790479023389/281474976710656, 245722321427869/140737488355328⟩, ⟨378347818804951/281474976710656, 403248538668457/281474976710656⟩, ⟨148123686576809/140737488355328, 161241277269115/140737488355328⟩]
def scE156CutCaps : Fin 3 → Fin 3 → ℚ := ![![514056009/5000000, 3326033463/50000000, 3860390097/100000000], ![3985157973/100000000, 3898595961/100000000, 371493101/20000000], ![387083/78125, 210165477/50000000, 60396777/20000000]]
def scE156CutWeightFloor : ℚ := 137978279/100000000
def scE156CutMargins : Fin 3 → ℚ := ![28831533/10000000000, 21427723/10000000000, 11757499/10000000000]

theorem scE156Cut_roots_ok : scE156CutCell.rootsOK scE156CutRoots = true := by decide +kernel

theorem scE156Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE156CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE156Cut_margin_le (i : Fin 3) : curvatureLoss scE156CutCell scE156CutCaps i ≤ scE156CutMargins i := by
  fin_cases i <;> decide +kernel

def scE157CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨7/20, 29/80⟩, ⟨11/80, 3/20⟩⟩
def scE157CutRoots : Fin 3 → RatBounds := ![⟨57694738387291/35184372088832, 490121813916329/281474976710656⟩, ⟨376438994946009/281474976710656, 401190228695909/281474976710656⟩, ⟨147170796030637/140737488355328, 320396181832203/281474976710656⟩]
def scE157CutCaps : Fin 3 → Fin 3 → ℚ := ![![10477085073/100000000, 6786923237/100000000, 157606173/4000000], ![1014964113/25000000, 1984015069/50000000, 1891887887/100000000], ![474805863/100000000, 402484567/100000000, 289206853/100000000]]
def scE157CutWeightFloor : ℚ := 140406533/100000000
def scE157CutMargins : Fin 3 → ℚ := ![1465991/500000000, 21791871/10000000000, 2391113/2000000000]

theorem scE157Cut_roots_ok : scE157CutCell.rootsOK scE157CutRoots = true := by decide +kernel

theorem scE157Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE157CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE157Cut_margin_le (i : Fin 3) : curvatureLoss scE157CutCell scE157CutCaps i ≤ scE157CutMargins i := by
  fin_cases i <;> decide +kernel

def scE158CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨7/20, 29/80⟩, ⟨3/20, 13/80⟩⟩
def scE158CutRoots : Fin 3 → RatBounds := ![⟨57545944112503/35184372088832, 244422714883507/140737488355328⟩, ⟨374599560617203/281474976710656, 399208154864699/281474976710656⟩, ⟨146253514146343/140737488355328, 39798652833395/35184372088832⟩]
def scE158CutCaps : Fin 3 → Fin 3 → ℚ := ![![10672861329/100000000, 432585893/6250000, 4019743187/100000000], ![4134364577/100000000, 2018672383/50000000, 1926242039/100000000], ![91079331/20000000, 385737927/100000000, 138607083/50000000]]
def scE158CutWeightFloor : ℚ := 35709093/25000000
def scE158CutMargins : Fin 3 → ℚ := ![2980981/1000000000, 22157143/10000000000, 12154687/10000000000]

theorem scE158Cut_roots_ok : scE158CutCell.rootsOK scE158CutRoots = true := by decide +kernel

theorem scE158Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE158CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE158Cut_margin_le (i : Fin 3) : curvatureLoss scE158CutCell scE158CutCaps i ≤ scE158CutMargins i := by
  fin_cases i <;> decide +kernel

def scE159CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨7/20, 29/80⟩, ⟨13/80, 1/6⟩⟩
def scE159CutRoots : Fin 3 → RatBounds := ![⟨460195557688785/281474976710656, 243690088354061/140737488355328⟩, ⟨374011033722449/281474976710656, 397277629825807/281474976710656⟩, ⟨145959187248021/140737488355328, 39555205499731/35184372088832⟩]
def scE159CutCaps : Fin 3 → Fin 3 → ℚ := ![![10556492399/100000000, 1712768591/25000000, 785918797/20000000], ![163834331/4000000, 3964970013/100000000, 46503673/2500000], ![34611817/10000000, 73046233/25000000, 26729471/12500000]]
def scE159CutWeightFloor : ℚ := 72955157/50000000
def scE159CutMargins : Fin 3 → ℚ := ![5738597/2000000000, 4237699/2000000000, 5677247/5000000000]

theorem scE159Cut_roots_ok : scE159CutCell.rootsOK scE159CutRoots = true := by decide +kernel

theorem scE159Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE159CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE159Cut_margin_le (i : Fin 3) : curvatureLoss scE159CutCell scE159CutCaps i ≤ scE159CutMargins i := by
  fin_cases i <;> decide +kernel

def scE160CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨29/80, 3/8⟩, ⟨1/8, 11/80⟩⟩
def scE160CutRoots : Fin 3 → RatBounds := ![⟨460504267624779/281474976710656, 488832990597257/281474976710656⟩, ⟨93285364976615/70368744177664, 99407746947677/70368744177664⟩, ⟨299026283936641/281474976710656, 162539143840847/140737488355328⟩]
def scE160CutCaps : Fin 3 → Fin 3 → ℚ := ![![492127809/5000000, 6289365559/100000000, 3770353107/100000000], ![93987253/2500000, 1807953881/50000000, 1835119803/100000000], ![246066657/50000000, 102621747/25000000, 3055949/1000000]]
def scE160CutWeightFloor : ℚ := 69534267/50000000
def scE160CutMargins : Fin 3 → ℚ := ![5505539/2000000000, 2014797/1000000000, 2309011/2000000000]

theorem scE160Cut_roots_ok : scE160CutCell.rootsOK scE160CutRoots = true := by decide +kernel

theorem scE160Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE160CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE160Cut_margin_le (i : Fin 3) : curvatureLoss scE160CutCell scE160CutCaps i ≤ scE160CutMargins i := by
  fin_cases i <;> decide +kernel

def scE161CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨29/80, 3/8⟩, ⟨11/80, 3/20⟩⟩
def scE161CutRoots : Fin 3 → RatBounds := ![⟨229641639732921/140737488355328, 487523005020253/281474976710656⟩, ⟨11601126534727/8796093022208, 395576243876239/281474976710656⟩, ⟨37140261479689/35184372088832, 80749205756321/70368744177664⟩]
def scE161CutCaps : Fin 3 → Fin 3 → ℚ := ![![10030074743/100000000, 6416806477/100000000, 3848893503/100000000], ![119685371/3125000, 920069499/25000000, 934516727/50000000], ![471576271/100000000, 393035761/100000000, 58530691/20000000]]
def scE161CutWeightFloor : ℚ := 141508403/100000000
def scE161CutMargins : Fin 3 → ℚ := ![27991373/10000000000, 20488517/10000000000, 2347883/2000000000]

theorem scE161Cut_roots_ok : scE161CutCell.rootsOK scE161CutRoots = true := by decide +kernel

theorem scE161Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE161CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE161Cut_margin_le (i : Fin 3) : curvatureLoss scE161CutCell scE161CutCaps i ≤ scE161CutMargins i := by
  fin_cases i <;> decide +kernel

def scE162CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨29/80, 3/8⟩, ⟨3/20, 13/80⟩⟩
def scE162CutRoots : Fin 3 → RatBounds := ![⟨458104128309855/281474976710656, 486259040553089/281474976710656⟩, ⟨92350007662525/70368744177664, 393597747115289/281474976710656⟩, ⟨73822250564413/70368744177664, 320994519582981/281474976710656⟩]
def scE162CutCaps : Fin 3 → Fin 3 → ℚ := ![![255435531/2500000, 102247857/1562500, 3927260647/100000000], ![1950096613/50000000, 1872269751/50000000, 475720583/25000000], ![4522661/1000000, 75332231/20000000, 70126787/25000000]]
def scE162CutWeightFloor : ℚ := 17993739/12500000
def scE162CutMargins : Fin 3 → ℚ := ![14228399/5000000000, 20830203/10000000000, 745929/625000000]

theorem scE162Cut_roots_ok : scE162CutCell.rootsOK scE162CutRoots = true := by decide +kernel

theorem scE162Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE162CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE162Cut_margin_le (i : Fin 3) : curvatureLoss scE162CutCell scE162CutCaps i ≤ scE162CutMargins i := by
  fin_cases i <;> decide +kernel

def scE163CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨29/80, 3/8⟩, ⟨13/80, 1/6⟩⟩
def scE163CutRoots : Fin 3 → RatBounds := ![⟨228968881871869/140737488355328, 121200963748137/70368744177664⟩, ⟨46101562140381/35184372088832, 195835550079997/140737488355328⟩, ⟨294700898774951/281474976710656, 19940699934739/17592186044416⟩]
def scE163CutCaps : Fin 3 → Fin 3 → ℚ := ![![5051759557/50000000, 6476502427/100000000, 95965517/2500000], ![1931212889/50000000, 36735511/1000000, 367509249/20000000], ![34350431/10000000, 142474327/50000000, 53990781/25000000]]
def scE163CutWeightFloor : ℚ := 147037883/100000000
def scE163CutMargins : Fin 3 → ℚ := ![13675891/5000000000, 9943081/5000000000, 11133131/10000000000]

theorem scE163Cut_roots_ok : scE163CutCell.rootsOK scE163CutRoots = true := by decide +kernel

theorem scE163Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE163CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE163Cut_margin_le (i : Fin 3) : curvatureLoss scE163CutCell scE163CutCaps i ≤ scE163CutMargins i := by
  fin_cases i <;> decide +kernel

def scE164CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨3/8, 31/80⟩, ⟨1/8, 11/80⟩⟩
def scE164CutRoots : Fin 3 → RatBounds := ![⟨57308813685841/35184372088832, 243262788933803/140737488355328⟩, ⟨184073118466741/140737488355328, 196135448727941/140737488355328⟩, ⟨150929851525823/140737488355328, 2560679198721/2199023255552⟩]
def scE164CutCaps : Fin 3 → Fin 3 → ℚ := ![![9458098399/100000000, 149270349/2500000, 3696613461/100000000], ![3564952049/100000000, 210289021/6250000, 182152363/10000000], ![489222699/100000000, 200574721/50000000, 309409741/100000000]]
def scE164CutWeightFloor : ℚ := 70090437/50000000
def scE164CutMargins : Fin 3 → ℚ := ![26391159/10000000000, 19016773/10000000000, 1422741/1250000000]

theorem scE164Cut_roots_ok : scE164CutCell.rootsOK scE164CutRoots = true := by decide +kernel

theorem scE164Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE164CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE164Cut_margin_le (i : Fin 3) : curvatureLoss scE164CutCell scE164CutCaps i ≤ scE164CutMargins i := by
  fin_cases i <;> decide +kernel

def scE165CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨3/8, 31/80⟩, ⟨11/80, 3/20⟩⟩
def scE165CutRoots : Fin 3 → RatBounds := ![⟨457259833775173/281474976710656, 121306751709791/70368744177664⟩, ⟨91560930242743/70368744177664, 390219016440529/281474976710656⟩, ⟨149978529785265/140737488355328, 325690075988097/281474976710656⟩]
def scE165CutCaps : Fin 3 → Fin 3 → ℚ := ![![963825101/10000000, 6091716169/100000000, 3774235143/100000000], ![1815856937/50000000, 684900101/20000000, 463771367/25000000], ![468754239/100000000, 384074137/100000000, 296295381/100000000]]
def scE165CutWeightFloor : ℚ := 28526523/20000000
def scE165CutMargins : Fin 3 → ℚ := ![6708359/2500000000, 9668253/5000000000, 11573469/10000000000]

theorem scE165Cut_roots_ok : scE165CutCell.rootsOK scE165CutRoots = true := by decide +kernel

theorem scE165Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE165CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE165Cut_margin_le (i : Fin 3) : curvatureLoss scE165CutCell scE165CutCaps i ≤ scE165CutMargins i := by
  fin_cases i <;> decide +kernel

def scE166CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨3/8, 31/80⟩, ⟨3/20, 13/80⟩⟩
def scE166CutRoots : Fin 3 → RatBounds := ![⟨114022663994615/70368744177664, 483974080376205/281474976710656⟩, ⟨182205307093781/140737488355328, 48530426770049/35184372088832⟩, ⟨298125402803021/281474976710656, 161846066139343/140737488355328⟩]
def scE166CutCaps : Fin 3 → Fin 3 → ℚ := ![![2454561413/25000000, 388265757/6250000, 1925842439/50000000], ![739660789/20000000, 871069387/25000000, 944292807/50000000], ![28095567/6250000, 368053373/100000000, 56797491/20000000]]
def scE166CutWeightFloor : ℚ := 36271513/25000000
def scE166CutMargins : Fin 3 → ℚ := ![13638749/5000000000, 19657389/10000000000, 11766129/10000000000]

theorem scE166Cut_roots_ok : scE166CutCell.rootsOK scE166CutRoots = true := by decide +kernel

theorem scE166Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE166CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE166Cut_margin_le (i : Fin 3) : curvatureLoss scE166CutCell scE166CutCaps i ≤ scE166CutMargins i := by
  fin_cases i <;> decide +kernel

def scE167CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨3/8, 31/80⟩, ⟨13/80, 1/6⟩⟩
def scE167CutRoots : Fin 3 → RatBounds := ![⟨455929306814311/281474976710656, 482527815824321/281474976710656⟩, ⟨363823914419375/281474976710656, 24144998082551/17592186044416⟩, ⟨297537836663323/281474976710656, 321752779141119/281474976710656⟩]
def scE167CutCaps : Fin 3 → Fin 3 → ℚ := ![![2426641619/25000000, 6147575747/100000000, 3764396947/100000000], ![3661198801/100000000, 3414530853/100000000, 1823882389/100000000], ![170609621/50000000, 34765227/12500000, 218255689/100000000]]
def scE167CutWeightFloor : ℚ := 29637667/20000000
def scE167CutMargins : Fin 3 → ℚ := ![13091483/5000000000, 9368173/5000000000, 10961973/10000000000]

theorem scE167Cut_roots_ok : scE167CutCell.rootsOK scE167CutRoots = true := by decide +kernel

theorem scE167Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE167CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE167Cut_margin_le (i : Fin 3) : curvatureLoss scE167CutCell scE167CutCaps i ≤ scE167CutMargins i := by
  fin_cases i <;> decide +kernel

def scE168CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨31/80, 2/5⟩, ⟨1/8, 11/80⟩⟩
def scE168CutRoots : Fin 3 → RatBounds := ![⟨456677938564771/281474976710656, 242253964334805/140737488355328⟩, ⟨90836695056807/70368744177664, 387149293884803/281474976710656⟩, ⟨304751939778885/281474976710656, 82637788193957/70368744177664⟩]
def scE168CutCaps : Fin 3 → Fin 3 → ℚ := ![![1140193711/12500000, 569078493/10000000, 1818906163/50000000], ![84945113/2500000, 31404201/1000000, 908035109/50000000], ![486693393/100000000, 392266263/100000000, 979437/312500]]
def scE168CutWeightFloor : ℚ := 141317187/100000000
def scE168CutMargins : Fin 3 → ℚ := ![25402437/10000000000, 18014593/10000000000, 11264263/10000000000]

theorem scE168Cut_roots_ok : scE168CutCell.rootsOK scE168CutRoots = true := by decide +kernel

theorem scE168Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE168CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE168Cut_margin_le (i : Fin 3) : curvatureLoss scE168CutCell scE168CutCaps i ≤ scE168CutMargins i := by
  fin_cases i <;> decide +kernel

def scE169CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨31/80, 2/5⟩, ⟨11/80, 3/20⟩⟩
def scE169CutRoots : Fin 3 → RatBounds := ![⟨227738175068511/140737488355328, 15100606273975/8796093022208⟩, ⟨180723342334529/140737488355328, 192549813286733/140737488355328⟩, ⟨302850786978309/281474976710656, 328478590673059/281474976710656⟩]
def scE169CutCaps : Fin 3 → Fin 3 → ℚ := ![![1161911687/12500000, 5805913/100000, 3714799381/100000000], ![865348021/25000000, 159814591/5000000, 924711943/50000000], ![93260333/20000000, 187775277/50000000, 300125237/100000000]]
def scE169CutWeightFloor : ℚ := 143781089/100000000
def scE169CutMargins : Fin 3 → ℚ := ![25826147/10000000000, 18315929/10000000000, 5726903/5000000000]

theorem scE169Cut_roots_ok : scE169CutCell.rootsOK scE169CutRoots = true := by decide +kernel

theorem scE169Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE169CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE169Cut_margin_le (i : Fin 3) : curvatureLoss scE169CutCell scE169CutCaps i ≤ scE169CutMargins i := by
  fin_cases i <;> decide +kernel

def scE170CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨31/80, 2/5⟩, ⟨3/20, 13/80⟩⟩
def scE170CutRoots : Fin 3 → RatBounds := ![⟨227157980345327/140737488355328, 240988093073343/140737488355328⟩, ⟨359616027824541/281474976710656, 383126288455903/281474976710656⟩, ⟨301020504680197/281474976710656, 326484711562703/281474976710656⟩]
def scE170CutCaps : Fin 3 → Fin 3 → ℚ := ![![2367222819/25000000, 1184138193/20000000, 3791615031/100000000], ![3524815397/100000000, 813018223/25000000, 941359243/50000000], ![89430031/20000000, 44983519/12500000, 143824383/50000000]]
def scE170CutWeightFloor : ℚ := 7312337/5000000
def scE170CutMargins : Fin 3 → ℚ := ![13125837/5000000000, 9309211/5000000000, 11644497/10000000000]

theorem scE170Cut_roots_ok : scE170CutCell.rootsOK scE170CutRoots = true := by decide +kernel

theorem scE170Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE170CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE170Cut_margin_le (i : Fin 3) : curvatureLoss scE170CutCell scE170CutCaps i ≤ scE170CutMargins i := by
  fin_cases i <;> decide +kernel

def scE171CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨31/80, 2/5⟩, ⟨13/80, 1/6⟩⟩
def scE171CutRoots : Fin 3 → RatBounds := ![⟨454159030015597/281474976710656, 120134436635079/70368744177664⟩, ⟨359030015645147/281474976710656, 381205421411769/281474976710656⟩, ⟨300433457542361/281474976710656, 162274517908309/140737488355328⟩]
def scE171CutCaps : Fin 3 → Fin 3 → ℚ := ![![9359210041/100000000, 117169409/2000000, 463191667/12500000], ![348830101/10000000, 31834463/1000000, 1420736/78125], ![67847653/20000000, 271667571/100000000, 220710931/100000000]]
def scE171CutWeightFloor : ℚ := 149363647/100000000
def scE171CutMargins : Fin 3 → ℚ := ![5033283/2000000000, 354379/200000000, 2709277/2500000000]

theorem scE171Cut_roots_ok : scE171CutCell.rootsOK scE171CutRoots = true := by decide +kernel

theorem scE171Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE171CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE171Cut_margin_le (i : Fin 3) : curvatureLoss scE171CutCell scE171CutCaps i ≤ scE171CutMargins i := by
  fin_cases i <;> decide +kernel

def scE172CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨2/5, 33/80⟩, ⟨1/8, 11/80⟩⟩
def scE172CutRoots : Fin 3 → RatBounds := ![⟨113779223655817/70368744177664, 120691936898591/70368744177664⟩, ⟨179364597063463/140737488355328, 382249214719761/281474976710656⟩, ⟨307707390698197/281474976710656, 41679253849749/35184372088832⟩]
def scE172CutCaps : Fin 3 → Fin 3 → ℚ := ![![1765561941/20000000, 340289067/6250000, 89822411/2500000], ![813753863/25000000, 29397537/1000000, 90918459/5000000], ![242260301/50000000, 383798969/100000000, 158812287/50000000]]
def scE172CutWeightFloor : ℚ := 142479389/100000000
def scE172CutMargins : Fin 3 → ℚ := ![12272799/5000000000, 4281337/2500000000, 11189239/10000000000]

theorem scE172Cut_roots_ok : scE172CutCell.rootsOK scE172CutRoots = true := by decide +kernel

theorem scE172Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE172CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE172Cut_margin_le (i : Fin 3) : curvatureLoss scE172CutCell scE172CutCaps i ≤ scE172CutMargins i := by
  fin_cases i <;> decide +kernel

def scE173CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨2/5, 33/80⟩, ⟨11/80, 3/20⟩⟩
def scE173CutRoots : Fin 3 → RatBounds := ![⟨453923207931969/281474976710656, 481487940290349/281474976710656⟩, ⟨178415542066971/140737488355328, 95050289921435/70368744177664⟩, ⟨305807653587777/281474976710656, 41420682868907/35184372088832⟩]
def scE173CutCaps : Fin 3 → Fin 3 → ℚ := ![![8996000883/100000000, 222186029/4000000, 366951731/10000000], ![1657938647/50000000, 1496023083/50000000, 925825531/50000000], ![58024327/12500000, 367427919/100000000, 304142471/100000000]]
def scE173CutWeightFloor : ℚ := 36238941/25000000
def scE173CutMargins : Fin 3 → ℚ := ![6238317/2500000000, 17410401/10000000000, 11377561/10000000000]

theorem scE173Cut_roots_ok : scE173CutCell.rootsOK scE173CutRoots = true := by decide +kernel

theorem scE173Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE173CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE173Cut_margin_le (i : Fin 3) : curvatureLoss scE173CutCell scE173CutCaps i ≤ scE173CutMargins i := by
  fin_cases i <;> decide +kernel


end HlawkaSchatten.BelowExponent.Vertex
