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

def scS32CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨23/80, 3/10⟩, ⟨0, 1/40⟩⟩
def scS32CutRoots : Fin 3 → RatBounds := ![⟨31398980618195/17592186044416, 539457740005681/281474976710656⟩, ⟨435982973013607/281474976710656, 235077583176171/140737488355328⟩, ⟨18974703073341/17592186044416, 21132224891111/17592186044416⟩]
def scS32CutCaps : Fin 3 → Fin 3 → ℚ := ![![1561053381/12500000, 2138104173/25000000, 4147527459/100000000], ![5311155857/100000000, 5590518891/100000000, 188600821/10000000], ![576734263/50000000, 1068950327/100000000, 38269149/6250000]]
def scS32CutWeightFloor : ℚ := 107858699/100000000
def scS32CutMargins : Fin 3 → ℚ := ![10944071/2500000000, 2248381/625000000, 16567893/10000000000]

theorem scS32Cut_roots_ok : scS32CutCell.rootsOK scS32CutRoots = true := by decide +kernel

theorem scS32Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS32CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS32Cut_margin_le (i : Fin 3) : curvatureLoss scS32CutCell scS32CutCaps i ≤ scS32CutMargins i := by
  fin_cases i <;> decide +kernel

def scS33CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨23/80, 3/10⟩, ⟨1/40, 1/20⟩⟩
def scS33CutRoots : Fin 3 → RatBounds := ![⟨498809785397653/281474976710656, 133828882546495/70368744177664⟩, ⟨430392327497807/281474976710656, 115945685551515/70368744177664⟩, ⟨37255415689905/35184372088832, 331608578905521/281474976710656⟩]
def scS33CutCaps : Fin 3 → Fin 3 → ℚ := ![![13053815287/100000000, 8971120481/100000000, 4336670367/100000000], ![5554721229/100000000, 583060111/10000000, 985871669/50000000], ![516583533/50000000, 954144099/100000000, 109323147/20000000]]
def scS33CutWeightFloor : ℚ := 14073441/12500000
def scS33CutMargins : Fin 3 → ℚ := ![1388013/312500000, 4545483/1250000000, 4147889/2500000000]

theorem scS33Cut_roots_ok : scS33CutCell.rootsOK scS33CutRoots = true := by decide +kernel

theorem scS33Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS33CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS33Cut_margin_le (i : Fin 3) : curvatureLoss scS33CutCell scS33CutCaps i ≤ scS33CutMargins i := by
  fin_cases i <;> decide +kernel

def scS34CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨23/80, 3/10⟩, ⟨1/20, 3/40⟩⟩
def scS34CutRoots : Fin 3 → RatBounds := ![⟨495511342241121/281474976710656, 531511727311637/281474976710656⟩, ⟨425264488770193/281474976710656, 228980635928085/140737488355328⟩, ⟨292971345877753/281474976710656, 325689399523693/281474976710656⟩]
def scS34CutCaps : Fin 3 → Fin 3 → ℚ := ![![6808250359/50000000, 9385833231/100000000, 4524243859/100000000], ![5796415523/100000000, 3034504273/50000000, 2056603763/100000000], ![930115291/100000000, 856312533/100000000, 2453201/500000]]
def scS34CutWeightFloor : ℚ := 11732643/10000000
def scS34CutMargins : Fin 3 → ℚ := ![22591189/5000000000, 1843759/500000000, 3337269/2000000000]

theorem scS34Cut_roots_ok : scS34CutCell.rootsOK scS34CutRoots = true := by decide +kernel

theorem scS34Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS34CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS34Cut_margin_le (i : Fin 3) : curvatureLoss scS34CutCell scS34CutCaps i ≤ scS34CutMargins i := by
  fin_cases i <;> decide +kernel

def scS35CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨23/80, 3/10⟩, ⟨3/40, 1/10⟩⟩
def scS35CutRoots : Fin 3 → RatBounds := ![⟨30778586208359/17592186044416, 264003031896413/140737488355328⟩, ⟨420543561508393/281474976710656, 226310678965569/140737488355328⟩, ⟨288319524393199/281474976710656, 320281662541543/281474976710656⟩]
def scS35CutCaps : Fin 3 → Fin 3 → ℚ := ![![7088372741/50000000, 9797008269/100000000, 4710432727/100000000], ![6036410119/100000000, 3152948613/50000000, 1070337847/50000000], ![420620537/50000000, 386166813/50000000, 442590967/100000000]]
def scS35CutWeightFloor : ℚ := 122073789/100000000
def scS35CutMargins : Fin 3 → ℚ := ![5756377/1250000000, 9371211/2500000000, 8419407/5000000000]

theorem scS35Cut_roots_ok : scS35CutCell.rootsOK scS35CutRoots = true := by decide +kernel

theorem scS35Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS35CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS35Cut_margin_le (i : Fin 3) : curvatureLoss scS35CutCell scS35CutCaps i ≤ scS35CutMargins i := by
  fin_cases i <;> decide +kernel

def scS36CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨3/10, 5/16⟩, ⟨0, 1/40⟩⟩
def scS36CutRoots : Fin 3 → RatBounds := ![⟨498013209343723/281474976710656, 267142027216941/140737488355328⟩, ⟨429009196520131/281474976710656, 115584792999155/70368744177664⟩, ⟨76544246443065/70368744177664, 170075922652525/140737488355328⟩]
def scS36CutCaps : Fin 3 → Fin 3 → ℚ := ![![5830675331/50000000, 1968057983/25000000, 3940398089/100000000], ![2429288999/50000000, 2535131483/50000000, 181322519/10000000], ![114231217/10000000, 1041794369/100000000, 619753999/100000000]]
def scS36CutWeightFloor : ℚ := 27193979/25000000
def scS36CutMargins : Fin 3 → ℚ := ![205949/50000000, 33417329/10000000000, 8039687/5000000000]

theorem scS36Cut_roots_ok : scS36CutCell.rootsOK scS36CutRoots = true := by decide +kernel

theorem scS36Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS36CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS36Cut_margin_le (i : Fin 3) : curvatureLoss scS36CutCell scS36CutCaps i ≤ scS36CutMargins i := by
  fin_cases i <;> decide +kernel

def scS37CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨3/10, 5/16⟩, ⟨1/40, 1/20⟩⟩
def scS37CutRoots : Fin 3 → RatBounds := ![⟨123623618494835/70368744177664, 530205335406891/281474976710656⟩, ⟨6616214814941/4398046511104, 56998834632725/35184372088832⟩, ⟨300629129338411/281474976710656, 333666256965235/281474976710656⟩]
def scS37CutCaps : Fin 3 → Fin 3 → ℚ := ![![6094099759/50000000, 4129065743/50000000, 824411569/20000000], ![5081680789/100000000, 2644053281/50000000, 23696051/1250000], ![1022863383/100000000, 929654861/100000000, 110631307/20000000]]
def scS37CutWeightFloor : ℚ := 113523717/100000000
def scS37CutMargins : Fin 3 → ℚ := ![10430339/2500000000, 1348817/400000000, 8037469/5000000000]

theorem scS37Cut_roots_ok : scS37CutCell.rootsOK scS37CutRoots = true := by decide +kernel

theorem scS37Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS37CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS37Cut_margin_le (i : Fin 3) : curvatureLoss scS37CutCell scS37CutCaps i ≤ scS37CutMargins i := by
  fin_cases i <;> decide +kernel

def scS38CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨3/10, 5/16⟩, ⟨1/20, 3/40⟩⟩
def scS38CutRoots : Fin 3 → RatBounds := ![⟨491247055607961/281474976710656, 526460196344381/281474976710656⟩, ⟨104582150410689/70368744177664, 112548103441301/70368744177664⟩, ⟨295560588509903/281474976710656, 327766212702619/281474976710656⟩]
def scS38CutCaps : Fin 3 → Fin 3 → ℚ := ![![12712625067/100000000, 8640342137/100000000, 2151108377/50000000], ![1060611029/20000000, 2752214187/50000000, 1977317531/100000000], ![460289133/50000000, 166824937/20000000, 24821/5000]]
def scS38CutWeightFloor : ℚ := 118282231/100000000
def scS38CutMargins : Fin 3 → ℚ := ![21189447/5000000000, 6828621/2000000000, 16142997/10000000000]

theorem scS38Cut_roots_ok : scS38CutCell.rootsOK scS38CutRoots = true := by decide +kernel

theorem scS38Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS38CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS38Cut_margin_le (i : Fin 3) : curvatureLoss scS38CutCell scS38CutCaps i ≤ scS38CutMargins i := by
  fin_cases i <;> decide +kernel

def scS39CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨3/10, 5/16⟩, ⟨3/40, 1/10⟩⟩
def scS39CutRoots : Fin 3 → RatBounds := ![⟨61030054167673/35184372088832, 523008909975025/281474976710656⟩, ⟨413625820245123/281474976710656, 222437471634315/140737488355328⟩, ⟨290911677109187/281474976710656, 161187821165997/140737488355328⟩]
def scS39CutCaps : Fin 3 → Fin 3 → ℚ := ![![6617429549/50000000, 1127410337/12500000, 4481051507/100000000], ![5522857573/100000000, 2859684021/50000000, 2058205309/100000000], ![52024651/6250000, 23504519/3125000, 447727071/100000000]]
def scS39CutWeightFloor : ℚ := 6152487/5000000
def scS39CutMargins : Fin 3 → ℚ := ![43139247/10000000000, 34662557/10000000000, 8134927/5000000000]

theorem scS39Cut_roots_ok : scS39CutCell.rootsOK scS39CutRoots = true := by decide +kernel

theorem scS39Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS39CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS39Cut_margin_le (i : Fin 3) : curvatureLoss scS39CutCell scS39CutCaps i ≤ scS39CutMargins i := by
  fin_cases i <;> decide +kernel

def scS40CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨5/16, 13/40⟩, ⟨0, 1/40⟩⟩
def scS40CutRoots : Fin 3 → RatBounds := ![⟨30877143573431/17592186044416, 529598990863811/281474976710656⟩, ⟨13199793708361/8796093022208, 227486804131341/140737488355328⟩, ⟨308787095724973/281474976710656, 171141259993071/140737488355328⟩]
def scS40CutCaps : Fin 3 → Fin 3 → ℚ := ![![10941702667/100000000, 7284550847/100000000, 187991299/5000000], ![4471095153/100000000, 28886467/625000, 219300087/12500000], ![566169171/50000000, 31755341/3125000, 313809133/50000000]]
def scS40CutWeightFloor : ℚ := 109703213/100000000
def scS40CutMargins : Fin 3 → ℚ := ![7789903/2000000000, 6238699/2000000000, 7836621/5000000000]

theorem scS40Cut_roots_ok : scS40CutCell.rootsOK scS40CutRoots = true := by decide +kernel

theorem scS40Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS40CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS40Cut_margin_le (i : Fin 3) : curvatureLoss scS40CutCell scS40CutCaps i ≤ scS40CutMargins i := by
  fin_cases i <;> decide +kernel

def scS41CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨5/16, 13/40⟩, ⟨1/40, 1/20⟩⟩
def scS41CutRoots : Fin 3 → RatBounds := ![⟨490566018030881/281474976710656, 525578115199121/281474976710656⟩, ⟨208419336963217/140737488355328, 224322770364091/140737488355328⟩, ⟨151621812389245/140737488355328, 167908646558511/140737488355328⟩]
def scS41CutCaps : Fin 3 → Fin 3 → ℚ := ![![5717556457/50000000, 955251509/12500000, 3935056801/100000000], ![4676692037/100000000, 1205137549/25000000, 91708717/5000000], ![1013648291/100000000, 906563931/100000000, 112014779/20000000]]
def scS41CutWeightFloor : ℚ := 57235099/50000000
def scS41CutMargins : Fin 3 → ℚ := ![39387497/10000000000, 31423473/10000000000, 15643607/10000000000]

theorem scS41Cut_roots_ok : scS41CutCell.rootsOK scS41CutRoots = true := by decide +kernel

theorem scS41Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS41CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS41Cut_margin_le (i : Fin 3) : curvatureLoss scS41CutCell scS41CutCaps i ≤ scS41CutMargins i := by
  fin_cases i <;> decide +kernel

def scS42CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨5/16, 13/40⟩, ⟨1/20, 3/40⟩⟩
def scS42CutRoots : Fin 3 → RatBounds := ![⟨121841315823019/70368744177664, 521886422546519/281474976710656⟩, ⟨411745904714837/281474976710656, 442867225763783/281474976710656⟩, ⟨298178798452467/281474976710656, 329935393414557/281474976710656⟩]
def scS42CutCaps : Fin 3 → Fin 3 → ℚ := ![![1490792461/12500000, 499752933/6250000, 4108847171/100000000], ![4880685401/100000000, 5017890963/100000000, 956585673/50000000], ![912045927/100000000, 406608589/50000000, 125635421/25000000]]
def scS42CutWeightFloor : ℚ := 119248541/100000000
def scS42CutMargins : Fin 3 → ℚ := ![1997579/500000000, 31771107/10000000000, 7843931/5000000000]

theorem scS42Cut_roots_ok : scS42CutCell.rootsOK scS42CutRoots = true := by decide +kernel

theorem scS42Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS42CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS42Cut_margin_le (i : Fin 3) : curvatureLoss scS42CutCell scS42CutCaps i ≤ scS42CutMargins i := by
  fin_cases i <;> decide +kernel

def scS43CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨5/16, 13/40⟩, ⟨3/40, 1/10⟩⟩
def scS43CutRoots : Fin 3 → RatBounds := ![⟨484401933399541/281474976710656, 518484677638321/281474976710656⟩, ⟨203529549237435/140737488355328, 218784579414001/140737488355328⟩, ⟨146766518425069/140737488355328, 81140267354893/70368744177664⟩]
def scS43CutCaps : Fin 3 → Fin 3 → ℚ := ![![12415588939/100000000, 8347044269/100000000, 2140683377/50000000], ![1270804819/25000000, 1303495093/25000000, 995732457/50000000], ![103059673/12500000, 366565921/50000000, 45317491/10000000]]
def scS43CutWeightFloor : ℚ := 124036419/100000000
def scS43CutMargins : Fin 3 → ℚ := ![4061859/1000000000, 32213969/10000000000, 7896027/5000000000]

theorem scS43Cut_roots_ok : scS43CutCell.rootsOK scS43CutRoots = true := by decide +kernel

theorem scS43Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS43CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS43Cut_margin_le (i : Fin 3) : curvatureLoss scS43CutCell scS43CutCaps i ≤ scS43CutMargins i := by
  fin_cases i <;> decide +kernel

def scS44CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨13/40, 27/80⟩, ⟨0, 1/40⟩⟩
def scS44CutRoots : Fin 3 → RatBounds := ![⟨490419169624689/281474976710656, 525364620049285/281474976710656⟩, ⟨416104233961145/281474976710656, 448016808511509/281474976710656⟩, ⟨311430861802983/281474976710656, 344507095134095/281474976710656⟩]
def scS44CutCaps : Fin 3 → Fin 3 → ℚ := ![![10312785937/100000000, 6774276073/100000000, 3602107081/100000000], ![4138146717/100000000, 52915941/1250000, 1707630533/100000000], ![561713337/50000000, 495957583/50000000, 158968963/25000000]]
def scS44CutWeightFloor : ℚ := 27660617/25000000
def scS44CutMargins : Fin 3 → ℚ := ![37001249/10000000000, 29248461/10000000000, 7669181/5000000000]

theorem scS44Cut_roots_ok : scS44CutCell.rootsOK scS44CutRoots = true := by decide +kernel

theorem scS44Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS44CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS44Cut_margin_le (i : Fin 3) : curvatureLoss scS44CutCell scS44CutCaps i ≤ scS44CutMargins i := by
  fin_cases i <;> decide +kernel

def scS45CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨13/40, 27/80⟩, ⟨1/40, 1/20⟩⟩
def scS45CutRoots : Fin 3 → RatBounds := ![⟨121749229596417/70368744177664, 521396328416965/281474976710656⟩, ⟨205282001496427/140737488355328, 220853007117965/140737488355328⟩, ⟨19118250875073/17592186044416, 338061220783083/281474976710656⟩]
def scS45CutCaps : Fin 3 → Fin 3 → ℚ := ![![2155412269/20000000, 88836937/1250000, 235739101/6250000], ![4328705243/100000000, 551894817/12500000, 357017041/20000000], ![50270563/5000000, 6911881/781250, 567346759/100000000]]
def scS45CutWeightFloor : ℚ := 115428923/100000000
def scS45CutMargins : Fin 3 → ℚ := ![18679113/5000000000, 29416009/10000000000, 15285739/10000000000]

theorem scS45Cut_roots_ok : scS45CutCell.rootsOK scS45CutRoots = true := by decide +kernel

theorem scS45Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS45CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS45Cut_margin_le (i : Fin 3) : curvatureLoss scS45CutCell scS45CutCaps i ≤ scS45CutMargins i := by
  fin_cases i <;> decide +kernel

def scS46CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨13/40, 27/80⟩, ⟨1/20, 3/40⟩⟩
def scS46CutRoots : Fin 3 → RatBounds := ![⟨241919364903311/140737488355328, 64719152900609/35184372088832⟩, ⟨202742761341841/140737488355328, 435944710813791/281474976710656⟩, ⟨75207775975089/70368744177664, 332196529661101/281474976710656⟩]
def scS46CutCaps : Fin 3 → Fin 3 → ℚ := ![![11239360207/100000000, 7436436827/100000000, 3940157081/100000000], ![903552893/20000000, 919184371/20000000, 1861881947/100000000], ![90441671/10000000, 396726139/50000000, 101797257/20000000]]
def scS46CutWeightFloor : ℚ := 24045477/20000000
def scS46CutMargins : Fin 3 → ℚ := ![3784139/1000000000, 29699547/10000000000, 15308563/10000000000]

theorem scS46Cut_roots_ok : scS46CutCell.rootsOK scS46CutRoots = true := by decide +kernel

theorem scS46Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS46CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS46Cut_margin_le (i : Fin 3) : curvatureLoss scS46CutCell scS46CutCaps i ≤ scS46CutMargins i := by
  fin_cases i <;> decide +kernel

def scS47CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨13/40, 27/80⟩, ⟨3/40, 1/10⟩⟩
def scS47CutRoots : Fin 3 → RatBounds := ![⟨30057180566953/17592186044416, 64299564524551/35184372088832⟩, ⟨200406366001187/140737488355328, 215331653270735/140737488355328⟩, ⟨148094331849109/140737488355328, 326837581216739/281474976710656⟩]
def scS47CutCaps : Fin 3 → Fin 3 → ℚ := ![![11699866323/100000000, 3881542199/50000000, 4107264959/100000000], ![2352728853/50000000, 298471537/6250000, 969005957/50000000], ![817396451/100000000, 357584489/50000000, 57364671/12500000]]
def scS47CutWeightFloor : ℚ := 5001437/4000000
def scS47CutMargins : Fin 3 → ℚ := ![38427559/10000000000, 939899/312500000, 7696237/5000000000]

theorem scS47Cut_roots_ok : scS47CutCell.rootsOK scS47CutRoots = true := by decide +kernel

theorem scS47Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS47CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS47Cut_margin_le (i : Fin 3) : curvatureLoss scS47CutCell scS47CutCaps i ≤ scS47CutMargins i := by
  fin_cases i <;> decide +kernel

def scS48CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨27/80, 7/20⟩, ⟨0, 1/40⟩⟩
def scS48CutRoots : Fin 3 → RatBounds := ![⟨243571882772803/140737488355328, 65193552582643/35184372088832⟩, ⟨205057022719675/140737488355328, 441432447108293/281474976710656⟩, ⟨314113305202519/281474976710656, 173412869953747/140737488355328⟩]
def scS48CutCaps : Fin 3 → Fin 3 → ℚ := ![![1952768843/20000000, 1582326241/25000000, 867212443/25000000], ![962812563/25000000, 3892974369/100000000, 1670760999/100000000], ![1784761/160000, 121110773/12500000, 644508511/100000000]]
def scS48CutWeightFloor : ℚ := 111595463/100000000
def scS48CutMargins : Fin 3 → ℚ := ![7061327/2000000000, 27534813/10000000000, 7536763/5000000000]

theorem scS48Cut_roots_ok : scS48CutCell.rootsOK scS48CutRoots = true := by decide +kernel

theorem scS48Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS48CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS48Cut_margin_le (i : Fin 3) : curvatureLoss scS48CutCell scS48CutCaps i ≤ scS48CutMargins i := by
  fin_cases i <;> decide +kernel

def scS49CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨27/80, 7/20⟩, ⟨1/40, 1/20⟩⟩
def scS49CutRoots : Fin 3 → RatBounds := ![⟨483763360959493/281474976710656, 64703473424397/35184372088832⟩, ⟨50573286584831/35184372088832, 435136072954539/281474976710656⟩, ⟨308579245713807/281474976710656, 340398256359519/281474976710656⟩]
def scS49CutCaps : Fin 3 → Fin 3 → ℚ := ![![10203779523/100000000, 33201439/500000, 29086371/800000], ![4028822541/100000000, 812049453/20000000, 436601139/25000000], ![199611889/20000000, 431998527/50000000, 574958913/100000000]]
def scS49CutWeightFloor : ℚ := 23280349/20000000
def scS49CutMargins : Fin 3 → ℚ := ![35595391/10000000000, 1382473/500000000, 7501989/5000000000]

theorem scS49Cut_roots_ok : scS49CutCell.rootsOK scS49CutRoots = true := by decide +kernel

theorem scS49Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS49CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS49Cut_margin_le (i : Fin 3) : curvatureLoss scS49CutCell scS49CutCaps i ≤ scS49CutMargins i := by
  fin_cases i <;> decide +kernel

def scS50CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨27/80, 7/20⟩, ⟨1/20, 3/40⟩⟩
def scS50CutRoots : Fin 3 → RatBounds := ![⟨480643869993795/281474976710656, 128507179710027/70368744177664⟩, ⟨99880053023179/70368744177664, 429389123080681/281474976710656⟩, ⟨18970149186751/17592186044416, 334549880250175/281474976710656⟩]
def scS50CutCaps : Fin 3 → Fin 3 → ℚ := ![![665117161/6250000, 868534367/12500000, 950332387/25000000], ![1051246373/25000000, 2113184717/50000000, 910673181/50000000], ![35904213/4000000, 774712601/100000000, 515739259/100000000]]
def scS50CutWeightFloor : ℚ := 24244137/20000000
def scS50CutMargins : Fin 3 → ℚ := ![9002579/2500000000, 174237/62500000, 7505501/5000000000]

theorem scS50Cut_roots_ok : scS50CutCell.rootsOK scS50CutRoots = true := by decide +kernel

theorem scS50Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS50CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS50Cut_margin_le (i : Fin 3) : curvatureLoss scS50CutCell scS50CutCaps i ≤ scS50CutMargins i := by
  fin_cases i <;> decide +kernel

def scS51CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨27/80, 7/20⟩, ⟨3/40, 1/10⟩⟩
def scS51CutRoots : Fin 3 → RatBounds := ![⟨477755927966907/281474976710656, 510712831762925/281474976710656⟩, ⟨394859663067503/281474976710656, 424121899548173/281474976710656⟩, ⟨298883378434887/281474976710656, 164602737403647/140737488355328⟩]
def scS51CutCaps : Fin 3 → Fin 3 → ℚ := ![![11078297263/100000000, 1813401547/25000000, 3965612727/100000000], ![2189931567/50000000, 274466839/6250000, 1895666579/100000000], ![811072977/100000000, 174537051/25000000, 232470651/50000000]]
def scS51CutWeightFloor : ℚ := 15756281/12500000
def scS51CutMargins : Fin 3 → ℚ := ![9132057/2500000000, 7049643/2500000000, 7540083/5000000000]

theorem scS51Cut_roots_ok : scS51CutCell.rootsOK scS51CutRoots = true := by decide +kernel

theorem scS51Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS51CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS51Cut_margin_le (i : Fin 3) : curvatureLoss scS51CutCell scS51CutCaps i ≤ scS51CutMargins i := by
  fin_cases i <;> decide +kernel

def scS52CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨7/20, 29/80⟩, ⟨0, 1/40⟩⟩
def scS52CutRoots : Fin 3 → RatBounds := ![⟨242093612529471/140737488355328, 518122462713347/281474976710656⟩, ⟨50549789442367/35184372088832, 435188693814075/281474976710656⟩, ⟨316839267770257/281474976710656, 174619624412599/140737488355328⟩]
def scS52CutCaps : Fin 3 → Fin 3 → ℚ := ![![4643813041/50000000, 2969927589/50000000, 3363885771/100000000], ![720728147/20000000, 3593390803/100000000, 821369299/50000000], ![554199761/50000000, 94696299/10000000, 65350249/10000000]]
def scS52CutWeightFloor : ℚ := 1407049/1250000
def scS52CutMargins : Fin 3 → ℚ := ![33837627/10000000000, 2601777/1000000000, 3721013/2500000000]

theorem scS52Cut_roots_ok : scS52CutCell.rootsOK scS52CutRoots = true := by decide +kernel

theorem scS52Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS52CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS52Cut_margin_le (i : Fin 3) : curvatureLoss scS52CutCell scS52CutCaps i ≤ scS52CutMargins i := by
  fin_cases i <;> decide +kernel

def scS53CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨7/20, 29/80⟩, ⟨1/40, 1/20⟩⟩
def scS53CutRoots : Fin 3 → RatBounds := ![⟨480844700543595/281474976710656, 514244849458297/281474976710656⟩, ⟨398881214811083/281474976710656, 107226037116263/70368744177664⟩, ⟨19456880983463/17592186044416, 171414615091831/140737488355328⟩]
def scS53CutCaps : Fin 3 → Fin 3 → ℚ := ![![606600117/6250000, 3115883621/50000000, 3527471707/100000000], ![3769974443/100000000, 3747808501/100000000, 171694447/10000000], ![991514379/100000000, 422141243/50000000, 582898129/100000000]]
def scS53CutWeightFloor : ℚ := 2347809/2000000
def scS53CutMargins : Fin 3 → ℚ := ![8516423/2500000000, 6521829/2500000000, 3699223/2500000000]

theorem scS53Cut_roots_ok : scS53CutCell.rootsOK scS53CutRoots = true := by decide +kernel

theorem scS53Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS53CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS53Cut_margin_le (i : Fin 3) : curvatureLoss scS53CutCell scS53CutCaps i ≤ scS53CutMargins i := by
  fin_cases i <;> decide +kernel

def scS54CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨7/20, 29/80⟩, ⟨1/20, 3/40⟩⟩
def scS54CutRoots : Fin 3 → RatBounds := ![⟨238880118785635/140737488355328, 510685532172871/281474976710656⟩, ⟨393825820871373/281474976710656, 423169136717617/281474976710656⟩, ⟨153128681419227/140737488355328, 336996307517829/281474976710656⟩]
def scS54CutCaps : Fin 3 → Fin 3 → ℚ := ![![10121882341/100000000, 1304172211/20000000, 3689667053/100000000], ![1967488569/50000000, 243828531/6250000, 1790520431/100000000], ![891539657/100000000, 756897187/100000000, 522789659/100000000]]
def scS54CutWeightFloor : ℚ := 12223029/10000000
def scS54CutMargins : Fin 3 → ℚ := ![17209979/5000000000, 13134479/5000000000, 7393893/5000000000]

theorem scS54Cut_roots_ok : scS54CutCell.rootsOK scS54CutRoots = true := by decide +kernel

theorem scS54Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS54CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS54Cut_margin_le (i : Fin 3) : curvatureLoss scS54CutCell scS54CutCaps i ≤ scS54CutMargins i := by
  fin_cases i <;> decide +kernel

def scS55CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨7/20, 29/80⟩, ⟨3/40, 1/10⟩⟩
def scS55CutRoots : Fin 3 → RatBounds := ![⟨474904788703197/281474976710656, 253703246509831/140737488355328⟩, ⟨389175903768441/281474976710656, 417913837383639/281474976710656⟩, ⟨301621840197989/281474976710656, 331665641267987/281474976710656⟩]
def scS55CutCaps : Fin 3 → Fin 3 → ℚ := ![![1053662029/10000000, 3403728139/50000000, 770126563/20000000], ![4098764761/100000000, 4053728011/100000000, 931740477/50000000], ![80544047/10000000, 340988393/50000000, 235618429/50000000]]
def scS55CutWeightFloor : ℚ := 127081299/100000000
def scS55CutMargins : Fin 3 → ℚ := ![34877241/10000000000, 5308239/2000000000, 14841917/10000000000]

theorem scS55Cut_roots_ok : scS55CutCell.rootsOK scS55CutRoots = true := by decide +kernel

theorem scS55Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS55CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS55Cut_margin_le (i : Fin 3) : curvatureLoss scS55CutCell scS55CutCaps i ≤ scS55CutMargins i := by
  fin_cases i <;> decide +kernel

def scS56CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨29/80, 3/8⟩, ⟨0, 1/40⟩⟩
def scS56CutRoots : Fin 3 → RatBounds := ![⟨481531463517587/281474976710656, 128765687506959/70368744177664⟩, ⟨398935213329233/281474976710656, 429257527736903/281474976710656⟩, ⟨319613481650597/281474976710656, 175874495268429/140737488355328⟩]
def scS56CutCaps : Fin 3 → Fin 3 → ℚ := ![![4434343577/50000000, 5597969743/100000000, 102332197/3125000], ![84746179/2500000, 3328811377/100000000, 1622908737/100000000], ![1102125783/100000000, 926041009/100000000, 41427989/6250000]]
def scS56CutWeightFloor : ℚ := 56774759/50000000
def scS56CutMargins : Fin 3 → ℚ := ![4069101/1250000000, 4933963/2000000000, 2948801/2000000000]

theorem scS56Cut_roots_ok : scS56CutCell.rootsOK scS56CutRoots = true := by decide +kernel

theorem scS56Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS56CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS56Cut_margin_le (i : Fin 3) : curvatureLoss scS56CutCell scS56CutCaps i ≤ scS56CutMargins i := by
  fin_cases i <;> decide +kernel

def scS57CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨29/80, 3/8⟩, ⟨1/40, 1/20⟩⟩
def scS57CutRoots : Fin 3 → RatBounds := ![⟨478223038972169/281474976710656, 255611882952653/140737488355328⟩, ⟨393427106660287/281474976710656, 211491224279311/140737488355328⟩, ⟨157044617642227/140737488355328, 345355536800419/281474976710656⟩]
def scS57CutCaps : Fin 3 → Fin 3 → ℚ := ![![9267410533/100000000, 18353291/312500, 1717485907/50000000], ![886611269/25000000, 1735976391/50000000, 1696055297/100000000], ![492854793/50000000, 412740849/50000000, 295577803/50000000]]
def scS57CutWeightFloor : ℚ := 118396781/100000000
def scS57CutMargins : Fin 3 → ℚ := ![16363959/5000000000, 24701041/10000000000, 14639941/10000000000]

theorem scS57Cut_roots_ok : scS57CutCell.rootsOK scS57CutRoots = true := by decide +kernel

theorem scS57Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS57CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS57Cut_margin_le (i : Fin 3) : curvatureLoss scS57CutCell scS57CutCaps i ≤ scS57CutMargins i := by
  fin_cases i <;> decide +kernel

def scS58CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨29/80, 3/8⟩, ⟨1/20, 3/40⟩⟩
def scS58CutRoots : Fin 3 → RatBounds := ![⟨475170107190759/281474976710656, 507700143123187/281474976710656⟩, ⟨388380842710467/281474976710656, 104314292862893/70368744177664⟩, ⟨77260161652023/70368744177664, 84884307237933/70368744177664⟩]
def scS58CutCaps : Fin 3 → Fin 3 → ℚ := ![![1932914487/20000000, 1229096207/20000000, 3594413329/100000000], ![3701780297/100000000, 56470429/1562500, 176855361/10000000], ![88615861/10000000, 369959369/50000000, 66266207/12500000]]
def scS58CutWeightFloor : ℚ := 24651601/20000000
def scS58CutMargins : Fin 3 → ℚ := ![4128659/1250000000, 3105289/1250000000, 14616183/10000000000]

theorem scS58Cut_roots_ok : scS58CutCell.rootsOK scS58CutRoots = true := by decide +kernel

theorem scS58Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS58CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS58Cut_margin_le (i : Fin 3) : curvatureLoss scS58CutCell scS58CutCaps i ≤ scS58CutMargins i := by
  fin_cases i <;> decide +kernel

def scS59CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨29/80, 3/8⟩, ⟨3/40, 1/10⟩⟩
def scS59CutRoots : Fin 3 → RatBounds := ![⟨118085976643429/70368744177664, 126113547945867/70368744177664⟩, ⟨383740093634219/281474976710656, 412011736744879/281474976710656⟩, ⟨304408612385667/281474976710656, 334219518528833/281474976710656⟩]
def scS59CutCaps : Fin 3 → Fin 3 → ℚ := ![![5030153023/50000000, 6415551027/100000000, 75053831/2000000], ![3855961701/100000000, 1877678851/50000000, 230057423/12500000], ![800442597/100000000, 10415227/1562500, 14931157/3125000]]
def scS59CutWeightFloor : ℚ := 1001023/781250
def scS59CutMargins : Fin 3 → ℚ := ![33433669/10000000000, 2507267/1000000000, 14656913/10000000000]

theorem scS59Cut_roots_ok : scS59CutCell.rootsOK scS59CutRoots = true := by decide +kernel

theorem scS59Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS59CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS59Cut_margin_le (i : Fin 3) : curvatureLoss scS59CutCell scS59CutCaps i ≤ scS59CutMargins i := by
  fin_cases i <;> decide +kernel

def scS60CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨3/8, 31/80⟩, ⟨0, 1/40⟩⟩
def scS60CutRoots : Fin 3 → RatBounds := ![⟨119790205470579/70368744177664, 512348688019757/281474976710656⟩, ⟨393705218608233/281474976710656, 423614176494759/281474976710656⟩, ⟨322440629608607/281474976710656, 354356872476759/281474976710656⟩]
def scS60CutCaps : Fin 3 → Fin 3 → ℚ := ![![424988953/5000000, 2648568021/50000000, 1600360837/50000000], ![25643383/800000, 309403481/10000000, 1610544299/100000000], ![13707411/1250000, 906029403/100000000, 168134469/25000000]]
def scS60CutWeightFloor : ℚ := 114553923/100000000
def scS60CutMargins : Fin 3 → ℚ := ![6285771/2000000000, 23467361/10000000000, 14651207/10000000000]

theorem scS60Cut_roots_ok : scS60CutCell.rootsOK scS60CutRoots = true := by decide +kernel

theorem scS60Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS60CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS60Cut_margin_le (i : Fin 3) : curvatureLoss scS60CutCell scS60CutCaps i ≤ scS60CutMargins i := by
  fin_cases i <;> decide +kernel

def scS61CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨3/8, 31/80⟩, ⟨1/40, 1/20⟩⟩
def scS61CutRoots : Fin 3 → RatBounds := ![⟨118970719738655/70368744177664, 254272077540341/140737488355328⟩, ⟨388204598107167/281474976710656, 208673200661725/140737488355328⟩, ⟨316921290172075/281474976710656, 347979100769583/281474976710656⟩]
def scS61CutCaps : Fin 3 → Fin 3 → ℚ := ![![2220422583/25000000, 5557373699/100000000, 1679506141/50000000], ![1676794303/50000000, 645417007/20000000, 841451041/50000000], ![490294357/50000000, 403755917/50000000, 299862779/50000000]]
def scS61CutWeightFloor : ℚ := 59711231/50000000
def scS61CutMargins : Fin 3 → ℚ := ![31557879/10000000000, 23465833/10000000000, 2906569/2000000000]

theorem scS61Cut_roots_ok : scS61CutCell.rootsOK scS61CutRoots = true := by decide +kernel

theorem scS61Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS61CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS61Cut_margin_le (i : Fin 3) : curvatureLoss scS61CutCell scS61CutCaps i ≤ scS61CutMargins i := by
  fin_cases i <;> decide +kernel

def scS62CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨3/8, 31/80⟩, ⟨1/20, 3/40⟩⟩
def scS62CutRoots : Fin 3 → RatBounds := ![⟨236429065734261/140737488355328, 505052366758123/281474976710656⟩, ⟨191583023539975/140737488355328, 411628841220433/281474976710656⟩, ⟨38984601455803/35184372088832, 171087292022051/140737488355328⟩]
def scS62CutCaps : Fin 3 → Fin 3 → ℚ := ![![9262118581/100000000, 90860579/1562500, 1757993769/50000000], ![3500551277/100000000, 209951209/6250000, 877317001/50000000], ![220352599/25000000, 45231337/6250000, 537754167/100000000]]
def scS62CutWeightFloor : ℚ := 124305613/100000000
def scS62CutMargins : Fin 3 → ℚ := ![31813109/10000000000, 4714493/2000000000, 3623847/2500000000]

theorem scS62Cut_roots_ok : scS62CutCell.rootsOK scS62CutRoots = true := by decide +kernel

theorem scS62Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS62CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS62Cut_margin_le (i : Fin 3) : curvatureLoss scS62CutCell scS62CutCaps i ≤ scS62CutMargins i := by
  fin_cases i <;> decide +kernel

def scS63CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨3/8, 31/80⟩, ⟨3/40, 1/10⟩⟩
def scS63CutRoots : Fin 3 → RatBounds := ![⟨235029036774261/140737488355328, 15682372670877/8796093022208⟩, ⟨189266566146947/140737488355328, 406391384345485/281474976710656⟩, ⟨153624109933471/140737488355328, 336869059178169/281474976710656⟩]
def scS63CutCaps : Fin 3 → Fin 3 → ℚ := ![![9641197397/100000000, 3035267519/50000000, 18359003/500000], ![729282719/20000000, 1745256327/50000000, 456448143/25000000], ![79603161/10000000, 162967933/25000000, 4846173/1000000]]
def scS63CutWeightFloor : ℚ := 129201023/100000000
def scS63CutMargins : Fin 3 → ℚ := ![32171363/10000000000, 2376667/1000000000, 363089/250000000]

theorem scS63Cut_roots_ok : scS63CutCell.rootsOK scS63CutRoots = true := by decide +kernel

theorem scS63Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scS63CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scS63Cut_margin_le (i : Fin 3) : curvatureLoss scS63CutCell scS63CutCaps i ≤ scS63CutMargins i := by
  fin_cases i <;> decide +kernel


end HlawkaSchatten.BelowExponent.Vertex
