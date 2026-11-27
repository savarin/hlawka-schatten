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

def scD84CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨31/80, 2/5⟩, ⟨1/10, 9/80⟩⟩
def scD84CutRoots : Fin 3 → RatBounds := ![⟨459213906545089/281474976710656, 487231312754099/281474976710656⟩, ⟨367371882581937/281474976710656, 391496234499737/281474976710656⟩, ⟨308784064064401/281474976710656, 83737954377415/70368744177664⟩]
def scD84CutCaps : Fin 3 → Fin 3 → ℚ := ![![8773595169/100000000, 218375883/4000000, 348328221/10000000], ![3270105361/100000000, 1514195291/50000000, 874588337/50000000], ![531641601/100000000, 429174679/100000000, 171380319/50000000]]
def scD84CutWeightFloor : ℚ := 3409879/2500000
def scD84CutMargins : Fin 3 → ℚ := ![383769/156250000, 17415943/10000000000, 10889101/10000000000]

theorem scD84Cut_roots_ok : scD84CutCell.rootsOK scD84CutRoots = true := by decide +kernel

theorem scD84Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD84CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD84Cut_margin_le (i : Fin 3) : curvatureLoss scD84CutCell scD84CutCaps i ≤ scD84CutMargins i := by
  fin_cases i <;> decide +kernel

def scD85CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨31/80, 2/5⟩, ⟨9/80, 1/8⟩⟩
def scD85CutRoots : Fin 3 → RatBounds := ![⟨457922982178593/281474976710656, 485844317851637/281474976710656⟩, ⟨22832523856067/17592186044416, 97319962902793/70368744177664⟩, ⟨306728179317801/281474976710656, 332707171892325/281474976710656⟩]
def scD85CutCaps : Fin 3 → Fin 3 → ℚ := ![![1789530553/20000000, 13938217/250000, 3560643627/100000000], ![3334045009/100000000, 1542227119/50000000, 356531051/20000000], ![101686677/20000000, 41010697/10000000, 327604849/100000000]]
def scD85CutWeightFloor : ℚ := 34713791/25000000
def scD85CutMargins : Fin 3 → ℚ := ![999229/400000000, 17714547/10000000000, 692249/625000000]

theorem scD85Cut_roots_ok : scD85CutCell.rootsOK scD85CutRoots = true := by decide +kernel

theorem scD85Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD85CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD85Cut_margin_le (i : Fin 3) : curvatureLoss scD85CutCell scD85CutCaps i ≤ scD85CutMargins i := by
  fin_cases i <;> decide +kernel

def scD86CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨2/5, 33/80⟩, ⟨1/10, 9/80⟩⟩
def scD86CutRoots : Fin 3 → RatBounds := ![⟨457636222877047/281474976710656, 242736382793477/140737488355328⟩, ⟨90687620207399/70368744177664, 96648294260645/70368744177664⟩, ⟨19483518484441/17592186044416, 168912979417961/140737488355328⟩]
def scD86CutCaps : Fin 3 → Fin 3 → ℚ := ![![2122748149/25000000, 5223488197/100000000, 859774511/25000000], ![3132788597/100000000, 566981341/20000000, 1751626431/100000000], ![16541533/3125000, 419949519/100000000, 347381259/100000000]]
def scD86CutWeightFloor : ℚ := 68766299/50000000
def scD86CutMargins : Fin 3 → ℚ := ![741767/312500000, 16559267/10000000000, 10816613/10000000000]

theorem scD86Cut_roots_ok : scD86CutCell.rootsOK scD86CutRoots = true := by decide +kernel

theorem scD86Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD86CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD86Cut_margin_le (i : Fin 3) : curvatureLoss scD86CutCell scD86CutCaps i ≤ scD86CutMargins i := by
  fin_cases i <;> decide +kernel

def scD87CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨2/5, 33/80⟩, ⟨9/80, 1/8⟩⟩
def scD87CutRoots : Fin 3 → RatBounds := ![⟨456353762677049/281474976710656, 484095113327781/281474976710656⟩, ⟨360700858908043/281474976710656, 384378238381235/281474976710656⟩, ⟨309682088809471/281474976710656, 335585812501247/281474976710656⟩]
def scD87CutCaps : Fin 3 → Fin 3 → ℚ := ![![2164868987/25000000, 1066848891/20000000, 1758046859/50000000], ![3193988497/100000000, 1443687481/50000000, 892514177/50000000], ![126548033/25000000, 401272811/100000000, 166005147/50000000]]
def scD87CutWeightFloor : ℚ := 17500619/12500000
def scD87CutMargins : Fin 3 → ℚ := ![4827991/2000000000, 16841587/10000000000, 2750553/2500000000]

theorem scD87Cut_roots_ok : scD87CutCell.rootsOK scD87CutRoots = true := by decide +kernel

theorem scD87Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD87CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD87Cut_margin_le (i : Fin 3) : curvatureLoss scD87CutCell scD87CutCaps i ≤ scD87CutMargins i := by
  fin_cases i <;> decide +kernel

def scD88CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨33/80, 17/40⟩, ⟨1/10, 9/80⟩⟩
def scD88CutRoots : Fin 3 → RatBounds := ![⟨28517767593157/17592186044416, 483984046741725/281474976710656⟩, ⟨179149586705911/140737488355328, 190948802006843/140737488355328⟩, ⟨39344556167915/35184372088832, 170401478996213/140737488355328⟩]
def scD88CutCaps : Fin 3 → Fin 3 → ℚ := ![![8245453373/100000000, 5016395091/100000000, 3407491027/100000000], ![1508279661/50000000, 2661257963/100000000, 880660889/50000000], ![527374293/100000000, 16445451/4000000, 352213179/100000000]]
def scD88CutWeightFloor : ℚ := 34674299/25000000
def scD88CutMargins : Fin 3 → ℚ := ![23026147/10000000000, 15798417/10000000000, 5391627/5000000000]

theorem scD88Cut_roots_ok : scD88CutCell.rootsOK scD88CutRoots = true := by decide +kernel

theorem scD88Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD88CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD88Cut_margin_le (i : Fin 3) : curvatureLoss scD88CutCell scD88CutCaps i ≤ scD88CutMargins i := by
  fin_cases i <;> decide +kernel

def scD89CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨33/80, 17/40⟩, ⟨9/80, 1/8⟩⟩
def scD89CutRoots : Fin 3 → RatBounds := ![⟨227504525922731/140737488355328, 482614364300991/281474976710656⟩, ⟨178125504834323/140737488355328, 23730219765151/17592186044416⟩, ⟨312703827301951/281474976710656, 338566983957249/281474976710656⟩]
def scD89CutCaps : Fin 3 → Fin 3 → ℚ := ![![8409139811/100000000, 5122616041/100000000, 1742190013/50000000], ![3075423591/100000000, 542100841/20000000, 179477967/10000000], ![126074369/25000000, 39283527/10000000, 336618923/100000000]]
def scD89CutWeightFloor : ℚ := 141182243/100000000
def scD89CutMargins : Fin 3 → ℚ := ![365871/156250000, 200829/125000000, 5484159/5000000000]

theorem scD89Cut_roots_ok : scD89CutCell.rootsOK scD89CutRoots = true := by decide +kernel

theorem scD89Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD89CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD89Cut_margin_le (i : Fin 3) : curvatureLoss scD89CutCell scD89CutCaps i ≤ scD89CutMargins i := by
  fin_cases i <;> decide +kernel

def scD90CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨17/40, 7/16⟩, ⟨1/10, 9/80⟩⟩
def scD90CutRoots : Fin 3 → RatBounds := ![⟨455151135625189/281474976710656, 482756521324989/281474976710656⟩, ⟨354006415624871/281474976710656, 377395763088125/281474976710656⟩, ⟨317849245933349/281474976710656, 171943421461505/140737488355328⟩]
def scD90CutCaps : Fin 3 → Fin 3 → ℚ := ![![8033680769/100000000, 302190159/6250000, 846978691/25000000], ![583899961/20000000, 2505042977/100000000, 444537593/25000000], ![525759067/100000000, 402702961/100000000, 89314703/25000000]]
def scD90CutWeightFloor : ℚ := 27978183/20000000
def scD90CutMargins : Fin 3 → ℚ := ![5604951/2500000000, 7561317/5000000000, 10787743/10000000000]

theorem scD90Cut_roots_ok : scD90CutCell.rootsOK scD90CutRoots = true := by decide +kernel

theorem scD90Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD90CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD90Cut_margin_le (i : Fin 3) : curvatureLoss scD90CutCell scD90CutCaps i ≤ scD90CutMargins i := by
  fin_cases i <;> decide +kernel

def scD91CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨17/40, 7/16⟩, ⟨9/80, 1/8⟩⟩
def scD91CutRoots : Fin 3 → RatBounds := ![⟨226940966564857/140737488355328, 120348368142891/70368744177664⟩, ⟨175979662102851/140737488355328, 375181972984005/281474976710656⟩, ⟨78949524512731/70368744177664, 170827354333127/140737488355328⟩]
def scD91CutCaps : Fin 3 → Fin 3 → ℚ := ![![1638656039/20000000, 1234315437/25000000, 1732474731/50000000], ![595278953/20000000, 2551395173/100000000, 90589717/5000000], ![125682957/25000000, 192381777/50000000, 85358279/25000000]]
def scD91CutWeightFloor : ℚ := 142389023/100000000
def scD91CutMargins : Fin 3 → ℚ := ![2279767/1000000000, 615111/400000000, 5486501/5000000000]

theorem scD91Cut_roots_ok : scD91CutCell.rootsOK scD91CutRoots = true := by decide +kernel

theorem scD91Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD91CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD91Cut_margin_le (i : Fin 3) : curvatureLoss scD91CutCell scD91CutCaps i ≤ scD91CutMargins i := by
  fin_cases i <;> decide +kernel

def scD92CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨7/16, 9/20⟩, ⟨1/10, 9/80⟩⟩
def scD92CutRoots : Fin 3 → RatBounds := ![⟨454231067903981/281474976710656, 481783198368517/281474976710656⟩, ⟨349861663303659/281474976710656, 373075262646955/281474976710656⟩, ⟨321019608192651/281474976710656, 173541065928193/140737488355328⟩]
def scD92CutCaps : Fin 3 → Fin 3 → ℚ := ![![7852999463/100000000, 4676879079/100000000, 845005951/25000000], ![568015369/20000000, 1182114809/50000000, 1802111709/100000000], ![524468663/100000000, 394621411/100000000, 181261059/50000000]]
def scD92CutWeightFloor : ℚ := 70557893/50000000
def scD92CutMargins : Fin 3 → ℚ := ![5477317/2500000000, 14522911/10000000000, 1082941/1000000000]

theorem scD92Cut_roots_ok : scD92CutCell.rootsOK scD92CutRoots = true := by decide +kernel

theorem scD92Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD92CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD92Cut_margin_le (i : Fin 3) : curvatureLoss scD92CutCell scD92CutCaps i ≤ scD92CutMargins i := by
  fin_cases i <;> decide +kernel

def scD93CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨7/16, 9/20⟩, ⟨9/80, 1/8⟩⟩
def scD93CutRoots : Fin 3 → RatBounds := ![⟨452966713982455/281474976710656, 240212738498779/140737488355328⟩, ⟨173907645171035/140737488355328, 11589414144143/8796093022208⟩, ⟨318969805818295/281474976710656, 172426748591067/140737488355328⟩]
def scD93CutCaps : Fin 3 → Fin 3 → ℚ := ![![64073341/800000, 2387788159/50000000, 3457453843/100000000], ![2895338457/100000000, 300997169/12500000, 5737723/312500], ![125370251/25000000, 18851527/5000000, 346456737/100000000]]
def scD93CutWeightFloor : ℚ := 143627351/100000000
def scD93CutMargins : Fin 3 → ℚ := ![22277319/10000000000, 14766767/10000000000, 1101559/1000000000]

theorem scD93Cut_roots_ok : scD93CutCell.rootsOK scD93CutRoots = true := by decide +kernel

theorem scD93Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD93CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD93Cut_margin_le (i : Fin 3) : curvatureLoss scD93CutCell scD93CutCaps i ≤ scD93CutMargins i := by
  fin_cases i <;> decide +kernel

def scD94CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨9/20, 37/80⟩, ⟨1/10, 9/80⟩⟩
def scD94CutRoots : Fin 3 → RatBounds := ![⟨453519506450031/281474976710656, 481058615459433/281474976710656⟩, ⟨345855254521093/281474976710656, 368924914714997/281474976710656⟩, ⟨324272699481959/281474976710656, 350393860172333/281474976710656⟩]
def scD94CutCaps : Fin 3 → Fin 3 → ℚ := ![![7701272061/100000000, 907958927/20000000, 3383659739/100000000], ![1388544727/50000000, 223709251/10000000, 114582041/6250000], ![52349157/10000000, 193433393/50000000, 92002149/25000000]]
def scD94CutWeightFloor : ℚ := 142373933/100000000
def scD94CutMargins : Fin 3 → ℚ := ![4297599/2000000000, 13991707/10000000000, 5454083/5000000000]

theorem scD94Cut_roots_ok : scD94CutCell.rootsOK scD94CutRoots = true := by decide +kernel

theorem scD94Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD94CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD94Cut_margin_le (i : Fin 3) : curvatureLoss scD94CutCell scD94CutCaps i ≤ scD94CutMargins i := by
  fin_cases i <;> decide +kernel

def scD95CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨9/20, 37/80⟩, ⟨9/80, 1/8⟩⟩
def scD95CutRoots : Fin 3 → RatBounds := ![⟨452258842327857/281474976710656, 479704938591693/281474976710656⟩, ⟨343809275580129/281474976710656, 366710198785055/281474976710656⟩, ⟨322224095796567/281474976710656, 348168375070021/281474976710656⟩]
def scD95CutCaps : Fin 3 → Fin 3 → ℚ := ![![7854622089/100000000, 4635405011/100000000, 692347163/20000000], ![2831029729/100000000, 227849281/10000000, 186771903/10000000], ![500533911/100000000, 92403077/25000000, 35169513/10000000]]
def scD95CutWeightFloor : ℚ := 72449689/50000000
def scD95CutMargins : Fin 3 → ℚ := ![1092401/500000000, 7112803/5000000000, 11095997/10000000000]

theorem scD95Cut_roots_ok : scD95CutCell.rootsOK scD95CutRoots = true := by decide +kernel

theorem scD95Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD95CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD95Cut_margin_le (i : Fin 3) : curvatureLoss scD95CutCell scD95CutCaps i ≤ scD95CutMargins i := by
  fin_cases i <;> decide +kernel

def scD96CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨37/80, 19/40⟩, ⟨1/10, 9/80⟩⟩
def scD96CutRoots : Fin 3 → RatBounds := ![⟨453012959289493/281474976710656, 120144687651229/70368744177664⟩, ⟨341978306775491/281474976710656, 364934601260967/281474976710656⟩, ⟨40951745581795/35184372088832, 353827614657737/281474976710656⟩]
def scD96CutCaps : Fin 3 → Fin 3 → ℚ := ![![7576836073/100000000, 552757019/12500000, 3398843961/100000000], ![21325231/781250, 1061081541/50000000, 374393333/20000000], ![522819239/100000000, 379417169/100000000, 2919729/781250]]
def scD96CutWeightFloor : ℚ := 143667583/100000000
def scD96CutMargins : Fin 3 → ℚ := ![5287737/2500000000, 1690341/1250000000, 2204897/2000000000]

theorem scD96Cut_roots_ok : scD96CutCell.rootsOK scD96CutRoots = true := by decide +kernel

theorem scD96Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD96CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD96Cut_margin_le (i : Fin 3) : curvatureLoss scD96CutCell scD96CutCaps i ≤ scD96CutMargins i := by
  fin_cases i <;> decide +kernel

def scD97CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨37/80, 19/40⟩, ⟨9/80, 1/8⟩⟩
def scD97CutRoots : Fin 3 → RatBounds := ![⟨112938710308991/70368744177664, 479227852743717/281474976710656⟩, ⟨339932424625715/281474976710656, 362718721524115/281474976710656⟩, ⟨325566394231187/281474976710656, 351604917122723/281474976710656⟩]
def scD97CutCaps : Fin 3 → Fin 3 → ℚ := ![![3863974353/50000000, 2257488917/50000000, 1738910787/50000000], ![1391271097/50000000, 2161445303/100000000, 1906954183/100000000], ![49988231/10000000, 362487747/100000000, 7143103/2000000]]
def scD97CutWeightFloor : ℚ := 228449/156250
def scD97CutMargins : Fin 3 → ℚ := ![5376159/2500000000, 13747873/10000000000, 11214709/10000000000]

theorem scD97Cut_roots_ok : scD97CutCell.rootsOK scD97CutRoots = true := by decide +kernel

theorem scD97Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD97CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD97Cut_margin_le (i : Fin 3) : curvatureLoss scD97CutCell scD97CutCaps i ≤ scD97CutMargins i := by
  fin_cases i <;> decide +kernel

def scD98CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨19/40, 39/80⟩, ⟨1/10, 9/80⟩⟩
def scD98CutRoots : Fin 3 → RatBounds := ![⟨452708965140459/281474976710656, 480340958465365/281474976710656⟩, ⟨338222627128081/281474976710656, 361095160141543/281474976710656⟩, ⟨331049173351937/281474976710656, 89347393904533/70368744177664⟩]
def scD98CutCaps : Fin 3 → Fin 3 → ℚ := ![![3739228957/50000000, 270141093/6250000, 53527759/1562500], ![168568089/6250000, 2018198611/100000000, 1918492461/100000000], ![522445897/100000000, 372253227/100000000, 379680961/100000000]]
def scD98CutWeightFloor : ℚ := 144999091/100000000
def scD98CutMargins : Fin 3 → ℚ := ![20894519/10000000000, 13110761/10000000000, 1117959/1000000000]

theorem scD98Cut_roots_ok : scD98CutCell.rootsOK scD98CutRoots = true := by decide +kernel

theorem scD98Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD98CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD98Cut_margin_le (i : Fin 3) : curvatureLoss scD98CutCell scD98CutCaps i ≤ scD98CutMargins i := by
  fin_cases i <;> decide +kernel

def scD99CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨19/40, 39/80⟩, ⟨9/80, 1/8⟩⟩
def scD99CutRoots : Fin 3 → RatBounds := ![⟨451452259914807/281474976710656, 478991585713545/281474976710656⟩, ⟨336176569822993/281474976710656, 358877683509515/281474976710656⟩, ⟨5140663305263/4398046511104, 88792322349137/70368744177664⟩]
def scD99CutCaps : Fin 3 → Fin 3 → ℚ := ![![7627890811/100000000, 2206429201/50000000, 701183971/20000000], ![1374629723/50000000, 82222811/4000000, 1954211993/100000000], ![99904129/20000000, 44454779/12500000, 90711303/25000000]]
def scD99CutWeightFloor : ℚ := 147553683/100000000
def scD99CutMargins : Fin 3 → ℚ := ![10621749/5000000000, 104127/78125000, 11373003/10000000000]

theorem scD99Cut_roots_ok : scD99CutCell.rootsOK scD99CutRoots = true := by decide +kernel

theorem scD99Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD99CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD99Cut_margin_le (i : Fin 3) : curvatureLoss scD99CutCell scD99CutCaps i ≤ scD99CutMargins i := by
  fin_cases i <;> decide +kernel

def scD100CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨39/80, 1/2⟩, ⟨1/10, 9/80⟩⟩
def scD100CutRoots : Fin 3 → RatBounds := ![⟨226303029598089/140737488355328, 480343928930135/281474976710656⟩, ⟨167290316592211/140737488355328, 357398287693417/281474976710656⟩, ⟨334584466626715/281474976710656, 180543283771051/140737488355328⟩]
def scD100CutCaps : Fin 3 → Fin 3 → ℚ := ![![296212063/4000000, 2119640537/50000000, 3464841321/100000000], ![269011291/10000000, 193583187/10000000, 995739707/50000000], ![522368437/100000000, 45669741/12500000, 385885949/100000000]]
def scD100CutWeightFloor : ℚ := 73185477/50000000
def scD100CutMargins : Fin 3 → ℚ := ![10368929/5000000000, 6387179/5000000000, 17829/15625000]

theorem scD100Cut_roots_ok : scD100CutCell.rootsOK scD100CutRoots = true := by decide +kernel

theorem scD100Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD100CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD100Cut_margin_le (i : Fin 3) : curvatureLoss scD100CutCell scD100CutCaps i ≤ scD100CutMargins i := by
  fin_cases i <;> decide +kernel

def scD101CutCell : ParameterCell := ⟨⟨1/80, 1/40⟩, ⟨39/80, 1/2⟩, ⟨9/80, 1/8⟩⟩
def scD101CutRoots : Fin 3 → RatBounds := ![⟨225674819817025/140737488355328, 478994833377331/281474976710656⟩, ⟨332534152401207/281474976710656, 44397350369863/35184372088832⟩, ⟨332538388734415/281474976710656, 179434149881701/140737488355328⟩]
def scD101CutCaps : Fin 3 → Fin 3 → ℚ := ![![755359801/10000000, 4327904773/100000000, 3546427053/100000000], ![274214569/10000000, 985885613/50000000, 2028474479/100000000], ![499445927/100000000, 349047351/100000000, 184387691/50000000]]
def scD101CutWeightFloor : ℚ := 18617609/12500000
def scD101CutMargins : Fin 3 → ℚ := ![4216871/2000000000, 3246447/2500000000, 1451093/1250000000]

theorem scD101Cut_roots_ok : scD101CutCell.rootsOK scD101CutRoots = true := by decide +kernel

theorem scD101Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scD101CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scD101Cut_margin_le (i : Fin 3) : curvatureLoss scD101CutCell scD101CutCaps i ≤ scD101CutMargins i := by
  fin_cases i <;> decide +kernel

def scE0CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨3/16, 1/5⟩, ⟨1/8, 11/80⟩⟩
def scE0CutRoots : Fin 3 → RatBounds := ![⟨540252443040237/281474976710656, 292251084976435/140737488355328⟩, ⟨487304297223729/281474976710656, 528072090740115/281474976710656⟩, ⟨130773956655421/140737488355328, 297338301392769/281474976710656⟩]
def scE0CutCaps : Fin 3 → Fin 3 → ℚ := ![![809273369/2500000, 6357972931/25000000, 4456046061/50000000], ![8397072341/50000000, 17863459243/100000000, 4025134397/100000000], ![625105337/100000000, 651848143/100000000, 139307633/50000000]]
def scE0CutWeightFloor : ℚ := 124416243/100000000
def scE0CutMargins : Fin 3 → ℚ := ![19449291/2000000000, 42917187/5000000000, 25812191/10000000000]

theorem scE0Cut_roots_ok : scE0CutCell.rootsOK scE0CutRoots = true := by decide +kernel

theorem scE0Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE0CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE0Cut_margin_le (i : Fin 3) : curvatureLoss scE0CutCell scE0CutCaps i ≤ scE0CutMargins i := by
  fin_cases i <;> decide +kernel

def scE1CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨3/16, 1/5⟩, ⟨11/80, 3/20⟩⟩
def scE1CutRoots : Fin 3 → RatBounds := ![⟨538701497526767/281474976710656, 582812217991703/281474976710656⟩, ⟨242601539211723/140737488355328, 525778101960309/281474976710656⟩, ⟨16225596420473/17592186044416, 295118772564413/281474976710656⟩]
def scE1CutCaps : Fin 3 → Fin 3 → ℚ := ![![8245765337/25000000, 324045731/1250000, 9065948083/100000000], ![17103350849/100000000, 18179303391/100000000, 512064191/12500000], ![75001939/12500000, 624936437/100000000, 267036611/100000000]]
def scE1CutWeightFloor : ℚ := 15837509/12500000
def scE1CutMargins : Fin 3 → ℚ := ![9899693/1000000000, 87359177/10000000000, 26229489/10000000000]

theorem scE1Cut_roots_ok : scE1CutCell.rootsOK scE1CutRoots = true := by decide +kernel

theorem scE1Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE1CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE1Cut_margin_le (i : Fin 3) : curvatureLoss scE1CutCell scE1CutCaps i ≤ scE1CutMargins i := by
  fin_cases i <;> decide +kernel

def scE2CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨3/16, 1/5⟩, ⟨3/20, 13/80⟩⟩
def scE2CutRoots : Fin 3 → RatBounds := ![⟨537202934245287/281474976710656, 36323783230047/17592186044416⟩, ⟨483175793594177/281474976710656, 261783121043103/140737488355328⟩, ⟨257744135241233/281474976710656, 292984370296415/281474976710656⟩]
def scE2CutCaps : Fin 3 → Fin 3 → ℚ := ![![2099627801/6250000, 6603506269/25000000, 9219475387/100000000], ![1741186397/10000000, 18494532879/100000000, 4167712953/100000000], ![288196557/50000000, 599642393/100000000, 12807841/5000000]]
def scE2CutWeightFloor : ℚ := 128984883/100000000
def scE2CutMargins : Fin 3 → ℚ := ![25186671/2500000000, 22220801/2500000000, 26647159/10000000000]

theorem scE2Cut_roots_ok : scE2CutCell.rootsOK scE2CutRoots = true := by decide +kernel

theorem scE2Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE2CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE2Cut_margin_le (i : Fin 3) : curvatureLoss scE2CutCell scE2CutCaps i ≤ scE2CutMargins i := by
  fin_cases i <;> decide +kernel

def scE3CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨3/16, 1/5⟩, ⟨13/80, 1/6⟩⟩
def scE3CutRoots : Fin 3 → RatBounds := ![⟨536887427321583/281474976710656, 144852482626191/70368744177664⟩, ⟨241257890527277/140737488355328, 521418381005455/281474976710656⟩, ⟨257137838487845/281474976710656, 2272836502103/2199023255552⟩]
def scE3CutCaps : Fin 3 → Fin 3 → ℚ := ![![33396682041/100000000, 26249276489/100000000, 9086147173/100000000], ![8676746399/50000000, 3672117871/20000000, 4064155871/100000000], ![449508919/100000000, 471732121/100000000, 103694627/50000000]]
def scE3CutWeightFloor : ℚ := 131879391/100000000
def scE3CutMargins : Fin 3 → ℚ := ![19843797/2000000000, 87231017/10000000000, 3216149/1250000000]

theorem scE3Cut_roots_ok : scE3CutCell.rootsOK scE3CutRoots = true := by decide +kernel

theorem scE3Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE3CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE3Cut_margin_le (i : Fin 3) : curvatureLoss scE3CutCell scE3CutCaps i ≤ scE3CutMargins i := by
  fin_cases i <;> decide +kernel

def scE4CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨1/5, 17/80⟩, ⟨1/8, 11/80⟩⟩
def scE4CutRoots : Fin 3 → RatBounds := ![⟨531441591310945/281474976710656, 573465442378127/281474976710656⟩, ⟨59474618703247/35184372088832, 64290347491945/35184372088832⟩, ⟨264158085187981/281474976710656, 298608741830747/281474976710656⟩]
def scE4CutCaps : Fin 3 → Fin 3 → ℚ := ![![889445251/3125000, 5492305463/25000000, 1000147383/12500000], ![287710121/2000000, 477821809/3125000, 3590232511/100000000], ![151930179/25000000, 124731697/20000000, 17359747/6250000]]
def scE4CutWeightFloor : ℚ := 125464371/100000000
def scE4CutMargins : Fin 3 → ℚ := ![3394959/400000000, 73990583/10000000000, 1448873/625000000]

theorem scE4Cut_roots_ok : scE4CutCell.rootsOK scE4CutRoots = true := by decide +kernel

theorem scE4Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE4CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE4Cut_margin_le (i : Fin 3) : curvatureLoss scE4CutCell scE4CutCaps i ≤ scE4CutMargins i := by
  fin_cases i <;> decide +kernel

def scE5CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨1/5, 17/80⟩, ⟨11/80, 3/20⟩⟩
def scE5CutRoots : Fin 3 → RatBounds := ![⟨66241360216623/35184372088832, 142955763336855/70368744177664⟩, ⟨236858638621267/140737488355328, 128014286672769/70368744177664⟩, ⟨65554569870363/70368744177664, 296400427743041/281474976710656⟩]
def scE5CutCaps : Fin 3 → Fin 3 → ℚ := ![![28999221999/100000000, 22394980481/100000000, 4070617399/50000000], ![7325242729/50000000, 3890120739/25000000, 365432317/10000000], ![116640939/20000000, 597816809/100000000, 16636791/6250000]]
def scE5CutWeightFloor : ℚ := 1277601/1000000
def scE5CutMargins : Fin 3 → ℚ := ![86392407/10000000000, 4706211/625000000, 23558099/10000000000]

theorem scE5Cut_roots_ok : scE5CutCell.rootsOK scE5CutRoots = true := by decide +kernel

theorem scE5Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE5CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE5Cut_margin_le (i : Fin 3) : curvatureLoss scE5CutCell scE5CutCaps i ≤ scE5CutMargins i := by
  fin_cases i <;> decide +kernel

def scE6CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨1/5, 17/80⟩, ⟨3/20, 13/80⟩⟩
def scE6CutRoots : Fin 3 → RatBounds := ![⟨264235622287615/140737488355328, 142559341666551/70368744177664⟩, ⟨29481937485037/17592186044416, 509872879723033/281474976710656⟩, ⟨4067991631169/4398046511104, 294276776809807/281474976710656⟩]
def scE6CutCaps : Fin 3 → Fin 3 → ℚ := ![![29535199469/100000000, 22819518583/100000000, 4140474727/50000000], ![14914867949/100000000, 15830144887/100000000, 148730121/4000000], ![280064603/50000000, 573533477/100000000, 255320863/100000000]]
def scE6CutWeightFloor : ℚ := 65028431/50000000
def scE6CutMargins : Fin 3 → ℚ := ![87910541/10000000000, 76607807/10000000000, 2991827/1250000000]

theorem scE6Cut_roots_ok : scE6CutCell.rootsOK scE6CutRoots = true := by decide +kernel

theorem scE6Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE6CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE6Cut_margin_le (i : Fin 3) : curvatureLoss scE6CutCell scE6CutCaps i ≤ scE6CutMargins i := by
  fin_cases i <;> decide +kernel

def scE7CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨1/5, 17/80⟩, ⟨13/80, 1/6⟩⟩
def scE7CutRoots : Fin 3 → RatBounds := ![⟨264086952339857/140737488355328, 568506349663795/281474976710656⟩, ⟨471057873055083/281474976710656, 507752237757805/281474976710656⟩, ⟨259744704453227/281474976710656, 146112868342691/140737488355328⟩]
def scE7CutCaps : Fin 3 → Fin 3 → ℚ := ![![3668687719/12500000, 4533833673/20000000, 254881291/3125000], ![14858205257/100000000, 15703424943/100000000, 3619406759/100000000], ![435255627/100000000, 224542999/50000000, 205595327/100000000]]
def scE7CutWeightFloor : ℚ := 132966461/100000000
def scE7CutMargins : Fin 3 → ℚ := ![17287527/2000000000, 7504393/1000000000, 5760963/2500000000]

theorem scE7Cut_roots_ok : scE7CutCell.rootsOK scE7CutRoots = true := by decide +kernel

theorem scE7Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE7CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE7Cut_margin_le (i : Fin 3) : curvatureLoss scE7CutCell scE7CutCaps i ≤ scE7CutMargins i := by
  fin_cases i <;> decide +kernel

def scE8CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨17/80, 9/40⟩, ⟨1/8, 11/80⟩⟩
def scE8CutRoots : Fin 3 → RatBounds := ![⟨523464248791495/281474976710656, 17611526689309/8796093022208⟩, ⟨232566765354917/140737488355328, 501719032660383/281474976710656⟩, ⟨133365940555899/140737488355328, 300014142746155/281474976710656⟩]
def scE8CutCaps : Fin 3 → Fin 3 → ℚ := ![![6322213729/25000000, 19190807729/100000000, 3634992201/50000000], ![6226086719/50000000, 13220554101/100000000, 1616896129/50000000], ![74075377/12500000, 598412583/100000000, 277524841/100000000]]
def scE8CutWeightFloor : ℚ := 7905791/6250000
def scE8CutMargins : Fin 3 → ℚ := ![37435187/5000000000, 8059027/1250000000, 2105723/1000000000]

theorem scE8Cut_roots_ok : scE8CutCell.rootsOK scE8CutRoots = true := by decide +kernel

theorem scE8Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE8CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE8Cut_margin_le (i : Fin 3) : curvatureLoss scE8CutCell scE8CutCaps i ≤ scE8CutMargins i := by
  fin_cases i <;> decide +kernel

def scE9CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨17/80, 9/40⟩, ⟨11/80, 3/20⟩⟩
def scE9CutRoots : Fin 3 → RatBounds := ![⟨521990284307461/281474976710656, 561969524312439/281474976710656⟩, ⟨463072947169363/281474976710656, 249739118353605/140737488355328⟩, ⟨264791204763511/281474976710656, 297816168832075/281474976710656⟩]
def scE9CutCaps : Fin 3 → Fin 3 → ℚ := ![![402576571/1562500, 4890884153/25000000, 7398610947/100000000], ![253633457/2000000, 13454044923/100000000, 3291869129/100000000], ![568583053/100000000, 573532471/100000000, 1038842/390625]]
def scE9CutWeightFloor : ℚ := 1006249/781250
def scE9CutMargins : Fin 3 → ℚ := ![38100739/5000000000, 13121529/2000000000, 4279853/2000000000]

theorem scE9Cut_roots_ok : scE9CutCell.rootsOK scE9CutRoots = true := by decide +kernel

theorem scE9Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE9CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE9Cut_margin_le (i : Fin 3) : curvatureLoss scE9CutCell scE9CutCaps i ≤ scE9CutMargins i := by
  fin_cases i <;> decide +kernel

def scE10CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨17/80, 9/40⟩, ⟨3/20, 13/80⟩⟩
def scE10CutRoots : Fin 3 → RatBounds := ![⟨520566195605123/281474976710656, 560425481849903/281474976710656⟩, ⟨230542647328787/140737488355328, 124329539063623/70368744177664⟩, ⟨262923523306895/281474976710656, 295702426153397/281474976710656⟩]
def scE10CutCaps : Fin 3 → Fin 3 → ℚ := ![![3280012683/12500000, 19935196293/100000000, 7526927909/100000000], ![806915753/6250000, 13687086221/100000000, 837450291/25000000], ![545980589/100000000, 275078613/50000000, 255063899/100000000]]
def scE10CutWeightFloor : ℚ := 131108173/100000000
def scE10CutMargins : Fin 3 → ℚ := ![19383171/2500000000, 66743047/10000000000, 2717723/1250000000]

theorem scE10Cut_roots_ok : scE10CutCell.rootsOK scE10CutRoots = true := by decide +kernel

theorem scE10Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE10CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE10Cut_margin_le (i : Fin 3) : curvatureLoss scE10CutCell scE10CutCaps i ≤ scE10CutMargins i := by
  fin_cases i <;> decide +kernel

def scE11CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨17/80, 9/40⟩, ⟨13/80, 1/6⟩⟩
def scE11CutRoots : Fin 3 → RatBounds := ![⟨520285577131365/281474976710656, 279365060034421/140737488355328⟩, ⟨230219137887839/140737488355328, 247610701839199/140737488355328⟩, ⟨262316475659367/281474976710656, 293660829767289/281474976710656⟩]
def scE11CutCaps : Fin 3 → Fin 3 → ℚ := ![![26064547101/100000000, 4949058999/25000000, 370303583/5000000], ![12855733203/100000000, 13568086887/100000000, 406973389/12500000], ![422914871/100000000, 107236803/25000000, 102179517/50000000]]
def scE11CutWeightFloor : ℚ := 4188509/3125000
def scE11CutMargins : Fin 3 → ℚ := ![76107951/10000000000, 65257781/10000000000, 5217073/2500000000]

theorem scE11Cut_roots_ok : scE11CutCell.rootsOK scE11CutRoots = true := by decide +kernel

theorem scE11Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE11CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE11Cut_margin_le (i : Fin 3) : curvatureLoss scE11CutCell scE11CutCaps i ≤ scE11CutMargins i := by
  fin_cases i <;> decide +kernel

def scE12CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨9/40, 19/80⟩, ⟨1/8, 11/80⟩⟩
def scE12CutRoots : Fin 3 → RatBounds := ![⟨258111461176585/140737488355328, 277331413736423/140737488355328⟩, ⟨455211131650107/281474976710656, 490106008972087/281474976710656⟩, ⟨269282522022851/281474976710656, 301541672118671/281474976710656⟩]
def scE12CutCaps : Fin 3 → Fin 3 → ℚ := ![![1417409091/6250000, 16934111819/100000000, 3336718723/50000000], ![2720024171/25000000, 11533544287/100000000, 2938304783/100000000], ![72422109/12500000, 287815663/50000000, 138915207/50000000]]
def scE12CutWeightFloor : ℚ := 127507409/100000000
def scE12CutMargins : Fin 3 → ℚ := ![66675819/10000000000, 56725171/10000000000, 4828893/2500000000]

theorem scE12Cut_roots_ok : scE12CutCell.rootsOK scE12CutRoots = true := by decide +kernel

theorem scE12Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE12CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE12Cut_margin_le (i : Fin 3) : curvatureLoss scE12CutCell scE12CutCaps i ≤ scE12CutMargins i := by
  fin_cases i <;> decide +kernel

def scE13CutCell : ParameterCell := ⟨⟨0, 1/80⟩, ⟨9/40, 19/80⟩, ⟨11/80, 3/20⟩⟩
def scE13CutRoots : Fin 3 → RatBounds := ![⟨514782584065211/281474976710656, 138275650473549/70368744177664⟩, ⟨453167496557001/281474976710656, 121971757155071/70368744177664⟩, ⟨66835358878797/70368744177664, 299353285015379/281474976710656⟩]
def scE13CutCaps : Fin 3 → Fin 3 → ℚ := ![![11552433171/50000000, 4315972771/25000000, 424553251/6250000], ![110807571/1000000, 1467143721/12500000, 2991364887/100000000], ![555788367/100000000, 551622053/100000000, 532427/200000]]
def scE13CutWeightFloor : ℚ := 32456453/25000000
def scE13CutMargins : Fin 3 → ℚ := ![848179/125000000, 11544009/2000000000, 19629747/10000000000]

theorem scE13Cut_roots_ok : scE13CutCell.rootsOK scE13CutRoots = true := by decide +kernel

theorem scE13Cut_caps_nonneg (k i : Fin 3) : 0 ≤ scE13CutCaps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem scE13Cut_margin_le (i : Fin 3) : curvatureLoss scE13CutCell scE13CutCaps i ≤ scE13CutMargins i := by
  fin_cases i <;> decide +kernel


end HlawkaSchatten.BelowExponent.Vertex
