/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H0NegPart2`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H0NegPart2Box : Box := (((((((((⟨![0, 4/25, 0, -8], ![9/136, 17/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 2 (5/16)).lowerChild 3 (0)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutTop1H0NegPart2Tree : CertTree :=
  .cut 1 (33/200)
    (.cut 3 (-3/16)
      (.cut 2 (7/32)
        (.row ⟨114055813619, 115752966124, (.direct 19358451269 18215106269), (.variance 559494540437)⟩)
        (.row ⟨114055813619, 115752966124, (.direct 19358451269 18215106269), (.chord (.midpoint ⟨480592274683, 115099718674, 199346001001, 345254717507, 199345462946, 239643475624⟩) 24716235638 43500686443)⟩))
      (.cut 2 (7/32)
        (.row ⟨114055813619, 115752966124, (.direct 10180561190 9330153225), (.chord (.midpoint ⟨500315701184, 103763586032, 191861842169, 354756969158, 191861262635, 168647478831⟩) 10180665226 24716235638)⟩)
        (.cut 0 (9/272)
          (.row ⟨114055813619, 115752966124, (.direct 10180561190 9751986835), (.chord (.midpoint ⟨585134818116, 61621862110, 158294028950, 406623275774, 158293295058, 292145484615⟩) 24716235638 43500686443)⟩)
          (.row ⟨114055813619, 115752966124, (.direct 10180561190 9330153225), (.chord (.midpoint ⟨572302762238, 67329772571, 159677241558, 404120939013, 163554156478, 289446576023⟩) 24716235638 43500686443)⟩))))
    (.cut 3 (-3/16)
      (.cut 2 (7/32)
        (.row ⟨115752966123, 117423580140, (.direct 19358451269 18177676427), (.variance 559795989668)⟩)
        (.row ⟨115752966123, 117423580140, (.direct 19358451269 18177676427), (.chord (.midpoint ⟨480993305352, 114863201925, 199194719940, 345440736783, 199194181022, 239643475624⟩) 24716235638 43500686443)⟩))
      (.cut 2 (7/32)
        (.row ⟨115752966123, 117423580140, (.direct 10180561190 9302456220), (.chord (.midpoint ⟨500866593248, 103455557925, 191651440683, 355033254540, 191650860018, 168647478831⟩) 10180665226 24716235638)⟩)
        (.cut 0 (9/272)
          (.row ⟨115752966123, 117423580140, (.direct 10180561190 9737906501), (.chord (.midpoint ⟨585339074477, 61532889567, 158209638892, 406777153736, 158208904682, 292145484615⟩) 24716235638 43500686443)⟩)
          (.row ⟨115752966123, 117423580140, (.direct 10180561190 9302456220), (.chord (.midpoint ⟨572707972224, 67145957199, 159509469288, 404422474355, 163389218000, 289529030804⟩) 24716235638 43500686443)⟩))))

set_option maxRecDepth 16000 in
theorem CutTop1H0NegPart2_checked : CutTop1H0NegPart2Tree.commonOK CutTop1H0NegPart2Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
