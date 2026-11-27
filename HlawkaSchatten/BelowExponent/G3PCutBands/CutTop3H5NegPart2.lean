/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H5NegPart2`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H5NegPart2Box : Box := ((((((((⟨![45/136, 9/50, 0, -8], ![27/68, 19/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 3 (0)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutTop3H5NegPart2Tree : CertTree :=
  .cut 2 (5/16)
    (.cut 2 (7/32)
      (.cut 3 (-3/16)
        (.row ⟨120689819474, 123862991200, (.direct 19358451269 11909793461), (.variance 625339902688)⟩)
        (.row ⟨120689819474, 123862991200, (.direct 10180561190 4831916512), (.chord (.midpoint ⟨422750782491, 151942183369, 188034661948, 359865038452, 220860459924, 164055286734⟩) 10180665226 24716235638)⟩))
      (.cut 3 (-3/16)
        (.row ⟨120689819474, 123862991200, (.direct 19358451269 11909793461), (.chord (.midpoint ⟨380397252619, 182583038579, 205275428952, 338148866655, 236354193759, 213087109985⟩) 24716235638 43500686443)⟩)
        (.row ⟨120689819474, 123862991200, (.direct 10180561190 4831916512), (.chord (.midpoint ⟨478748776951, 116190212295, 164419167718, 395816478006, 200040444393, 262365531506⟩) 24716235638 43500686443)⟩)))
    (.cut 3 (-3/16)
      (.cut 0 (99/272)
        (.row ⟨120689819474, 123862991200, (.direct 19358451269 12478876827), (.chord (.midpoint ⟨460535369525, 127254065202, 172231550184, 382992199672, 206869728056, 269523019058⟩) 43500686443 91625974997)⟩)
        (.row ⟨120689819474, 123862991200, (.direct 19358451269 11909793461), (.chord (.midpoint ⟨447512031438, 135493985735, 174082856750, 380097889103, 211715937657, 266248054708⟩) 43500686443 91625974997)⟩))
      (.cut 2 (13/32)
        (.cut 0 (99/272)
          (.row ⟨120689819474, 123862991200, (.direct 10180561190 5220603515), (.chord (.midpoint ⟨504700277051, 101324777452, 153007985153, 416541081451, 190184463596, 299867363094⟩) 43500686443 65931360876)⟩)
          (.row ⟨120689819474, 123862991200, (.direct 10180561190 4831916512), (.chord (.midpoint ⟨491964577577, 108490007701, 154688940514, 413324442090, 195041448440, 296733709279⟩) 43500686443 65931360876)⟩))
        (.cut 0 (99/272)
          (.row ⟨120689819474, 123862991200, (.direct 10180561190 5220603515), (.chord (.midpoint ⟨525493539675, 90153692930, 143576936169, 435773914366, 182159244446, 316148135171⟩) 65931360876 91625974997)⟩)
          (.row ⟨120689819474, 123862991200, (.direct 10180561190 4831916512), (.chord (.midpoint ⟨511576586922, 97558707686, 145789994174, 431070117602, 187544330216, 312709945660⟩) 65931360876 91625974997)⟩))))

set_option maxRecDepth 16000 in
theorem CutTop3H5NegPart2_checked : CutTop3H5NegPart2Tree.commonOK CutTop3H5NegPart2Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
