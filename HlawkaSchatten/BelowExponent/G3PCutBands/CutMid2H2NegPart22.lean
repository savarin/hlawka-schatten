/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H2NegPart22`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H2NegPart22Box : Box := (((((⟨![9/34, 9/100, 0, -8], ![27/68, 11/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).upperChild 2 (1/2)

set_option maxRecDepth 16000 in
def CutMid2H2NegPart22Tree : CertTree :=
  .cut 3 (0)
    (.cut 3 (-1/8)
      (.row ⟨86531900008, 95281442641, (.direct 10180561190 7035160075), (.chord (.midpoint ⟨599932283266, 55328313336, 116752699582, 504647309884, 152122900495, 295879007654⟩) 91625974997 274877906944)⟩)
      (.cut 3 (-1/16)
        (.row ⟨86531900008, 95281442641, (.direct 3393509060 1538789231), (.chord (.midpoint ⟨635797865650, 41347859216, 97595179195, 573080096177, 136618349583, 332008258422⟩) 91625974997 274877906944)⟩)
        (.cut 0 (45/136)
          (.row ⟨86531900008, 95281442641, (.direct 0 525173054), (.chord (.secant 681787866565 26061698721 71978582293 6978025724) 91625974997 274877906944)⟩)
          (.row ⟨86531900008, 95281442641, (.direct 0 701135139), (.chord (.secant 646510699050 37521002228 88430826451 6248740456) 91625974997 274877906944)⟩))))
    (.cut 3 (1/8)
      (.cut 3 (1/16)
        (.row ⟨86531900008, 95281442641, (.direct 3393509060 5438924473), (.chord (.secant 762547387046 6741617391 60446293976 263826759) 91625974997 274877906944)⟩)
        (.row ⟨86531900008, 95281442641, (.direct 10180561190 12911777146), (.chord (.secant 841517956482 831534857 45809678785 4453551826) 91625974997 274877906944)⟩))
      (.cut 2 (3/4)
        (.row ⟨86531900008, 95281442641, (.direct 30541785600 33965417195), (.chord (.secant 1007897674076 34495532831 24197183542 18340675193) 91625974997 174227471798)⟩)
        (.row ⟨86531900008, 95281442641, (.direct 30541785600 33965417195), (.chord (.secant 885386672119 6234541697 32727966325 11624961016) 174227471798 274877906944)⟩)))

set_option maxRecDepth 16000 in
theorem CutMid2H2NegPart22_checked : CutMid2H2NegPart22Tree.commonOK CutMid2H2NegPart22Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
