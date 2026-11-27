/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H1NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid1H1NegRestPart2`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid1H1NegRestPart2Box : Box := ((((((⟨![9/68, 7/100, 0, -8], ![9/34, 9/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutMid1H1NegRestPart2Tree : RatioRemainder :=
  .cut 2 (5/16)
    (.cut 2 (7/32)
      (.cut 3 (0)
        (.cut 1 (2/25)
          (.cut 1 (3/40)
            (.cut 2 (11/64)
              (.cut 3 (-1/8)
                (.original (.row ⟨76698504228, 79281022314, (.direct 10180561190 8724141326), (.variance 678445119678)⟩))
                (.covered))
              (.cut 3 (-1/8)
                (.original (.row ⟨76698504228, 79281022314, (.direct 10180561190 8724141326), (.chord (.midpoint ⟨441912313395, 139123041135, 200791846830, 343488962686, 213791359008, 140023191382⟩) 16864782083 24716235638)⟩))
                (.covered)))
            (.cut 3 (-1/8)
              (.original (.row ⟨79281022313, 81775466253, (.direct 10180561190 8626098130), (.variance 680455936934)⟩))
              (.covered)))
          (.cut 3 (-1/8)
            (.cut 0 (27/136)
              (.original (.row ⟨81775466252, 86531900009, (.direct 10180561190 8855983343), (.variance 675785615917)⟩))
              (.original (.row ⟨81775466252, 86531900009, (.direct 10180561190 8429717858), (.variance 684571726439)⟩)))
            (.covered)))
        (.cut 3 (1/8)
          (.cut 1 (2/25)
            (.cut 3 (1/16)
              (.covered)
              (.cut 3 (3/32)
                (.covered)
                (.original (.row ⟨76698504228, 81775466253, (.direct 10180561190 11454296155), (.chord (.secant 1522615797730 251242396844 18749005654 77113646728) 10180665226 24716235638)⟩))))
            (.cut 3 (1/16)
              (.covered)
              (.cut 3 (3/32)
                (.covered)
                (.cut 2 (11/64)
                  (.original (.row ⟨81775466252, 86531900009, (.direct 10180561190 11625075029), (.chord (.secant 1530905511417 255514684593 42912244029 114198617533) 10180665226 16864782083)⟩))
                  (.covered)))))
          (.cut 2 (11/64)
            (.cut 3 (3/16)
              (.cut 3 (5/32)
                (.original (.row ⟨76698504228, 86531900009, (.direct 14500097491 16078409073), (.chord (.secant 1738528283073 367869576342 87880425814 174857605888) 10180665226 16864782083)⟩))
                (.original (.row ⟨76698504228, 86531900009, (.direct 19358451269 21043030001), (.chord (.secant 1955737086522 494646621234 144999352791 246121546667) 10180665226 16864782083)⟩)))
              (.original (.row ⟨76698504228, 86531900009, (.direct 30541785600 32373100089), (.variance 545959776953)⟩)))
            (.cut 3 (3/16)
              (.original (.row ⟨76698504228, 86531900009, (.direct 19358451269 21043030001), (.chord (.secant 1582594252014 282549738697 46499454903 119311531382) 16864782083 24716235638)⟩))
              (.original (.row ⟨76698504228, 86531900009, (.direct 30541785600 32373100089), (.chord (.secant 1891328252992 456199824337 125659929174 222434980563) 16864782083 24716235638)⟩))))))
      (.cut 3 (0)
        (.cut 1 (2/25)
          (.cut 3 (-1/8)
            (.original (.row ⟨76698504228, 81775466253, (.direct 10180561190 8626098130), (.chord (.midpoint ⟨526750202479, 89499225194, 166970160263, 391516237856, 181670069051, 207798072906⟩) 24716235638 43500686443)⟩))
            (.covered))
          (.cut 3 (-1/8)
            (.original (.row ⟨81775466252, 86531900009, (.direct 10180561190 8429717858), (.chord (.midpoint ⟨529631639240, 88007389050, 165776879971, 393513683096, 180546512239, 208597445250⟩) 24716235638 43500686443)⟩))
            (.covered)))
        (.cut 3 (1/8)
          (.covered)
          (.cut 3 (3/16)
            (.covered)
            (.original (.row ⟨76698504228, 86531900009, (.direct 30541785600 32373100089), (.chord (.secant 1612414205281 298444617089 51536523009 126382965575) 24716235638 43500686443)⟩))))))
    (.covered)

set_option maxRecDepth 16000 in
theorem CutMid1H1NegRestPart2_ok : CutMid1H1NegRestPart2Tree.geometryOK CutMid1H1NegPowerCache CutMid1H1NegRestPart2Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
