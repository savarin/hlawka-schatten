/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H2NegPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H2NegPart0Box : Box := (((⟨![9/34, 11/100, 0, -8], ![27/68, 13/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutMid3H2NegPart0Tree : CertTree :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.row ⟨95281442640, 103236350716, (.direct 3523554676644 3340395442726), (.variance 142927558602)⟩)
          (.row ⟨95281442640, 103236350716, (.direct 824633666698 771179020422), (.variance 209809172087)⟩))
        (.cut 3 (-5)
          (.row ⟨95281442640, 103236350716, (.direct 3523554676644 3340395442726), (.variance 142927558602)⟩)
          (.cut 3 (-7/2)
            (.row ⟨95281442640, 103236350716, (.direct 2002014560937 1890587928749), (.variance 165900219039)⟩)
            (.row ⟨95281442640, 103236350716, (.direct 824633666698 771179020422), (.variance 209809172087)⟩))))
      (.cut 3 (-5)
        (.row ⟨95281442640, 103236350716, (.direct 3523554676644 3340395442726), (.variance 142927558602)⟩)
        (.cut 3 (-7/2)
          (.row ⟨95281442640, 103236350716, (.direct 2002014560937 1890587928749), (.variance 165900219039)⟩)
          (.row ⟨95281442640, 103236350716, (.direct 824633666698 771179020422), (.variance 209809172087)⟩))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.row ⟨95281442640, 103236350716, (.direct 30541785600 24136081652), (.variance 519741543711)⟩)
        (.cut 3 (-9/8)
          (.row ⟨95281442640, 103236350716, (.direct 331294831298 304337817470), (.variance 267646520798)⟩)
          (.cut 3 (-11/16)
            (.row ⟨95281442640, 103236350716, (.direct 151782739331 135809783307), (.variance 330615749578)⟩)
            (.cut 0 (45/136)
              (.cut 3 (-15/32)
                (.row ⟨95281442640, 103236350716, (.direct 82716570280 73468910141), (.variance 388324565731)⟩)
                (.cut 0 (81/272)
                  (.cut 1 (3/25)
                    (.row ⟨95281442640, 99345187400, (.direct 30541785600 26070902892), (.variance 509351906931)⟩)
                    (.row ⟨99345187399, 103236350716, (.direct 30541785600 25685184373), (.variance 511343870232)⟩))
                  (.cut 1 (3/25)
                    (.row ⟨95281442640, 99345187400, (.direct 30541785600 25590367042), (.variance 511839320094)⟩)
                    (.row ⟨99345187399, 103236350716, (.direct 30541785600 25164869054), (.variance 514091549917)⟩))))
              (.cut 0 (99/272)
                (.cut 3 (-15/32)
                  (.row ⟨95281442640, 103236350716, (.direct 82716570280 72566502806), (.variance 389583335304)⟩)
                  (.cut 1 (3/25)
                    (.row ⟨95281442640, 99345187400, (.direct 30541785600 25113138675), (.variance 514368641730)⟩)
                    (.row ⟨99345187399, 103236350716, (.direct 30541785600 24648494329), (.variance 516890228737)⟩)))
                (.cut 3 (-15/32)
                  (.row ⟨95281442640, 103236350716, (.direct 82716570280 71668218297), (.variance 390856126062)⟩)
                  (.cut 1 (3/25)
                    (.row ⟨95281442640, 99345187400, (.direct 30541785600 24639234136), (.variance 516941091437)⟩)
                    (.row ⟨99345187399, 103236350716, (.direct 30541785600 24136081652), (.variance 519741543711)⟩))))))))
      (.cut 3 (-9/8)
        (.row ⟨95281442640, 103236350716, (.direct 331294831298 304337817470), (.variance 267646520798)⟩)
        (.cut 3 (-11/16)
          (.row ⟨95281442640, 103236350716, (.direct 151782739331 135809783307), (.variance 330615749578)⟩)
          (.cut 3 (-15/32)
            (.row ⟨95281442640, 103236350716, (.direct 82716570280 71668218297), (.variance 390856126062)⟩)
            (.cut 3 (-23/64)
              (.row ⟨95281442640, 103236350716, (.direct 54287234842 45582039245), (.variance 440028630859)⟩)
              (.row ⟨95281442640, 103236350716, (.direct 30541785600 24136081652), (.chord (.midpoint ⟨533659749006, 85942381538, 148207708265, 426068890135, 178971271016, 262802438137⟩) 91625974997 274877906944)⟩))))))

set_option maxRecDepth 16000 in
theorem CutMid3H2NegPart0_checked : CutMid3H2NegPart0Tree.commonOK CutMid3H2NegPart0Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
