/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H6NegPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H6NegPart0Box : Box := (((⟨![27/68, 9/50, 0, -8], ![63/136, 19/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutTop3H6NegPart0Tree : CertTree :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.cut 3 (-13/2)
            (.row ⟨120689819474, 123862991200, (.direct 5340438828596 4873417665484), (.variance 129467953751)⟩)
            (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3203306558382), (.variance 144504571388)⟩))
          (.row ⟨120689819474, 123862991200, (.direct 824633666698 731356754041), (.variance 212742344158)⟩))
        (.cut 3 (-5)
          (.cut 3 (-13/2)
            (.row ⟨120689819474, 123862991200, (.direct 5340438828596 4873417665484), (.variance 129467953751)⟩)
            (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3203306558382), (.variance 144504571388)⟩))
          (.cut 3 (-7/2)
            (.row ⟨120689819474, 123862991200, (.direct 2002014560937 1807300549809), (.variance 167869021275)⟩)
            (.row ⟨120689819474, 123862991200, (.direct 824633666698 731356754041), (.variance 212742344158)⟩))))
      (.cut 3 (-5)
        (.cut 3 (-13/2)
          (.row ⟨120689819474, 123862991200, (.direct 5340438828596 4873417665484), (.variance 129467953751)⟩)
          (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3203306558382), (.variance 144504571388)⟩))
        (.cut 3 (-7/2)
          (.row ⟨120689819474, 123862991200, (.direct 2002014560937 1807300549809), (.variance 167869021275)⟩)
          (.row ⟨120689819474, 123862991200, (.direct 824633666698 731356754041), (.variance 212742344158)⟩))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.row ⟨120689819474, 123862991200, (.direct 30541785600 19640228804), (.variance 548566345757)⟩)
        (.cut 3 (-9/8)
          (.row ⟨120689819474, 123862991200, (.direct 331294831298 284377627551), (.variance 272443217095)⟩)
          (.cut 3 (-11/16)
            (.row ⟨120689819474, 123862991200, (.direct 151782739331 124088951440), (.variance 338522777001)⟩)
            (.cut 3 (-15/32)
              (.row ⟨120689819474, 123862991200, (.direct 82716570280 63651474217), (.variance 403187855506)⟩)
              (.cut 2 (5/16)
                (.row ⟨120689819474, 123862991200, (.direct 30541785600 19640228804), (.variance 548566345757)⟩)
                (.cut 3 (-23/64)
                  (.row ⟨120689819474, 123862991200, (.direct 54287234842 39335586627), (.chord (.midpoint ⟨282055190062, 267769133415, 238598005020, 303917465723, 272232545584, 113765781052⟩) 43500686443 91625974997)⟩)
                  (.row ⟨120689819474, 123862991200, (.direct 30541785600 19640228804), (.chord (.midpoint ⟨378927733344, 183705898027, 199259939336, 345360511648, 236889619206, 195317492868⟩) 43500686443 91625974997)⟩)))))))
      (.cut 3 (-9/8)
        (.row ⟨120689819474, 123862991200, (.direct 331294831298 284377627551), (.variance 272443217095)⟩)
        (.cut 3 (-11/16)
          (.row ⟨120689819474, 123862991200, (.direct 151782739331 124088951440), (.variance 338522777001)⟩)
          (.cut 3 (-15/32)
            (.row ⟨120689819474, 123862991200, (.direct 82716570280 63651474217), (.variance 403187855506)⟩)
            (.cut 2 (3/4)
              (.row ⟨120689819474, 123862991200, (.direct 30541785600 19640228804), (.chord (.midpoint ⟨442636594000, 138650703924, 172481894726, 382597710012, 213523182771, 225828228806⟩) 91625974997 174227471798)⟩)
              (.row ⟨120689819474, 123862991200, (.direct 30541785600 19640228804), (.chord (.midpoint ⟨475842531314, 117920228738, 157926620499, 407294239262, 201134606033, 273051407234⟩) 174227471798 274877906944)⟩))))))

set_option maxRecDepth 16000 in
theorem CutTop3H6NegPart0_checked : CutTop3H6NegPart0Tree.commonOK CutTop3H6NegPart0Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
