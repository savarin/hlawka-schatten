/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H5NegRestPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H5NegRestPart0Box : Box := (((⟨![45/136, 19/100, 0, -8], ![27/68, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutTop4H5NegRestPart0Tree : RatioRemainder :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.cut 3 (-13/2)
            (.original (.row ⟨123862991199, 126950446638, (.direct 5340438828596 4916064237281), (.variance 129172910217)⟩))
            (.original (.row ⟨123862991199, 126950446638, (.direct 3523554676644 3232530974750), (.variance 144161328916)⟩)))
          (.original (.row ⟨123862991199, 126950446638, (.direct 824633666698 739832218923), (.variance 212101443382)⟩)))
        (.cut 3 (-5)
          (.cut 3 (-13/2)
            (.original (.row ⟨123862991199, 126950446638, (.direct 5340438828596 4916064237281), (.variance 129172910217)⟩))
            (.original (.row ⟨123862991199, 126950446638, (.direct 3523554676644 3232530974750), (.variance 144161328916)⟩)))
          (.cut 3 (-7/2)
            (.original (.row ⟨123862991199, 126950446638, (.direct 2002014560937 1825047468614), (.variance 167440032438)⟩))
            (.original (.row ⟨123862991199, 126950446638, (.direct 824633666698 739832218923), (.variance 212101443382)⟩)))))
      (.cut 3 (-5)
        (.cut 3 (-13/2)
          (.original (.row ⟨123862991199, 126950446638, (.direct 5340438828596 4916064237281), (.variance 129172910217)⟩))
          (.original (.row ⟨123862991199, 126950446638, (.direct 3523554676644 3232530974750), (.variance 144161328916)⟩)))
        (.cut 3 (-7/2)
          (.original (.row ⟨123862991199, 126950446638, (.direct 2002014560937 1825047468614), (.variance 167440032438)⟩))
          (.original (.row ⟨123862991199, 126950446638, (.direct 824633666698 739832218923), (.variance 212101443382)⟩)))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.original (.row ⟨123862991199, 126950446638, (.direct 30541785600 20575579627), (.variance 541923703492)⟩))
        (.cut 3 (-9/8)
          (.original (.row ⟨123862991199, 126950446638, (.direct 331294831298 288616580942), (.variance 271389695945)⟩))
          (.cut 3 (-11/16)
            (.original (.row ⟨123862991199, 126950446638, (.direct 151782739331 126569910114), (.variance 336772479601)⟩))
            (.cut 3 (-15/32)
              (.original (.row ⟨123862991199, 126950446638, (.direct 82716570280 65341283274), (.variance 400430999791)⟩))
              (.cut 2 (5/16)
                (.original (.row ⟨123862991199, 126950446638, (.direct 30541785600 20575579627), (.variance 541923703492)⟩))
                (.cut 3 (-23/64)
                  (.original (.row ⟨123862991199, 126950446638, (.direct 54287234842 40646629456), (.chord (.midpoint ⟨306135129102, 244880950267, 234874430188, 307328178045, 263401358271, 126734397499⟩) 43500686443 91625974997)⟩))
                  (.covered)))))))
      (.cut 3 (-9/8)
        (.original (.row ⟨123862991199, 126950446638, (.direct 331294831298 288616580942), (.variance 271389695945)⟩))
        (.cut 3 (-11/16)
          (.original (.row ⟨123862991199, 126950446638, (.direct 151782739331 126569910114), (.variance 336772479601)⟩))
          (.cut 3 (-15/32)
            (.cut 2 (3/4)
              (.original (.row ⟨123862991199, 126950446638, (.direct 82716570280 65341283274), (.chord (.midpoint ⟨333872690323, 220227968260, 223867727646, 317974004802, 253285443411, 147537315988⟩) 91625974997 174227471798)⟩))
              (.covered))
            (.covered)))))

set_option maxRecDepth 16000 in
theorem CutTop4H5NegRestPart0_ok : CutTop4H5NegRestPart0Tree.ok CutTop4H5NegRestPart0Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
