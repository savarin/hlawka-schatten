/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H2NegPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H2NegPart0Box : Box := (((⟨![9/68, 3/20, 0, -8], ![27/136, 4/25, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutTop0H2NegPart0Tree : CertTree :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3408590994373), (.variance 142173176149)⟩)
          (.row ⟨110576703734, 114055813620, (.direct 824633666698 791048230190), (.variance 208416237902)⟩))
        (.cut 3 (-5)
          (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3408590994373), (.variance 142173176149)⟩)
          (.row ⟨110576703734, 114055813620, (.direct 824633666698 791048230190), (.variance 208416237902)⟩)))
      (.cut 3 (-5)
        (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3408590994373), (.variance 142173176149)⟩)
        (.cut 3 (-7/2)
          (.row ⟨110576703734, 114055813620, (.direct 2002014560937 1932054880402), (.variance 164960363142)⟩)
          (.row ⟨110576703734, 114055813620, (.direct 824633666698 791048230190), (.variance 208416237902)⟩))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.row ⟨110576703734, 114055813620, (.direct 30541785600 26470350539), (.variance 507327863227)⟩)
        (.cut 3 (-9/8)
          (.row ⟨110576703734, 114055813620, (.direct 331294831298 314336516783), (.variance 265390536791)⟩)
          (.cut 3 (-11/16)
            (.row ⟨110576703734, 114055813620, (.direct 151782739331 141716212328), (.variance 326950610460)⟩)
            (.cut 3 (-15/32)
              (.row ⟨110576703734, 114055813620, (.direct 82716570280 75738290053), (.variance 385243396400)⟩)
              (.cut 2 (5/16)
                (.row ⟨110576703734, 114055813620, (.direct 30541785600 26470350539), (.variance 507327863227)⟩)
                (.cut 3 (-23/64)
                  (.row ⟨110576703734, 114055813620, (.direct 54287234842 48777094939), (.variance 432291260172)⟩)
                  (.row ⟨110576703734, 114055813620, (.direct 30541785600 26470350539), (.chord (.midpoint ⟨474286142538, 118852195755, 188140633470, 359721211181, 201719841738, 222769440717⟩) 43500686443 91625974997)⟩)))))))
      (.cut 3 (-9/8)
        (.row ⟨110576703734, 114055813620, (.direct 331294831298 314336516783), (.variance 265390536791)⟩)
        (.cut 3 (-11/16)
          (.row ⟨110576703734, 114055813620, (.direct 151782739331 141716212328), (.variance 326950610460)⟩)
          (.cut 3 (-15/32)
            (.row ⟨110576703734, 114055813620, (.direct 82716570280 75738290053), (.variance 385243396400)⟩)
            (.cut 2 (3/4)
              (.row ⟨110576703734, 114055813620, (.direct 30541785600 26470350539), (.chord (.midpoint ⟨557951431137, 73991021193, 153836679434, 414947801037, 169349205580, 257690272195⟩) 91625974997 174227471798)⟩)
              (.row ⟨110576703734, 114055813620, (.direct 30541785600 26470350539), (.chord (.midpoint ⟨601638356832, 54622489874, 134480252920, 456488585058, 151403764578, 305439444903⟩) 174227471798 274877906944)⟩))))))

set_option maxRecDepth 16000 in
theorem CutTop0H2NegPart0_checked : CutTop0H2NegPart0Tree.commonOK CutTop0H2NegPart0Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
