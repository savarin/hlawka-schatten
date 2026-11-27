/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H7NegPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H7NegPart0Box : Box := (((⟨![63/136, 19/100, 0, -8], ![9/17, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutTop4H7NegPart0Tree : CertTree :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.cut 3 (-13/2)
            (.row ⟨123862991199, 126950446638, (.direct 5340438828596 4777489351785), (.variance 130143691457)⟩)
            (.row ⟨123862991199, 126950446638, (.direct 3523554676644 3137584503365), (.variance 145291126658)⟩))
          (.row ⟨123862991199, 126950446638, (.direct 824633666698 712324780632), (.variance 214216297194)⟩))
        (.cut 3 (-5)
          (.cut 3 (-13/2)
            (.row ⟨123862991199, 126950446638, (.direct 5340438828596 4777489351785), (.variance 130143691457)⟩)
            (.row ⟨123862991199, 126950446638, (.direct 3523554676644 3137584503365), (.variance 145291126658)⟩))
          (.cut 3 (-7/2)
            (.row ⟨123862991199, 126950446638, (.direct 2002014560937 1767406687117), (.variance 168853068621)⟩)
            (.row ⟨123862991199, 126950446638, (.direct 824633666698 712324780632), (.variance 214216297194)⟩))))
      (.cut 3 (-5)
        (.cut 3 (-13/2)
          (.row ⟨123862991199, 126950446638, (.direct 5340438828596 4777489351785), (.variance 130143691457)⟩)
          (.row ⟨123862991199, 126950446638, (.direct 3523554676644 3137584503365), (.variance 145291126658)⟩))
        (.cut 3 (-7/2)
          (.row ⟨123862991199, 126950446638, (.direct 2002014560937 1767406687117), (.variance 168853068621)⟩)
          (.row ⟨123862991199, 126950446638, (.direct 824633666698 712324780632), (.variance 214216297194)⟩))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.row ⟨123862991199, 126950446638, (.direct 30541785600 17585057964), (.variance 564675750160)⟩)
        (.cut 3 (-9/8)
          (.row ⟨123862991199, 126950446638, (.direct 331294831298 274877906944), (.variance 274877906944)⟩)
          (.cut 3 (-11/16)
            (.row ⟨123862991199, 126950446638, (.direct 151782739331 118546014691), (.variance 342597982457)⟩)
            (.cut 3 (-15/32)
              (.row ⟨123862991199, 126950446638, (.direct 82716570280 59891013431), (.variance 409668707255)⟩)
              (.cut 2 (5/16)
                (.row ⟨123862991199, 126950446638, (.direct 30541785600 17585057964), (.variance 564675750160)⟩)
                (.cut 3 (-23/64)
                  (.row ⟨123862991199, 126950446638, (.direct 54287234842 36429942350), (.chord (.midpoint ⟨265329708920, 284550116420, 239550656231, 303059434860, 278408747001, 106945794918⟩) 43500686443 91625974997)⟩)
                  (.row ⟨123862991199, 126950446638, (.direct 30541785600 17585057964), (.chord (.midpoint ⟨359167708590, 199214281644, 200790476314, 343490626148, 244082363095, 190047493698⟩) 43500686443 91625974997)⟩)))))))
      (.cut 3 (-9/8)
        (.row ⟨123862991199, 126950446638, (.direct 331294831298 274877906944), (.variance 274877906944)⟩)
        (.cut 3 (-11/16)
          (.row ⟨123862991199, 126950446638, (.direct 151782739331 118546014691), (.variance 342597982457)⟩)
          (.cut 3 (-15/32)
            (.row ⟨123862991199, 126950446638, (.direct 82716570280 59891013431), (.chord (.midpoint ⟨345127508776, 210711928954, 206639873058, 336563146537, 249189759458, 124919151789⟩) 91625974997 274877906944)⟩)
            (.cut 2 (3/4)
              (.row ⟨123862991199, 126950446638, (.direct 30541785600 17585057964), (.chord (.midpoint ⟨417363583850, 155660231445, 176057543494, 377068124648, 222839910280, 218593789705⟩) 91625974997 174227471798)⟩)
              (.row ⟨123862991199, 126950446638, (.direct 30541785600 17585057964), (.chord (.midpoint ⟨447655049755, 135401981945, 162721748509, 398741581931, 211662868327, 265241166538⟩) 174227471798 274877906944)⟩))))))

set_option maxRecDepth 16000 in
theorem CutTop4H7NegPart0_checked : CutTop4H7NegPart0Tree.commonOK CutTop4H7NegPart0Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
