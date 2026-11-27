/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H0NegPart10`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H0NegPart10Box : Box := ((((((((((⟨![0, 11/100, 0, -8], ![9/68, 13/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 2 (5/16)).lowerChild 3 (0)).upperChild 1 (3/25)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutMid3H0NegPart10Tree : CertTree :=
  .cut 1 (1/8)
    (.cut 2 (7/32)
      (.cut 0 (9/136)
        (.row ⟨99345187399, 101311009181, (.direct 10180561190 9547454202), (.chord .universal 10180665226 24716235638)⟩)
        (.row ⟨99345187399, 101311009181, (.direct 10180561190 8929377816), (.chord .universal 10180665226 24716235638)⟩))
      (.cut 3 (-3/16)
        (.row ⟨99345187399, 101311009181, (.direct 19358451269 17672236463), (.chord (.midpoint ⟨486451108388, 111669359723, 197132338247, 348001012481, 197131787673, 227702871141⟩) 24716235638 43500686443)⟩)
        (.cut 0 (9/136)
          (.row ⟨99345187399, 101311009181, (.direct 10180561190 9547454202), (.chord (.midpoint ⟨588115274812, 60329436209, 157060526482, 408886516109, 157059787987, 287018225720⟩) 24716235638 43500686443)⟩)
          (.row ⟨99345187399, 101311009181, (.direct 10180561190 8929377816), (.chord (.midpoint ⟨559367704680, 73320542570, 161138418113, 401517494747, 168781208353, 280217248563⟩) 24716235638 43500686443)⟩))))
    (.cut 2 (7/32)
      (.cut 0 (9/136)
        (.row ⟨101311009180, 103236350716, (.direct 10180561190 9520700696), (.chord .universal 10180665226 24716235638)⟩)
        (.row ⟨101311009180, 103236350716, (.direct 10180561190 8877205668), (.chord .universal 10180665226 24716235638)⟩))
      (.cut 3 (-3/16)
        (.row ⟨101311009180, 103236350716, (.direct 19358451269 17601362690), (.chord (.midpoint ⟨487222818663, 111221512995, 196840184673, 348367402686, 196839632463, 227702871141⟩) 24716235638 43500686443)⟩)
        (.cut 0 (9/136)
          (.row ⟨101311009180, 103236350716, (.direct 10180561190 9520700696), (.chord (.midpoint ⟨588507278057, 60160382876, 156897951584, 409187077472, 156897212488, 287018225720⟩) 24716235638 43500686443)⟩)
          (.row ⟨101311009180, 103236350716, (.direct 10180561190 8877205668), (.chord (.midpoint ⟨560137443871, 72957347525, 160819020844, 402083124894, 168472157759, 280378863312⟩) 24716235638 43500686443)⟩))))

set_option maxRecDepth 16000 in
theorem CutMid3H0NegPart10_checked : CutMid3H0NegPart10Tree.commonOK CutMid3H0NegPart10Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
