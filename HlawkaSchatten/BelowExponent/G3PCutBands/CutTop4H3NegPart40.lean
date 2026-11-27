/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H3NegPart40`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H3NegPart40Box : Box := ((((((((((⟨![27/136, 19/100, 0, -8], ![9/34, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).upperChild 3 (0)).upperChild 2 (5/16)).lowerChild 3 (1/8)).upperChild 3 (1/16)

set_option maxRecDepth 16000 in
def CutTop4H3NegPart40Tree : CertTree :=
  .cut 2 (13/32)
    (.cut 3 (3/32)
      (.cut 2 (23/64)
        (.cut 0 (63/272)
          (.row ⟨123862991199, 126950446638, (.direct 6452795533 9176488165), (.chord (.secant 942650508021 17526877821 32672973 26444048106) 43500686443 54287507865)⟩)
          (.row ⟨123862991199, 126950446638, (.direct 6452795533 9593842888), (.chord (.secant 927299405450 14123395158 916620329 28126881322) 43500686443 54287507865)⟩))
        (.cut 0 (63/272)
          (.row ⟨123862991199, 126950446638, (.direct 6452795533 9176488165), (.chord (.secant 909321720413 10470947341 1042384829 21773865813) 54287507865 65931360876)⟩)
          (.row ⟨123862991199, 126950446638, (.direct 6452795533 9593842888), (.chord (.secant 893238070746 7539195226 2751364818 23159500285) 54287507865 65931360876)⟩)))
      (.cut 2 (23/64)
        (.row ⟨123862991199, 126950446638, (.direct 10180561190 13697503795), (.chord (.secant 1017672982591 37345597964 2286455008 43704226308) 43500686443 54287507865)⟩)
        (.row ⟨123862991199, 126950446638, (.direct 10180561190 13697503795), (.chord (.secant 973597476508 25103610127 266511400 35985789894) 54287507865 65931360876)⟩)))
    (.cut 3 (3/32)
      (.cut 0 (63/272)
        (.row ⟨123862991199, 126950446638, (.direct 6452795533 9176488165), (.chord (.secant 883986699218 6011198509 3837630004 15667818430) 65931360876 91625974997)⟩)
        (.cut 2 (29/64)
          (.row ⟨123862991199, 126950446638, (.direct 6452795533 9593842888), (.chord (.secant 867358504921 3590260773 4672244118 19478820881) 65931360876 78389578142)⟩)
          (.row ⟨123862991199, 126950446638, (.direct 6452795533 9593842888), (.chord (.secant 847033674881 1299129987 6493080168 16664879287) 78389578142 91625974997)⟩)))
      (.row ⟨123862991199, 126950446638, (.direct 10180561190 13697503795), (.chord (.secant 940185755629 16963702132 1635437001 25894291209) 65931360876 91625974997)⟩))

set_option maxRecDepth 16000 in
theorem CutTop4H3NegPart40_checked : CutTop4H3NegPart40Tree.commonOK CutTop4H3NegPart40Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
