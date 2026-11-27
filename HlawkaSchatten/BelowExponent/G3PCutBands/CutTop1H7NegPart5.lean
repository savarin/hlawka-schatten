/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H7NegPart5`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H7NegPart5Box : Box := ((((((((((⟨![63/136, 4/25, 0, -8], ![9/17, 17/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 3 (0)).upperChild 3 (-1/8)).upperChild 2 (5/16)).lowerChild 3 (-1/16)

set_option maxRecDepth 16000 in
def CutTop1H7NegPart5Tree : CertTree :=
  .cut 0 (135/272)
    (.cut 2 (13/32)
      (.cut 3 (-3/32)
        (.row ⟨114055813619, 117423580140, (.direct 6452795533 1898267526), (.chord (.midpoint ⟨484623240104, 112733825817, 145802352812, 431044192599, 197823243708, 313012743410⟩) 43500686443 65931360876)⟩)
        (.row ⟨114055813619, 117423580140, (.direct 3393509060 299495063), (.chord (.midpoint ⟨524620487107, 90609753585, 126369659073, 477087322271, 182498799250, 326868836447⟩) 43500686443 65931360876)⟩))
      (.row ⟨114055813619, 117423580140, (.direct 3393509060 299495063), (.chord (.midpoint ⟨528073573953, 88812540123, 124620670916, 481828358470, 181154380727, 321558621256⟩) 65931360876 91625974997)⟩))
    (.cut 2 (13/32)
      (.cut 1 (33/200)
        (.row ⟨114055813619, 115752966124, (.direct 3393509060 245565111), (.chord (.midpoint ⟨508578626819, 99191869538, 129859835173, 467953728028, 188696985923, 309667019451⟩) 43500686443 65931360876)⟩)
        (.row ⟨115752966123, 117423580140, (.direct 3393509060 193168660), (.chord (.midpoint ⟨510834838968, 97961519528, 128727645110, 470870193575, 187829751688, 310448237015⟩) 43500686443 65931360876)⟩))
      (.row ⟨114055813619, 117423580140, (.direct 3393509060 193168660), (.chord (.midpoint ⟨513426967180, 96557451798, 127420402510, 474292612101, 186831631514, 317930283081⟩) 65931360876 91625974997)⟩))

set_option maxRecDepth 16000 in
theorem CutTop1H7NegPart5_checked : CutTop1H7NegPart5Tree.commonOK CutTop1H7NegPart5Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
