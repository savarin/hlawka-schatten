/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H5NegPart29`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H5NegPart29Box : Box := (((((((((⟨![45/136, 9/50, 0, -8], ![27/68, 19/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).upperChild 3 (0)).upperChild 2 (5/16)).upperChild 3 (1/8)

set_option maxRecDepth 16000 in
def CutTop3H5NegPart29Tree : CertTree :=
  .cut 2 (13/32)
    (.cut 3 (3/16)
      (.cut 3 (5/32)
        (.cut 2 (23/64)
          (.row ⟨120689819474, 123862991200, (.direct 14500097491 20003609075), (.chord (.secant 1016141298859 36894197379 1085328144 71481093624) 43500686443 54287507865)⟩)
          (.row ⟨120689819474, 123862991200, (.direct 14500097491 20003609075), (.chord (.secant 960325508749 21743015541 509056831 58857090809) 54287507865 65931360876)⟩))
        (.row ⟨120689819474, 123862991200, (.direct 19358451269 25186201612), (.chord (.secant 1084612431411 58686992063 2813052386 78240415891) 43500686443 65931360876)⟩))
      (.cut 3 (7/32)
        (.row ⟨120689819474, 123862991200, (.direct 24716051037 30796556727), (.chord (.secant 1154717541011 83997861973 10824223683 99587013679) 43500686443 65931360876)⟩)
        (.row ⟨120689819474, 123862991200, (.direct 30541785600 36812648456), (.chord (.secant 1226430037943 112507738328 22184927010 122776050106) 43500686443 65931360876)⟩)))
    (.cut 3 (3/16)
      (.cut 2 (29/64)
        (.row ⟨120689819474, 123862991200, (.direct 19358451269 25186201612), (.chord (.secant 968813573175 23873753096 3014890478 49503085790) 65931360876 78389578142)⟩)
        (.row ⟨120689819474, 123862991200, (.direct 19358451269 25186201612), (.chord (.secant 930010946553 14706213074 6026304507 42351790905) 78389578142 91625974997)⟩))
      (.row ⟨120689819474, 123862991200, (.direct 30541785600 36812648456), (.chord (.secant 1073040377778 54784962194 1123661303 71659817403) 65931360876 91625974997)⟩))

set_option maxRecDepth 16000 in
theorem CutTop3H5NegPart29_checked : CutTop3H5NegPart29Tree.commonOK CutTop3H5NegPart29Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
