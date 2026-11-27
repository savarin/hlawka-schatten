/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCertBands.Low0H0NegPart0
public import HlawkaSchatten.BelowExponent.G3PCertBands.Low0H0NegPart1
public import HlawkaSchatten.BelowExponent.G3PCertBands.Low0H0NegPart2
public import HlawkaSchatten.BelowExponent.G3PCertBands.Low0H0NegPart3
public import HlawkaSchatten.BelowExponent.G3PCertBands.Low0H0NegPart4
public import HlawkaSchatten.BelowExponent.G3PCertBands.Low0H0NegPart5

/-! Exact joins of the checked central G3 subtrees. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def Low0H0NegBox : Box := ⟨![0, 7/10000, 0, -8], ![9/17, 1/20, 1, 8]⟩

def Low0H0NegTree : CertTree :=
  .cut 3 (3/4)
    (.cut 3 (-1/4)
      (Low0H0NegPart0Tree)
      (.cut 3 (1/4)
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (Low0H0NegPart1Tree)
            (Low0H0NegPart2Tree))
          (Low0H0NegPart3Tree))
        (Low0H0NegPart4Tree)))
    (Low0H0NegPart5Tree)

theorem Low0H0Neg_ok : Low0H0NegTree.ok Low0H0NegBox false = true :=
  CertTree.cut_ok
    (CertTree.cut_ok
      (Low0H0NegPart0_ok)
      (CertTree.cut_ok
        (CertTree.cut_ok
          (CertTree.cut_ok
            (Low0H0NegPart1_ok)
            (Low0H0NegPart2_ok))
          (Low0H0NegPart3_ok))
        (Low0H0NegPart4_ok)))
    (Low0H0NegPart5_ok)

end HlawkaSchatten.BelowExponent.G3P
