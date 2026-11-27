/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Fin.VecNotation

/-! Data and exact signs for an adaptive partition of the \(p=1\) G3 chart. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

/-- The four coordinates are \(h,\sigma,|s|,z\), in that order. -/
structure Box where
  lo : Fin 4 → ℚ
  hi : Fin 4 → ℚ

def root : Box :=
  ⟨![0, 7 / 10000, 0, -8], ![17 / 32, 1 / 5, 1, 8]⟩

def Box.lowerChild (B : Box) (j : Fin 4) (m : ℚ) : Box :=
  ⟨B.lo, fun k => if k = j then m else B.hi k⟩

def Box.upperChild (B : Box) (j : Fin 4) (m : ℚ) : Box :=
  ⟨fun k => if k = j then m else B.lo k, B.hi⟩

/-- Integer numerators of a lower quadratic on a unit interval. The scale is positive. -/
structure Quad where
  a : ℤ
  b : ℤ
  c : ℤ
  scale : ℕ

def Quad.ok (q : Quad) : Bool :=
  decide (0 < q.scale ∧ 0 ≤ q.c ∧ 0 ≤ q.a + q.b + q.c ∧
    (0 < q.a ∧ -2 * q.a < q.b ∧ q.b < 0 → 0 ≤ 4 * q.a * q.c - q.b ^ 2))

inductive Tree where
  | cone
  | box : Quad → Tree
  | cut : Fin 4 → ℚ → Tree → Tree → Tree

def coneBox (B : Box) : Prop := B.hi 2 ≤ 1 / 8 ∧ 3 / 4 ≤ B.lo 3 ∧ B.hi 3 ≤ 5 / 4

instance (B : Box) : Decidable (coneBox B) := by
  unfold coneBox
  infer_instance

def Tree.ok (B : Box) : Tree → Bool
  | .cone => decide (coneBox B)
  | .box q => decide (B.lo 2 < B.hi 2) && q.ok
  | .cut j m lower upper =>
      decide (B.lo j < m ∧ m < B.hi j) &&
        lower.ok (B.lowerChild j m) && upper.ok (B.upperChild j m)

def Tree.numericLeaves (B : Box) : Tree → List (Box × Quad)
  | .cone => []
  | .box q => [(B, q)]
  | .cut j m lower upper =>
      lower.numericLeaves (B.lowerChild j m) ++ upper.numericLeaves (B.upperChild j m)

end HlawkaSchatten.BelowExponent.G3P
