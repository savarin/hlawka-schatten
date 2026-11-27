/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Fin.VecNotation

/-! Exact fifth-root bounds for the normalized VC and SC coefficient cells. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

structure RatBounds where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq, Repr

def RatBounds.point (q : ℚ) : RatBounds := ⟨q,q⟩

def RatBounds.add (a b : RatBounds) : RatBounds := ⟨a.lo+b.lo,a.hi+b.hi⟩

def RatBounds.sub (a b : RatBounds) : RatBounds := ⟨a.lo-b.hi,a.hi-b.lo⟩

def RatBounds.mul (a b : RatBounds) : RatBounds :=
  ⟨min (min (a.lo*b.lo) (a.lo*b.hi)) (min (a.hi*b.lo) (a.hi*b.hi)),
   max (max (a.lo*b.lo) (a.lo*b.hi)) (max (a.hi*b.lo) (a.hi*b.hi))⟩

structure ParameterCell where
  a : RatBounds
  b : RatBounds
  η : RatBounds
  deriving DecidableEq, Repr

def ParameterCell.direction (c : ParameterCell) : Fin 3 → RatBounds :=
  ![c.a,c.b,((RatBounds.point 1).sub c.a).sub c.b]

def ParameterCell.depth (c : ParameterCell) : RatBounds :=
  ⟨c.η.lo/(1+2*c.η.lo),c.η.hi/(1+2*c.η.hi)⟩

def ParameterCell.base (c : ParameterCell) (j : Fin 3) : RatBounds :=
  let one := RatBounds.point 1
  ((one.sub c.depth).mul (one.sub (c.direction j))).add
    (c.depth.mul ((c.direction (j+1)).mul (c.direction (j+2))))

def ParameterCell.other (c : ParameterCell) (j : Fin 3) : RatBounds :=
  (RatBounds.point 1).sub (c.depth.mul (c.direction j))

def ParameterCell.sigma (c : ParameterCell) : RatBounds :=
  let e := c.direction
  (((e 0).mul (e 1)).add ((e 0).mul (e 2))).add ((e 1).mul (e 2))

/-- The radicand is A² B³/S². The bounds are checked by cross multiplication. -/
def rootBoundsOK (A B S R : RatBounds) : Bool :=
  decide (0 ≤ A.lo ∧ 0 ≤ B.lo ∧ 0 < S.lo ∧ 0 ≤ R.lo ∧ R.lo ≤ R.hi ∧
    R.lo^5 * S.hi^2 ≤ A.lo^2 * B.lo^3 ∧ A.hi^2 * B.hi^3 ≤ R.hi^5 * S.lo^2)

def ParameterCell.rootsOK (c : ParameterCell) (roots : Fin 3 → RatBounds) : Bool :=
  decide (0 ≤ c.η.lo) && (List.finRange 3).all (fun j =>
    rootBoundsOK (c.base j) (c.other j) c.sigma (roots j))

end HlawkaSchatten.BelowExponent.Vertex
