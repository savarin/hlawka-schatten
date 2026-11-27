/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G1CompactDataCore

/-! Exact one-time clearing of the denominators in each compact G1 bin. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G1CompactData

structure IntegerCoefficients where
  a : Int
  b : Int
  c : Int
  den : Int

def intCoefficients (P : G1CompactParams) : IntegerCoefficients :=
  let a := P.k * P.l ^ 2 / P.μ
  let b := P.β
  let c := P.α
  let squareDen : Int := (4096 * 256) ^ 2
  let ordinateDen : Int := 4096 * 2 ^ 36
  { a := a.num * (4096 ^ 2) * (b.den : Int) * c.den * ordinateDen
    b := b.num * squareDen * (a.den : Int) * c.den * ordinateDen
    c := c.num * (a.den : Int) * b.den * ordinateDen
    den := squareDen * (a.den : Int) * b.den * c.den }

def intCorner (l : Nat) (coeff : IntegerCoefficients) (node : Fin 129) : Bool :=
  let x := knotNum node
  let z := (4096 - (l : Int)) * x + 256 * l
  let ord := lowerOrdinates[x.natAbs]?.getD 0
  let rhs := (l : Int) * 2 ^ 36 + (4096 - (l : Int)) * ord
  decide (coeff.a * (x - 256) ^ 2 + coeff.b + coeff.c * z ^ 2 ≤ coeff.den * rhs)

def intBox (l w : Nat) (coeff : IntegerCoefficients) (z : Fin 128) : Bool :=
  !decide (overlapsCompact l w z) ||
    (intCorner l coeff z.castSucc && intCorner l coeff z.succ)

def intBin (i : Fin 13) (right : Bool) (j : Fin 64) : Bool :=
  (List.finRange 128).all (intBox (lengthNum i right) (compactWitness i right j).2.1
    (intCoefficients (compactParams i right j)))

def intSide (i : Fin 13) (right : Bool) : Bool :=
  (List.finRange 64).all (intBin i right)

def intSlab (i : Fin 13) : Bool := intSide i false && intSide i true

end HlawkaSchatten.BelowExponent.G1CompactData
