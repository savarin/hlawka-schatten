/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G1CompactIntegerBlocks
public import HlawkaSchatten.BelowExponent.G1CompactOrdinateTable
public import HlawkaSchatten.BelowExponent.Vertex.IntegerKernel

/-! Compact G1 checks with the same traversal and kernel integer arithmetic. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G1CompactData

open Vertex

/-- The bias preserves the negative centre ordinate; invalid indices keep the old zero default. -/
noncomputable def lowerOrdinateKernel (n : Nat) : Int :=
  bif Nat.ble n 64 then
    Int.sub_k (Int.ofNat (Nat.land
      (Nat.shiftRight packedLowerOrdinates (compactOrdinateBits * n))
      (2 ^ compactOrdinateBits - 1))) (Int.ofNat compactOrdinateBias)
  else 0

noncomputable def intCoefficientsKernel (P : G1CompactParams) : IntegerCoefficients :=
  let a := P.k * P.l ^ 2 / P.μ
  let b := P.β
  let c := P.α
  let squareDen : Int := (4096 * 256) ^ 2
  let ordinateDen : Int := 4096 * 2 ^ 36
  { a := Int.mul_k (Int.mul_k (Int.mul_k (Int.mul_k a.num (4096 ^ 2))
      (Int.ofNat b.den)) (Int.ofNat c.den)) ordinateDen
    b := Int.mul_k (Int.mul_k (Int.mul_k (Int.mul_k b.num squareDen)
      (Int.ofNat a.den)) (Int.ofNat c.den)) ordinateDen
    c := Int.mul_k (Int.mul_k (Int.mul_k c.num (Int.ofNat a.den))
      (Int.ofNat b.den)) ordinateDen
    den := Int.mul_k (Int.mul_k (Int.mul_k squareDen (Int.ofNat a.den))
      (Int.ofNat b.den)) (Int.ofNat c.den) }

noncomputable def intCornerKernel (l : Nat) (coeff : IntegerCoefficients) (node : Fin 129) : Bool :=
  let x := knotNum node
  let length := Int.ofNat l
  let scale := Int.sub_k 4096 length
  let z := Int.add_k (Int.mul_k scale x) (Int.mul_k 256 length)
  let ord := lowerOrdinateKernel x.natAbs
  let rhs := Int.add_k (Int.mul_k length (2 ^ 36)) (Int.mul_k scale ord)
  let xm := Int.sub_k x 256
  let lhs := Int.add_k (Int.add_k (Int.mul_k coeff.a (Int.mul_k xm xm)) coeff.b)
    (Int.mul_k coeff.c (Int.mul_k z z))
  intNonnegK (Int.sub_k (Int.mul_k coeff.den rhs) lhs)

noncomputable def overlapsCompactKernel (l w : Nat) (node : Fin 128) : Bool :=
  let length := Int.ofNat l
  let scale := Int.sub_k 4096 length
  let shift := Int.mul_k 256 length
  let bound := Int.mul_k 64 (Int.ofNat w)
  let left := Int.add_k (Int.mul_k scale (knotNum node.castSucc)) shift
  let right := Int.add_k (Int.mul_k scale (knotNum node.succ)) shift
  intNonnegK (Int.add_k right bound) && intNonnegK (Int.sub_k bound left)

noncomputable def intBoxKernel (l w : Nat) (coeff : IntegerCoefficients) (z : Fin 128) : Bool :=
  !overlapsCompactKernel l w z ||
    (intCornerKernel l coeff z.castSucc && intCornerKernel l coeff z.succ)

noncomputable def intBinKernel (i : Fin 13) (right : Bool) (j : Fin 64) : Bool :=
  (List.finRange 128).all (intBoxKernel (lengthNum i right) (compactWitness i right j).2.1
    (intCoefficientsKernel (compactParams i right j)))

noncomputable def intSideBlockKernel (i : Fin 13) (right : Bool) (block : Fin 16) : Bool :=
  (List.finRange 4).all fun offset => intBinKernel i right (compactBlockBin block offset)

end HlawkaSchatten.BelowExponent.G1CompactData
