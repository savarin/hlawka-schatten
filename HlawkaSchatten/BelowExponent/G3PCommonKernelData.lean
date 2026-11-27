/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen
public import Init.Data.Int.Kernel
public import HlawkaSchatten.BelowExponent.G3PowerCore

/-! Kernel-oriented common interval arithmetic and raw coefficient data. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

noncomputable section

namespace CommonDen.Kernel

def minInt (a b : Int) : Int := Bool.rec b a (Int.ble' a b)

def maxInt (a b : Int) : Int := Bool.rec a b (Int.ble' a b)

def absInt (a : Int) : Int := (Int.natAbs_k a : Int)

def ofBounds (x : Vertex.RatBounds) : CommonDen :=
  Bool.rec ⟨Int.mul_k x.lo.num (Int.ofNat x.hi.den), Int.mul_k x.hi.num (Int.ofNat x.lo.den),
    Nat.mul x.lo.den x.hi.den, Nat.mul_pos x.lo.den_pos x.hi.den_pos⟩
    ⟨x.lo.num, x.hi.num, x.lo.den, x.lo.den_pos⟩
    (Nat.beq x.lo.den x.hi.den)

def add (a b : CommonDen) : CommonDen :=
  Bool.rec ⟨Int.add_k (Int.mul_k a.lo (Int.ofNat b.den)) (Int.mul_k b.lo (Int.ofNat a.den)),
    Int.add_k (Int.mul_k a.hi (Int.ofNat b.den)) (Int.mul_k b.hi (Int.ofNat a.den)),
    Nat.mul a.den b.den, Nat.mul_pos a.den_pos b.den_pos⟩
    ⟨Int.add_k a.lo b.lo, Int.add_k a.hi b.hi, a.den, a.den_pos⟩
    (Nat.beq a.den b.den)

def sub (a b : CommonDen) : CommonDen :=
  Bool.rec ⟨Int.sub_k (Int.mul_k a.lo (Int.ofNat b.den)) (Int.mul_k b.hi (Int.ofNat a.den)),
    Int.sub_k (Int.mul_k a.hi (Int.ofNat b.den)) (Int.mul_k b.lo (Int.ofNat a.den)),
    Nat.mul a.den b.den, Nat.mul_pos a.den_pos b.den_pos⟩
    ⟨Int.sub_k a.lo b.hi, Int.sub_k a.hi b.lo, a.den, a.den_pos⟩
    (Nat.beq a.den b.den)

/-- `0 ≤ x`, read from the sign constructor. -/
def nonnegInt (x : Int) : Bool := Int.rec (motive := fun _ => Bool) (fun _ => true) (fun _ => false) x

/-- `x ≤ 0`, read from the sign constructor. -/
def nonposInt (x : Int) : Bool :=
  Int.rec (motive := fun _ => Bool) (fun n => Nat.beq n 0) (fun _ => true) x

/-- The interval product as the minimum and maximum of its four products (any bounds). -/
def mulGeneral (a b : CommonDen) : CommonDen :=
  let aa := Int.mul_k a.lo b.lo
  let ab := Int.mul_k a.lo b.hi
  let ba := Int.mul_k a.hi b.lo
  let bb := Int.mul_k a.hi b.hi
  ⟨minInt (minInt aa ab) (minInt ba bb), maxInt (maxInt aa ab) (maxInt ba bb),
    Nat.mul a.den b.den, Nat.mul_pos a.den_pos b.den_pos⟩

/-- The interval product of ordered intervals chosen by endpoint signs: two products, unless
both intervals straddle zero (`mul_eq`). -/
def mulOrdered (a b : CommonDen) : CommonDen :=
  Bool.rec
    (Bool.rec
      (Bool.rec
        (Bool.rec (mulGeneral a b)
          ⟨Int.mul_k a.hi b.lo, Int.mul_k a.lo b.lo, Nat.mul a.den b.den,
            Nat.mul_pos a.den_pos b.den_pos⟩
          (nonposInt b.hi))
        ⟨Int.mul_k a.lo b.hi, Int.mul_k a.hi b.hi, Nat.mul a.den b.den,
          Nat.mul_pos a.den_pos b.den_pos⟩
        (nonnegInt b.lo))
      ⟨Int.mul_k (Bool.rec a.hi a.lo (nonnegInt b.hi)) b.hi,
        Int.mul_k (Bool.rec a.lo a.hi (nonnegInt b.lo)) b.lo,
        Nat.mul a.den b.den, Nat.mul_pos a.den_pos b.den_pos⟩
      (nonposInt a.hi))
    ⟨Int.mul_k (Bool.rec a.hi a.lo (nonnegInt b.lo)) b.lo,
      Int.mul_k (Bool.rec a.lo a.hi (nonnegInt b.hi)) b.hi,
      Nat.mul a.den b.den, Nat.mul_pos a.den_pos b.den_pos⟩
    (nonnegInt a.lo)

/-- The interval product: by endpoint signs for ordered intervals, else `mulGeneral`. -/
def mul (a b : CommonDen) : CommonDen :=
  Bool.rec (mulGeneral a b) (mulOrdered a b)
    (Bool.rec false (Int.ble' b.lo b.hi) (Int.ble' a.lo a.hi))

def abs (a : CommonDen) : CommonDen :=
  ⟨maxInt 0 (maxInt a.lo (Int.neg_k a.hi)), maxInt (absInt a.lo) (absInt a.hi),
    a.den, a.den_pos⟩

def posPow (a : CommonDen) (n : Nat) : CommonDen :=
  ⟨Int.pow_k a.lo n, Int.pow_k a.hi n, Nat.pow a.den n, Nat.pow_pos a.den_pos⟩

def evenPow (a : CommonDen) (n : Nat) : CommonDen := posPow (abs a) n

end CommonDen.Kernel

def tailKernel (b W U : CommonDen) : ℚ :=
  let A := CommonDen.Kernel.abs W
  if Int.ble' (Int.mul_k A.hi U.den) (Int.mul_k U.lo A.den) then 0
  else (CommonDen.Kernel.mul
    (CommonDen.Kernel.mul
      (CommonDen.Kernel.mul b (CommonDen.Kernel.ofBounds remScale))
      (CommonDen.Kernel.posPow A 5))
    (CommonDen.ofRat (max 0 (A.upper-U.lower)))).upper

def nearTermsKernel (B : Box) (positive : Bool) (w : RowWitness) : LowerPolynomial :=
  let P := CommonDen.ofRat
  let O := CommonDen.Kernel.ofBounds
  let mul := CommonDen.Kernel.mul
  let add := CommonDen.Kernel.add
  let sub := CommonDen.Kernel.sub
  let even := CommonDen.Kernel.evenPow
  let H := O (bounds B 0)
  let U := O (bounds B 2)
  let K := O (kBounds B)
  let S := mul (P (signRat positive)) U
  let W := mul K (sub (O (bounds B 3)) (P 1))
  let h2 := sub (P 2) H
  let h1 := sub (P 1) H
  let V := add (mul h1 S) (mul H W)
  let M := O (muBounds B w)
  let b := sub (P 1) M
  let mk := mul M K
  let u2 := even U 2
  let w2 := even W 2
  let cross2 := mul (mul (mul (P 2) h1) W) S
  let d2 := sub (sub (mul h2 u2) cross2) (mul H w2)
  let gain := mul (O c4)
    (add (mul (mul b d2) (add u2 (even V 2))) (mul mk (even U 4)))
  let C := O c2
  ⟨(mul C (add (mul b h2) mk)).lower,
    (mul (mul (mul (mul b C) (P 2)) h1) (mul W (P (signRat positive)))).upper,
    (add (mul mk (P (w.jensen.value B))) gain).lower -
      (mul (mul (mul b C) H) w2).upper - tailKernel b W U⟩

structure RawScalar where
  num : Int
  den : Nat
  den_pos : 0 < den

namespace RawScalar

def value (a : RawScalar) : ℚ := (a.num : ℚ)/a.den

def ofRat (a : ℚ) : RawScalar := ⟨a.num, a.den, a.den_pos⟩

def lower (a : CommonDen) : RawScalar := ⟨a.lo, a.den, a.den_pos⟩

def upper (a : CommonDen) : RawScalar := ⟨a.hi, a.den, a.den_pos⟩

def add (a b : RawScalar) : RawScalar :=
  Bool.rec ⟨Int.add_k (Int.mul_k a.num (Int.ofNat b.den)) (Int.mul_k b.num (Int.ofNat a.den)),
    Nat.mul a.den b.den, Nat.mul_pos a.den_pos b.den_pos⟩
    ⟨Int.add_k a.num b.num, a.den, a.den_pos⟩
    (Nat.beq a.den b.den)

def sub (a b : RawScalar) : RawScalar :=
  Bool.rec ⟨Int.sub_k (Int.mul_k a.num (Int.ofNat b.den)) (Int.mul_k b.num (Int.ofNat a.den)),
    Nat.mul a.den b.den, Nat.mul_pos a.den_pos b.den_pos⟩
    ⟨Int.sub_k a.num b.num, a.den, a.den_pos⟩
    (Nat.beq a.den b.den)

def mul (a b : RawScalar) : RawScalar :=
  ⟨Int.mul_k a.num b.num, Nat.mul a.den b.den, Nat.mul_pos a.den_pos b.den_pos⟩

def pow (a : RawScalar) (n : Nat) : RawScalar :=
  ⟨Int.pow_k a.num n, Nat.pow a.den n, Nat.pow_pos a.den_pos⟩

def toQuad (a b c : RawScalar) : Quad :=
  ⟨Int.mul_k (Int.mul_k a.num (Int.ofNat b.den)) (Int.ofNat c.den),
    Int.mul_k (Int.mul_k b.num (Int.ofNat a.den)) (Int.ofNat c.den),
    Int.mul_k (Int.mul_k c.num (Int.ofNat a.den)) (Int.ofNat b.den),
    Nat.mul (Nat.mul a.den b.den) c.den⟩

end RawScalar

namespace RawQuad

def scaled (q : Quad) (n : Nat) : Quad :=
  ⟨(n : Int)*q.a, (n : Int)*q.b, (n : Int)*q.c, n*q.scale⟩

end RawQuad

namespace CommonDen.Kernel

def pointUpper (a : CommonDen) : CommonDen := ⟨a.hi, a.hi, a.den, a.den_pos⟩
def pointLower (a : CommonDen) : CommonDen := ⟨a.lo, a.lo, a.den, a.den_pos⟩
def pointGap (a b : CommonDen) : CommonDen := sub (pointUpper a) (pointLower b)

end CommonDen.Kernel

def tailRaw (b W U : CommonDen) : RawScalar :=
  let A := CommonDen.Kernel.abs W
  Bool.rec
    (RawScalar.upper (CommonDen.Kernel.mul
      (CommonDen.Kernel.mul
        (CommonDen.Kernel.mul b (CommonDen.Kernel.ofBounds remScale))
        (CommonDen.Kernel.posPow A 5))
      (CommonDen.Kernel.pointGap A U)))
    (RawScalar.ofRat 0)
    (Int.ble' (Int.mul_k A.hi (Int.ofNat U.den)) (Int.mul_k U.lo (Int.ofNat A.den)))

def Quad.kernelOK (q : Quad) : Bool :=
  let endpoint := Int.add_k (Int.add_k q.a q.b) q.c
  let interior := Int.blt' 0 q.a && Int.blt' (Int.mul_k (-2) q.a) q.b && Int.blt' q.b 0
  let discriminant := Int.sub_k (Int.mul_k (Int.mul_k 4 q.a) q.c) (Int.pow_k q.b 2)
  Nat.blt 0 q.scale && Int.ble' 0 q.c && Int.ble' 0 endpoint &&
    (!interior || Int.ble' 0 discriminant)

structure RawLowerPolynomial where
  squared : RawScalar
  linearCost : RawScalar
  constant : RawScalar

def RawLowerPolynomial.value (p : RawLowerPolynomial) : LowerPolynomial :=
  ⟨p.squared.value, p.linearCost.value, p.constant.value⟩

def nearTermsRaw (B : Box) (positive : Bool) (w : RowWitness) : RawLowerPolynomial :=
  let P := CommonDen.ofRat
  let O := CommonDen.Kernel.ofBounds
  let mul := CommonDen.Kernel.mul
  let add := CommonDen.Kernel.add
  let sub := CommonDen.Kernel.sub
  let even := CommonDen.Kernel.evenPow
  let H := O (bounds B 0)
  let U := O (bounds B 2)
  let K := O (kBounds B)
  let S := mul (P (signRat positive)) U
  let W := mul K (sub (O (bounds B 3)) (P 1))
  let h2 := sub (P 2) H
  let h1 := sub (P 1) H
  let V := add (mul h1 S) (mul H W)
  let M := O (muBounds B w)
  let b := sub (P 1) M
  let mk := mul M K
  let u2 := even U 2
  let w2 := even W 2
  let cross2 := mul (mul (mul (P 2) h1) W) S
  let d2 := sub (sub (mul h2 u2) cross2) (mul H w2)
  let gain := mul (O c4)
    (add (mul (mul b d2) (add u2 (even V 2))) (mul mk (even U 4)))
  let C := O c2
  ⟨RawScalar.lower (mul C (add (mul b h2) mk)),
    RawScalar.upper (mul (mul (mul (mul b C) (P 2)) h1) (mul W (P (signRat positive)))),
    RawScalar.sub
      (RawScalar.sub (RawScalar.lower (add (mul mk (P (w.jensen.value B))) gain))
        (RawScalar.upper (mul (mul (mul b C) H) w2)))
      (tailRaw b W U)⟩

def RawLowerPolynomial.quad (p : RawLowerPolynomial) (adjustment u width p0 p1 : RawScalar) : Quad :=
  let a := RawScalar.sub p.squared adjustment
  let qa := RawScalar.mul a (RawScalar.pow width 2)
  let qb := RawScalar.sub
    (RawScalar.mul (RawScalar.sub
      (RawScalar.mul (RawScalar.mul (RawScalar.ofRat 2) a) u) p.linearCost) width)
    (RawScalar.sub p1 p0)
  let qc := RawScalar.sub
    (RawScalar.add (RawScalar.sub (RawScalar.mul a (RawScalar.pow u 2))
      (RawScalar.mul p.linearCost u)) p.constant) p0
  RawScalar.toQuad qa qb qc

def rowQuadRaw (B : Box) (positive : Bool) (w : RowWitness) : Quad :=
  let base := nearTermsRaw B positive w
  let adjustment := match w.far with
    | .chord .. => RawScalar.ofRat 0
    | .variance n => RawScalar.ofRat (varianceCost B w n).hi
  let costs := chordCosts B positive w
  let u := RawScalar.ofRat (B.lo 2)
  let width := RawScalar.sub (RawScalar.ofRat (B.hi 2)) u
  base.quad adjustment u width (RawScalar.ofRat costs.1) (RawScalar.ofRat costs.2)

def rowQuadKernel (B : Box) (positive : Bool) (w : RowWitness) : Quad :=
  rowQuadRaw B positive w

def rowOKKernel (B : Box) (positive : Bool) (w : RowWitness) : Bool :=
  decide (Domain B) &&
    G3Power.Kernel.crossIntLE (units w.sigmaLower).num (units w.sigmaLower).den
      (B.lo 1).num (B.lo 1).den 25 12 &&
    G3Power.Kernel.crossIntLE (B.hi 1).num (B.hi 1).den
      (units w.sigmaUpper).num (units w.sigmaUpper).den 12 25 &&
    w.jensen.ok B && w.far.ok B positive && (rowQuadKernel B positive w).kernelOK

def CertTree.kernelOK (B : Box) (positive : Bool) : CertTree → Bool
  | .cone => decide (coneBox B)
  | .empty => decide (B.hi 1 ≤ 1/5 ∧ 1/(2-G3S.kMax B) < B.lo 0)
  | .row w => rowOKKernel B positive w
  | .cut j knot a b =>
    a.kernelOK (B.lowerChild j knot) positive && b.kernelOK (B.upperChild j knot) positive

end

end HlawkaSchatten.BelowExponent.G3P
