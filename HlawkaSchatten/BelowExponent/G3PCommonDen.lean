/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCertData

/-! Exact interval polynomials with one positive denominator for both endpoints. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

open Vertex (RatBounds)

structure CommonDen where
  lo : ℤ
  hi : ℤ
  den : ℕ
  den_pos : 0 < den

namespace CommonDen

def ofRat (x : ℚ) : CommonDen := ⟨x.num, x.num, x.den, x.den_pos⟩

def ofBounds (x : RatBounds) : CommonDen :=
  if x.lo.den = x.hi.den then ⟨x.lo.num, x.hi.num, x.lo.den, x.lo.den_pos⟩
  else ⟨x.lo.num * x.hi.den, x.hi.num * x.lo.den, x.lo.den * x.hi.den,
    Nat.mul_pos x.lo.den_pos x.hi.den_pos⟩

def lower (x : CommonDen) : ℚ := (x.lo : ℚ) / x.den
def upper (x : CommonDen) : ℚ := (x.hi : ℚ) / x.den
def toBounds (x : CommonDen) : RatBounds := ⟨x.lower, x.upper⟩

def add (a b : CommonDen) : CommonDen :=
  if a.den = b.den then ⟨a.lo + b.lo, a.hi + b.hi, a.den, a.den_pos⟩
  else ⟨a.lo*b.den + b.lo*a.den, a.hi*b.den + b.hi*a.den,
    a.den*b.den, Nat.mul_pos a.den_pos b.den_pos⟩

def sub (a b : CommonDen) : CommonDen :=
  if a.den = b.den then ⟨a.lo - b.hi, a.hi - b.lo, a.den, a.den_pos⟩
  else ⟨a.lo*b.den - b.hi*a.den, a.hi*b.den - b.lo*a.den,
    a.den*b.den, Nat.mul_pos a.den_pos b.den_pos⟩

def mul (a b : CommonDen) : CommonDen :=
  let aa := a.lo*b.lo
  let ab := a.lo*b.hi
  let ba := a.hi*b.lo
  let bb := a.hi*b.hi
  ⟨min (min aa ab) (min ba bb), max (max aa ab) (max ba bb),
    a.den*b.den, Nat.mul_pos a.den_pos b.den_pos⟩

def abs (a : CommonDen) : CommonDen :=
  ⟨max 0 (max a.lo (-a.hi)), max |a.lo| |a.hi|, a.den, a.den_pos⟩

def posPow (a : CommonDen) (n : ℕ) : CommonDen :=
  ⟨a.lo ^ n, a.hi ^ n, a.den ^ n, Nat.pow_pos a.den_pos⟩

def evenPow (a : CommonDen) (n : ℕ) : CommonDen := a.abs.posPow n

end CommonDen

def nearTermsCommon (B : Box) (positive : Bool) (w : RowWitness) : LowerPolynomial :=
  let P := CommonDen.ofRat
  let H := CommonDen.ofBounds (bounds B 0)
  let U := CommonDen.ofBounds (bounds B 2)
  let K := CommonDen.ofBounds (kBounds B)
  let S := (P (signRat positive)).mul U
  let W := K.mul ((CommonDen.ofBounds (bounds B 3)).sub (P 1))
  let h2 := (P 2).sub H
  let h1 := (P 1).sub H
  let V := (h1.mul S).add (H.mul W)
  let M := CommonDen.ofBounds (muBounds B w)
  let b := (P 1).sub M
  let mk := M.mul K
  let u2 := U.evenPow 2
  let w2 := W.evenPow 2
  let cross2 := (((P 2).mul h1).mul W).mul S
  let d2 := ((h2.mul u2).sub cross2).sub (H.mul w2)
  let gain := (CommonDen.ofBounds c4).mul
    (((b.mul d2).mul (u2.add (V.evenPow 2))).add (mk.mul (U.evenPow 4)))
  let tail := ((b.mul (CommonDen.ofBounds remScale)).mul (W.abs.posPow 5)).mul
    (P (max 0 (W.abs.upper - U.lower)))
  let C := CommonDen.ofBounds c2
  ⟨(C.mul ((b.mul h2).add mk)).lower,
   ((((b.mul C).mul (P 2)).mul h1).mul (W.mul (P (signRat positive)))).upper,
   ((mk.mul (P (w.jensen.value B))).add gain).lower - (((b.mul C).mul H).mul w2).upper - tail.upper⟩

def rowQuadCommon (B : Box) (positive : Bool) (w : RowWitness) : Quad :=
  let base := nearTermsCommon B positive w
  let a := match w.far with
    | .chord .. => base.squared
    | .variance n => base.squared - (varianceCost B w n).hi
  let costs := chordCosts B positive w
  let u := B.lo 2
  let width := B.hi 2 - u
  clearDen (a * width ^ 2) ((2*a*u - base.linearCost)*width - (costs.2-costs.1))
    (a*u^2 - base.linearCost*u + base.constant - costs.1)

def rowOKCommon (B : Box) (positive : Bool) (w : RowWitness) : Bool :=
  decide (Domain B) &&
    G3Power.crossLE (units w.sigmaLower) (B.lo 1) 25 12 &&
    G3Power.crossLE (B.hi 1) (units w.sigmaUpper) 12 25 &&
    w.jensen.ok B && w.far.ok B positive && (rowQuadCommon B positive w).ok

def CertTree.commonOK (B : Box) (positive : Bool) : CertTree → Bool
  | .cone => decide (coneBox B)
  | .empty => decide (B.hi 1 ≤ 1/5 ∧ 1/(2-G3S.kMax B) < B.lo 0)
  | .row w => rowOKCommon B positive w
  | .cut j knot a b =>
    a.commonOK (B.lowerChild j knot) positive && b.commonOK (B.upperChild j knot) positive

theorem CertTree.commonCut_ok {B : Box} {positive : Bool} {j : Fin 4} {knot : ℚ}
    {a b : CertTree} (hl : a.commonOK (B.lowerChild j knot) positive = true)
    (hu : b.commonOK (B.upperChild j knot) positive = true) :
    (CertTree.cut j knot a b).commonOK B positive = true := by
  simp only [CertTree.commonOK, hl, hu, Bool.and_self]

end HlawkaSchatten.BelowExponent.G3P
