/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3SData
public import HlawkaSchatten.BelowExponent.Vertex.ParameterBounds

/-! Rational endpoint witnesses and polynomial checks for the central G3 chart. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

open Vertex (RatBounds)

abbrev point := RatBounds.point

def bounds (B : Box) (j : Fin 4) : RatBounds := ⟨B.lo j, B.hi j⟩

def absBounds (a : RatBounds) : RatBounds :=
  ⟨max 0 (max a.lo (-a.hi)), max |a.lo| |a.hi|⟩

def posPow (a : RatBounds) (n : Nat) : RatBounds := ⟨a.lo ^ n, a.hi ^ n⟩

def evenPow (a : RatBounds) (n : Nat) : RatBounds := posPow (absBounds a) n

def recip (a : RatBounds) : RatBounds := ⟨1 / a.hi, 1 / a.lo⟩

def qBounds : RatBounds := ⟨1054 / 665, 485 / 306⟩

def c2 : RatBounds := ((qBounds.mul (qBounds.sub (point 1))).mul (point (1 / 2)))
def c4 : RatBounds := ((c2.mul (qBounds.sub (point 2))).mul (qBounds.sub (point 3))).mul (point (1 / 12))
def remScale : RatBounds := qBounds.mul ((point (7 / 4)).sub qBounds)

def signRat (positive : Bool) : ℚ := if positive then 1 else -1

def kBounds (B : Box) : RatBounds := ⟨G3S.kMin B, G3S.kMax B⟩
def lBounds (B : Box) : RatBounds := (bounds B 0).mul (kBounds B)

def center (B : Box) : RatBounds :=
  let L := lBounds B
  let zk (z : ℚ) := (point z).add ((point (1 - z)).mul L)
  ⟨(zk (B.lo 3)).lo, (zk (B.hi 3)).hi⟩

def signedRatio (B : Box) (positive : Bool) : RatBounds :=
  ((point (signRat positive)).mul (center B)).mul (recip (bounds B 2))

def jensenBase (B : Box) : ℚ := min (max 1 (B.lo 3)) (B.hi 3)

def jensenShift (B : Box) : ℚ :=
  let z := jensenBase B
  z + (lBounds B).hi * (1 - z)

def units (n : Nat) : ℚ := (n : ℚ) / 274877906944

inductive JensenWitness
  | zero
  | direct (baseLow shiftHigh : Nat)

def JensenWitness.ok (B : Box) : JensenWitness → Bool
  | .zero => true
  | .direct f g => G3Power.tightLower (jensenBase B) (units f) &&
      G3Power.tightUpper (jensenShift B) (units g)

def JensenWitness.value (B : Box) : JensenWitness → ℚ
  | .zero => 0
  | .direct f g => ((1 - (lBounds B).hi) * units f + (lBounds B).hi - units g) / (lBounds B).hi

structure MidpointWitness where
  pairHigh : Nat
  pairLow : Nat
  midUpper : Nat
  curvature : Nat
  yLower : Nat
  twoMinusYLower : Nat

def predLower (x y : ℚ) : Bool :=
  if x ≤ 1 then G3Power.crossLE y x 306 179 else G3Power.crossLE y x 665 389

def predUpper (x y : ℚ) : Bool :=
  if x ≤ 1 then G3Power.crossLE x y 389 665 else G3Power.crossLE x y 179 306

def slopeGain (w : MidpointWitness) : ℚ :=
  qBounds.hi * (qBounds.hi - 1) * units w.curvature

def slopeLoss (w : MidpointWitness) : ℚ :=
  qBounds.lo / 2 * (units w.yLower + units w.twoMinusYLower)

def midpointOK (B : Box) (positive : Bool) (w : MidpointWitness) : Bool :=
  let A := signedRatio B positive
  let y := A.lo + B.lo 0
  let m := A.lo + B.lo 0 / 2
  let ymax := A.hi + B.hi 0
  decide (0 < B.lo 2 ∧ 0 ≤ A.lo ∧ 0 < y ∧ 0 < m ∧ ymax < 2) &&
    G3Power.tightUpper (y - 2) (units w.pairHigh) &&
    G3Power.tightLower y (units w.pairLow) &&
    predUpper m (units w.midUpper) &&
    G3Power.tightCurve m (units w.curvature) &&
    predLower y (units w.yLower) &&
    predLower (2 - ymax) (units w.twoMinusYLower)

def midpointValue (B : Box) (positive : Bool) (w : MidpointWitness) : ℚ :=
  let A := signedRatio B positive
  let D := slopeGain w
  let L := slopeLoss w
  max 0 ((units w.pairHigh - units w.pairLow) / 2 + qBounds.hi * units w.midUpper +
    max 0 (D - L) * (A.hi - A.lo) + max 0 (D / 2 - L) * (B.hi 0 - B.lo 0))

inductive FarFactor
  | universal
  | secant (pairHigh pairLow shiftHigh shiftLow : Nat)
  | midpoint (w : MidpointWitness)

def FarFactor.ok (B : Box) (positive : Bool) : FarFactor → Bool
  | .universal => true
  | .secant a b c d =>
    let A := signedRatio B positive
    let x := A.lo + B.lo 0
    decide (0 < B.lo 2) &&
      G3Power.tightUpper (x - 2) (units a) &&
      G3Power.tightLower x (units b) &&
      G3Power.tightUpper (A.hi + B.hi 0) (units c) &&
      G3Power.tightLower A.hi (units d)
  | .midpoint w => midpointOK B positive w

def FarFactor.value (B : Box) (positive : Bool) : FarFactor → ℚ
  | .universal => 2
  | .secant a b c d =>
    max 0 ((units a - units b) / 2 + (units c - units d) / B.hi 0)
  | .midpoint w => midpointValue B positive w

inductive FarWitness
  | chord (factor : FarFactor) (left right : Nat)
  | variance (curve : Nat)

def FarWitness.ok (B : Box) (positive : Bool) : FarWitness → Bool
  | .chord ff a b => ff.ok B positive &&
    G3Power.tightUpper (B.lo 2) (units a) && G3Power.tightUpper (B.hi 2) (units b)
  | .variance q => decide (0 < (absBounds (center B)).lo) &&
    G3Power.tightCurve (absBounds (center B)).lo (units q)

structure RowWitness where
  sigmaLower : Nat
  sigmaUpper : Nat
  jensen : JensenWitness
  far : FarWitness

def muBounds (B : Box) (w : RowWitness) : RatBounds :=
  ⟨G3S.weightLower B (units w.sigmaLower), G3S.weightUpper B (units w.sigmaUpper)⟩

structure LowerPolynomial where
  squared : ℚ
  linearCost : ℚ
  constant : ℚ

def nearTerms (B : Box) (positive : Bool) (w : RowWitness) : LowerPolynomial :=
  let H := bounds B 0
  let U := bounds B 2
  let S := (point (signRat positive)).mul U
  let W := (kBounds B).mul ((bounds B 3).sub (point 1))
  let V := (((point 1).sub H).mul S).add (H.mul W)
  let M := muBounds B w
  let b := (point 1).sub M
  let mk := M.mul (kBounds B)
  let h2 := (point 2).sub H
  let h1 := (point 1).sub H
  let u2 := evenPow U 2
  let w2 := evenPow W 2
  let cross2 := (((point 2).mul h1).mul W).mul S
  let d2 := ((h2.mul u2).sub cross2).sub (H.mul w2)
  let gain := c4.mul (((b.mul d2).mul (u2.add (evenPow V 2))).add (mk.mul (evenPow U 4)))
  let tail := ((b.mul remScale).mul (posPow (absBounds W) 5)).mul
    (point (max 0 ((absBounds W).hi - U.lo)))
  ⟨(c2.mul ((b.mul h2).add mk)).lo,
    ((((b.mul c2).mul (point 2)).mul h1).mul (W.mul (point (signRat positive)))).hi,
    ((mk.mul (point (w.jensen.value B))).add gain).lo - (((b.mul c2).mul H).mul w2).hi - tail.hi⟩

def clearDen (a b c : ℚ) : Quad :=
  ⟨a.num * b.den * c.den, b.num * a.den * c.den,
    c.num * a.den * b.den, a.den * b.den * c.den⟩

def varianceCost (B : Box) (w : RowWitness) (curv : Nat) : RatBounds :=
  (((muBounds B w).mul qBounds).mul (point (1/2))).mul
    (((point 2).sub (bounds B 0)).mul (point (units curv)))

def adjustedLeading (B : Box) (positive : Bool) (w : RowWitness) : ℚ :=
  let a := (nearTerms B positive w).squared
  match w.far with
  | .chord .. => a
  | .variance curv => a - (varianceCost B w curv).hi

def chordCosts (B : Box) (positive : Bool) (w : RowWitness) : ℚ × ℚ :=
  match w.far with
  | .chord ff l r => let F := (muBounds B w).hi * ff.value B positive; (F * units l, F * units r)
  | .variance _ => (0, 0)

def rowQuad (B : Box) (positive : Bool) (w : RowWitness) : Quad :=
  let base := nearTerms B positive w
  let a := adjustedLeading B positive w
  let p₀ := (chordCosts B positive w).1
  let p₁ := (chordCosts B positive w).2
  let u₀ := B.lo 2
  let width := B.hi 2 - u₀
  clearDen (a * width ^ 2) ((2 * a * u₀ - base.linearCost) * width - (p₁ - p₀))
    (a * u₀ ^ 2 - base.linearCost * u₀ + base.constant - p₀)

def Domain (B : Box) : Prop :=
  0 ≤ B.lo 0 ∧ 0 < B.hi 0 ∧ B.hi 0 ≤ 9/17 ∧
  0 < B.lo 1 ∧ B.hi 1 ≤ 1/5 ∧ 0 < (lBounds B).hi ∧ (lBounds B).hi ≤ 1 ∧
  0 ≤ B.lo 2 ∧ B.lo 2 < B.hi 2 ∧ B.hi 2 ≤ 1

instance (B : Box) : Decidable (Domain B) := by unfold Domain; infer_instance

def rowOK (B : Box) (positive : Bool) (w : RowWitness) : Bool :=
  decide (Domain B) &&
    G3Power.crossLE (units w.sigmaLower) (B.lo 1) 25 12 &&
    G3Power.crossLE (B.hi 1) (units w.sigmaUpper) 12 25 &&
    w.jensen.ok B && w.far.ok B positive && (rowQuad B positive w).ok

inductive CertTree
  | cone
  | empty
  | row (w : RowWitness)
  | cut (j : Fin 4) (knot : ℚ) (lower upper : CertTree)

def CertTree.ok (B : Box) (positive : Bool) : CertTree → Bool
  | .cone => decide (coneBox B)
  | .empty => decide (B.hi 1 ≤ 1/5 ∧ 1/(2-G3S.kMax B) < B.lo 0)
  | .row w => rowOK B positive w
  | .cut j knot lower upper => lower.ok (B.lowerChild j knot) positive &&
    upper.ok (B.upperChild j knot) positive

theorem CertTree.cut_ok {B : Box} {positive : Bool} {j : Fin 4} {knot : ℚ}
    {lower upper : CertTree}
    (hl : lower.ok (B.lowerChild j knot) positive = true)
    (hu : upper.ok (B.upperChild j knot) positive = true) :
    (CertTree.cut j knot lower upper).ok B positive = true := by
  simp only [CertTree.ok, hl, hu, Bool.and_self]

end HlawkaSchatten.BelowExponent.G3P
