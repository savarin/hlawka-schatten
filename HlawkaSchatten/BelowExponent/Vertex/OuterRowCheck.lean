/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCheck
public import HlawkaSchatten.BelowExponent.Vertex.CornerGridData

/-! Exact interval operations common to the VC and SC outer row certificates. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

structure OuterAxisBounds where
  absChord : DyadicBounds
  absTangent : DyadicBounds
  signedChord : DyadicBounds
  signedTangent : DyadicBounds
  deriving DecidableEq, Repr

def outerSpanMidpoint (U : RatBounds) : ℚ := (U.lo + U.hi) / 2

def outerMidpoint (i : Fin 34) : ℚ := outerSpanMidpoint (outerInterval i)

def outerExponent : DyadicBounds := .ofRat ⟨1054/665, 485/306⟩

/-- The four multipliers can be shared by every parameter point on this row interval. -/
def outerSpanAxisBounds (U : RatBounds) (e : Bool)
    (endAbs endSigned midAbs midSigned midSlope : DyadicBounds) : OuterAxisBounds :=
  let dx := DyadicBounds.point (outerEndpoint U e - outerSpanMidpoint U)
  ⟨endAbs, midAbs.add ((outerExponent.mul dx).mul midSigned),
   endSigned, midSigned.add (((outerExponent.sub (.point 1)).mul midSlope).mul dx)⟩

def outerAxisBounds (i : Fin 34) (e : Bool)
    (endAbs endSigned midAbs midSigned midSlope : DyadicBounds) : OuterAxisBounds :=
  outerSpanAxisBounds (outerInterval i) e endAbs endSigned midAbs midSigned midSlope

def OuterAxisBounds.eval (A : OuterAxisBounds) (positive : Bool) (d c : ℤ) : DyadicBounds :=
  let unsigned := if 0 ≤ d then A.absTangent else A.absChord
  let signed := if (if positive then c else -c) < 0 then A.signedTangent else A.signedChord
  ((DyadicBounds.ofNumerator d).mul unsigned).add ((DyadicBounds.ofNumerator c).mul signed)

structure OuterPointBounds where
  diagonal : Vector DyadicBounds 3
  coupling : Vector (Vector DyadicBounds 3) 3
  argument : Vector ℚ 3
  deriving DecidableEq, Repr

def outerParameterCell (a b η : ℚ) : ParameterCell := ⟨.point a, .point b, .point η⟩

def OuterPointBounds.atPoint (a b η : ℚ) (margins : Vector ℚ 3) (roots : Fin 3 → RatBounds) :
    OuterPointBounds :=
  let v := axisCoefficientIntervals (outerParameterCell a b η) roots 0
  let H := Vector.ofFn fun i => Vector.ofFn fun j => outerExponent.mul ((v.h.get i).get j).value
  let direction := ![a,b,1-a-b]
  ⟨Vector.ofFn fun j => ((v.d.get j).value.sub (.point (margins.get j))).add ((H.get j).get j),
   H, Vector.ofFn fun j => 1 + 2*η*(1-direction j)⟩

def OuterPointBounds.linearCoeff (P : OuterPointBounds) (k cross axis : Fin 3) (x : ℚ) : DyadicBounds :=
  ((P.coupling.get k).get axis).add (((P.coupling.get cross).get axis).mul (.point x))

def outerSignedNumerator (axis : RatBounds) (c : DyadicBounds) : ℤ :=
  if 0 ≤ axis.lo then c.lo else c.hi

def OuterPointBounds.argumentAt (P : OuterPointBounds) (k m n : Fin 3) (x y : ℚ) : ℚ :=
  P.argument.get k + P.argument.get m*x + P.argument.get n*y

def OuterPointBounds.remainderLinear (P : OuterPointBounds) (k m n : Fin 3) (x y : ℚ) : DyadicBounds :=
  ((P.diagonal.get k).add (((P.coupling.get m).get k).mul (.point x))).add
    (((P.coupling.get n).get k).mul (.point y))

def OuterPointBounds.spanEndpointBound (P : OuterPointBounds) (k m n : Fin 3) (U V : RatBounds) (x y : Bool)
    (Au Av : Bool → OuterAxisBounds) (chord : ℚ → ℚ) : DyadicBounds :=
  let u := outerEndpoint U x
  let v := outerEndpoint V y
  let a := P.argumentAt k m n u v
  let du := P.diagonal.get m
  let dv := P.diagonal.get n
  let cu := P.linearCoeff k n m v
  let cv := P.linearCoeff k m n u
  let first := (Au x).eval (decide (0 ≤ U.lo)) du.lo (outerSignedNumerator U cu)
  let second := (Av y).eval (decide (0 ≤ V.lo)) dv.lo (outerSignedNumerator V cv)
  (((P.remainderLinear k m n u v).sub (.point (chord a))).add first).add second

def OuterPointBounds.spanEndpointOK (P : OuterPointBounds) (k m n : Fin 3) (U V : RatBounds) (x y : Bool)
    (Au Av : Bool → OuterAxisBounds) (chord : ℚ → ℚ) : Bool :=
  let u := outerEndpoint U x
  let v := outerEndpoint V y
  (P.diagonal.get m).ok && (P.diagonal.get n).ok &&
    (P.linearCoeff k n m v).ok && (P.linearCoeff k m n u).ok &&
    decide (|P.argumentAt k m n u v| ≤ 4) && (P.spanEndpointBound k m n U V x y Au Av chord).lowerOK 0

def OuterPointBounds.endpointBound (P : OuterPointBounds) (k m n : Fin 3) (i j : Fin 34) (x y : Bool)
    (axes : Fin 34 → Bool → OuterAxisBounds) (chord : ℚ → ℚ) : DyadicBounds :=
  P.spanEndpointBound k m n (outerInterval i) (outerInterval j) x y (axes i) (axes j) chord

def OuterPointBounds.endpointOK (P : OuterPointBounds) (k m n : Fin 3) (i j : Fin 34) (x y : Bool)
    (axes : Fin 34 → Bool → OuterAxisBounds) (chord : ℚ → ℚ) : Bool :=
  P.spanEndpointOK k m n (outerInterval i) (outerInterval j) x y (axes i) (axes j) chord

def outerTransverse (k : Fin 3) : Fin 3 × Fin 3 := ![(1,2),(0,2),(0,1)] k

def OuterPointBounds.spanOK (P : OuterPointBounds) (k : Fin 3) (U V : RatBounds)
    (Au Av : Bool → OuterAxisBounds) (chord : ℚ → ℚ) : Bool :=
  let (m,n) := outerTransverse k
  decide (U.lo < U.hi ∧ V.lo < V.hi ∧ (0 ≤ U.lo ∨ U.hi ≤ 0) ∧ (0 ≤ V.lo ∨ V.hi ≤ 0)) &&
    [false,true].all fun x => [false,true].all fun y => P.spanEndpointOK k m n U V x y Au Av chord

def OuterPointBounds.stripOK (P : OuterPointBounds) (side : Bool) (k : Fin 3) (i : Fin 34)
    (axes : Fin 34 → Bool → OuterAxisBounds) (chord : ℚ → ℚ) : Bool :=
  let (m,n) := outerTransverse k
  (List.finRange 34).all fun j => (side && outerSideSkip k i j) ||
    [false,true].all fun x => [false,true].all fun y => P.endpointOK k m n i j x y axes chord

end HlawkaSchatten.BelowExponent.Vertex
