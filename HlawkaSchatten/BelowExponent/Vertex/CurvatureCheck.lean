/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.RadicalCheck
public import Mathlib.Data.Rat.Floor
public import Mathlib.Algebra.BigOperators.Fin

/-! Fixed-point interval evaluation and the exact VC/SC curvature and weight checks. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex


/-- The endpoints are in units of 2⁻⁹⁶. A failed denominator test propagates to `ok`. -/
structure DyadicBounds where
  lo : ℤ
  hi : ℤ
  ok : Bool := true
  deriving DecidableEq, Repr

namespace DyadicBounds

def units : ℕ := 2 ^ 96

def lower (a : DyadicBounds) : ℚ := (a.lo : ℚ) / (units : ℚ)

def upper (a : DyadicBounds) : ℚ := (a.hi : ℚ) / (units : ℚ)

def ofRat (a : RatBounds) : DyadicBounds := ⟨⌊a.lo * units⌋, ⌈a.hi * units⌉, true⟩

def point (q : ℚ) : DyadicBounds := ofRat (RatBounds.point q)

def ofNumerator (n : ℤ) : DyadicBounds := ⟨n, n, true⟩

def require (a : DyadicBounds) (b : Bool) : DyadicBounds := { a with ok := a.ok && b }

def add (a b : DyadicBounds) : DyadicBounds := ⟨a.lo+b.lo, a.hi+b.hi, a.ok && b.ok⟩

def sub (a b : DyadicBounds) : DyadicBounds := ⟨a.lo-b.hi, a.hi-b.lo, a.ok && b.ok⟩

def ceilDiv (a b : ℤ) : ℤ := -((-a) / b)

def productLo (a b : DyadicBounds) : ℤ :=
  min (min (a.lo*b.lo) (a.lo*b.hi)) (min (a.hi*b.lo) (a.hi*b.hi))

def productHi (a b : DyadicBounds) : ℤ :=
  max (max (a.lo*b.lo) (a.lo*b.hi)) (max (a.hi*b.lo) (a.hi*b.hi))

def mul (a b : DyadicBounds) : DyadicBounds := ⟨productLo a b / units, ceilDiv (productHi a b) units, a.ok && b.ok⟩

def abs (a : DyadicBounds) : DyadicBounds := ⟨max 0 (max a.lo (-a.hi)), max |a.lo| |a.hi|, a.ok⟩

def square (a : DyadicBounds) : DyadicBounds := a.abs.mul a.abs

def reciprocal (a : DyadicBounds) : DyadicBounds := ⟨
  ((units : ℤ) * units) / a.hi, ceilDiv ((units : ℤ) * units) a.lo, a.ok && decide (0 < a.lo)⟩

def div (a b : DyadicBounds) : DyadicBounds := a.mul b.reciprocal

def intersect (a b : DyadicBounds) : DyadicBounds := ⟨max a.lo b.lo, min a.hi b.hi, a.ok && b.ok⟩

def upperOK (a : DyadicBounds) (q : ℚ) : Bool := a.ok && decide (a.upper ≤ q)

def lowerOK (a : DyadicBounds) (q : ℚ) : Bool := a.ok && decide (q ≤ a.lower)

def sumThree (f : Fin 3 → DyadicBounds) : DyadicBounds := ((f 0).add (f 1)).add (f 2)

def refinementDenominator (r a : DyadicBounds) : DyadicBounds :=
  let r₂ := r.square
  let a₂ := a.square
  ((((r₂.square.add ((r₂.mul r).mul a)).add (r₂.mul a₂)).add ((r.mul a₂).mul a)).add a₂.square)

def refineRadical (r power : DyadicBounds) : DyadicBounds :=
  let m := (r.lo + r.hi) / 2
  let a := ofNumerator m
  let a₅ := a.square.square.mul a
  let next := a.add ((power.sub a₅).div (refinementDenominator r a))
  (r.intersect next).require (decide (0 < m))

end DyadicBounds

structure IntervalJet where
  value : DyadicBounds
  first : DyadicBounds
  second : DyadicBounds
  deriving DecidableEq

namespace IntervalJet

def const (q : ℚ) : IntervalJet := ⟨DyadicBounds.point q, DyadicBounds.point 0, DyadicBounds.point 0⟩

def add (a b : IntervalJet) : IntervalJet := ⟨a.value.add b.value, a.first.add b.first, a.second.add b.second⟩

def sub (a b : IntervalJet) : IntervalJet := ⟨a.value.sub b.value, a.first.sub b.first, a.second.sub b.second⟩

def mul (a b : IntervalJet) : IntervalJet :=
  ⟨a.value.mul b.value, (a.first.mul b.value).add (a.value.mul b.first),
    ((a.second.mul b.value).add (((DyadicBounds.point 2).mul a.first).mul b.first)).add (a.value.mul b.second)⟩

def scale (r : ℚ) (a : IntervalJet) : IntervalJet :=
  let c := DyadicBounds.point r
  ⟨c.mul a.value, c.mul a.first, c.mul a.second⟩

def sumThree (f : Fin 3 → IntervalJet) : IntervalJet := ((f 0).add (f 1)).add (f 2)

def div (a b : IntervalJet) : IntervalJet :=
  let v := a.value.div b.value
  let v' := (a.first.sub (v.mul b.first)).div b.value
  let v'' := ((a.second.sub (v.mul b.second)).sub (((DyadicBounds.point 2).mul v').mul b.first)).div b.value
  ⟨v, v', v''⟩

def logFirst (a : IntervalJet) : DyadicBounds := a.first.div a.value

def logSecond (a : IntervalJet) : DyadicBounds := (a.second.div a.value).sub a.logFirst.square

def logRadicalFirst (a b s : IntervalJet) : DyadicBounds :=
  let t := ((DyadicBounds.point 2).mul a.logFirst).add ((DyadicBounds.point 3).mul b.logFirst)
  (t.sub ((DyadicBounds.point 2).mul s.logFirst)).div (DyadicBounds.point 5)

def logRadicalSecond (a b s : IntervalJet) : DyadicBounds :=
  let t := ((DyadicBounds.point 2).mul a.logSecond).add ((DyadicBounds.point 3).mul b.logSecond)
  (t.sub ((DyadicBounds.point 2).mul s.logSecond)).div (DyadicBounds.point 5)

def radical (r : DyadicBounds) (a b s : IntervalJet) : IntervalJet :=
  let h := logRadicalFirst a b s
  let h' := logRadicalSecond a b s
  ⟨r, r.mul h, r.mul (h.square.add h')⟩

end IntervalJet

local notation "pt" => DyadicBounds.point

def axisSlopeRat (k i : Fin 3) : ℚ := if i = k then 1 else 0

def directionSlopeRat (k : Fin 3) (i : Fin 3) : ℚ :=
  ![axisSlopeRat k 0, axisSlopeRat k 1, -axisSlopeRat k 0 - axisSlopeRat k 1] i

def coordinateInterval (c : ParameterCell) (k i : Fin 3) : IntervalJet :=
  ⟨DyadicBounds.ofRat (![c.a, c.b, c.η] i), pt (axisSlopeRat k i), pt 0⟩

def directionInterval (c : ParameterCell) (k i : Fin 3) : IntervalJet :=
  ⟨DyadicBounds.ofRat (c.direction i), pt (directionSlopeRat k i), pt 0⟩

/-- Bound η/(1+mη) with its compact derivatives for the two normalizers. -/
def ratioInterval (c : ParameterCell) (k : Fin 3) (m : ℚ) : IntervalJet :=
  let η := DyadicBounds.ofRat c.η
  let t := pt (axisSlopeRat k 2)
  let n := (pt 1).add ((pt m).mul η)
  let n₂ := n.square
  ⟨η.div n, t.div n₂, (((pt (-2 * m)).mul t).div (n₂.mul n))⟩

def depthInterval (c : ParameterCell) (k : Fin 3) : IntervalJet := ratioInterval c k 2

def etaRatioInterval (c : ParameterCell) (k : Fin 3) : IntervalJet := ratioInterval c k 1

def radicalBaseInterval (c : ParameterCell) (k j : Fin 3) : IntervalJet :=
  let e := directionInterval c k
  let ε := depthInterval c k
  let a := (pt 1).sub (e j).value
  let b := ((e (j + 1)).value).mul (e (j + 2)).value
  let bp := (((e (j + 1)).first).mul (e (j + 2)).value).add (((e (j + 1)).value).mul (e (j + 2)).first)
  let v := (e j).first
  let value := (((pt 1).sub ε.value).mul a).add (ε.value.mul b)
  let first := (((pt 0).sub v).add (ε.first.mul (b.sub a))).add (ε.value.mul (bp.add v))
  let second := ((ε.second.mul (b.sub a)).add (((pt 2).mul ε.first).mul (bp.add v))).add
    ((((pt 2).mul ε.value).mul (e (j + 1)).first).mul (e (j + 2)).first)
  ⟨value, first, second⟩

def radicalOtherInterval (c : ParameterCell) (k j : Fin 3) : IntervalJet :=
  let e := directionInterval c k j
  let ε := depthInterval c k
  let value := (pt 1).sub (ε.value.mul e.value)
  let first := (((pt 0).sub ε.first).mul e.value).sub (ε.value.mul e.first)
  let second := (((pt 0).sub ε.second).mul e.value).sub (((pt 2).mul ε.first).mul e.first)
  ⟨value, first, second⟩

def radicalSigmaInterval (c : ParameterCell) (k : Fin 3) : IntervalJet :=
  let e := directionInterval c k
  let prod := fun i j => (e i).value.mul (e j).value
  let value := ((prod 0 1).add (prod 0 2)).add (prod 1 2)
  let first := (pt 0).sub (DyadicBounds.sumThree (fun i => (e i).value.mul (e i).first))
  let second := (pt 0).sub (DyadicBounds.sumThree (fun i => (e i).first.square))
  ⟨value, first, second⟩

def radicalPowerInterval (a b s : IntervalJet) : DyadicBounds :=
  ((a.value.square.mul b.value.square).mul b.value).div s.value.square

def radicalInterval (c : ParameterCell) (roots : Fin 3 → RatBounds) (k j : Fin 3) : IntervalJet :=
  let a := radicalBaseInterval c k j
  let b := radicalOtherInterval c k j
  let s := radicalSigmaInterval c k
  let P := radicalPowerInterval a b s
  let r₀ := DyadicBounds.ofRat (roots j)
  let r₁ := r₀.refineRadical P
  let r₂ := r₁.refineRadical P
  let r₃ := r₂.refineRadical P
  IntervalJet.radical r₃ a b s

def betaCoordinateInterval (c : ParameterCell) (k : Fin 3) (i : Fin 4) : IntervalJet :=
  let e := directionInterval c k
  ![IntervalJet.const 1, (e 0).div (e 1), (e 0).div (e 2), (e 0).mul (etaRatioInterval c k)] i

def betaNumeratorInterval (c : ParameterCell) (k : Fin 3) (i : Fin 4) : IntervalJet :=
  let v := betaCoordinateInterval c k i
  v.mul v

def betaDenInterval (c : ParameterCell) (k : Fin 3) : IntervalJet :=
  let n := betaNumeratorInterval c k
  (((n 0).add (n 1)).add (n 2)).add (n 3)

def betaInterval (c : ParameterCell) (k j : Fin 3) : IntervalJet :=
  (betaNumeratorInterval c k j.castSucc).div (betaDenInterval c k)

def betaHeavyInterval (c : ParameterCell) (k : Fin 3) : IntervalJet :=
  let v := (directionInterval c k 0).mul ((IntervalJet.const 1).add (etaRatioInterval c k))
  (v.mul v).div (betaDenInterval c k)

def complementInterval (c : ParameterCell) (k i : Fin 3) : IntervalJet :=
  (IntervalJet.const 1).sub (directionInterval c k i)

def signedRadicalInterval (R : Fin 3 → IntervalJet) (j : Fin 3) : IntervalJet :=
  IntervalJet.sumThree (fun i => IntervalJet.scale (if i = j then -1 else 1) (R i))

def sharedCoefficientInterval (ε bh : IntervalJet) (R S b e : Fin 3 → IntervalJet) : IntervalJet :=
  let T := IntervalJet.sumThree R
  let first := (((ε.mul bh).mul ((IntervalJet.const 1).sub ε)).mul (T.sub ε))
  let next := fun i => ((b i).mul (e i)).mul (ε.add (S i))
  (IntervalJet.scale (2 / 3) first).add (IntervalJet.sumThree (fun i => IntervalJet.scale (2 / 3) (next i)))

def dInterval (ε bh X A : IntervalJet) (b R S : Fin 3 → IntervalJet) (j : Fin 3) : IntervalJet :=
  let M := (IntervalJet.const 1).sub (ε.mul A)
  let first := M.mul ((IntervalJet.const 1).sub (IntervalJet.scale 2 (b j)))
  let second := A.mul (S j)
  let third := IntervalJet.scale (-2) (((ε.mul bh).mul (R j)).mul M)
  let fourth := IntervalJet.scale (-2) (A.mul (((b (j + 1)).mul (R (j + 2))).add ((b (j + 2)).mul (R (j + 1)))))
  (((first.add second).add third).add fourth).add X

structure AxisCoefficientIntervals where
  d : Vector IntervalJet 3
  weight : Vector IntervalJet 3
  h : Vector (Vector IntervalJet 3) 3

/-- The coefficient intervals from the three radical jets of this axis. -/
def axisCoefficientsFromRadicals (c : ParameterCell) (k : Fin 3) (R : Vector IntervalJet 3) : AxisCoefficientIntervals :=
  let S := Vector.ofFn (signedRadicalInterval R.get)
  let e := Vector.ofFn (directionInterval c k)
  let A := Vector.ofFn (complementInterval c k)
  let b := Vector.ofFn (betaInterval c k)
  let bh := betaHeavyInterval c k
  let ε := depthInterval c k
  let X := sharedCoefficientInterval ε bh R.get S.get b.get e.get
  let d := Vector.ofFn fun j => dInterval ε bh X (A.get j) b.get R.get S.get j
  let η := coordinateInterval c k 2
  let n := (IntervalJet.const 1).add (IntervalJet.scale 2 η)
  let weight := Vector.ofFn fun j => (n.mul (R.get j)).add (η.mul (d.get j))
  ⟨d, weight, Vector.ofFn fun i => Vector.ofFn fun j => (A.get i).mul (weight.get j)⟩

def axisCoefficientIntervals (c : ParameterCell) (roots : Fin 3 → RatBounds) (k : Fin 3) : AxisCoefficientIntervals :=
  axisCoefficientsFromRadicals c k (Vector.ofFn (radicalInterval c roots k))

def qInterval : DyadicBounds := DyadicBounds.ofRat ⟨15849/10000, 317/200⟩

/-- The upper bound on one coefficient of |zᵢ|^q in the directional curvature. -/
def curvatureInterval (v : AxisCoefficientIntervals) (i : Fin 3) : DyadicBounds :=
  let d := (v.d.get i).second
  let h := fun j l => ((v.h.get j).get l).second
  let diag := d.add (qInterval.mul (h i i))
  let row := (h i (i+1)).abs.add (h i (i+2)).abs
  let col := (h (i+1) i).abs.add (h (i+2) i).abs
  (diag.add row).add ((qInterval.sub (DyadicBounds.point 1)).mul col)

def radicalIntervalTable (c : ParameterCell) (roots : Fin 3 → RatBounds) : Vector (Vector IntervalJet 3) 3 :=
  Vector.ofFn fun k => Vector.ofFn (radicalInterval c roots k)

def subcellCurvatureFromRadicalsOK (c : ParameterCell) (table : Vector (Vector IntervalJet 3) 3)
    (maxima : Fin 3 → Fin 3 → ℚ) (weightFloor : ℚ) : Bool :=
  let v := Vector.ofFn fun k => axisCoefficientsFromRadicals c k (table.get k)
  (List.finRange 3).all (fun j => ((v.get 0).weight.get j).value.lowerOK weightFloor) &&
  (List.finRange 3).all fun k => (List.finRange 3).all fun i => (curvatureInterval (v.get k) i).upperOK (maxima k i)

/-- Finite comparisons for one subcell, after the parent fifth roots have been supplied. -/
def subcellCurvatureOK (c : ParameterCell) (roots : Fin 3 → RatBounds) (maxima : Fin 3 → Fin 3 → ℚ)
    (weightFloor : ℚ) : Bool :=
  subcellCurvatureFromRadicalsOK c (radicalIntervalTable c roots) maxima weightFloor

/-- Replaying the radical jets and downstream comparisons separately shares the intermediate values. -/
theorem subcellCurvatureOK_of_radical_table {c : ParameterCell} {roots : Fin 3 → RatBounds}
    {table : Vector (Vector IntervalJet 3) 3} {maxima : Fin 3 → Fin 3 → ℚ} {weightFloor : ℚ}
    (hr : radicalIntervalTable c roots = table) (hc : subcellCurvatureFromRadicalsOK c table maxima weightFloor = true) :
    subcellCurvatureOK c roots maxima weightFloor = true := by
  unfold subcellCurvatureOK
  rw [hr]
  exact hc

namespace RatBounds

def knot (r : RatBounds) (n i : ℕ) : ℚ := r.lo + (i : ℚ) * ((r.hi-r.lo) / n)

def subinterval (r : RatBounds) (n i : ℕ) : RatBounds := ⟨r.knot n i, r.knot n (i+1)⟩

end RatBounds

namespace ParameterCell

def coordinate (c : ParameterCell) (i : Fin 3) : RatBounds := ![c.a,c.b,c.η] i

def grid (c : ParameterCell) (na nb nη : ℕ) : List ParameterCell :=
  (List.finRange na).flatMap fun i =>
    (List.finRange nb).flatMap fun j =>
      (List.finRange nη).map fun k =>
        ⟨c.a.subinterval na i.val, c.b.subinterval nb j.val, c.η.subinterval nη k.val⟩

end ParameterCell

def gridCurvatureOK (c : ParameterCell) (roots : Fin 3 → RatBounds) (na nb nη : ℕ)
    (maxima : Fin 3 → Fin 3 → ℚ) (weightFloor : ℚ) : Bool :=
  (c.grid na nb nη).all fun d => subcellCurvatureOK d roots maxima weightFloor

/-- A single first-coordinate layer, so a grid can be replayed in independent blocks. -/
def gridLayerCurvatureOK (c : ParameterCell) (roots : Fin 3 → RatBounds) (na nb nη : ℕ)
    (maxima : Fin 3 → Fin 3 → ℚ) (weightFloor : ℚ) (i : Fin na) : Bool :=
  (List.finRange nb).all fun j => (List.finRange nη).all fun k => subcellCurvatureOK
    ⟨c.a.subinterval na i.val, c.b.subinterval nb j.val, c.η.subinterval nη k.val⟩ roots maxima weightFloor

theorem gridLayerCurvatureOK_of_cells {c : ParameterCell} {roots : Fin 3 → RatBounds} {na nb nη : ℕ}
    {maxima : Fin 3 → Fin 3 → ℚ} {weightFloor : ℚ} (i : Fin na)
    (h : ∀ (j : Fin nb) (k : Fin nη), subcellCurvatureOK
      ⟨c.a.subinterval na i.val, c.b.subinterval nb j.val, c.η.subinterval nη k.val⟩ roots maxima weightFloor = true) :
    gridLayerCurvatureOK c roots na nb nη maxima weightFloor i = true := by
  simp only [gridLayerCurvatureOK, List.all_eq_true]
  exact fun j _ k _ => h j k

/-- The three curvature allowances to pay at each parent corner. -/
def curvatureLoss (c : ParameterCell) (maxima : Fin 3 → Fin 3 → ℚ) (i : Fin 3) : ℚ :=
  ∑ k, maxima k i * ((c.coordinate k).hi - (c.coordinate k).lo)^2 / 8

end HlawkaSchatten.BelowExponent.Vertex
