/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.RadicalCheck
public import HlawkaSchatten.BelowExponent.Vertex.IntegerKernel
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

theorem units_int : ((units : ℕ) : ℤ) = Int.ofNat 79228162514264337593543950336 := by
  simp only [units, Int.ofNat_eq_natCast]; norm_num

private theorem units_pos_rat : (0 : ℚ) < ((units : ℕ) : ℚ) := by
  simp only [units]; positivity

def lower (a : DyadicBounds) : ℚ := (a.lo : ℚ) / (units : ℚ)

def upper (a : DyadicBounds) : ℚ := (a.hi : ℚ) / (units : ℚ)

def ofRatImpl (a : RatBounds) : DyadicBounds := ⟨⌊a.lo * units⌋, ⌈a.hi * units⌉, true⟩

/-- `⌊a.lo * 2^96⌋` and `⌈a.hi * 2^96⌉` by integer division of the lowest-terms fractions, for
kernel reduction; compiled code runs `ofRatImpl` (`ofRat_eq_ofRatImpl`). -/
noncomputable def ofRat (a : RatBounds) : DyadicBounds :=
  ⟨Int.ediv_k (Int.mul_k a.lo.num (Int.ofNat 79228162514264337593543950336)) (Int.ofNat a.lo.den),
    Int.neg_k (Int.ediv_k (Int.neg_k (Int.mul_k a.hi.num (Int.ofNat 79228162514264337593543950336)))
      (Int.ofNat a.hi.den)), true⟩

private theorem floor_mul_units (q : ℚ) :
    ⌊q * ((units : ℕ) : ℚ)⌋ = q.num * ((units : ℕ) : ℤ) / (q.den : ℤ) := by
  rw [← Rat.floor_intCast_div_natCast]; congr 1
  conv_lhs => rw [← Rat.num_div_den q]
  push_cast; ring

@[csimp] theorem ofRat_eq_ofRatImpl : @ofRat = @ofRatImpl := by
  funext a
  have hc : ⌈a.hi * ((units : ℕ) : ℚ)⌉ =
      -((-(a.hi.num * ((units : ℕ) : ℤ))) / (a.hi.den : ℤ)) := by
    have h1 : ⌈a.hi * ((units : ℕ) : ℚ)⌉ = -⌊(-a.hi) * ((units : ℕ) : ℚ)⌋ := by
      rw [neg_mul, Int.floor_neg, neg_neg]
    rw [h1, floor_mul_units, Rat.neg_num, Rat.neg_den, neg_mul]
  simp only [ofRat, ofRatImpl, Int.ediv_k_eq, Int.mul_k_eq, Int.neg_k_eq, Int.mul_def, units_int.symm,
    Int.ofNat_eq_natCast, floor_mul_units, hc]
  rfl

theorem ofRat_def (a : RatBounds) : ofRat a = ⟨⌊a.lo * units⌋, ⌈a.hi * units⌉, true⟩ := by
  rw [ofRat_eq_ofRatImpl]; rfl

def point (q : ℚ) : DyadicBounds := ofRat (RatBounds.point q)

def ofNumerator (n : ℤ) : DyadicBounds := ⟨n, n, true⟩

def require (a : DyadicBounds) (b : Bool) : DyadicBounds := { a with ok := a.ok && b }

def addImpl (a b : DyadicBounds) : DyadicBounds := ⟨a.lo+b.lo, a.hi+b.hi, a.ok && b.ok⟩

noncomputable def add (a b : DyadicBounds) : DyadicBounds :=
  ⟨Int.add_k a.lo b.lo, Int.add_k a.hi b.hi, a.ok && b.ok⟩

@[csimp] theorem add_eq_addImpl : @add = @addImpl := by
  funext a b; simp only [add, addImpl, Int.add_k_eq, Int.add_def]

theorem add_def (a b : DyadicBounds) : a.add b = ⟨a.lo+b.lo, a.hi+b.hi, a.ok && b.ok⟩ := by
  rw [add_eq_addImpl]; rfl

def subImpl (a b : DyadicBounds) : DyadicBounds := ⟨a.lo-b.hi, a.hi-b.lo, a.ok && b.ok⟩

noncomputable def sub (a b : DyadicBounds) : DyadicBounds :=
  ⟨Int.sub_k a.lo b.hi, Int.sub_k a.hi b.lo, a.ok && b.ok⟩

@[csimp] theorem sub_eq_subImpl : @sub = @subImpl := by
  funext a b; simp only [sub, subImpl, Int.sub_k_eq]

theorem sub_def (a b : DyadicBounds) : a.sub b = ⟨a.lo-b.hi, a.hi-b.lo, a.ok && b.ok⟩ := by
  rw [sub_eq_subImpl]; rfl

def ceilDiv (a b : ℤ) : ℤ := -((-a) / b)

def productLo (a b : DyadicBounds) : ℤ :=
  min (min (a.lo*b.lo) (a.lo*b.hi)) (min (a.hi*b.lo) (a.hi*b.hi))

def productHi (a b : DyadicBounds) : ℤ :=
  max (max (a.lo*b.lo) (a.lo*b.hi)) (max (a.hi*b.lo) (a.hi*b.hi))

def mulImpl (a b : DyadicBounds) : DyadicBounds :=
  ⟨productLo a b / units, ceilDiv (productHi a b) units, a.ok && b.ok⟩

noncomputable def mul (a b : DyadicBounds) : DyadicBounds :=
  let p1 := Int.mul_k a.lo b.lo
  let p2 := Int.mul_k a.lo b.hi
  let p3 := Int.mul_k a.hi b.lo
  let p4 := Int.mul_k a.hi b.hi
  ⟨Int.ediv_k (intMinK (intMinK p1 p2) (intMinK p3 p4)) (Int.ofNat 79228162514264337593543950336),
    Int.neg_k (Int.ediv_k (Int.neg_k (intMaxK (intMaxK p1 p2) (intMaxK p3 p4))) (Int.ofNat 79228162514264337593543950336)),
    a.ok && b.ok⟩

@[csimp] theorem mul_eq_mulImpl : @mul = @mulImpl := by
  funext a b
  simp only [mul, mulImpl, productLo, productHi, ceilDiv, intMinK_eq, intMaxK_eq, Int.mul_k_eq,
    Int.ediv_k_eq, Int.neg_k_eq, units_int]
  rfl

theorem mul_def (a b : DyadicBounds) :
    a.mul b = ⟨productLo a b / units, ceilDiv (productHi a b) units, a.ok && b.ok⟩ := by
  rw [mul_eq_mulImpl]; rfl

def absImpl (a : DyadicBounds) : DyadicBounds := ⟨max 0 (max a.lo (-a.hi)), max |a.lo| |a.hi|, a.ok⟩

noncomputable def abs (a : DyadicBounds) : DyadicBounds :=
  ⟨intMaxK (Int.ofNat 0) (intMaxK a.lo (Int.neg_k a.hi)),
    intMaxK (Int.ofNat (Int.natAbs_k a.lo)) (Int.ofNat (Int.natAbs_k a.hi)), a.ok⟩

@[csimp] theorem abs_eq_absImpl : @abs = @absImpl := by
  funext a
  simp only [abs, absImpl, intMaxK_eq, Int.neg_k_eq, Int.natAbs_k_eq, Int.ofNat_eq_natCast,
    Int.natCast_natAbs, Nat.cast_zero]
  rfl

theorem abs_def (a : DyadicBounds) : a.abs = ⟨max 0 (max a.lo (-a.hi)), max |a.lo| |a.hi|, a.ok⟩ := by
  rw [abs_eq_absImpl]; rfl

def square (a : DyadicBounds) : DyadicBounds := a.abs.mul a.abs

def reciprocalImpl (a : DyadicBounds) : DyadicBounds := ⟨
  ((units : ℤ) * units) / a.hi, ceilDiv ((units : ℤ) * units) a.lo, a.ok && decide (0 < a.lo)⟩

noncomputable def reciprocal (a : DyadicBounds) : DyadicBounds :=
  ⟨Int.ediv_k (Int.ofNat 6277101735386680763835789423207666416102355444464034512896) a.hi,
    Int.neg_k (Int.ediv_k (Int.neg_k (Int.ofNat 6277101735386680763835789423207666416102355444464034512896)) a.lo), a.ok && intPosK a.lo⟩

@[csimp] theorem reciprocal_eq_reciprocalImpl : @reciprocal = @reciprocalImpl := by
  funext a
  have h : ((units : ℕ) : ℤ) * ((units : ℕ) : ℤ) = Int.ofNat 6277101735386680763835789423207666416102355444464034512896 := by
    simp only [units, Int.ofNat_eq_natCast]; norm_num
  simp only [reciprocal, reciprocalImpl, ceilDiv, h, Int.ediv_k_eq, Int.neg_k_eq, intPosK_eq]
  rfl

theorem reciprocal_def (a : DyadicBounds) : a.reciprocal = ⟨((units : ℤ) * units) / a.hi,
    ceilDiv ((units : ℤ) * units) a.lo, a.ok && decide (0 < a.lo)⟩ := by
  rw [reciprocal_eq_reciprocalImpl]; rfl

def div (a b : DyadicBounds) : DyadicBounds := a.mul b.reciprocal

def intersectImpl (a b : DyadicBounds) : DyadicBounds := ⟨max a.lo b.lo, min a.hi b.hi, a.ok && b.ok⟩

noncomputable def intersect (a b : DyadicBounds) : DyadicBounds :=
  ⟨intMaxK a.lo b.lo, intMinK a.hi b.hi, a.ok && b.ok⟩

@[csimp] theorem intersect_eq_intersectImpl : @intersect = @intersectImpl := by
  funext a b; simp only [intersect, intersectImpl, intMaxK_eq, intMinK_eq]

theorem intersect_def (a b : DyadicBounds) :
    a.intersect b = ⟨max a.lo b.lo, min a.hi b.hi, a.ok && b.ok⟩ := by
  rw [intersect_eq_intersectImpl]; rfl

def upperOKImpl (a : DyadicBounds) (q : ℚ) : Bool := a.ok && decide (a.upper ≤ q)

noncomputable def upperOK (a : DyadicBounds) (q : ℚ) : Bool :=
  a.ok && intNonnegK (Int.sub_k (Int.mul_k q.num (Int.ofNat 79228162514264337593543950336)) (Int.mul_k a.hi (Int.ofNat q.den)))

@[csimp] theorem upperOK_eq_upperOKImpl : @upperOK = @upperOKImpl := by
  funext a q
  unfold upperOK upperOKImpl upper
  congr 1
  rw [intNonnegK_eq, Int.sub_k_eq, Int.mul_k_eq, Int.mul_k_eq, Int.mul_def, Int.mul_def, ← units_int]
  apply decide_eq_decide.mpr
  have hd : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
  rw [sub_nonneg, div_le_iff₀ units_pos_rat]
  conv_rhs => rw [← Rat.num_div_den q]
  rw [div_mul_eq_mul_div, le_div_iff₀ hd]
  constructor <;> intro h <;> exact_mod_cast h

theorem upperOK_def (a : DyadicBounds) (q : ℚ) : a.upperOK q = (a.ok && decide (a.upper ≤ q)) := by
  rw [upperOK_eq_upperOKImpl]; rfl

def lowerOKImpl (a : DyadicBounds) (q : ℚ) : Bool := a.ok && decide (q ≤ a.lower)

noncomputable def lowerOK (a : DyadicBounds) (q : ℚ) : Bool :=
  a.ok && intNonnegK (Int.sub_k (Int.mul_k a.lo (Int.ofNat q.den)) (Int.mul_k q.num (Int.ofNat 79228162514264337593543950336)))

@[csimp] theorem lowerOK_eq_lowerOKImpl : @lowerOK = @lowerOKImpl := by
  funext a q
  unfold lowerOK lowerOKImpl lower
  congr 1
  rw [intNonnegK_eq, Int.sub_k_eq, Int.mul_k_eq, Int.mul_k_eq, Int.mul_def, Int.mul_def, ← units_int]
  apply decide_eq_decide.mpr
  have hd : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
  rw [sub_nonneg, le_div_iff₀ units_pos_rat]
  conv_rhs => rw [← Rat.num_div_den q]
  rw [div_mul_eq_mul_div, div_le_iff₀ hd]
  constructor <;> intro h <;> exact_mod_cast h

theorem lowerOK_def (a : DyadicBounds) (q : ℚ) : a.lowerOK q = (a.ok && decide (q ≤ a.lower)) := by
  rw [lowerOK_eq_lowerOKImpl]; rfl

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
