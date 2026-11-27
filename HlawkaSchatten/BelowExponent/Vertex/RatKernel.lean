/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.IntegerKernel
public import HlawkaSchatten.BelowExponent.Vertex.RadicalCheck
public import HlawkaSchatten.BelowExponent.G3Power
public import Mathlib.Data.Rat.Floor

/-! Kernel-reduction forms of rational operations: `RatK`, unreduced fractions with a positive
denominator. Each operation is proved to agree with the operation it replaces for all inputs, on
values (`RatK.val`, `RatBoundsK.val`). Shared by the families whose checkers run rational
arithmetic in the kernel. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

/-! ### Exact fractions for kernel reduction -/

/-- The fraction `num / (pred + 1)`, not reduced: its operations never compute a gcd, and its
denominator is positive by construction. Each operation is proved to act on `val` as the rational
operation it replaces. -/
structure RatK where
  num : ℤ
  pred : ℕ

namespace RatK

/-- The rational number `num / (pred + 1)`. -/
def val (x : RatK) : ℚ := (x.num : ℚ) / ((x.pred : ℚ) + 1)

theorem den_pos (x : RatK) : (0 : ℚ) < (x.pred : ℚ) + 1 := by positivity

/-- A rational in lowest terms. -/
def ofRat (q : ℚ) : RatK := ⟨q.num, q.den - 1⟩

theorem val_ofRat (q : ℚ) : (ofRat q).val = q := by
  have h : ((q.den - 1 : ℕ) : ℚ) + 1 = q.den := by
    have := q.den_pos; exact_mod_cast (by omega : q.den - 1 + 1 = q.den)
  simp only [val, ofRat, h, Rat.num_div_den]

def zero : RatK := ⟨Int.ofNat 0, 0⟩
def one : RatK := ⟨Int.ofNat 1, 0⟩
def two : RatK := ⟨Int.ofNat 2, 0⟩
def four : RatK := ⟨Int.ofNat 4, 0⟩
def negOne : RatK := ⟨Int.negSucc 0, 0⟩
@[simp] theorem val_zero : zero.val = 0 := by simp [val, zero]
@[simp] theorem val_one : one.val = 1 := by simp [val, one]
@[simp] theorem val_two : two.val = 2 := by simp [val, two]
@[simp] theorem val_four : four.val = 4 := by simp [val, four]
@[simp] theorem val_negOne : negOne.val = -1 := by simp [val, negOne]
private theorem pred_mul_cast (x y : RatK) :
    ((Nat.add (Nat.add (Nat.mul x.pred y.pred) x.pred) y.pred : ℕ) : ℚ) + 1 =
      ((x.pred : ℚ) + 1) * ((y.pred : ℚ) + 1) := by
  simp only [Nat.add_eq, Nat.mul_eq]; push_cast; ring

noncomputable def mul (x y : RatK) : RatK :=
  ⟨Int.mul_k x.num y.num, Nat.add (Nat.add (Nat.mul x.pred y.pred) x.pred) y.pred⟩

noncomputable def add (x y : RatK) : RatK :=
  ⟨Int.add_k (Int.mul_k x.num (Int.ofNat (Nat.succ y.pred)))
      (Int.mul_k y.num (Int.ofNat (Nat.succ x.pred))),
    Nat.add (Nat.add (Nat.mul x.pred y.pred) x.pred) y.pred⟩

noncomputable def sub (x y : RatK) : RatK :=
  ⟨Int.sub_k (Int.mul_k x.num (Int.ofNat (Nat.succ y.pred)))
      (Int.mul_k y.num (Int.ofNat (Nat.succ x.pred))),
    Nat.add (Nat.add (Nat.mul x.pred y.pred) x.pred) y.pred⟩

/-- `x⁻¹`, with `0⁻¹ = 0` as in `ℚ`. -/
noncomputable def inv (x : RatK) : RatK :=
  Int.rec (motive := fun _ => RatK)
    (fun n => Nat.rec (motive := fun _ => RatK) ⟨Int.ofNat 0, 0⟩
      (fun k _ => ⟨Int.ofNat (Nat.succ x.pred), k⟩) n)
    (fun n => ⟨Int.negSucc x.pred, n⟩) x.num

theorem val_mul (x y : RatK) : (x.mul y).val = x.val * y.val := by
  simp only [val, mul, pred_mul_cast, Int.mul_k_eq, Int.mul_def, Int.cast_mul]
  rw [mul_div_mul_comm]

theorem val_add (x y : RatK) : (x.add y).val = x.val + y.val := by
  have hx := x.den_pos; have hy := y.den_pos
  simp only [val, add, pred_mul_cast, Int.add_k_eq, Int.mul_k_eq, Int.mul_def, Int.add_def,
    Int.ofNat_eq_natCast, Nat.succ_eq_add_one]
  push_cast
  field_simp

theorem val_sub (x y : RatK) : (x.sub y).val = x.val - y.val := by
  have hx := x.den_pos; have hy := y.den_pos
  simp only [val, sub, pred_mul_cast, Int.sub_k_eq, Int.mul_k_eq, Int.mul_def,
    Int.ofNat_eq_natCast, Nat.succ_eq_add_one]
  push_cast
  field_simp

theorem val_inv (x : RatK) : x.inv.val = x.val⁻¹ := by
  have hx := x.den_pos
  rcases x with ⟨n | n, p⟩
  · rcases n with _ | k
    · simp [inv, val]
    · simp only [inv, val, Int.ofNat_eq_natCast, Nat.succ_eq_add_one, inv_div]
      push_cast; ring
  · simp only [inv, val, Int.cast_negSucc, inv_div]
    push_cast
    rw [neg_div, div_neg]

/-- `decide (x.val ≤ y.val)`, by cross-multiplication. -/
noncomputable def le (x y : RatK) : Bool :=
  intNonnegK (Int.sub_k (Int.mul_k y.num (Int.ofNat (Nat.succ x.pred)))
    (Int.mul_k x.num (Int.ofNat (Nat.succ y.pred))))

/-- `decide (x.val < y.val)`, by cross-multiplication. -/
noncomputable def lt (x y : RatK) : Bool :=
  intPosK (Int.sub_k (Int.mul_k y.num (Int.ofNat (Nat.succ x.pred)))
    (Int.mul_k x.num (Int.ofNat (Nat.succ y.pred))))

private theorem cross_iff (x y : RatK) :
    x.val ≤ y.val ↔ x.num * ((y.pred : ℤ) + 1) ≤ y.num * ((x.pred : ℤ) + 1) := by
  simp only [val]
  rw [div_le_div_iff₀ x.den_pos y.den_pos]
  constructor <;> intro h
  · exact_mod_cast h
  · exact_mod_cast h

private theorem cross_lt_iff (x y : RatK) :
    x.val < y.val ↔ x.num * ((y.pred : ℤ) + 1) < y.num * ((x.pred : ℤ) + 1) := by
  simp only [val]
  rw [div_lt_div_iff₀ x.den_pos y.den_pos]
  constructor <;> intro h
  · exact_mod_cast h
  · exact_mod_cast h

theorem le_eq (x y : RatK) : x.le y = decide (x.val ≤ y.val) := by
  simp only [le, intNonnegK_eq, Int.sub_k_eq, Int.mul_k_eq, Int.mul_def, Int.ofNat_eq_natCast,
    Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
  apply decide_eq_decide.mpr
  rw [cross_iff, sub_nonneg]

theorem lt_eq (x y : RatK) : x.lt y = decide (x.val < y.val) := by
  simp only [lt, intPosK_eq, Int.sub_k_eq, Int.mul_k_eq, Int.mul_def, Int.ofNat_eq_natCast,
    Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
  apply decide_eq_decide.mpr
  rw [cross_lt_iff, sub_pos]

/-- `decide (x.val = 0)`. -/
noncomputable def isZero (x : RatK) : Bool := Int.beqZero_k x.num

theorem isZero_eq (x : RatK) : x.isZero = decide (x.val = 0) := by
  have hx := x.den_pos
  simp only [isZero, Int.beqZero_k_eq, val, div_eq_zero_iff, Int.cast_eq_zero, hx.ne', or_false]
  by_cases h : x.num = 0 <;> simp [h]

noncomputable def minK (x y : RatK) : RatK := Bool.rec y x (x.le y)
noncomputable def maxK (x y : RatK) : RatK := Bool.rec x y (x.le y)

theorem val_minK (x y : RatK) : (x.minK y).val = min x.val y.val := by
  unfold minK; rw [le_eq]
  by_cases h : x.val ≤ y.val
  · simp [h]
  · simp [h, min_eq_right (le_of_not_ge h)]

theorem val_maxK (x y : RatK) : (x.maxK y).val = max x.val y.val := by
  unfold maxK; rw [le_eq]
  by_cases h : x.val ≤ y.val
  · simp [h]
  · simp [h, max_eq_left (le_of_not_ge h)]

/-- `⌊x.val⌋` and `⌈x.val⌉` by integer division. -/
noncomputable def floor (x : RatK) : ℤ := Int.ediv_k x.num (Int.ofNat (Nat.succ x.pred))
noncomputable def ceil (x : RatK) : ℤ :=
  Int.neg_k (Int.ediv_k (Int.neg_k x.num) (Int.ofNat (Nat.succ x.pred)))

theorem floor_eq (x : RatK) : x.floor = ⌊x.val⌋ := by
  have h := Rat.floor_intCast_div_natCast x.num (x.pred + 1)
  push_cast at h
  simp only [floor, val, Int.ediv_k_eq, Int.ofNat_eq_natCast, Nat.succ_eq_add_one, h]
  push_cast; rfl

theorem ceil_eq (x : RatK) : x.ceil = ⌈x.val⌉ := by
  have h := Rat.floor_intCast_div_natCast (-x.num) (x.pred + 1)
  push_cast at h
  rw [neg_div, Int.floor_neg] at h
  simp only [ceil, val, Int.ediv_k_eq, Int.neg_k_eq, Int.ofNat_eq_natCast, Nat.succ_eq_add_one]
  show -((-x.num) / ((x.pred + 1 : ℕ) : ℤ)) = ⌈(x.num : ℚ) / ((x.pred : ℚ) + 1)⌉
  push_cast
  rw [← h, neg_neg]

private theorem natAbs_cross_iff {a c : ℤ} {b d : ℕ} (hb : 0 < b) (hd : 0 < d) (m n : ℕ) :
    a.natAbs ^ m * d ^ n ≤ c.natAbs ^ n * b ^ m ↔
      |(a : ℚ) / b| ^ m ≤ |(c : ℚ) / d| ^ n := by
  have hb' : (0 : ℚ) < b := by exact_mod_cast hb
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  rw [abs_div, abs_div, Nat.abs_cast, Nat.abs_cast, div_pow, div_pow,
    div_le_div_iff₀ (by positivity) (by positivity), ← Nat.cast_le (α := ℚ)]
  push_cast
  simp only [Nat.cast_natAbs, Int.cast_abs]

/-- `G3Power.crossLE` on values, by cross-multiplied powers. -/
noncomputable def crossLE (x y : RatK) (m n : ℕ) : Bool :=
  Nat.ble (Nat.mul (Nat.pow (Int.natAbs_k x.num) m) (Nat.pow (Nat.succ y.pred) n))
    (Nat.mul (Nat.pow (Int.natAbs_k y.num) n) (Nat.pow (Nat.succ x.pred) m))

theorem crossLE_eq (x y : RatK) (m n : ℕ) : x.crossLE y m n = G3Power.crossLE x.val y.val m n := by
  unfold crossLE G3Power.crossLE
  rw [Bool.eq_iff_iff, Nat.ble_eq, decide_eq_true_iff]
  simp only [Nat.mul_eq, Nat.pow_eq, Int.natAbs_k_eq, Nat.succ_eq_add_one]
  rw [natAbs_cross_iff (Nat.succ_pos _) (Nat.succ_pos _),
    natAbs_cross_iff x.val.den_pos y.val.den_pos, Rat.num_div_den, Rat.num_div_den]
  simp only [val, Nat.cast_succ]

/-- The lowest-terms form of `x`, by one gcd: `reduce x = ofRat x.val`. -/
noncomputable def reduce (x : RatK) : RatK :=
  let g := Nat.gcd (Nat.succ x.pred) (Int.natAbs_k x.num)
  ⟨Int.ediv_k x.num (Int.ofNat g), Nat.sub (Nat.div (Nat.succ x.pred) g) 1⟩

theorem reduce_eq (x : RatK) : x.reduce = ofRat x.val := by
  have hv : x.val = mkRat x.num (x.pred + 1) := by
    rw [val, Rat.mkRat_eq_div]; push_cast; rfl
  have hd : (mkRat x.num (x.pred + 1)).den = (x.pred + 1) / (x.pred + 1).gcd x.num.natAbs := by
    rw [Rat.den_mkRat]; simp
  have hn : (mkRat x.num (x.pred + 1)).num = x.num / (((x.pred + 1).gcd x.num.natAbs : ℕ) : ℤ) := by
    rw [Rat.num_mkRat]; simp
  unfold reduce ofRat
  rw [hv, hd, hn]
  simp only [Int.ediv_k_eq, Int.natAbs_k_eq, Int.ofNat_eq_natCast, Nat.succ_eq_add_one]
  rfl

theorem val_reduce (x : RatK) : x.reduce.val = x.val := by rw [reduce_eq, val_ofRat]

end RatK

/-- Rational intervals with `RatK` endpoints. -/
structure RatBoundsK where
  lo : RatK
  hi : RatK

namespace RatBoundsK

def val (a : RatBoundsK) : RatBounds := ⟨a.lo.val, a.hi.val⟩
def ofRat (a : RatBounds) : RatBoundsK := ⟨RatK.ofRat a.lo, RatK.ofRat a.hi⟩
def point (x : RatK) : RatBoundsK := ⟨x, x⟩

noncomputable def add (a b : RatBoundsK) : RatBoundsK := ⟨a.lo.add b.lo, a.hi.add b.hi⟩
noncomputable def sub (a b : RatBoundsK) : RatBoundsK := ⟨a.lo.sub b.hi, a.hi.sub b.lo⟩
noncomputable def mul (a b : RatBoundsK) : RatBoundsK :=
  let p1 := a.lo.mul b.lo
  let p2 := a.lo.mul b.hi
  let p3 := a.hi.mul b.lo
  let p4 := a.hi.mul b.hi
  ⟨(p1.minK p2).minK (p3.minK p4), (p1.maxK p2).maxK (p3.maxK p4)⟩
theorem val_ofRat (a : RatBounds) : (ofRat a).val = a := by simp [val, ofRat, RatK.val_ofRat]
theorem val_point (x : RatK) : (point x).val = RatBounds.point x.val := rfl
theorem val_add (a b : RatBoundsK) : (a.add b).val = a.val.add b.val := by
  simp [val, add, RatBounds.add, RatK.val_add]
theorem val_sub (a b : RatBoundsK) : (a.sub b).val = a.val.sub b.val := by
  simp [val, sub, RatBounds.sub, RatK.val_sub]
theorem val_mul (a b : RatBoundsK) : (a.mul b).val = a.val.mul b.val := by
  simp [val, mul, RatBounds.mul, RatK.val_minK, RatK.val_maxK, RatK.val_mul]
end RatBoundsK

end HlawkaSchatten.BelowExponent.Vertex
