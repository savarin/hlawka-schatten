/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import Mathlib.Data.Rat.Floor

/-! Kernel-reduction forms of integer minimum, maximum and sign tests: each reads the constructor of
an `Int.*_k` result, and each is proved equal to the operation it replaces for all inputs. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

/-- `Int.rec` on the sign of `x`, as an `if`. -/
theorem intRec_eq_ite_nonneg {α : Sort u} (x : ℤ) (p q : α) :
    Int.rec (motive := fun _ => α) (fun _ => p) (fun _ => q) x = if 0 ≤ x then p else q := by
  cases x with
  | ofNat n => simp
  | negSucc n => simp

/-- `decide (0 ≤ x)` by the constructor of `x`. -/
noncomputable def intNonnegK (x : ℤ) : Bool :=
  Int.rec (motive := fun _ => Bool) (fun _ => true) (fun _ => false) x

theorem intNonnegK_eq (x : ℤ) : intNonnegK x = decide (0 ≤ x) := by
  unfold intNonnegK; rw [intRec_eq_ite_nonneg]; by_cases h : 0 ≤ x <;> simp [h]

/-- `min` and `max` on `ℤ` by the sign of `b - a`, on the kernel integer operations. -/
noncomputable def intMinK (a b : ℤ) : ℤ :=
  Int.rec (motive := fun _ => ℤ) (fun _ => a) (fun _ => b) (Int.sub_k b a)

noncomputable def intMaxK (a b : ℤ) : ℤ :=
  Int.rec (motive := fun _ => ℤ) (fun _ => b) (fun _ => a) (Int.sub_k b a)

/-- `decide (0 < x)` by the constructor of `x`. -/
noncomputable def intPosK (x : ℤ) : Bool :=
  Int.rec (motive := fun _ => Bool) (fun n => Nat.blt 0 n) (fun _ => false) x

theorem intPosK_eq (x : ℤ) : intPosK x = decide (0 < x) := by
  cases x with
  | ofNat n =>
    show Nat.blt 0 n = decide (0 < (n : ℤ))
    rw [Bool.eq_iff_iff, decide_eq_true_iff, Nat.blt_eq]; omega
  | negSucc n => simp [intPosK]

theorem intMinK_eq (a b : ℤ) : intMinK a b = min a b := by
  unfold intMinK
  rw [Int.sub_k_eq]
  rcases h : b - a with n | n
  · show a = min a b
    have : 0 ≤ b - a := by rw [h]; exact Int.natCast_nonneg n
    exact (min_eq_left (by omega)).symm
  · show b = min a b
    have : b - a < 0 := by rw [h]; exact Int.negSucc_lt_zero n
    exact (min_eq_right (by omega)).symm

theorem intMaxK_eq (a b : ℤ) : intMaxK a b = max a b := by
  unfold intMaxK
  rw [Int.sub_k_eq]
  rcases h : b - a with n | n
  · show b = max a b
    have : 0 ≤ b - a := by rw [h]; exact Int.natCast_nonneg n
    exact (max_eq_right (by omega)).symm
  · show a = max a b
    have : b - a < 0 := by rw [h]; exact Int.negSucc_lt_zero n
    exact (max_eq_left (by omega)).symm

end HlawkaSchatten.BelowExponent.Vertex
