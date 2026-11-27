/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FSlabNearInteger
public import HlawkaSchatten.BelowExponent.Vertex.IntegerKernel

/-! Kernel integer forms of the exact F-slab near numerators. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FSlabNearKernel

open FSlabNearInteger Vertex

noncomputable def square (x : Int) : Int := Int.mul_k x x
noncomputable def cube (x : Int) : Int := Int.mul_k (square x) x

theorem square_eq (x : Int) : square x = x^2 := by
  simp only [square, Int.mul_k_eq, Int.mul_def, pow_two]

theorem cube_eq (x : Int) : cube x = x^3 := by
  simp [cube, square_eq, Int.mul_k_eq, pow_succ]

noncomputable def upperNumK (D w : Nat) : Int :=
  let d := Int.ofNat D
  let wi := Int.ofNat w
  let n := Int.sub_k wi d
  let q := if w ≤ D then qLoNum else qHiNum
  let c := if w ≤ D then c3HiNum else c3LoNum
  Int.sub_k
    (Int.add_k
      (Int.add_k (Int.mul_k (Int.mul_k (Int.ofNat coeffDen) (square d)) (square wi))
        (Int.mul_k (Int.mul_k (Int.mul_k q n) d) (square wi)))
      (Int.mul_k (Int.mul_k c2HiNum (square n)) (square wi)))
    (Int.mul_k (Int.mul_k c (cube n)) d)

theorem upperNumK_eq (D w : Nat) : upperNumK D w = upperNum D w := by
  simp only [upperNumK, upperNum, square_eq, cube_eq, Int.mul_k_eq, Int.add_k_eq,
    Int.sub_k_eq, Int.ofNat_eq_natCast, Int.mul_def, Int.add_def]

noncomputable def tangentNumK (R : Int) (S M Da : Nat) : Int :=
  let si := Int.ofNat S
  let di := Int.ofNat Da
  let first := Int.mul_k (Int.mul_k (Int.ofNat coeffDen) (cube si)) di
  let second := Int.mul_k (Int.mul_k (Int.mul_k c2LoNum (square R)) si) di
  let third := Int.mul_k (Int.mul_k (Int.mul_k 2 c3LoNum) (cube R)) di
  let slope := Int.add_k
    (Int.add_k (Int.mul_k (Int.sub_k 0 qHiNum) (square si))
      (Int.mul_k (Int.mul_k (Int.mul_k 2 c2LoNum) R) si))
    (Int.mul_k (Int.mul_k 3 c3LoNum) (square R))
  Int.add_k (Int.sub_k (Int.sub_k first second) third)
    (Int.mul_k (Int.mul_k slope si) (Int.sub_k di (Int.ofNat M)))

theorem tangentNumK_eq (R : Int) (S M Da : Nat) :
    tangentNumK R S M Da = tangentNum R S M Da := by
  simp only [tangentNumK, tangentNum, square_eq, cube_eq, Int.mul_k_eq, Int.add_k_eq,
    Int.sub_k_eq, Int.ofNat_eq_natCast, Int.mul_def, Int.add_def, zero_sub]

noncomputable def inputNumK (Da g0 ga gb ma mb : Nat) (r s : ℚ) : Int :=
  let r3 := cube (Int.ofNat r.den)
  let s3 := cube (Int.ofNat s.den)
  let first := Int.mul_k (Int.mul_k (Int.mul_k (Int.mul_k
    (Int.ofNat g0) (Int.ofNat coeffDen)) (Int.ofNat Da)) r3) s3
  let second := Int.mul_k (Int.mul_k (Int.ofNat ga) (tangentNumK r.num r.den ma Da)) s3
  let third := Int.mul_k (Int.mul_k (Int.ofNat gb) (tangentNumK s.num s.den mb Da)) r3
  Int.mul_k 2 (Int.add_k (Int.add_k first second) third)

theorem inputNumK_eq (Da g0 ga gb ma mb : Nat) (r s : ℚ) :
    inputNumK Da g0 ga gb ma mb r s = inputNum Da g0 ga gb ma mb r s := by
  simp only [inputNumK, inputNum, tangentNumK_eq, cube_eq, Int.mul_k_eq,
    Int.add_k_eq, Int.ofNat_eq_natCast, Int.mul_def, Int.add_def]

noncomputable def sumAuxK (D : Nat) : List (Nat × Nat) → Int × Nat → Int × Nat
  | [], acc => acc
  | (p,w)::tail, (n,d) =>
    sumAuxK D tail
      (Int.add_k (Int.mul_k n (square (Int.ofNat w)))
        (Int.mul_k (Int.mul_k (Int.ofNat p) (upperNumK D w)) (Int.ofNat d)), d*w^2)

theorem sumAuxK_eq (D : Nat) (xs : List (Nat × Nat)) (acc : Int × Nat) :
    sumAuxK D xs acc = sumAux D xs acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨p,w⟩
    rcases acc with ⟨n,d⟩
    simp only [sumAuxK, sumAux, square_eq, upperNumK_eq, Int.mul_k_eq,
      Int.add_k_eq, Int.ofNat_eq_natCast, Int.mul_def, Int.add_def, ih]

noncomputable def upperSumK (D : Nat) (xs : List (Nat × Nat)) : Int × Nat :=
  sumAuxK D xs (0,1)

theorem upperSumK_eq (D : Nat) (xs : List (Nat × Nat)) :
    upperSumK D xs = upperSum D xs := sumAuxK_eq D xs (0,1)

noncomputable def groupOKK (D Da g0 ga gb ma mb : Nat) (r s : ℚ)
    (xs : List (Nat × Nat)) : Bool :=
  xs.all (fun x => decide (0 < x.2)) &&
    let v := upperSumK D xs
    let lhs := Int.mul_k (Int.mul_k (Int.mul_k v.1 (Int.ofNat Da))
      (cube (Int.ofNat r.den))) (cube (Int.ofNat s.den))
    let rhs := Int.mul_k (Int.mul_k (inputNumK Da g0 ga gb ma mb r s)
      (Int.ofNat v.2)) (square (Int.ofNat D))
    intNonnegK (Int.sub_k rhs lhs)

theorem groupOKK_eq (D Da g0 ga gb ma mb : Nat) (r s : ℚ) (xs : List (Nat × Nat)) :
    groupOKK D Da g0 ga gb ma mb r s xs = groupOK D Da g0 ga gb ma mb r s xs := by
  simp only [groupOKK, groupOK, upperSumK_eq, inputNumK_eq, square_eq, cube_eq,
    Int.mul_k_eq, Int.sub_k_eq, Int.ofNat_eq_natCast, Int.mul_def, intNonnegK_eq, sub_nonneg]

end HlawkaSchatten.BelowExponent.FSlabNearKernel
