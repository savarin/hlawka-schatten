/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.SideOuterWideInteger

/-! The corner rectangle test in the form the kernel evaluates fastest: lookups by direct list
walks with `Nat.beq` and `Nat.sub`, and interval arithmetic on the kernel integer operations
`Int.*_k` of `Init.Data.Int.Kernel`. Each definition is proved equal to the one it replaces, for
all inputs; the axis-bank lookup and the rectangle test itself follow in `SideOuterWideCheck`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

/-- `l.getD k d` by a direct walk with `Nat.beq` and `Nat.sub`, without `Array` or `match`. -/
def outerListGetK {α : Type} (d : α) (l : List α) (k : ℕ) : α :=
  List.rec (motive := fun _ => ℕ → α) (fun _ => d)
    (fun a _ ih k => Bool.rec (ih (Nat.sub k 1)) a (Nat.beq k 0)) l k

theorem outerListGetK_eq {α : Type} (d : α) (l : List α) (k : ℕ) :
    outerListGetK d l k = l.getD k d := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih =>
    cases k with
    | zero => rfl
    | succ k => exact ih k

theorem outerListGetK_vector {α : Type} {n : ℕ} (d : α) (v : Vector α n) (i : Fin n) :
    outerListGetK d v.toList i.val = v.get i := by
  rw [outerListGetK_eq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp)]
  simp [Vector.get]

/-- `min` and `max` by the sign of `b - a`, on the kernel integer operations. -/
noncomputable def outerMinK (a b : ℤ) : ℤ :=
  Int.rec (motive := fun _ => ℤ) (fun _ => a) (fun _ => b) (Int.sub_k b a)

noncomputable def outerMaxK (a b : ℤ) : ℤ :=
  Int.rec (motive := fun _ => ℤ) (fun _ => b) (fun _ => a) (Int.sub_k b a)

theorem outerMinK_eq (a b : ℤ) : outerMinK a b = min a b := by
  unfold outerMinK
  rw [Int.sub_k_eq]
  rcases h : b - a with n | n
  · show a = min a b
    have : 0 ≤ b - a := by rw [h]; exact Int.natCast_nonneg n
    exact (min_eq_left (by omega)).symm
  · show b = min a b
    have : b - a < 0 := by rw [h]; exact Int.negSucc_lt_zero n
    exact (min_eq_right (by omega)).symm

theorem outerMaxK_eq (a b : ℤ) : outerMaxK a b = max a b := by
  unfold outerMaxK
  rw [Int.sub_k_eq]
  rcases h : b - a with n | n
  · show b = max a b
    have : 0 ≤ b - a := by rw [h]; exact Int.natCast_nonneg n
    exact (max_eq_right (by omega)).symm
  · show a = max a b
    have : b - a < 0 := by rw [h]; exact Int.negSucc_lt_zero n
    exact (max_eq_left (by omega)).symm

/-- `DyadicBounds.mul` on kernel integer operations. -/
noncomputable def outerMulK (a b : DyadicBounds) : DyadicBounds :=
  let p1 := Int.mul_k a.lo b.lo
  let p2 := Int.mul_k a.lo b.hi
  let p3 := Int.mul_k a.hi b.lo
  let p4 := Int.mul_k a.hi b.hi
  ⟨Int.ediv_k (outerMinK (outerMinK p1 p2) (outerMinK p3 p4))
      (Int.ofNat 79228162514264337593543950336),
    Int.neg_k (Int.ediv_k (Int.neg_k (outerMaxK (outerMaxK p1 p2) (outerMaxK p3 p4)))
      (Int.ofNat 79228162514264337593543950336)), a.ok && b.ok⟩

theorem outerMulK_eq (a b : DyadicBounds) : outerMulK a b = a.mul b := by
  have hu : ((DyadicBounds.units : ℕ) : ℤ) = Int.ofNat 79228162514264337593543950336 := by
    simp only [DyadicBounds.units, Int.ofNat_eq_natCast]; norm_num
  simp only [outerMulK, DyadicBounds.mul_def, DyadicBounds.productLo, DyadicBounds.productHi,
    DyadicBounds.ceilDiv, outerMinK_eq, outerMaxK_eq, Int.mul_k_eq, Int.ediv_k_eq, Int.neg_k_eq, hu]
  rfl

/-- `DyadicBounds.add` and `DyadicBounds.sub` on kernel integer operations. -/
noncomputable def outerAddK (a b : DyadicBounds) : DyadicBounds :=
  ⟨Int.add_k a.lo b.lo, Int.add_k a.hi b.hi, a.ok && b.ok⟩

noncomputable def outerSubK (a b : DyadicBounds) : DyadicBounds :=
  ⟨Int.sub_k a.lo b.hi, Int.sub_k a.hi b.lo, a.ok && b.ok⟩

theorem outerAddK_eq (a b : DyadicBounds) : outerAddK a b = a.add b := by
  simp only [outerAddK, DyadicBounds.add_def, Int.add_k_eq]; rfl

theorem outerSubK_eq (a b : DyadicBounds) : outerSubK a b = a.sub b := by
  simp only [outerSubK, DyadicBounds.sub_def, Int.sub_k_eq]

/-- `Int.rec` on the sign of `x`, as an `if`. -/
theorem outerIntRec_eq_ite {α : Sort u} (x : ℤ) (p q : α) :
    Int.rec (motive := fun _ => α) (fun _ => p) (fun _ => q) x = if 0 ≤ x then p else q := by
  cases x with
  | ofNat n => simp
  | negSucc n => simp

theorem outerIntRec_eq_ite_neg {α : Sort u} (x : ℤ) (p q : α) :
    Int.rec (motive := fun _ => α) (fun _ => p) (fun _ => q) x = if x < 0 then q else p := by
  rw [outerIntRec_eq_ite]; by_cases h : x < 0 <;> simp [h, not_lt.mp]

/-- `decide (0 ≤ x)` by the constructor of `x`. -/
noncomputable def outerNonnegK (x : ℤ) : Bool :=
  Int.rec (motive := fun _ => Bool) (fun _ => true) (fun _ => false) x

theorem outerNonnegK_eq (x : ℤ) : outerNonnegK x = decide (0 ≤ x) := by
  unfold outerNonnegK; rw [outerIntRec_eq_ite]; by_cases h : 0 ≤ x <;> simp [h]

theorem outerNatBle_eq (a b : ℕ) : Nat.ble a b = decide (a ≤ b) := by
  rw [Bool.eq_iff_iff]; simp [Nat.ble_eq]

theorem outerNatBlt_eq (a b : ℕ) : Nat.blt a b = decide (a < b) := by
  rw [Bool.eq_iff_iff]; simp [Nat.blt_eq]

/-- `outerTableEntry` by direct walks: row `k / 64`, then entry `k % 64`. -/
def outerTableEntryK (values : Array (Array ℤ)) (k : ℕ) : ℤ :=
  outerListGetK 0 (outerListGetK #[] values.toList (Nat.div k 64)).toList (Nat.mod k 64)

theorem outerTableEntryK_eq (values : Array (Array ℤ)) (k : ℕ) :
    outerTableEntryK values k = outerTableEntry values k := by
  simp only [outerTableEntryK, outerTableEntry, outerListGetK_eq, List.getD_eq_getElem?_getD,
    Array.getElem?_toList]
  rfl

/-- `outerChordPointInt` on `Nat` primitives and kernel integer operations. -/
noncomputable def outerChordPointK (values : Array (Array ℤ)) (N : ℤ) (D : ℕ) : DyadicBounds :=
  let a := Nat.mul 256 (Int.natAbs_k N)
  let j := Nat.div a D
  let r := Nat.mod a D
  let W := Int.mul_k (Int.add_k (Int.mul_k (Int.ofNat (Nat.sub D r)) (outerTableEntryK values j))
    (Int.mul_k (Int.ofNat r) (outerTableEntryK values (Nat.add j 1)))) (Int.ofNat 4294967296)
  ⟨Int.ediv_k W (Int.ofNat D), Int.neg_k (Int.ediv_k (Int.neg_k W) (Int.ofNat D)), true⟩

theorem outerChordPointK_eq (values : Array (Array ℤ)) (N : ℤ) (D : ℕ) :
    outerChordPointK values N D = outerChordPointInt values N D := by
  simp only [outerChordPointK, outerChordPointInt, Int.natAbs_k_eq, outerTableEntryK_eq,
    Int.add_k_eq, Int.mul_k_eq, Int.ediv_k_eq, Int.neg_k_eq, Int.ofNat_eq_natCast]
  rfl

/-- `outerArgNum` and `outerArgDen` on kernel integer and `Nat` operations. -/
noncomputable def outerArgNumK (A B C : ℚ) (nu nv : ℤ) : ℤ :=
  Int.add_k (Int.add_k (Int.mul_k (Int.mul_k (Int.mul_k (Int.ofNat 256) A.num) (Int.ofNat B.den))
      (Int.ofNat C.den))
    (Int.mul_k (Int.mul_k (Int.mul_k B.num nu) (Int.ofNat A.den)) (Int.ofNat C.den)))
    (Int.mul_k (Int.mul_k (Int.mul_k C.num nv) (Int.ofNat A.den)) (Int.ofNat B.den))

def outerArgDenK (A B C : ℚ) : ℕ := Nat.mul (Nat.mul (Nat.mul 256 A.den) B.den) C.den

theorem outerArgNumK_eq (A B C : ℚ) (nu nv : ℤ) :
    outerArgNumK A B C nu nv = outerArgNum A B C nu nv := by
  simp only [outerArgNumK, outerArgNum, Int.add_k_eq, Int.mul_k_eq, Int.ofNat_eq_natCast]; rfl

theorem outerArgDenK_eq (A B C : ℚ) : outerArgDenK A B C = outerArgDen A B C := rfl

/-- The grid numerators and fixed-point grid points by a direct walk. -/
def outerNodeNumK (i : Fin 35) : ℤ := outerListGetK 0 outerNodeNum.toList i.val

theorem outerNodeNumK_eq (i : Fin 35) : outerNodeNumK i = outerNodeNum.get i :=
  outerListGetK_vector 0 _ i

noncomputable def outerNodePointK (i : Fin 35) : DyadicBounds :=
  ⟨Int.mul_k (outerNodeNumK i) (Int.ofNat 309485009821345068724781056),
    Int.mul_k (outerNodeNumK i) (Int.ofNat 309485009821345068724781056), true⟩

theorem outerNodePointK_eq (i : Fin 35) : outerNodePointK i = outerNodePoint i := by
  simp only [outerNodePointK, outerNodePoint, outerNodeNumK_eq, Int.mul_k_eq]; rfl

/-- The sign tests and the order of the grid nodes, from their indices (node 17 is 0). -/
theorem outerNode_nonneg_iff :
    ∀ i : Fin 35, decide (0 ≤ outerNodeNum.get i) = Nat.ble 17 i.val := by
  decide +kernel

theorem outerNode_nonpos_iff :
    ∀ i : Fin 35, decide (outerNodeNum.get i ≤ 0) = Nat.ble i.val 17 := by
  decide +kernel

theorem outerNode_lt_iff : ∀ i j : Fin 35,
    decide (outerNodeNum.get i < outerNodeNum.get j) = Nat.blt i.val j.val := by
  decide +kernel

/-- `OuterAxisBounds.eval` with its sign tests by `Int.rec` and kernel interval arithmetic. -/
noncomputable def OuterAxisBounds.evalK (A : OuterAxisBounds) (positive : Bool) (d c : ℤ) :
    DyadicBounds :=
  let unsigned :=
    Int.rec (motive := fun _ => DyadicBounds) (fun _ => A.absTangent) (fun _ => A.absChord) d
  let signed :=
    Int.rec (motive := fun _ => DyadicBounds) (fun _ => A.signedChord) (fun _ => A.signedTangent)
      (Bool.rec (Int.neg_k c) c positive)
  outerAddK (outerMulK (DyadicBounds.ofNumerator d) unsigned)
    (outerMulK (DyadicBounds.ofNumerator c) signed)

theorem OuterAxisBounds.evalK_eq (A : OuterAxisBounds) (positive : Bool) (d c : ℤ) :
    A.evalK positive d c = A.eval positive d c := by
  have hs : (Bool.rec (Int.neg_k c) c positive : ℤ) = if positive then c else -c := by
    cases positive
    · exact Int.neg_k_eq c
    · rfl
  have hu : Int.rec (motive := fun _ => DyadicBounds) (fun _ => A.absTangent)
      (fun _ => A.absChord) d = if 0 ≤ d then A.absTangent else A.absChord :=
    outerIntRec_eq_ite d _ _
  have hg : Int.rec (motive := fun _ => DyadicBounds) (fun _ => A.signedChord)
      (fun _ => A.signedTangent) (Bool.rec (Int.neg_k c) c positive) =
      if (if positive then c else -c) < 0 then A.signedTangent else A.signedChord := by
    rw [hs]; exact outerIntRec_eq_ite_neg _ _ _
  simp only [OuterAxisBounds.evalK, OuterAxisBounds.eval, hu, hg, outerAddK_eq, outerMulK_eq]


/-! The endpoint and rectangle checks in kernel form. -/

/-- `spanEndpointBoundInt` and `spanEndpointOKInt` in kernel form. -/
noncomputable def OuterPointBounds.spanEndpointBoundK (P : OuterPointBounds) (k m n : Fin 3)
    (U V : SideOuterSpan) (x y : Bool) (Au Av : Bool → OuterAxisBounds) : DyadicBounds :=
  let iu := outerSpanIndex U x
  let iv := outerSpanIndex V y
  let pu := outerNodePointK iu
  let pv := outerNodePointK iv
  let A := P.argument.get k
  let B := P.argument.get m
  let C := P.argument.get n
  let du := P.diagonal.get m
  let dv := P.diagonal.get n
  let cu := outerAddK ((P.coupling.get k).get m) (outerMulK ((P.coupling.get n).get m) pv)
  let cv := outerAddK ((P.coupling.get k).get n) (outerMulK ((P.coupling.get m).get n) pu)
  let su := Nat.ble 17 U.lo.val
  let sv := Nat.ble 17 V.lo.val
  let first := (Au x).evalK su du.lo (Bool.rec cu.hi cu.lo su)
  let second := (Av y).evalK sv dv.lo (Bool.rec cv.hi cv.lo sv)
  let rem := outerAddK (outerAddK (P.diagonal.get k) (outerMulK ((P.coupling.get m).get k) pu))
    (outerMulK ((P.coupling.get n).get k) pv)
  outerAddK (outerAddK (outerSubK rem (outerChordPointK outerChordQTable
      (outerArgNumK A B C (outerNodeNumK iu) (outerNodeNumK iv)) (outerArgDenK A B C))) first)
    second

noncomputable def OuterPointBounds.spanEndpointOKK (P : OuterPointBounds) (k m n : Fin 3)
    (U V : SideOuterSpan) (x y : Bool) (Au Av : Bool → OuterAxisBounds) : Bool :=
  let iu := outerSpanIndex U x
  let iv := outerSpanIndex V y
  let A := P.argument.get k
  let B := P.argument.get m
  let C := P.argument.get n
  (P.diagonal.get m).ok && (P.diagonal.get n).ok &&
    (outerAddK ((P.coupling.get k).get m)
      (outerMulK ((P.coupling.get n).get m) (outerNodePointK iv))).ok &&
    (outerAddK ((P.coupling.get k).get n)
      (outerMulK ((P.coupling.get m).get n) (outerNodePointK iu))).ok &&
    Nat.ble (Int.natAbs_k (outerArgNumK A B C (outerNodeNumK iu) (outerNodeNumK iv)))
      (Nat.mul 4 (outerArgDenK A B C)) &&
    (let b := P.spanEndpointBoundK k m n U V x y Au Av; b.ok && outerNonnegK b.lo)

theorem outerBoolRec_decide {α : Sort u} (p : Prop) [Decidable p] (a b : α) :
    (Bool.rec b a (decide p) : α) = if p then a else b := by
  by_cases h : p <;> simp [h]

theorem outerSpanEndpointBoundK_eq (P : OuterPointBounds) (k m n : Fin 3) (U V : SideOuterSpan)
    (x y : Bool) (Au Av : Bool → OuterAxisBounds) :
    P.spanEndpointBoundK k m n U V x y Au Av = P.spanEndpointBoundInt k m n U V x y Au Av := by
  simp only [OuterPointBounds.spanEndpointBoundK, OuterPointBounds.spanEndpointBoundInt,
    ← outerNode_nonneg_iff, outerBoolRec_decide, OuterAxisBounds.evalK_eq, outerAddK_eq,
    outerMulK_eq, outerSubK_eq, outerNodePointK_eq, outerNodeNumK_eq, outerChordPointK_eq,
    outerArgNumK_eq,
    outerArgDenK_eq]

theorem outerSpanEndpointOKK_eq (P : OuterPointBounds) (k m n : Fin 3) (U V : SideOuterSpan)
    (x y : Bool) (Au Av : Bool → OuterAxisBounds) :
    P.spanEndpointOKK k m n U V x y Au Av = P.spanEndpointOKInt k m n U V x y Au Av := by
  simp only [OuterPointBounds.spanEndpointOKK, OuterPointBounds.spanEndpointOKInt,
    outerSpanEndpointBoundK_eq, outerNonnegK_eq, outerNatBle_eq, Int.natAbs_k_eq, outerAddK_eq,
    outerMulK_eq, outerNodePointK_eq, outerNodeNumK_eq, outerArgNumK_eq, outerArgDenK_eq]
  rfl

end HlawkaSchatten.BelowExponent.Vertex
