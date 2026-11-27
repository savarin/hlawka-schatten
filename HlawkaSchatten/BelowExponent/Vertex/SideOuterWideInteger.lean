/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.SideOuterWideData
public import HlawkaSchatten.BelowExponent.Vertex.CornerPowerData.Chord
public import HlawkaSchatten.BelowExponent.Vertex.OuterRowCheck
public import HlawkaSchatten.BelowExponent.Vertex.CornerPowerLookup

/-! The corner rectangle test in integer arithmetic. The grid nodes are n/256, so every endpoint,
the argument at two endpoints and the chord value have exact integer forms. Each integer function
is proved equal to the rational one it replaces, for all inputs. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

/-- The grid nodes as numerators over 256. -/
def outerNodeNum : Vector ℤ 35 := #v[-256, -224, -192, -160, -128, -96, -64, -56, -48, -40, -32,
  -24, -16, -8, -4, -2, -1, 0, 1, 2, 4, 8, 16, 24, 32, 40, 48, 56, 64, 96, 128, 160, 192, 224, 256]

theorem outerNodes_get_num : ∀ i : Fin 35, outerNodes.get i = (outerNodeNum.get i : ℚ) / 256 := by
  decide +kernel

/-- `DyadicBounds.point` of n/256 is exact: n * 2^88. -/
theorem outerPoint_div_256 (n : ℤ) :
    DyadicBounds.point ((n : ℚ) / 256) =
      ⟨n * 309485009821345068724781056, n * 309485009821345068724781056, true⟩ := by
  have h : (n : ℚ) / 256 * ((DyadicBounds.units : ℕ) : ℚ) =
      ((n * 309485009821345068724781056 : ℤ) : ℚ) := by
    simp only [DyadicBounds.units]; push_cast; ring
  simp only [DyadicBounds.point, DyadicBounds.ofRat, RatBounds.point, h, Int.floor_intCast,
    Int.ceil_intCast]

/-- `lowerOK 0` without the division by 2^96. -/
theorem outerLowerOK_zero (a : DyadicBounds) : a.lowerOK 0 = (a.ok && decide (0 ≤ a.lo)) := by
  simp only [DyadicBounds.lowerOK, DyadicBounds.lower, DyadicBounds.units]
  congr 1
  apply decide_eq_decide.mpr
  constructor
  · intro h
    have hpos : (0 : ℚ) < ((2 ^ 96 : ℕ) : ℚ) := by positivity
    have := (div_nonneg_iff.mp h)
    rcases this with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact_mod_cast h1
    · exact absurd h2 (not_le.mpr hpos)
  · intro h
    exact div_nonneg (by exact_mod_cast h) (by positivity)


/-- The argument at two nodes n/256 as one integer fraction. -/
def outerArgNum (A B C : ℚ) (nu nv : ℤ) : ℤ :=
  256 * A.num * B.den * C.den + B.num * nu * A.den * C.den + C.num * nv * A.den * B.den

def outerArgDen (A B C : ℚ) : ℕ := 256 * A.den * B.den * C.den

theorem outerArgDen_pos (A B C : ℚ) : 0 < outerArgDen A B C := by
  unfold outerArgDen; positivity

theorem outerArgument_eq_frac (A B C : ℚ) (nu nv : ℤ) :
    A + B * ((nu : ℚ) / 256) + C * ((nv : ℚ) / 256) =
      (outerArgNum A B C nu nv : ℚ) / (outerArgDen A B C : ℚ) := by
  have hA : (A.den : ℚ) ≠ 0 := by exact_mod_cast A.den_nz
  have hB : (B.den : ℚ) ≠ 0 := by exact_mod_cast B.den_nz
  have hC : (C.den : ℚ) ≠ 0 := by exact_mod_cast C.den_nz
  have eA : (A.num : ℚ) = A * A.den := (Rat.mul_den_eq_num A).symm
  have eB : (B.num : ℚ) = B * B.den := (Rat.mul_den_eq_num B).symm
  have eC : (C.num : ℚ) = C * C.den := (Rat.mul_den_eq_num C).symm
  unfold outerArgNum outerArgDen
  push_cast
  rw [eA, eB, eC]
  field_simp

theorem outerAbsFrac_le_four (N : ℤ) (D : ℕ) (hD : 0 < D) :
    decide (|(N : ℚ) / (D : ℚ)| ≤ 4) = decide (N.natAbs ≤ 4 * D) := by
  apply decide_eq_decide.mpr
  have hD' : (0 : ℚ) < D := by exact_mod_cast hD
  rw [abs_div, abs_of_pos hD', div_le_iff₀ hD', ← Int.cast_abs, Int.abs_eq_natAbs]
  constructor
  · intro h; exact_mod_cast h
  · intro h; exact_mod_cast h


/-- A table entry as the integer numerator over 2^64. -/
def outerTableEntry (values : Array (Array ℤ)) (k : Nat) : ℤ :=
  ((values[k / 64]?).getD #[])[k % 64]?.getD 0

theorem outerUpperEntry_eq (values : Array (Array ℤ)) (k : Nat) :
    outerUpperEntry values k = (outerTableEntry values k : ℚ) / 2^64 := rfl

/-- The chord at N/D as a fixed-point point, by natural and integer division only. -/
def outerChordPointInt (values : Array (Array ℤ)) (N : ℤ) (D : ℕ) : DyadicBounds :=
  let a := 256 * N.natAbs
  let j := a / D
  let r := a % D
  let W : ℤ := ((D - r : ℕ) : ℤ) * outerTableEntry values j +
    (r : ℤ) * outerTableEntry values (j + 1)
  ⟨W * 4294967296 / D, -((-(W * 4294967296)) / D), true⟩

theorem outerAbsFrac_mul_256 (N : ℤ) (D : ℕ) (hD : 0 < D) :
    256 * |(N : ℚ) / (D : ℚ)| = ((256 * N.natAbs : ℕ) : ℚ) / (D : ℚ) := by
  have hD' : (0 : ℚ) < D := by exact_mod_cast hD
  rw [abs_div, abs_of_pos hD', Nat.cast_mul, Nat.cast_natAbs]
  push_cast
  ring

theorem outerChordIndex_frac (N : ℤ) (D : ℕ) (hD : 0 < D) :
    outerChordIndex ((N : ℚ) / D) = 256 * N.natAbs / D := by
  unfold outerChordIndex
  rw [outerAbsFrac_mul_256 N D hD]
  have h := Rat.floor_intCast_div_natCast ((256 * N.natAbs : ℕ) : ℤ) D
  rw [Int.cast_natCast] at h
  rw [h, ← Int.natCast_div, Int.toNat_natCast]

theorem outerChordFraction_frac (N : ℤ) (D : ℕ) (hD : 0 < D) :
    outerChordFraction ((N : ℚ) / D) = ((256 * N.natAbs % D : ℕ) : ℚ) / D := by
  unfold outerChordFraction
  rw [outerChordIndex_frac N D hD, outerAbsFrac_mul_256 N D hD]
  have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have hM : ((256 * N.natAbs : ℕ) : ℚ) =
      (D : ℚ) * ((256 * N.natAbs / D : ℕ) : ℚ) + ((256 * N.natAbs % D : ℕ) : ℚ) := by
    exact_mod_cast (Nat.div_add_mod (256 * N.natAbs) D).symm
  rw [hM]
  field_simp
  ring


theorem outerChord_value_frac (values : Array (Array ℤ)) (N : ℤ) (D : ℕ) (hD : 0 < D) :
    outerRpowChord values ((N : ℚ) / D) =
      (((((D - 256 * N.natAbs % D : ℕ) : ℤ) * outerTableEntry values (256 * N.natAbs / D) +
        ((256 * N.natAbs % D : ℕ) : ℤ) *
          outerTableEntry values (256 * N.natAbs / D + 1) : ℤ) : ℚ)) /
        ((D : ℚ) * 2^64) := by
  have hr : 256 * N.natAbs % D ≤ D := (Nat.mod_lt _ hD).le
  have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  unfold outerRpowChord
  simp only [outerChordIndex_frac N D hD, outerChordFraction_frac N D hD, outerUpperEntry_eq]
  generalize 256 * N.natAbs / D = j
  generalize 256 * N.natAbs % D = r at hr ⊢
  rw [Int.cast_add, Int.cast_mul, Int.cast_mul, Int.cast_natCast, Int.cast_natCast, Nat.cast_sub hr]
  field_simp

theorem outerCeil_intCast_div_natCast (n : ℤ) (d : ℕ) :
    ⌈(n : ℚ) / (d : ℚ)⌉ = -((-n) / (d : ℤ)) := by
  rw [← Rat.floor_intCast_div_natCast, Int.cast_neg, neg_div, Int.floor_neg, neg_neg]

theorem outerChord_point_eq (values : Array (Array ℤ)) (N : ℤ) (D : ℕ) (hD : 0 < D) :
    DyadicBounds.point (outerRpowChord values ((N : ℚ) / D)) = outerChordPointInt values N D := by
  have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  rw [outerChord_value_frac values N D hD]
  simp only [outerChordPointInt]
  generalize ((((D - 256 * N.natAbs % D : ℕ) : ℤ) * outerTableEntry values (256 * N.natAbs / D) +
        ((256 * N.natAbs % D : ℕ) : ℤ) * outerTableEntry values (256 * N.natAbs / D + 1) : ℤ)) = W
  have hc : (W : ℚ) / ((D : ℚ) * 2^64) * ((DyadicBounds.units : ℕ) : ℚ) =
      ((W * 4294967296 : ℤ) : ℚ) / (D : ℚ) := by
    simp only [DyadicBounds.units]; push_cast; field_simp; ring
  simp only [DyadicBounds.point, DyadicBounds.ofRat, RatBounds.point, hc,
    Rat.floor_intCast_div_natCast,
    outerCeil_intCast_div_natCast]


def outerSpanIndex (S : SideOuterSpan) (x : Bool) : Fin 35 := if x then S.hi else S.lo

def outerNodePoint (i : Fin 35) : DyadicBounds :=
  ⟨outerNodeNum.get i * 309485009821345068724781056,
    outerNodeNum.get i * 309485009821345068724781056, true⟩

def OuterPointBounds.spanEndpointBoundInt (P : OuterPointBounds) (k m n : Fin 3)
    (U V : SideOuterSpan)
    (x y : Bool) (Au Av : Bool → OuterAxisBounds) : DyadicBounds :=
  let iu := outerSpanIndex U x
  let iv := outerSpanIndex V y
  let pu := outerNodePoint iu
  let pv := outerNodePoint iv
  let A := P.argument.get k
  let B := P.argument.get m
  let C := P.argument.get n
  let du := P.diagonal.get m
  let dv := P.diagonal.get n
  let cu := ((P.coupling.get k).get m).add (((P.coupling.get n).get m).mul pv)
  let cv := ((P.coupling.get k).get n).add (((P.coupling.get m).get n).mul pu)
  let first := (Au x).eval (decide (0 ≤ outerNodeNum.get U.lo)) du.lo
    (if 0 ≤ outerNodeNum.get U.lo then cu.lo else cu.hi)
  let second := (Av y).eval (decide (0 ≤ outerNodeNum.get V.lo)) dv.lo
    (if 0 ≤ outerNodeNum.get V.lo then cv.lo else cv.hi)
  let rem := ((P.diagonal.get k).add (((P.coupling.get m).get k).mul pu)).add
    (((P.coupling.get n).get k).mul pv)
  ((rem.sub (outerChordPointInt outerChordQTable
      (outerArgNum A B C (outerNodeNum.get iu) (outerNodeNum.get iv)) (outerArgDen A B C))).add
        first).add second

def OuterPointBounds.spanEndpointOKInt (P : OuterPointBounds) (k m n : Fin 3) (U V : SideOuterSpan)
    (x y : Bool) (Au Av : Bool → OuterAxisBounds) : Bool :=
  let iu := outerSpanIndex U x
  let iv := outerSpanIndex V y
  let A := P.argument.get k
  let B := P.argument.get m
  let C := P.argument.get n
  (P.diagonal.get m).ok && (P.diagonal.get n).ok &&
    (((P.coupling.get k).get m).add (((P.coupling.get n).get m).mul (outerNodePoint iv))).ok &&
    (((P.coupling.get k).get n).add (((P.coupling.get m).get n).mul (outerNodePoint iu))).ok &&
    decide ((outerArgNum A B C (outerNodeNum.get iu) (outerNodeNum.get iv)).natAbs ≤
      4 * outerArgDen A B C) &&
    (let b := P.spanEndpointBoundInt k m n U V x y Au Av; b.ok && decide (0 ≤ b.lo))

theorem outerEndpoint_spanBounds (S : SideOuterSpan) (x : Bool) :
    outerEndpoint S.bounds x = (outerNodeNum.get (outerSpanIndex S x) : ℚ) / 256 := by
  cases x <;> simp [outerEndpoint, SideOuterSpan.bounds, outerSpanIndex, outerNodes_get_num]

theorem outerSpanBounds_lo (S : SideOuterSpan) :
    S.bounds.lo = (outerNodeNum.get S.lo : ℚ) / 256 := by
  simp [SideOuterSpan.bounds, outerNodes_get_num]

theorem outerSpanBounds_hi (S : SideOuterSpan) :
    S.bounds.hi = (outerNodeNum.get S.hi : ℚ) / 256 := by
  simp [SideOuterSpan.bounds, outerNodes_get_num]

theorem outerDiv256_nonneg_iff (a : ℤ) : (0 : ℚ) ≤ (a : ℚ) / 256 ↔ 0 ≤ a := by
  constructor
  · intro h; have : (0 : ℚ) ≤ a := by linarith [h]
    exact_mod_cast this
  · intro h; have : (0 : ℚ) ≤ a := by exact_mod_cast h
    positivity

theorem outerDiv256_nonpos_iff (a : ℤ) : (a : ℚ) / 256 ≤ 0 ↔ a ≤ 0 := by
  constructor
  · intro h; have : (a : ℚ) ≤ 0 := by linarith [h]
    exact_mod_cast this
  · intro h; have : (a : ℚ) ≤ 0 := by exact_mod_cast h
    linarith

theorem outerDiv256_lt_iff (a b : ℤ) : (a : ℚ) / 256 < (b : ℚ) / 256 ↔ a < b := by
  constructor
  · intro h; have : (a : ℚ) < b := by linarith [h]
    exact_mod_cast this
  · intro h; have : (a : ℚ) < b := by exact_mod_cast h
    linarith


theorem outerSpanEndpointBound_int (P : OuterPointBounds) (k m n : Fin 3) (U V : SideOuterSpan)
    (x y : Bool)
    (Au Av : Bool → OuterAxisBounds) :
    P.spanEndpointBound k m n U.bounds V.bounds x y Au Av (outerRpowChord outerChordQTable) =
      P.spanEndpointBoundInt k m n U V x y Au Av := by
  simp only [OuterPointBounds.spanEndpointBound, OuterPointBounds.spanEndpointBoundInt,
    OuterPointBounds.argumentAt, OuterPointBounds.linearCoeff, OuterPointBounds.remainderLinear,
    outerSignedNumerator, outerEndpoint_spanBounds, outerSpanBounds_lo, outerPoint_div_256,
    outerArgument_eq_frac,
    outerChord_point_eq _ _ _ (outerArgDen_pos _ _ _), outerDiv256_nonneg_iff, outerNodePoint]


theorem outerSpanEndpointOK_int (P : OuterPointBounds) (k m n : Fin 3) (U V : SideOuterSpan)
    (x y : Bool)
    (Au Av : Bool → OuterAxisBounds) :
    P.spanEndpointOK k m n U.bounds V.bounds x y Au Av (outerRpowChord outerChordQTable) =
      P.spanEndpointOKInt k m n U V x y Au Av := by
  simp only [OuterPointBounds.spanEndpointOK, OuterPointBounds.spanEndpointOKInt,
    outerSpanEndpointBound_int, outerLowerOK_zero, OuterPointBounds.argumentAt,
    OuterPointBounds.linearCoeff,
    outerEndpoint_spanBounds, outerPoint_div_256, outerArgument_eq_frac, outerNodePoint,
    outerAbsFrac_le_four _ _ (outerArgDen_pos _ _ _)]

end HlawkaSchatten.BelowExponent.Vertex
