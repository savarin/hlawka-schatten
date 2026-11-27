/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.SideConeFastRows
public import HlawkaSchatten.BelowExponent.Vertex.SideConeParameterKernel
public import HlawkaSchatten.BelowExponent.Vertex.DyadicKernel

/-! The side-cone leaf test in kernel form. Its determinant test runs on the integer numerators
of the fixed-point lower coefficients, which avoids forming rationals; each step is proved equal to
the test it replaces, for all inputs. `SideFastParameter.leafCheck` itself stays computable for the
compiled preparation. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

/-- The numerators, over `2 ^ 96`, of the lower coefficients `(A.toRat).lower s t`. -/
structure SideLowerNumerators where
  value : ℤ
  first : ℤ
  second : ℤ
  diagonalFirst : ℤ
  mixed : ℤ
  diagonalSecond : ℤ

def SideDyadicCoefficients.lowerNum (A : SideDyadicCoefficients) (s t : Bool) :
    SideLowerNumerators :=
  ⟨A.value.lo, if s then A.first.lo else A.first.hi, if t then A.second.lo else A.second.hi,
    A.diagonalFirst.lo, if (s == t) then A.mixed.lo else A.mixed.hi, A.diagonalSecond.lo⟩

/-- `SideLowerCoefficients.detOK` on the numerators, with the rational cap cleared. -/
def SideLowerNumerators.detOKInt (N : SideLowerNumerators) (cap : ℚ) : Bool :=
  let A := N.diagonalFirst
  let C := N.diagonalSecond
  let D := A * C - N.mixed ^ 2
  let X := C * N.first ^ 2 - 2 * N.mixed * N.first * N.second + A * N.second ^ 2
  decide (0 < A ∧ 0 < D ∧ cap.num * X ≤ 4 * (cap.den : ℤ) * D * N.value)

theorem SideDyadicCoefficients.lower_eq_num (A : SideDyadicCoefficients) (s t : Bool) :
    A.toRat.lower s t =
      let N := A.lowerNum s t
      let U : ℚ := ((DyadicBounds.units : ℕ) : ℚ)
      (⟨N.value / U, N.first / U, N.second / U, N.diagonalFirst / U, N.mixed / U,
        N.diagonalSecond / U⟩ : SideLowerCoefficients) := by
  cases s <;> cases t <;>
    simp [SideDyadicCoefficients.toRat, SideCoefficientIntervals.lower, signEndpoint,
      SideDyadicCoefficients.lowerNum, DyadicBounds.toSideRat, DyadicBounds.lower,
      DyadicBounds.upper]

theorem SideLowerNumerators.detOKInt_eq (N : SideLowerNumerators) (cap : ℚ) {U : ℚ} (hU : 0 < U) :
    N.detOKInt cap =
      (⟨N.value / U, N.first / U, N.second / U, N.diagonalFirst / U, N.mixed / U,
        N.diagonalSecond / U⟩ : SideLowerCoefficients).detOK cap := by
  unfold SideLowerNumerators.detOKInt SideLowerCoefficients.detOK
  apply decide_eq_decide.mpr
  have hU2 : 0 < U ^ 2 := by positivity
  have hU3 : 0 < U ^ 3 := by positivity
  have hd : (0 : ℚ) < cap.den := by exact_mod_cast cap.den_pos
  set A := N.diagonalFirst
  set C := N.diagonalSecond
  have hD : (A / U) * (C / U) - (N.mixed / U) ^ 2 = ((A * C - N.mixed ^ 2 : ℤ) : ℚ) / U ^ 2 := by
    push_cast; field_simp
  have hX : (C / U) * (N.first / U) ^ 2 - 2 * (N.mixed / U) * (N.first / U) * (N.second / U) +
      (A / U) * (N.second / U) ^ 2 =
      ((C * N.first ^ 2 - 2 * N.mixed * N.first * N.second + A * N.second ^ 2 : ℤ) : ℚ) /
        U ^ 3 := by
    push_cast; field_simp
  rw [hD, hX]
  set D := A * C - N.mixed ^ 2
  set X := C * N.first ^ 2 - 2 * N.mixed * N.first * N.second + A * N.second ^ 2
  have h1 : (0 < A) ↔ (0 : ℚ) < (A : ℚ) / U := by
    rw [div_pos_iff_of_pos_right hU]; exact_mod_cast Iff.rfl
  have h2 : (0 < D) ↔ (0 : ℚ) < (D : ℚ) / U ^ 2 := by
    rw [div_pos_iff_of_pos_right hU2]; exact_mod_cast Iff.rfl
  have h3 : cap.num * X ≤ 4 * (cap.den : ℤ) * D * N.value ↔
      cap * ((X : ℚ) / U ^ 3) ≤ 4 * ((D : ℚ) / U ^ 2) * ((N.value : ℚ) / U) := by
    have e : 4 * ((D : ℚ) / U ^ 2) * ((N.value : ℚ) / U) = (4 * D * N.value : ℚ) / U ^ 3 := by
      field_simp
    rw [e, mul_div_assoc', div_le_div_iff_of_pos_right hU3]
    conv_rhs => rw [← Rat.num_div_den cap]
    rw [div_mul_eq_mul_div, div_le_iff₀ hd]
    constructor
    · intro h
      have h' : ((cap.num * X : ℤ) : ℚ) ≤ ((4 * (cap.den : ℤ) * D * N.value : ℤ) : ℚ) := by
        exact_mod_cast h
      push_cast at h'; linarith
    · intro h
      have h' : ((cap.num * X : ℤ) : ℚ) ≤ ((4 * (cap.den : ℤ) * D * N.value : ℤ) : ℚ) := by
        push_cast; linarith
      exact_mod_cast h'
  rw [h1, h2, h3]

theorem SideDyadicCoefficients.detOK_eq_num (A : SideDyadicCoefficients) (s t : Bool) (cap : ℚ) :
    (A.toRat.lower s t).detOK cap = (A.lowerNum s t).detOKInt cap := by
  have hU : (0 : ℚ) < ((DyadicBounds.units : ℕ) : ℚ) := by
    simp only [DyadicBounds.units]; positivity
  rw [A.lower_eq_num s t, (A.lowerNum s t).detOKInt_eq cap hU]

/-- `SideLowerNumerators.detOKInt` on kernel integer operations. -/
noncomputable def SideLowerNumerators.detOKK (N : SideLowerNumerators) (cap : ℚ) : Bool :=
  let A := N.diagonalFirst
  let C := N.diagonalSecond
  let M := N.mixed
  let D := Int.sub_k (Int.mul_k A C) (Int.mul_k M M)
  let X := Int.add_k (Int.sub_k (Int.mul_k C (Int.mul_k N.first N.first))
      (Int.mul_k (Int.mul_k (Int.mul_k (Int.ofNat 2) M) N.first) N.second))
    (Int.mul_k A (Int.mul_k N.second N.second))
  intPosK A && intPosK D && intNonnegK (Int.sub_k
    (Int.mul_k (Int.mul_k (Int.mul_k (Int.ofNat 4) (Int.ofNat cap.den)) D) N.value)
    (Int.mul_k cap.num X))

theorem SideLowerNumerators.detOKK_eq (N : SideLowerNumerators) (cap : ℚ) :
    N.detOKK cap = N.detOKInt cap := by
  simp only [SideLowerNumerators.detOKK, SideLowerNumerators.detOKInt, Int.mul_k_eq, Int.sub_k_eq,
    Int.add_k_eq, intPosK_eq, intNonnegK_eq, Int.ofNat_eq_natCast, Nat.cast_ofNat, Int.mul_def,
    Int.add_def]
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  have hD : N.diagonalFirst * N.diagonalSecond - N.mixed * N.mixed =
      N.diagonalFirst * N.diagonalSecond - N.mixed ^ 2 := by ring
  have hX : 4 * (cap.den : ℤ) * (N.diagonalFirst * N.diagonalSecond - N.mixed * N.mixed) * N.value -
      cap.num * (N.diagonalSecond * (N.first * N.first) - 2 * N.mixed * N.first * N.second +
        N.diagonalFirst * (N.second * N.second)) =
      4 * (cap.den : ℤ) * (N.diagonalFirst * N.diagonalSecond - N.mixed ^ 2) * N.value -
      cap.num * (N.diagonalSecond * N.first ^ 2 - 2 * N.mixed * N.first * N.second +
        N.diagonalFirst * N.second ^ 2) := by ring
  rw [hX, hD, sub_nonneg, and_assoc]

/-- `SideFastDiagonalTerms.evaluate` on kernel integer operations. -/
noncomputable def SideFastDiagonalTerms.evaluateK (T : SideFastDiagonalTerms)
    (R : SideFastAxisIntervals) (F : DyadicBounds) : DyadicBounds :=
  let one := DyadicBounds.oneK
  let slope := T.slope.mulK R.slope
  let direct := (((T.d.mulK R.second).addK (T.first.mulK R.first)).addK slope).subK
    (T.baseSquared.mulK F)
  let centered := (((T.center.addK (T.d.mulK (R.second.subK one))).addK
    (T.first.mulK (R.first.subK one))).addK slope).subK (T.baseSquared.mulK (F.subK one))
  direct.intersectK centered

theorem SideFastDiagonalTerms.evaluateK_eq (T : SideFastDiagonalTerms) (R : SideFastAxisIntervals)
    (F : DyadicBounds) : T.evaluateK R F = T.evaluate R F := by
  simp only [SideFastDiagonalTerms.evaluateK, SideFastDiagonalTerms.evaluate, DyadicBounds.mulK_eq,
    DyadicBounds.addK_eq, DyadicBounds.subK_eq, DyadicBounds.intersectK_eq, DyadicBounds.oneK_eq]

/-- `SideFastParameterTerms.evaluate` on kernel integer operations. -/
noncomputable def SideFastParameterTerms.evaluateK (P : SideFastParameterTerms)
    (U V : SideFastAxisIntervals) (F : DyadicBounds) : SideDyadicCoefficients :=
  ⟨P.value, P.first, P.second, P.scale.mulK (P.diagU.evaluateK U F),
    P.scale.mulK (((P.mixedV.mulK V.first).addK (P.mixedU.mulK U.first)).subK
      (P.mixedBase.mulK F)),
    P.scale.mulK (P.diagV.evaluateK V F)⟩

theorem SideFastParameterTerms.evaluateK_eq (P : SideFastParameterTerms)
    (U V : SideFastAxisIntervals) (F : DyadicBounds) : P.evaluateK U V F = P.evaluate U V F := by
  simp only [SideFastParameterTerms.evaluateK, SideFastParameterTerms.evaluate,
    SideFastDiagonalTerms.evaluateK_eq, DyadicBounds.mulK_eq, DyadicBounds.addK_eq,
    DyadicBounds.subK_eq]

/-! ### The rational part of the leaf in exact kernel fractions -/

theorem SideFastParameter.box_u (P : SideFastParameter) (U V : RatBounds) : (P.box U V).u = U := rfl
theorem SideFastParameter.box_v (P : SideFastParameter) (U V : RatBounds) : (P.box U V).v = V := rfl
theorem SideFastParameter.box_cell (P : SideFastParameter) (U V : RatBounds) :
    (P.box U V).cell = P.cell := rfl
theorem SideFastParameter.box_exponent (P : SideFastParameter) (U V : RatBounds) :
    (P.box U V).exponent = sideNearExponent := rfl

theorem sideBaseK_val (P : SideFastParameter) (U V : RatBounds) :
    (sideBaseK P.cell).val = (P.box U V).base := by
  simp only [sideBaseK, SideNearBox.base, SideNearBox.baseShift, SideFastParameter.box_cell,
    RatBoundsK.val_add, RatBoundsK.val_mul, RatBoundsK.val_point, RatBoundsK.val_ofRat,
    RatK.val_one, RatK.val_four]

theorem sideShiftK_val (P : SideFastParameter) (U V : RatBounds) :
    (sideShiftK P.cell U V).val = (P.box U V).shift := by
  simp only [sideShiftK, SideNearBox.shift, SideFastParameter.box_cell, SideFastParameter.box_u,
    SideFastParameter.box_v, RatBoundsK.val_add, RatBoundsK.val_mul, RatBoundsK.val_sub,
    RatBoundsK.val_point, RatBoundsK.val_ofRat, RatK.val_one, RatK.val_two]

/-- `P.mixedInterval U V mixed`, from the cell base and the argument interval. -/
noncomputable def sideMixedK (base X : RatBoundsK) (mixed : FactorSamples) : DyadicBounds :=
  ((⟨base.hi.inv, RatK.one⟩ : RatBoundsK).mul
    (sideSecondFactorRangeK sideNearExponent X mixed)).toDyadic

theorem sideMixedK_eq (P : SideFastParameter) (U V : RatBounds) (mixed : FactorSamples) :
    sideMixedK (sideBaseK P.cell) ((sideShiftK P.cell U V).divPositive (sideBaseK P.cell)) mixed =
      P.mixedInterval U V mixed := by
  have hb := congrArg RatBounds.hi (sideBaseK_val P U V)
  simp only [RatBoundsK.val] at hb
  rw [sideMixedK, RatBoundsK.toDyadic_eq, RatBoundsK.val_mul, sideSecondFactorRangeK_val,
    RatBoundsK.val_divPositive, sideShiftK_val P U V, sideBaseK_val P U V]
  simp only [SideFastParameter.mixedInterval, SideNearBox.scaledBase, SideNearBox.argument,
    SideFastParameter.box_exponent, RatBoundsK.val, RatK.val_inv, RatK.val_one, hb, one_div]

/-- `sideAxisSignOK` and `sideAxisSign` by the sign of a numerator. -/
noncomputable def sideSignOKK (I : RatBounds) : Bool :=
  intNonnegK I.lo.num || intNonnegK (Int.neg_k I.hi.num)

theorem sideSignOKK_eq (I : RatBounds) : sideSignOKK I = sideAxisSignOK I := by
  simp only [sideSignOKK, sideAxisSignOK, intNonnegK_eq, Int.neg_k_eq, Bool.decide_or]
  congr 1
  · exact decide_eq_decide.mpr Rat.num_nonneg
  · apply decide_eq_decide.mpr
    show (0 : ℤ) ≤ -I.hi.num ↔ I.hi ≤ 0
    rw [Int.neg_nonneg, Rat.num_nonpos]

theorem sideAxisSignK_eq (I : RatBounds) : intNonnegK I.lo.num = sideAxisSign I := by
  rw [intNonnegK_eq, sideAxisSign]; exact decide_eq_decide.mpr Rat.num_nonneg

/-! ### The rectangle fallback in exact kernel fractions -/

/-- `sidePoly` on exact fractions. -/
noncomputable def sidePolyK (A G V x : RatK) : RatK := ((A.mul (x.mul x)).add (G.mul x)).add V

theorem sidePolyK_val (A G V x : RatK) :
    (sidePolyK A G V x).val = sidePoly A.val G.val V.val x.val := by
  simp only [sidePolyK, sidePoly, RatK.val_add, RatK.val_mul, sq]

/-- `sideIntervalOK` on exact fractions. -/
noncomputable def sideIntervalOKK (A G V : RatK) (I : RatBoundsK) : Bool :=
  let z := (RatK.zero.sub G).mul (RatK.two.mul A).inv
  !(I.lo.le I.hi) ||
    (RatK.zero.le (sidePolyK A G V I.lo) && RatK.zero.le (sidePolyK A G V I.hi) &&
      (!(RatK.zero.lt A) || !(I.lo.le z) || !(z.le I.hi) || RatK.zero.le (sidePolyK A G V z)))

theorem sideIntervalOKK_eq (A G V : RatK) (I : RatBoundsK) :
    sideIntervalOKK A G V I = sideIntervalOK A.val G.val V.val I.val := by
  have hlo : I.val.lo = I.lo.val := rfl
  have hhi : I.val.hi = I.hi.val := rfl
  have hz : -G.val / (2 * A.val) = ((RatK.zero.sub G).mul (RatK.two.mul A).inv).val := by
    simp only [RatK.val_mul, RatK.val_sub, RatK.val_inv, RatK.val_zero, RatK.val_two, zero_sub,
      div_eq_mul_inv]
  unfold sideIntervalOKK sideIntervalOK
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    RatK.le_eq, RatK.lt_eq, decide_eq_false_iff_not]
  simp only [hlo, hhi, ← hz, sidePolyK_val, RatK.val_zero]
  tauto

/-- `sideAffinePreimage` on exact fractions. -/
noncomputable def sideAffinePreimageK (s t : RatK) (U V : RatBoundsK) : RatBoundsK :=
  Bool.rec
    (let l := (U.lo.sub t).mul s.inv
     let r := (U.hi.sub t).mul s.inv
     ⟨V.lo.maxK (l.minK r), V.hi.minK (l.maxK r)⟩)
    (Bool.rec ⟨RatK.one, RatK.zero⟩ V (U.lo.le t && t.le U.hi))
    s.isZero

theorem sideAffinePreimageK_val (s t : RatK) (U V : RatBoundsK) :
    (sideAffinePreimageK s t U V).val = sideAffinePreimage s.val t.val U.val V.val := by
  unfold sideAffinePreimageK sideAffinePreimage
  rw [RatK.isZero_eq]
  by_cases h : s.val = 0
  · simp only [h, decide_true, ite_true, RatK.le_eq]
    by_cases h3 : U.lo.val ≤ t.val <;> by_cases h4 : t.val ≤ U.hi.val <;>
      simp [h3, h4, RatBoundsK.val, RatK.val_one, RatK.val_zero]
  · simp only [h, decide_false, ite_false, RatBoundsK.val, RatK.val_maxK, RatK.val_minK,
      RatK.val_mul, RatK.val_sub, RatK.val_inv, div_eq_mul_inv]

/-- The six lower coefficients as exact fractions. -/
structure SideLowerK where
  value : RatK
  first : RatK
  second : RatK
  diagonalFirst : RatK
  mixed : RatK
  diagonalSecond : RatK

/-- The six lower numerators as exact fractions over `2 ^ 96`. -/
def SideLowerNumerators.toK (N : SideLowerNumerators) : SideLowerK :=
  ⟨⟨N.value, 79228162514264337593543950335⟩, ⟨N.first, 79228162514264337593543950335⟩,
    ⟨N.second, 79228162514264337593543950335⟩, ⟨N.diagonalFirst, 79228162514264337593543950335⟩,
    ⟨N.mixed, 79228162514264337593543950335⟩, ⟨N.diagonalSecond, 79228162514264337593543950335⟩⟩

/-- `SideLowerCoefficients.rectangleEndpointOK` on exact fractions. -/
noncomputable def SideLowerNumerators.rectangleEndpointOKK (N : SideLowerNumerators) (a : RatK)
    (U V : RatBoundsK) : Bool :=
  let c := N.toK
  let A := c.diagonalFirst
  let B := c.mixed
  let C := c.diagonalSecond
  let G := a.mul c.first
  let K := a.mul c.second
  let J := a.mul c.value
  let edge (u : RatK) := sideIntervalOKK C (K.add ((RatK.two.mul B).mul u))
    ((J.add (G.mul u)).add (A.mul (u.mul u))) V
  edge U.lo && edge U.hi &&
    Bool.rec true
      (sideIntervalOKK (C.sub ((B.mul B).mul A.inv)) (K.sub ((B.mul G).mul A.inv))
        (J.sub ((G.mul G).mul (RatK.four.mul A).inv))
        (sideAffinePreimageK ((RatK.zero.sub B).mul A.inv)
          ((RatK.zero.sub G).mul (RatK.two.mul A).inv) U V))
      (RatK.zero.lt A)

noncomputable def SideLowerNumerators.rectangleOKK (N : SideLowerNumerators) (a U V : RatBoundsK) :
    Bool :=
  N.rectangleEndpointOKK a.lo U V && N.rectangleEndpointOKK a.hi U V

private theorem units_pred_cast :
    ((79228162514264337593543950335 : ℕ) : ℚ) + 1 = ((DyadicBounds.units : ℕ) : ℚ) := by
  simp only [DyadicBounds.units]; norm_num

theorem SideLowerNumerators.toK_val (N : SideLowerNumerators) :
    N.toK.value.val = N.value / ((DyadicBounds.units : ℕ) : ℚ) ∧
    N.toK.first.val = N.first / ((DyadicBounds.units : ℕ) : ℚ) ∧
    N.toK.second.val = N.second / ((DyadicBounds.units : ℕ) : ℚ) ∧
    N.toK.diagonalFirst.val = N.diagonalFirst / ((DyadicBounds.units : ℕ) : ℚ) ∧
    N.toK.mixed.val = N.mixed / ((DyadicBounds.units : ℕ) : ℚ) ∧
    N.toK.diagonalSecond.val = N.diagonalSecond / ((DyadicBounds.units : ℕ) : ℚ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [SideLowerNumerators.toK, RatK.val, units_pred_cast]

theorem SideLowerNumerators.rectangleEndpointOKK_eq (N : SideLowerNumerators) (a : RatK)
    (U V : RatBoundsK) :
    N.rectangleEndpointOKK a U V =
      (⟨N.value / ((DyadicBounds.units : ℕ) : ℚ), N.first / ((DyadicBounds.units : ℕ) : ℚ),
        N.second / ((DyadicBounds.units : ℕ) : ℚ),
        N.diagonalFirst / ((DyadicBounds.units : ℕ) : ℚ), N.mixed / ((DyadicBounds.units : ℕ) : ℚ),
        N.diagonalSecond / ((DyadicBounds.units : ℕ) : ℚ)⟩ :
        SideLowerCoefficients).rectangleEndpointOK a.val U.val V.val := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := N.toK_val
  have hlo : U.val.lo = U.lo.val := rfl
  have hhi : U.val.hi = U.hi.val := rfl
  unfold SideLowerNumerators.rectangleEndpointOKK SideLowerCoefficients.rectangleEndpointOK
  simp only [sideIntervalOKK_eq, sideAffinePreimageK_val, RatK.lt_eq, RatK.val_add, RatK.val_sub,
    RatK.val_mul, RatK.val_inv, RatK.val_zero, RatK.val_two, RatK.val_four, h0, h1, h2, h3, h4, h5,
    hlo, hhi]
  by_cases hA : (0 : ℚ) < N.diagonalFirst / ((DyadicBounds.units : ℕ) : ℚ)
  · simp only [hA, decide_true, ite_true]
    congr 1 <;> congr 1 <;> ring_nf
  · simp only [hA, decide_false, ite_false]
    congr 1; congr 1 <;> ring_nf

theorem SideLowerNumerators.rectangleOKK_eq (N : SideLowerNumerators) (a U V : RatBoundsK) :
    N.rectangleOKK a U V =
      (⟨N.value / ((DyadicBounds.units : ℕ) : ℚ), N.first / ((DyadicBounds.units : ℕ) : ℚ),
        N.second / ((DyadicBounds.units : ℕ) : ℚ),
        N.diagonalFirst / ((DyadicBounds.units : ℕ) : ℚ), N.mixed / ((DyadicBounds.units : ℕ) : ℚ),
        N.diagonalSecond / ((DyadicBounds.units : ℕ) : ℚ)⟩ :
        SideLowerCoefficients).rectangleOK a.val U.val V.val := by
  unfold SideLowerNumerators.rectangleOKK SideLowerCoefficients.rectangleOK
  rw [N.rectangleEndpointOKK_eq, N.rectangleEndpointOKK_eq]; rfl

/-- `SideFastParameter.leafCheck` in kernel form: the fixed-point products and the determinant
test on kernel integer operations, and the box, argument, power and mixed-interval computations in
exact kernel fractions. Only the rectangle test, run where the determinant test fails, stays
rational. -/
noncomputable def SideFastParameter.leafCheckK (P : SideFastParameter) (U V : RatBounds)
    (U' V' : SideFastAxis) (mixed : FactorSamples) : Bool :=
  let base := sideBaseK P.cell
  let X := (sideShiftK P.cell U V).divPositive base
  let A := P.terms.evaluateK U'.bounds V'.bounds (sideMixedK base X mixed)
  let s := intNonnegK U.lo.num
  let t := intNonnegK V.lo.num
  (sideSignOKK U && sideSignOKK V) && sideSecondFactorRangeOKK sideNearExponent X mixed &&
    A.valid &&
    ((A.lowerNum s t).detOKK P.cell.a.hi ||
      (A.lowerNum s t).rectangleOKK (RatBoundsK.ofRat P.cell.a) (RatBoundsK.ofRat U)
        (RatBoundsK.ofRat V))

theorem SideFastParameter.leafCheckK_eq (P : SideFastParameter) (U V : RatBounds)
    (U' V' : SideFastAxis) (mixed : FactorSamples) :
    P.leafCheckK U V U' V' mixed = P.leafCheck U V U' V' mixed := by
  have harg : ((sideShiftK P.cell U V).divPositive (sideBaseK P.cell)).val =
      (P.box U V).argument := by
    rw [RatBoundsK.val_divPositive, sideShiftK_val, sideBaseK_val]; rfl
  simp only [SideFastParameter.leafCheckK, SideFastParameter.leafCheck, sideMixedK_eq,
    SideFastParameterTerms.evaluateK_eq, sideSecondFactorRangeOKK_eq, harg, sideSignOKK_eq,
    sideAxisSignK_eq, SideLowerNumerators.detOKK_eq, ← SideDyadicCoefficients.detOK_eq_num,
    SideLowerNumerators.rectangleOKK_eq, RatBoundsK.val_ofRat,
    ← SideDyadicCoefficients.lower_eq_num,
    SideNearBox.signsOK, SideFastParameter.box_u, SideFastParameter.box_v,
    SideFastParameter.box_exponent]

end HlawkaSchatten.BelowExponent.Vertex
