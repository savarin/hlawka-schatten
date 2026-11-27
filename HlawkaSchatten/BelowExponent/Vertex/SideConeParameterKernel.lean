/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.SideConeBox
public import HlawkaSchatten.BelowExponent.Vertex.SideConePowerData
public import HlawkaSchatten.BelowExponent.Vertex.DyadicKernel

/-! The side-cone cell and parameter computations in exact kernel fractions: the cell intervals,
the root and gradient guards, the side-gradient factors and the factor ranges. Each is proved equal,
for all inputs, to the rational computation it replaces. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

noncomputable def RatBoundsK.divPositive (N D : RatBoundsK) : RatBoundsK :=
  N.mul ⟨D.hi.inv, D.lo.inv⟩

theorem RatBoundsK.val_divPositive (N D : RatBoundsK) :
    (N.divPositive D).val = N.val.divPositive D.val := by
  simp only [RatBoundsK.divPositive, RatBounds.divPositive, RatBoundsK.val_mul]
  simp [RatBoundsK.val, RatK.val_inv, one_div]

/-- `SideNearBox.base` of the cell. -/
noncomputable def sideBaseK (c : ParameterCell) : RatBoundsK :=
  (RatBoundsK.point RatK.one).add
    (((RatBoundsK.point RatK.four).mul (RatBoundsK.ofRat c.η)).mul (RatBoundsK.ofRat c.a))

/-- `SideNearBox.shift` of the cell and the axis bounds. -/
noncomputable def sideShiftK (c : ParameterCell) (U V : RatBounds) : RatBoundsK :=
  let P := RatBoundsK.point
  let depth := (P RatK.two).mul (RatBoundsK.ofRat c.η)
  let C := (P RatK.one).add (depth.mul ((P RatK.one).sub (RatBoundsK.ofRat c.b)))
  let D := (P RatK.one).add (depth.mul ((RatBoundsK.ofRat c.a).add (RatBoundsK.ofRat c.b)))
  (C.mul (RatBoundsK.ofRat U)).add (D.mul (RatBoundsK.ofRat V))

/-- `secondPoint`, with the exponent `p` read from its literal. -/
noncomputable def sideSecondPointK (p : ℚ) (x : RatK) (Q : RatBounds) : RatBoundsK :=
  let pK := RatK.ofRat p
  Bool.rec
    ((((RatBoundsK.ofRat Q).sub (RatBoundsK.point RatK.one)).sub
        (RatBoundsK.point (pK.mul x))).mul
      (RatBoundsK.point (RatK.two.mul ((pK.mul (pK.sub RatK.one)).mul (x.mul x)).inv)))
    (RatBoundsK.point RatK.one) x.isZero

theorem sideSecondPointK_val (p : ℚ) (x : RatK) (Q : RatBounds) :
    (sideSecondPointK p x Q).val = secondPoint p x.val Q := by
  unfold sideSecondPointK secondPoint
  rw [RatK.isZero_eq]
  by_cases h : x.val = 0
  · simp [h, RatBoundsK.val_point]
  · simp only [h, decide_false, ite_false, RatBoundsK.val_mul, RatBoundsK.val_sub,
      RatBoundsK.val_point, RatBoundsK.val_ofRat, RatK.val_mul, RatK.val_sub, RatK.val_inv,
      RatK.val_ofRat, RatK.val_one, RatK.val_two, div_eq_mul_inv, sq]

noncomputable def sideExponentLowerK (P : RatBounds) (x : RatK) : ℚ :=
  Bool.rec P.lo P.hi (x.le RatK.zero)

noncomputable def sideExponentUpperK (P : RatBounds) (x : RatK) : ℚ :=
  Bool.rec P.hi P.lo (x.le RatK.zero)

theorem sideExponentLowerK_eq (P : RatBounds) (x : RatK) :
    sideExponentLowerK P x = exponentLower P x.val := by
  unfold sideExponentLowerK exponentLower; rw [RatK.le_eq, RatK.val_zero]
  by_cases h : x.val ≤ 0 <;> simp [h]

theorem sideExponentUpperK_eq (P : RatBounds) (x : RatK) :
    sideExponentUpperK P x = exponentUpper P x.val := by
  unfold sideExponentUpperK exponentUpper; rw [RatK.le_eq, RatK.val_zero]
  by_cases h : x.val ≤ 0 <;> simp [h]

noncomputable def sideSecondFactorRangeK (P : RatBounds) (X : RatBoundsK) (W : FactorSamples) :
    RatBoundsK :=
  ⟨(sideSecondPointK (sideExponentLowerK P X.hi) X.hi W.lowerPower).lo,
    (sideSecondPointK (sideExponentUpperK P X.lo) X.lo W.upperPower).hi⟩

theorem sideSecondFactorRangeK_val (P : RatBounds) (X : RatBoundsK) (W : FactorSamples) :
    (sideSecondFactorRangeK P X W).val = secondFactorRange P X.val W := by
  have h1 := congrArg RatBounds.lo
    (sideSecondPointK_val (sideExponentLowerK P X.hi) X.hi W.lowerPower)
  have h2 := congrArg RatBounds.hi
    (sideSecondPointK_val (sideExponentUpperK P X.lo) X.lo W.upperPower)
  simp only [RatBoundsK.val, sideExponentLowerK_eq, sideExponentUpperK_eq] at h1 h2
  simp only [sideSecondFactorRangeK, secondFactorRange, RatBoundsK.val, sideExponentLowerK_eq,
    sideExponentUpperK_eq, h1, h2]

noncomputable def sidePowerOKK (p : ℚ) (x : RatK) (Q : RatBounds) : Bool :=
  RatK.negOne.lt x && intPosK p.num && intNonnegK Q.lo.num && intNonnegK Q.hi.num &&
    (RatK.ofRat Q.lo).crossLE (RatK.one.add x) p.den p.num.natAbs &&
    (RatK.one.add x).crossLE (RatK.ofRat Q.hi) p.num.natAbs p.den

theorem sidePowerOKK_eq (p : ℚ) (x : RatK) (Q : RatBounds) :
    sidePowerOKK p x Q = sidePowerOK p x.val Q := by
  simp only [sidePowerOKK, sidePowerOK, RatK.lt_eq, RatK.val_negOne, intPosK_eq, intNonnegK_eq,
    RatK.crossLE_eq, RatK.val_ofRat, RatK.val_add, RatK.val_one, Bool.decide_and, Rat.num_pos,
    Rat.num_nonneg, Bool.and_assoc]

noncomputable def sideSecondFactorRangeOKK (P : RatBounds) (X : RatBoundsK) (W : FactorSamples) :
    Bool :=
  RatK.negOne.lt X.lo && decide (sideExponentLowerK P X.hi ≠ 1) &&
    decide (sideExponentUpperK P X.lo ≠ 1) &&
    sidePowerOKK (sideExponentLowerK P X.hi) X.hi W.lowerPower &&
    sidePowerOKK (sideExponentUpperK P X.lo) X.lo W.upperPower

theorem sideSecondFactorRangeOKK_eq (P : RatBounds) (X : RatBoundsK) (W : FactorSamples) :
    sideSecondFactorRangeOKK P X W = secondFactorRangeOK P X.val W := by
  have hlo : X.val.lo = X.lo.val := rfl
  have hhi : X.val.hi = X.hi.val := rfl
  unfold sideSecondFactorRangeOKK secondFactorRangeOK
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq, RatK.lt_eq]
  simp only [RatK.val_negOne, sideExponentLowerK_eq, sideExponentUpperK_eq, sidePowerOKK_eq, hlo,
    hhi, and_assoc]


/-! ### Cell intervals -/

noncomputable def RatBoundsK.square (I : RatBoundsK) : RatBoundsK := I.mul I

theorem RatBoundsK.val_square (I : RatBoundsK) : I.square.val = I.val.sideSquare := by
  simp only [RatBoundsK.square, RatBounds.sideSquare, RatBoundsK.val_mul]

noncomputable def ParameterCell.directionK (c : ParameterCell) : Fin 3 → RatBoundsK :=
  ![RatBoundsK.ofRat c.a, RatBoundsK.ofRat c.b,
    ((RatBoundsK.point RatK.one).sub (RatBoundsK.ofRat c.a)).sub (RatBoundsK.ofRat c.b)]

theorem ParameterCell.directionK_val (c : ParameterCell) (j : Fin 3) :
    (c.directionK j).val = c.direction j := by
  fin_cases j <;> simp [ParameterCell.directionK, ParameterCell.direction, RatBoundsK.val_sub,
    RatBoundsK.val_point, RatBoundsK.val_ofRat, RatK.val_one]

/-- `ParameterCell.depth`: `η/(1+2η)` at both endpoints. -/
noncomputable def ParameterCell.depthK (c : ParameterCell) : RatBoundsK :=
  let lo := RatK.ofRat c.η.lo
  let hi := RatK.ofRat c.η.hi
  ⟨lo.mul (RatK.one.add (RatK.two.mul lo)).inv, hi.mul (RatK.one.add (RatK.two.mul hi)).inv⟩

theorem ParameterCell.depthK_val (c : ParameterCell) : c.depthK.val = c.depth := by
  simp [ParameterCell.depthK, ParameterCell.depth, RatBoundsK.val, RatK.val_mul, RatK.val_add,
    RatK.val_inv, RatK.val_ofRat, RatK.val_one, RatK.val_two, div_eq_mul_inv]

noncomputable def ParameterCell.baseK (c : ParameterCell) (j : Fin 3) : RatBoundsK :=
  let one := RatBoundsK.point RatK.one
  ((one.sub c.depthK).mul (one.sub (c.directionK j))).add
    (c.depthK.mul ((c.directionK (j+1)).mul (c.directionK (j+2))))

theorem ParameterCell.baseK_val (c : ParameterCell) (j : Fin 3) : (c.baseK j).val = c.base j := by
  simp only [ParameterCell.baseK, ParameterCell.base, RatBoundsK.val_add, RatBoundsK.val_mul,
    RatBoundsK.val_sub, RatBoundsK.val_point, RatK.val_one, ParameterCell.depthK_val,
    ParameterCell.directionK_val]

noncomputable def ParameterCell.otherK (c : ParameterCell) (j : Fin 3) : RatBoundsK :=
  (RatBoundsK.point RatK.one).sub (c.depthK.mul (c.directionK j))

theorem ParameterCell.otherK_val (c : ParameterCell) (j : Fin 3) :
    (c.otherK j).val = c.other j := by
  simp only [ParameterCell.otherK, ParameterCell.other, RatBoundsK.val_sub, RatBoundsK.val_mul,
    RatBoundsK.val_point, RatK.val_one, ParameterCell.depthK_val, ParameterCell.directionK_val]

noncomputable def ParameterCell.sigmaK (c : ParameterCell) : RatBoundsK :=
  let e := c.directionK
  (((e 0).mul (e 1)).add ((e 0).mul (e 2))).add ((e 1).mul (e 2))

theorem ParameterCell.sigmaK_val (c : ParameterCell) : c.sigmaK.val = c.sigma := by
  simp only [ParameterCell.sigmaK, ParameterCell.sigma, RatBoundsK.val_add, RatBoundsK.val_mul,
    ParameterCell.directionK_val]

/-! ### The root guard -/

/-- `rootBoundsOK` on exact fractions, the radical bounds read from their literals. -/
noncomputable def rootBoundsOKK (A B S : RatBoundsK) (R : RatBounds) : Bool :=
  let rl := RatK.ofRat R.lo
  let rh := RatK.ofRat R.hi
  let p5 (x : RatK) := (((x.mul x).mul x).mul x).mul x
  let p3 (x : RatK) := (x.mul x).mul x
  let p2 (x : RatK) := x.mul x
  RatK.zero.le A.lo && RatK.zero.le B.lo && RatK.zero.lt S.lo && RatK.zero.le rl && rl.le rh &&
    ((p5 rl).mul (p2 S.hi)).le ((p2 A.lo).mul (p3 B.lo)) &&
    ((p2 A.hi).mul (p3 B.hi)).le ((p5 rh).mul (p2 S.lo))

theorem rootBoundsOKK_eq (A B S : RatBoundsK) (R : RatBounds) :
    rootBoundsOKK A B S R = rootBoundsOK A.val B.val S.val R := by
  have hAlo : A.val.lo = A.lo.val := rfl
  have hAhi : A.val.hi = A.hi.val := rfl
  have hBlo : B.val.lo = B.lo.val := rfl
  have hBhi : B.val.hi = B.hi.val := rfl
  have hSlo : S.val.lo = S.lo.val := rfl
  have hShi : S.val.hi = S.hi.val := rfl
  unfold rootBoundsOKK rootBoundsOK
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq, RatK.le_eq, RatK.lt_eq]
  simp only [RatK.val_mul, RatK.val_zero, RatK.val_ofRat, hAlo, hAhi, hBlo, hBhi, hSlo, hShi]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩
    exact ⟨h1, h2, h3, h4, h5, by ring_nf; ring_nf at h6; exact h6,
      by ring_nf; ring_nf at h7; exact h7⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, by ring_nf; ring_nf at h6; exact h6⟩,
      by ring_nf; ring_nf at h7; exact h7⟩

/-- `ParameterCell.rootsOK` on exact fractions. -/
noncomputable def ParameterCell.rootsOKK (c : ParameterCell) (roots : Fin 3 → RatBounds) : Bool :=
  intNonnegK c.η.lo.num && (List.finRange 3).all (fun j =>
    rootBoundsOKK (c.baseK j) (c.otherK j) c.sigmaK (roots j))

theorem ParameterCell.rootsOKK_eq (c : ParameterCell) (roots : Fin 3 → RatBounds) :
    c.rootsOKK roots = c.rootsOK roots := by
  unfold ParameterCell.rootsOKK ParameterCell.rootsOK
  congr 1
  · rw [intNonnegK_eq]; exact decide_eq_decide.mpr Rat.num_nonneg
  · congr 1; funext j
    rw [rootBoundsOKK_eq, ParameterCell.baseK_val, ParameterCell.otherK_val,
      ParameterCell.sigmaK_val]

/-! ### The side-gradient factors and guard -/

noncomputable def ParameterCell.sideEtaDenK (c : ParameterCell) : RatBoundsK :=
  (RatBoundsK.point RatK.one).add (RatBoundsK.ofRat c.η)

theorem ParameterCell.sideEtaDenK_val (c : ParameterCell) : c.sideEtaDenK.val = c.sideEtaDen := by
  simp only [ParameterCell.sideEtaDenK, ParameterCell.sideEtaDen, RatBoundsK.val_add,
    RatBoundsK.val_point, RatBoundsK.val_ofRat, RatK.val_one]

noncomputable def ParameterCell.sideEtaRatioK (c : ParameterCell) : RatBoundsK :=
  (RatBoundsK.ofRat c.η).divPositive c.sideEtaDenK

theorem ParameterCell.sideEtaRatioK_val (c : ParameterCell) :
    c.sideEtaRatioK.val = c.sideEtaRatio := by
  simp only [ParameterCell.sideEtaRatioK, ParameterCell.sideEtaRatio, RatBoundsK.val_divPositive,
    RatBoundsK.val_ofRat, ParameterCell.sideEtaDenK_val]

noncomputable def ParameterCell.sideBetaDenK (c : ParameterCell) : RatBoundsK :=
  let e := c.directionK
  (((RatBoundsK.point RatK.one).add ((e 0).divPositive (e 1)).square).add
    ((e 0).divPositive (e 2)).square).add ((e 0).mul c.sideEtaRatioK).square

theorem ParameterCell.sideBetaDenK_val (c : ParameterCell) :
    c.sideBetaDenK.val = c.sideBetaDen := by
  simp only [ParameterCell.sideBetaDenK, ParameterCell.sideBetaDen, RatBoundsK.val_add,
    RatBoundsK.val_square, RatBoundsK.val_divPositive, RatBoundsK.val_mul, RatBoundsK.val_point,
    RatK.val_one, ParameterCell.directionK_val, ParameterCell.sideEtaRatioK_val]

noncomputable def ParameterCell.sideBetaFactorK (c : ParameterCell) (j : Fin 3) : RatBoundsK :=
  ((c.directionK 0).divPositive (c.directionK j).square).divPositive c.sideBetaDenK

theorem ParameterCell.sideBetaFactorK_val (c : ParameterCell) (j : Fin 3) :
    (c.sideBetaFactorK j).val = c.sideBetaFactor j := by
  simp only [ParameterCell.sideBetaFactorK, ParameterCell.sideBetaFactor,
    RatBoundsK.val_divPositive, RatBoundsK.val_square, ParameterCell.directionK_val,
    ParameterCell.sideBetaDenK_val]

noncomputable def ParameterCell.sideHeavyFactorK (c : ParameterCell) : RatBoundsK :=
  ((c.directionK 0).mul ((RatBoundsK.point RatK.one).add c.sideEtaRatioK).square).divPositive
    c.sideBetaDenK

theorem ParameterCell.sideHeavyFactorK_val (c : ParameterCell) :
    c.sideHeavyFactorK.val = c.sideHeavyFactor := by
  simp only [ParameterCell.sideHeavyFactorK, ParameterCell.sideHeavyFactor,
    RatBoundsK.val_divPositive, RatBoundsK.val_mul, RatBoundsK.val_square, RatBoundsK.val_add,
    RatBoundsK.val_point, RatK.val_one, ParameterCell.directionK_val,
    ParameterCell.sideEtaRatioK_val, ParameterCell.sideBetaDenK_val]

/-- `ParameterCell.sideGradientOK` on exact fractions. -/
noncomputable def ParameterCell.sideGradientOKK (c : ParameterCell) : Bool :=
  RatK.zero.lt c.sideEtaDenK.lo && RatK.zero.lt (c.directionK 1).lo &&
    RatK.zero.lt (c.directionK 2).lo && RatK.zero.lt (c.directionK 1).square.lo &&
    RatK.zero.lt (c.directionK 2).square.lo && RatK.zero.lt c.sideBetaDenK.lo

theorem ParameterCell.sideGradientOKK_eq (c : ParameterCell) :
    c.sideGradientOKK = c.sideGradientOK := by
  have h1 := congrArg RatBounds.lo c.sideEtaDenK_val
  have h2 := congrArg RatBounds.lo (c.directionK_val 1)
  have h3 := congrArg RatBounds.lo (c.directionK_val 2)
  have h4 := congrArg RatBounds.lo ((c.directionK 1).val_square.trans (by rw [c.directionK_val 1]))
  have h5 := congrArg RatBounds.lo ((c.directionK 2).val_square.trans (by rw [c.directionK_val 2]))
  have h6 := congrArg RatBounds.lo c.sideBetaDenK_val
  simp only [RatBoundsK.val] at h1 h2 h3 h4 h5 h6
  unfold ParameterCell.sideGradientOKK ParameterCell.sideGradientOK
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq, RatK.lt_eq]
  simp only [RatK.val_zero, h1, h2, h3, h4, h5, h6, and_assoc]

/-! ### The side gradient -/

/-- `SideGradientInputs` with exact-fraction intervals. -/
structure SideGradientInputsK where
  eta : RatBoundsK
  eps : RatBoundsK
  direction : Fin 3 → RatBoundsK
  root : Fin 3 → RatBoundsK
  betaZero : RatBoundsK
  betaOne : RatBoundsK
  betaTwo : RatBoundsK
  betaLarge : RatBoundsK

def SideGradientInputsK.val (I : SideGradientInputsK) : SideGradientInputs :=
  ⟨I.eta.val, I.eps.val, fun i => (I.direction i).val, fun i => (I.root i).val, I.betaZero.val,
    I.betaOne.val, I.betaTwo.val, I.betaLarge.val⟩

/-- `2/3` and `-2` as literal fractions. -/
def RatK.twoThirds : RatK := ⟨Int.ofNat 2, 2⟩
def RatK.negTwo : RatK := ⟨Int.negSucc 1, 0⟩

@[simp] theorem RatK.val_twoThirds : RatK.twoThirds.val = 2/3 := by
  norm_num [RatK.val, RatK.twoThirds]
@[simp] theorem RatK.val_negTwo : RatK.negTwo.val = -2 := by
  norm_num [RatK.val, RatK.negTwo]

/-- `SideGradientInputs.correction` on exact fractions, operation for operation. -/
noncomputable def SideGradientInputsK.correction (I : SideGradientInputsK) : Fin 3 → RatBoundsK :=
  let P := RatBoundsK.point
  let T := ((I.root 0).add (I.root 1)).add (I.root 2)
  let Δ := fun j => T.sub ((P RatK.two).mul (I.root j))
  let A := fun j => (P RatK.one).sub (I.direction j)
  let B := (I.betaOne.add I.betaTwo).add ((I.eps.mul I.eps).mul I.betaLarge)
  let E := fun j => (P RatK.one).sub (I.eps.mul (A j))
  let weightedRoot (j : Fin 3) (beta : RatBoundsK) :=
    (beta.mul (I.direction j)).mul (I.eps.add (Δ j))
  let heavyRoot := ((I.eps.mul I.betaLarge).mul ((P RatK.one).sub I.eps)).mul (T.sub I.eps)
  let zeroRoot := I.betaZero.mul (I.eps.add (Δ 0))
  let X := (P RatK.twoThirds).mul (((heavyRoot.add zeroRoot).add (weightedRoot 1 I.betaOne)).add
    (weightedRoot 2 I.betaTwo))
  let heavy (j : Fin 3) := ((((P RatK.two).mul I.eps).mul I.betaLarge).mul (I.root j)).mul (E j)
  let apart (j : Fin 3) (R B : RatBoundsK) := (((P RatK.two).mul (A j)).mul R).mul B
  let c₀ := ((P RatK.zero).sub (I.eps.add (Δ 0))).add (((P RatK.two).mul (E 0)).mul B)
  let c₀cross := ((P RatK.two).mul (A 0)).mul
    ((I.betaOne.mul (I.root 2)).add (I.betaTwo.mul (I.root 1)))
  let c₁ := (((P RatK.negTwo).mul (E 1)).mul I.betaOne).add (apart 1 (I.root 2) B)
  let c₂ := (((P RatK.negTwo).mul (E 2)).mul I.betaTwo).add (apart 2 (I.root 1) B)
  ![(((c₀.sub (heavy 0)).sub c₀cross).add X),
    (((c₁.sub (heavy 1)).sub (apart 1 I.betaTwo (I.root 0))).add X),
    (((c₂.sub (heavy 2)).sub (apart 2 I.betaOne (I.root 0))).add X)]

theorem SideGradientInputsK.correction_val (I : SideGradientInputsK) (j : Fin 3) :
    (I.correction j).val = I.val.correction j := by
  fin_cases j <;>
    simp [SideGradientInputsK.correction, SideGradientInputs.correction, SideGradientInputsK.val,
      addThree, RatBoundsK.val_add, RatBoundsK.val_sub, RatBoundsK.val_mul, RatBoundsK.val_point]

noncomputable def SideGradientInputsK.evaluate (I : SideGradientInputsK) (j : Fin 3) : RatBoundsK :=
  (I.correction j).sub ((((RatBoundsK.point RatK.two).mul I.eta).mul
    ((RatBoundsK.point RatK.one).sub (I.direction j))).mul (I.correction 0))

theorem SideGradientInputsK.evaluate_val (I : SideGradientInputsK) (j : Fin 3) :
    (I.evaluate j).val = I.val.evaluate j := by
  simp only [SideGradientInputsK.evaluate, SideGradientInputs.evaluate, RatBoundsK.val_sub,
    RatBoundsK.val_mul, RatBoundsK.val_point, RatK.val_one, RatK.val_two,
    SideGradientInputsK.correction_val]
  rfl

/-- `ParameterCell.sideGradient` with exact-fraction intervals. -/
noncomputable def ParameterCell.sideGradientK (c : ParameterCell) (roots : Fin 3 → RatBounds) :
    SideGradientInputsK :=
  ⟨RatBoundsK.ofRat c.η, c.depthK, c.directionK, fun j => RatBoundsK.ofRat (roots j),
    (RatBoundsK.point RatK.one).divPositive c.sideBetaDenK, c.sideBetaFactorK 1,
    c.sideBetaFactorK 2,
    c.sideHeavyFactorK⟩

theorem ParameterCell.sideGradientK_val (c : ParameterCell) (roots : Fin 3 → RatBounds) :
    (c.sideGradientK roots).val = c.sideGradient roots := by
  simp only [ParameterCell.sideGradientK, SideGradientInputsK.val, ParameterCell.sideGradient,
    RatBoundsK.val_ofRat, ParameterCell.depthK_val, ParameterCell.directionK_val,
    RatBoundsK.val_divPositive, RatBoundsK.val_point, RatK.val_one, ParameterCell.sideBetaDenK_val,
    ParameterCell.sideBetaFactorK_val, ParameterCell.sideHeavyFactorK_val]

/-! ### First-factor ranges and the base shift -/

/-- `firstPoint`, with the exponent `p` read from its literal. -/
noncomputable def sideFirstPointK (p : ℚ) (x : RatK) (Q : RatBounds) : RatBoundsK :=
  Bool.rec
    (((RatBoundsK.ofRat Q).sub (RatBoundsK.point RatK.one)).mul
      (RatBoundsK.point ((RatK.ofRat p).mul x).inv))
    (RatBoundsK.point RatK.one) x.isZero

theorem sideFirstPointK_val (p : ℚ) (x : RatK) (Q : RatBounds) :
    (sideFirstPointK p x Q).val = firstPoint p x.val Q := by
  unfold sideFirstPointK firstPoint
  rw [RatK.isZero_eq]
  by_cases h : x.val = 0
  · simp [h, RatBoundsK.val_point]
  · simp only [h, decide_false, ite_false, RatBoundsK.val_mul, RatBoundsK.val_sub,
      RatBoundsK.val_point, RatBoundsK.val_ofRat, RatK.val_mul, RatK.val_inv, RatK.val_ofRat,
      RatK.val_one, one_div]

noncomputable def sideArgumentLowerK (X : RatBoundsK) (inc : Bool) : RatK := Bool.rec X.hi X.lo inc
noncomputable def sideArgumentUpperK (X : RatBoundsK) (inc : Bool) : RatK := Bool.rec X.lo X.hi inc

theorem sideArgumentLowerK_val (X : RatBoundsK) (inc : Bool) :
    (sideArgumentLowerK X inc).val = argumentLower X.val inc := by
  cases inc <;> rfl

theorem sideArgumentUpperK_val (X : RatBoundsK) (inc : Bool) :
    (sideArgumentUpperK X inc).val = argumentUpper X.val inc := by
  cases inc <;> rfl

noncomputable def sideFirstFactorRangeK (P : RatBounds) (X : RatBoundsK) (inc : Bool)
    (W : FactorSamples) : RatBoundsK :=
  let x₀ := sideArgumentLowerK X inc
  let x₁ := sideArgumentUpperK X inc
  ⟨(sideFirstPointK (sideExponentLowerK P x₀) x₀ W.lowerPower).lo,
    (sideFirstPointK (sideExponentUpperK P x₁) x₁ W.upperPower).hi⟩

theorem sideFirstFactorRangeK_val (P : RatBounds) (X : RatBoundsK) (inc : Bool)
    (W : FactorSamples) :
    (sideFirstFactorRangeK P X inc W).val = firstFactorRange P X.val inc W := by
  have h1 := congrArg RatBounds.lo (sideFirstPointK_val (sideExponentLowerK P
    (sideArgumentLowerK X inc)) (sideArgumentLowerK X inc) W.lowerPower)
  have h2 := congrArg RatBounds.hi (sideFirstPointK_val (sideExponentUpperK P
    (sideArgumentUpperK X inc)) (sideArgumentUpperK X inc) W.upperPower)
  simp only [RatBoundsK.val, sideExponentLowerK_eq, sideExponentUpperK_eq,
    sideArgumentLowerK_val, sideArgumentUpperK_val] at h1 h2
  simp only [sideFirstFactorRangeK, firstFactorRange, RatBoundsK.val, sideExponentLowerK_eq,
    sideExponentUpperK_eq, sideArgumentLowerK_val, sideArgumentUpperK_val, h1, h2]

noncomputable def sideFirstFactorRangeOKK (P : RatBounds) (X : RatBoundsK) (inc : Bool)
    (W : FactorSamples) : Bool :=
  let x₀ := sideArgumentLowerK X inc
  let x₁ := sideArgumentUpperK X inc
  RatK.negOne.lt X.lo && sidePowerOKK (sideExponentLowerK P x₀) x₀ W.lowerPower &&
    sidePowerOKK (sideExponentUpperK P x₁) x₁ W.upperPower

theorem sideFirstFactorRangeOKK_eq (P : RatBounds) (X : RatBoundsK) (inc : Bool)
    (W : FactorSamples) :
    sideFirstFactorRangeOKK P X inc W = firstFactorRangeOK P X.val inc W := by
  have hlo : X.val.lo = X.lo.val := rfl
  unfold sideFirstFactorRangeOKK firstFactorRangeOK
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq, RatK.lt_eq]
  simp only [RatK.val_negOne, sideExponentLowerK_eq, sideExponentUpperK_eq, sidePowerOKK_eq,
    sideArgumentLowerK_val, sideArgumentUpperK_val, hlo]

/-- `SideNearBox.baseShift` of the cell. -/
noncomputable def sideBaseShiftK (c : ParameterCell) : RatBoundsK :=
  ((RatBoundsK.point RatK.four).mul (RatBoundsK.ofRat c.η)).mul (RatBoundsK.ofRat c.a)

theorem sideBaseShiftK_val (B : SideNearBox) : (sideBaseShiftK B.cell).val = B.baseShift := by
  simp only [sideBaseShiftK, SideNearBox.baseShift, RatBoundsK.val_mul, RatBoundsK.val_point,
    RatBoundsK.val_ofRat, RatK.val_four]

theorem sideBaseK_val' (B : SideNearBox) : (sideBaseK B.cell).val = B.base := by
  simp only [sideBaseK, SideNearBox.base, SideNearBox.baseShift, RatBoundsK.val_add,
    RatBoundsK.val_mul, RatBoundsK.val_point, RatBoundsK.val_ofRat, RatK.val_one, RatK.val_four]

theorem sideShiftK_val' (B : SideNearBox) : (sideShiftK B.cell B.u B.v).val = B.shift := by
  simp only [sideShiftK, SideNearBox.shift, RatBoundsK.val_add, RatBoundsK.val_mul,
    RatBoundsK.val_sub, RatBoundsK.val_point, RatBoundsK.val_ofRat, RatK.val_one, RatK.val_two]

/-- Converting a fixed-point interval to rationals and back returns its endpoints. -/
theorem DyadicBounds.ofRat_toSideRat (v : DyadicBounds) :
    DyadicBounds.ofRat v.toSideRat = ⟨v.lo, v.hi, true⟩ := by
  have hU : ((DyadicBounds.units : ℕ) : ℚ) ≠ 0 := by simp [DyadicBounds.units]
  rw [DyadicBounds.ofRat_def]
  simp only [DyadicBounds.toSideRat, DyadicBounds.lower, DyadicBounds.upper, div_mul_cancel₀ _ hU,
    Int.floor_intCast, Int.ceil_intCast]

end HlawkaSchatten.BelowExponent.Vertex
