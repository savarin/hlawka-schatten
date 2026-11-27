/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PGeometryData
public import HlawkaSchatten.BelowExponent.G3PPreparedNearSound
public import HlawkaSchatten.BelowExponent.G3PSharedPowerSound

/-! The native G3 geometry and power checks preserve their rational specifications. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P.Geometry

open Vertex (RatK RatBoundsK RatBounds)

noncomputable section

private theorem val_mk (a b : RatK) : (RatBoundsK.mk a b).val = ⟨a.val,b.val⟩ := rfl
private theorem lo_val (A : RatBoundsK) : A.lo.val = A.val.lo := rfl
private theorem hi_val (A : RatBoundsK) : A.hi.val = A.val.hi := rfl

attribute [local simp] RatK.val_ofRat RatK.val_mul RatK.val_add RatK.val_sub RatK.val_inv
  RatK.val_minK RatK.val_maxK RatK.val_zero RatK.val_one RatK.val_two RatK.val_negOne
  RatBoundsK.val_ofRat RatBoundsK.val_point RatBoundsK.val_add RatBoundsK.val_sub RatBoundsK.val_mul
  val_mk lo_val hi_val

@[simp] theorem neg_val (x : RatK) : (neg x).val = -x.val := by simp [neg]

@[simp] theorem ratOfK_eq (x : RatK) : ratOfK x = x.val := by
  have h := RatK.reduce_eq x
  have hd := x.val.den_pos
  apply Rat.ext
  · simp [ratOfK, h, RatK.ofRat]
  · simp [ratOfK, h, RatK.ofRat]; omega

@[simp] theorem boundsOfK_eq (A : RatBoundsK) : boundsOfK A = A.val := by
  simp only [boundsOfK, ratOfK_eq]; rfl

theorem unitBoxK_eq (h a : RatBounds) : unitBoxK h a = unitBox h a := by
  simp only [unitBoxK, unitBox]
  congr 1 <;> funext k <;> rcases k with ⟨_ | _ | _ | _ | n, hk⟩ <;>
    first | rfl | exact absurd hk (by omega)

theorem minK_idem (x : RatK) : x.minK x = x := by
  unfold RatK.minK; cases x.le x <;> rfl

theorem maxK_idem (x : RatK) : x.maxK x = x := by
  unfold RatK.maxK; cases x.le x <;> rfl

theorem pointMul_eq (c : RatK) (X : RatBoundsK) : pointMul c X = (RatBoundsK.point c).mul X := by
  simp only [pointMul, RatBoundsK.mul, RatBoundsK.point, minK_idem, maxK_idem]

theorem mulPoint_eq (X : RatBoundsK) (c : RatK) : mulPoint X c = X.mul (RatBoundsK.point c) := by
  simp only [mulPoint, RatBoundsK.mul, RatBoundsK.point, minK_idem, maxK_idem]

theorem minK_of_le {x y : RatK} (h : x.le y = true) : x.minK y = x := by
  unfold RatK.minK; rw [h]

theorem maxK_of_le {x y : RatK} (h : x.le y = true) : x.maxK y = y := by
  unfold RatK.maxK; rw [h]

private theorem le_of_val {x y : RatK} (h : x.val ≤ y.val) : x.le y = true := by
  rw [RatK.le_eq]; exact decide_eq_true h

private theorem val_nonneg_of {x : RatK} (h : Vertex.intNonnegK x.num = true) : 0 ≤ x.val := by
  rw [Vertex.intNonnegK_eq] at h
  have h0 : (0 : ℚ) ≤ x.num := by exact_mod_cast of_decide_eq_true h
  simp only [RatK.val]
  positivity

theorem mulNonneg_eq (A B : RatBoundsK) : mulNonneg A B = A.mul B := by
  unfold mulNonneg
  cases hA : Vertex.intNonnegK A.lo.num
  · rfl
  cases hB : Vertex.intNonnegK B.lo.num
  · rfl
  cases hoA : A.lo.le A.hi
  · rfl
  cases hoB : B.lo.le B.hi
  · rfl
  have h1 := val_nonneg_of hA
  have h2 := val_nonneg_of hB
  have h3 : A.lo.val ≤ A.hi.val := by rw [RatK.le_eq] at hoA; exact of_decide_eq_true hoA
  have h4 : B.lo.val ≤ B.hi.val := by rw [RatK.le_eq] at hoB; exact of_decide_eq_true hoB
  have l12 := le_of_val (x := A.lo.mul B.lo) (y := A.lo.mul B.hi)
    (by rw [RatK.val_mul, RatK.val_mul]; exact mul_le_mul_of_nonneg_left h4 h1)
  have l34 := le_of_val (x := A.hi.mul B.lo) (y := A.hi.mul B.hi)
    (by rw [RatK.val_mul, RatK.val_mul]; exact mul_le_mul_of_nonneg_left h4 (h1.trans h3))
  have l13 := le_of_val (x := A.lo.mul B.lo) (y := A.hi.mul B.lo)
    (by rw [RatK.val_mul, RatK.val_mul]; exact mul_le_mul_of_nonneg_right h3 h2)
  have l24 := le_of_val (x := A.lo.mul B.hi) (y := A.hi.mul B.hi)
    (by rw [RatK.val_mul, RatK.val_mul]; exact mul_le_mul_of_nonneg_right h3 (h2.trans h4))
  show (⟨A.lo.mul B.lo, A.hi.mul B.hi⟩ : RatBoundsK) = A.mul B
  simp only [RatBoundsK.mul, minK_of_le l12, minK_of_le l34, minK_of_le l13, maxK_of_le l12,
    maxK_of_le l34, maxK_of_le l24]

@[simp] theorem threeTwentieths_val : threeTwentieths.val = 3/20 := by
  simp only [threeTwentieths, RatK.val]; norm_num

@[simp] theorem fortyNineFiftieths_val : fortyNineFiftieths.val = 49/50 := by
  simp only [fortyNineFiftieths, RatK.val]; norm_num
@[simp] theorem abs_val (x : RatK) : (abs x).val = |x.val| := by
  rw [abs, RatK.val_maxK, neg_val]
  by_cases h : 0 ≤ x.val
  · rw [abs_of_nonneg h, max_eq_left (by linarith)]
  · rw [abs_of_nonpos (le_of_not_ge h), max_eq_right (by linarith)]

@[simp] theorem half_val : half.val = (1/2 : ℚ) := by simp [half]
@[simp] theorem unit_val (n : Nat) : (unit n).val = units n := by
  change (n : ℚ) / ((274877906943 : ℚ) + 1) = (n : ℚ) / 274877906944
  norm_num

@[simp] theorem sign_val (b : Bool) : (sign b).val = signRat b := by
  cases b <;> simp [sign, signRat]

@[simp] theorem interval_val (B : Box) (j : Fin 4) : (interval B j).val = bounds B j := by
  simp [interval]

@[simp] theorem reciprocal_val (A : RatBoundsK) : (reciprocal A).val = recip A.val := by
  simp [reciprocal, recip, one_div]

@[simp] theorem absolute_val (A : RatBoundsK) : (absolute A).val = absBounds A.val := by
  simp [absolute, absBounds]

@[simp] theorem ratio_val (x : ℚ) : (ratio x).val = G3S.ratio x := by
  simp [ratio, G3S.ratio, div_eq_mul_inv]

@[simp] theorem kBounds_val (B : Box) : (kBounds B).val = G3P.kBounds B := by
  simp [kBounds, G3P.kBounds, G3S.kMin, G3S.kMax]

@[simp] theorem lBounds_val (B : Box) : (lBounds B).val = G3P.lBounds B := by
  simp [lBounds, G3P.lBounds, mulNonneg_eq]

@[simp] theorem center_val (B : Box) : (center B).val = G3P.center B := by
  simp [center, G3P.center, pointMul_eq]

@[simp] theorem signedRatio_val (B : Box) (b : Bool) :
    (signedRatio B b).val = G3P.signedRatio B b := by
  simp [signedRatio, G3P.signedRatio, pointMul_eq]

@[simp] theorem ratioCenter_val (B : Box) (b : Bool) :
    (ratioCenter B b).val = ratioCenterBounds B b := by
  simp [ratioCenter, ratioCenterBounds, pointMul_eq]

@[simp] theorem ratioZ_val (B : Box) (b : Bool) : (ratioZ B b).val = ratioZBounds B b := by
  simp [ratioZ, ratioZBounds]

theorem physicalBox_eq (B : Box) (b : Bool) : physicalBox B b = ratioPhysicalBox B b := by
  have hlo := congrArg RatBounds.lo (ratioZ_val B b)
  have hhi := congrArg RatBounds.hi (ratioZ_val B b)
  change (ratioZ B b).lo.val = (ratioZBounds B b).lo at hlo
  change (ratioZ B b).hi.val = (ratioZBounds B b).hi at hhi
  simp only [physicalBox, ratioPhysicalBox, ratOfK_eq, hlo, hhi]
  congr 1 <;> funext k <;> rcases k with ⟨_ | _ | _ | _ | n, hk⟩ <;>
    first | rfl | exact absurd hk (by omega)

@[simp] theorem jensenBase_val (B : Box) : (jensenBase B).val = G3P.jensenBase B := by
  simp [jensenBase, G3P.jensenBase]

@[simp] theorem jensenShift_val (B : Box) : (jensenShift B).val = G3P.jensenShift B := by
  simp [jensenShift, G3P.jensenShift]

@[simp] theorem coefficient_val (h : ℚ) : (coefficient h).val = G3S.coefficient h := by
  simp [coefficient, G3S.coefficient, div_eq_mul_inv]

@[simp] theorem muBounds_val (B : Box) (w : RowWitness) :
    (muBounds B w).val = G3P.muBounds B w := by
  by_cases hlo : B.lo 1 < 3/20 <;> by_cases hhi : B.hi 1 < 3/20 <;>
    simp [muBounds, G3P.muBounds, G3S.weightLower, G3S.weightUpper, hlo, hhi, RatK.lt_eq]

@[simp] theorem jensenValue_val (B : Box) (w : JensenWitness) :
    (jensenValue B w).val = w.value B := by
  cases w <;> simp [jensenValue, JensenWitness.value, div_eq_mul_inv]

theorem cross_eq (x y : RatK) (m n : Nat) : cross x y m n = G3Power.crossLE x.val y.val m n := by
  simp only [cross, RatK.crossLE_eq, RatK.val_reduce]

theorem tightLower_eq (x : RatK) (n : Nat) : tightLower x n = G3Power.tightLower x.val (units n) := by
  by_cases h : |x.val| ≤ 1 <;>
    simp [tightLower, G3Power.tightLower, RatK.le_eq, cross_eq, h]

theorem tightUpper_eq (x : RatK) (n : Nat) : tightUpper x n = G3Power.tightUpper x.val (units n) := by
  by_cases h : |x.val| ≤ 1 <;>
    simp [tightUpper, G3Power.tightUpper, RatK.le_eq, cross_eq, h]

theorem tightCurve_eq (x : RatK) (n : Nat) : tightCurve x n = G3Power.tightCurve x.val (units n) := by
  by_cases h : x.val ≤ 1 <;>
    simp [tightCurve, G3Power.tightCurve, RatK.le_eq, cross_eq, h, one_div]

theorem predLower_eq (x : RatK) (n : Nat) : predLower x n = G3P.predLower x.val (units n) := by
  by_cases h : x.val ≤ 1 <;> simp [predLower, G3P.predLower, RatK.le_eq, cross_eq, h]

theorem predUpper_eq (x : RatK) (n : Nat) : predUpper x n = G3P.predUpper x.val (units n) := by
  by_cases h : x.val ≤ 1 <;> simp [predUpper, G3P.predUpper, RatK.le_eq, cross_eq, h]

theorem jensenOK_eq (B : Box) (w : JensenWitness) : jensenOK B w = w.ok B := by
  cases w <;> simp [jensenOK, JensenWitness.ok, tightLower_eq, tightUpper_eq]

@[simp] theorem slopeGain_val (w : MidpointWitness) : (slopeGain w).val = G3P.slopeGain w := by
  simp [slopeGain, G3P.slopeGain]

@[simp] theorem slopeLoss_val (w : MidpointWitness) : (slopeLoss w).val = G3P.slopeLoss w := by
  simp [slopeLoss, G3P.slopeLoss, div_eq_mul_inv]

theorem midpointOK_eq (B : Box) (b : Bool) (w : MidpointWitness) :
    midpointOK B b w = G3P.midpointOK B b w := by
  apply Bool.eq_iff_iff.mpr
  simp only [midpointOK, G3P.midpointOK, RatK.lt_eq, RatK.le_eq,
    Bool.and_eq_true, decide_eq_true_eq, tightLower_eq, tightUpper_eq,
    predLower_eq, predUpper_eq, tightCurve_eq]
  simp [div_eq_mul_inv, and_assoc]

@[simp] theorem midpointValue_val (B : Box) (b : Bool) (w : MidpointWitness) :
    (midpointValue B b w).val = G3P.midpointValue B b w := by
  simp [midpointValue, G3P.midpointValue, div_eq_mul_inv]

theorem farOK_eq (B : Box) (b : Bool) (w : FarFactor) : farOK B b w = w.ok B b := by
  cases w with
  | universal => rfl
  | midpoint w => exact midpointOK_eq B b w
  | secant p q r s =>
    apply Bool.eq_iff_iff.mpr
    simp only [farOK, FarFactor.ok, RatK.lt_eq, Bool.and_eq_true, decide_eq_true_eq,
      tightLower_eq, tightUpper_eq]
    simp

@[simp] theorem farValue_val (B : Box) (b : Bool) (w : FarFactor) :
    (farValue B b w).val = w.value B b := by
  cases w <;> simp [farValue, FarFactor.value, div_eq_mul_inv]

theorem farWitnessOK_eq {c : PowerCache} (hc : c.valid = true)
    (B : Box) (b : Bool) (w : FarWitness) : farWitnessOK c B b w = w.ok B b := by
  cases w with
  | chord f l r => simp only [farWitnessOK, FarWitness.ok, farOK_eq, PowerCache.upperCheck_eq hc]
  | variance n =>
    apply Bool.eq_iff_iff.mpr
    simp only [farWitnessOK, FarWitness.ok, RatK.lt_eq, Bool.and_eq_true, decide_eq_true_eq,
      tightCurve_eq]
    simp

theorem farTilesOK_eq (t : FarTiles) (h a : RatBounds) (cap : ℚ) :
    farTilesOK h a cap t = t.ok h a cap := by
  induction t generalizing h a with
  | leaf f =>
    apply Bool.eq_iff_iff.mpr
    simp only [farTilesOK, unitBoxK_eq, FarTiles.ok, farOK_eq, RatK.le_eq, Bool.and_eq_true,
      decide_eq_true_eq]
    simp
  | height m l r hl hr => simp only [farTilesOK, FarTiles.ok, hl, hr]
  | ratio m l r hl hr => simp only [farTilesOK, FarTiles.ok, hl, hr]

@[simp] theorem varianceCost_val (B : Box) (w : RowWitness) (n : Nat) :
    (varianceCost B w n).val = G3P.varianceCost B w n := by
  simp [varianceCost, G3P.varianceCost, mulPoint_eq, mulNonneg_eq]

theorem chordCosts_val (B : Box) (b : Bool) (w : RowWitness) :
    ((chordCosts B b w).1.val, (chordCosts B b w).2.val) = G3P.chordCosts B b w := by
  cases hf : w.far <;> simp [chordCosts, G3P.chordCosts, hf]

theorem preparedNear_eq (B : Box) (w : RowWitness) : preparedNear B w = PreparedNear.fromBox B w := by
  simp only [preparedNear, PreparedNear.fromBox, boundsOfK_eq, ratOfK_eq, kBounds_val, muBounds_val,
    jensenValue_val]

theorem nearRaw_eq (B : Box) (b : Bool) (w : RowWitness) : nearRaw B b w = nearTermsRaw B b w := by
  rw [nearRaw, preparedNear_eq, nearRawPrepared_fromBox]

theorem rowQuad_eq (B : Box) (b : Bool) (w : RowWitness) : rowQuad B b w = rowQuadRaw B b w := by
  have h0 := congrArg Prod.fst (chordCosts_val B b w)
  have h1 := congrArg Prod.snd (chordCosts_val B b w)
  change (chordCosts B b w).1.val = (G3P.chordCosts B b w).1 at h0
  change (chordCosts B b w).2.val = (G3P.chordCosts B b w).2 at h1
  cases hf : w.far <;>
    simp only [rowQuad, rowQuadRaw, hf, nearRaw_eq, ratOfK_eq, hi_val, varianceCost_val, h0, h1]

theorem tiledQuad_eq (w : TiledRow) (B : Box) (b : Bool) : tiledQuad w B b = w.quadRaw B b := by
  simp only [tiledQuad, TiledRow.quadRaw, nearRaw_eq, ratOfK_eq, unit_val, hi_val, muBounds_val]

theorem domainOK_eq (B : Box) : domainOK B = decide (Domain B) := by
  apply Bool.eq_iff_iff.mpr
  simp only [domainOK, RatK.lt_eq, RatK.le_eq, Bool.and_eq_true, decide_eq_true_eq]
  simp [Domain, bounds, and_assoc]

end

end HlawkaSchatten.BelowExponent.G3P.Geometry
