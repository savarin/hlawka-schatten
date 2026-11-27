/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.OuterRowCheck
public import HlawkaSchatten.BelowExponent.Vertex.CornerGrid
public import HlawkaSchatten.BelowExponent.Vertex.CornerCoefficientBounds

/-! Soundness of the shared fixed-point endpoint comparisons on the outer row charts. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

noncomputable section

theorem outerExponent_mem : outerExponent.Contains criticalQ := by
  apply DyadicBounds.ofRat_mem
  simpa [RatBounds.Contains] using And.intro criticalQ_bracket.1.le criticalQ_bracket.2.le

structure OuterAxisBounds.EnclosesSpan (A : OuterAxisBounds) (U : RatBounds) (e : Bool) : Prop where
  absChord : A.absChord.Contains (|(outerEndpoint U e : ℝ)|^criticalQ)
  absTangent : A.absTangent.Contains
    (|(outerSpanMidpoint U : ℝ)|^criticalQ +
      criticalQ*((outerEndpoint U e : ℝ)-outerSpanMidpoint U)*signedPower criticalQ (outerSpanMidpoint U))
  signedChord : A.signedChord.Contains (signedPower criticalQ (outerEndpoint U e))
  signedTangent : A.signedTangent.Contains
    (signedPower criticalQ (outerSpanMidpoint U) +
      (criticalQ-1)*|(outerSpanMidpoint U : ℝ)|^(criticalQ-2)*((outerEndpoint U e : ℝ)-outerSpanMidpoint U))

theorem outerSpanAxisBounds_encloses (U : RatBounds) (e : Bool)
    {endAbs endSigned midAbs midSigned midSlope : DyadicBounds}
    (he : endAbs.Contains (|(outerEndpoint U e : ℝ)|^criticalQ))
    (hes : endSigned.Contains (signedPower criticalQ (outerEndpoint U e)))
    (hm : midAbs.Contains (|(outerSpanMidpoint U : ℝ)|^criticalQ))
    (hms : midSigned.Contains (signedPower criticalQ (outerSpanMidpoint U)))
    (hr : midSlope.Contains (|(outerSpanMidpoint U : ℝ)|^(criticalQ-2))) :
    (outerSpanAxisBounds U e endAbs endSigned midAbs midSigned midSlope).EnclosesSpan U e := by
  have hd := DyadicBounds.point_mem (outerEndpoint U e - outerSpanMidpoint U)
  rw [Rat.cast_sub] at hd
  have h₁ := DyadicBounds.point_mem 1
  rw [Rat.cast_one] at h₁
  exact ⟨he, hm.add ((outerExponent_mem.mul hd).mul hms), hes,
    hms.add (((outerExponent_mem.sub h₁).mul hr).mul hd)⟩

abbrev OuterAxisBounds.Encloses (A : OuterAxisBounds) (i : Fin 34) (e : Bool) :=
  A.EnclosesSpan (outerInterval i) e

theorem outerAxisBounds_encloses (i : Fin 34) (e : Bool)
    {endAbs endSigned midAbs midSigned midSlope : DyadicBounds}
    (he : endAbs.Contains (|(outerEndpoint (outerInterval i) e : ℝ)|^criticalQ))
    (hes : endSigned.Contains (signedPower criticalQ (outerEndpoint (outerInterval i) e)))
    (hm : midAbs.Contains (|(outerMidpoint i : ℝ)|^criticalQ))
    (hms : midSigned.Contains (signedPower criticalQ (outerMidpoint i)))
    (hr : midSlope.Contains (|(outerMidpoint i : ℝ)|^(criticalQ-2))) :
    (outerAxisBounds i e endAbs endSigned midAbs midSigned midSlope).Encloses i e :=
  outerSpanAxisBounds_encloses (outerInterval i) e he hes hm hms hr

private theorem realAxis_eq {q lo hi : ℝ} (hq : 1 < q) (hw : lo < hi)
    (hs : 0 ≤ lo ∨ hi ≤ 0) (d c : ℝ) (e : Bool) :
    let m := (lo+hi)/2
    let x := chooseCorner e lo hi
    cornerAxisMinorant q d c lo hi e =
      d*(if 0 ≤ d then |m|^q + q*(x-m)*signedPower q m else |x|^q) +
      c*(if (if 0 ≤ lo then c else -c) < 0 then
        signedPower q m + (q-1)*|m|^(q-2)*(x-m) else signedPower q x) := by
  dsimp only
  unfold cornerAxisMinorant
  congr 1
  · unfold cornerAbsMinorant
    split <;> rfl
  · have hx₀ : lo ≤ chooseCorner e lo hi := by cases e <;> simp [chooseCorner, hw.le]
    have hx₁ : chooseCorner e lo hi ≤ hi := by cases e <;> simp [chooseCorner, hw.le]
    have hr : q-1-1 = q-2 := by ring
    by_cases hp : 0 ≤ lo
    · have hm : 0 ≤ (lo+hi)/2 := by linarith
      have hx := hp.trans hx₀
      simp only [cornerSignedMinorant, ite_eq_left hp, concavePowerMinorant, signedPower,
        ite_eq_left hm, ite_eq_left hx, abs_of_nonneg hm, abs_of_nonneg hx, hr]
      split <;> rfl
    · have hn := hs.resolve_left hp
      have hm : (lo+hi)/2 ≤ 0 := by linarith
      have hx := hx₁.trans hn
      have hmid : -(lo+hi)/2 = -((lo+hi)/2) := by ring
      simp only [cornerSignedMinorant, ite_eq_right hp, concavePowerMinorant, signedPower_eq_neg_rpow hq hm,
        signedPower_eq_neg_rpow hq hx, abs_of_nonpos hm, hmid, hr]
      split <;> ring

private theorem decode_nonneg_iff (n : ℤ) : 0 ≤ DyadicBounds.decode n ↔ 0 ≤ n := by
  have h : (0 : ℝ) < DyadicBounds.units := by norm_num [DyadicBounds.units]
  simp [DyadicBounds.decode, le_div_iff₀ h]

private theorem decode_lt_zero_iff (n : ℤ) : DyadicBounds.decode n < 0 ↔ n < 0 := by
  simpa only [not_le] using not_congr (decode_nonneg_iff n)

private theorem decode_neg (n : ℤ) : DyadicBounds.decode (-n) = -DyadicBounds.decode n := by
  simp [DyadicBounds.decode, neg_div]

private theorem axis_signed_sign (lo : ℚ) (c : ℤ) :
    ((if (0 : ℝ) ≤ lo then DyadicBounds.decode c else -DyadicBounds.decode c) < 0) ↔
    ((if decide (0 ≤ lo) then c else -c) < 0) := by
  by_cases h : 0 ≤ lo
  · have h' : (0 : ℝ) ≤ lo := by exact_mod_cast h
    simpa [h, h'] using decode_lt_zero_iff c
  · have h' : ¬ (0 : ℝ) ≤ lo := by exact_mod_cast h
    simpa only [h, h', decide_false, Bool.false_eq_true, ite_false, decode_neg] using decode_lt_zero_iff (-c)

theorem OuterAxisBounds.eval_mem_span {A : OuterAxisBounds} {U : RatBounds} {e : Bool}
    (hA : A.EnclosesSpan U e) (hwidth : U.lo < U.hi) (hsign : 0 ≤ U.lo ∨ U.hi ≤ 0) (d c : ℤ) :
    (A.eval (decide (0 ≤ U.lo)) d c).Contains
      (cornerAxisMinorant criticalQ (DyadicBounds.decode d) (DyadicBounds.decode c)
        U.lo U.hi e) := by
  have hw : (U.lo : ℝ) < U.hi := by exact_mod_cast hwidth
  have hs : (0 : ℝ) ≤ U.lo ∨ (U.hi : ℝ) ≤ 0 := by exact_mod_cast hsign
  have hm : (outerSpanMidpoint U : ℝ) = (U.lo + (U.hi : ℝ))/2 := by
    simp [outerSpanMidpoint]
  have hx : (outerEndpoint U e : ℝ) =
      chooseCorner e (U.lo : ℝ) (U.hi : ℝ) := by cases e <;> rfl
  have hq : 1 < criticalQ := by linarith only [criticalQ_bracket.1]
  rw [realAxis_eq hq hw hs, ← hm, ← hx]
  unfold OuterAxisBounds.eval
  apply DyadicBounds.Contains.add
  · apply (DyadicBounds.numerator_mem d).mul
    simp only [decode_nonneg_iff]
    split
    · exact hA.absTangent
    · exact hA.absChord
  · apply (DyadicBounds.numerator_mem c).mul
    simp only [axis_signed_sign]
    by_cases h : (if decide (0 ≤ U.lo) then c else -c) < 0
    · simpa only [ite_eq_left h] using hA.signedTangent
    · simpa only [ite_eq_right h] using hA.signedChord

theorem OuterAxisBounds.eval_mem {A : OuterAxisBounds} {i : Fin 34} {e : Bool}
    (hA : A.Encloses i e) (d c : ℤ) :
    (A.eval (decide (0 ≤ (outerInterval i).lo)) d c).Contains
      (cornerAxisMinorant criticalQ (DyadicBounds.decode d) (DyadicBounds.decode c)
        (outerInterval i).lo (outerInterval i).hi e) := by
  have hg : ∀ k : Fin 34, (outerInterval k).lo < (outerInterval k).hi ∧
      (0 ≤ (outerInterval k).lo ∨ (outerInterval k).hi ≤ 0) := by decide +kernel
  exact OuterAxisBounds.eval_mem_span hA (hg i).1 (hg i).2 d c

structure OuterPointBounds.Encloses (P : OuterPointBounds) (D : CornerRowCoefficients) : Prop where
  diagonal : ∀ j, (P.diagonal.get j).Contains (D.diagonal j)
  coupling : ∀ i j, ((P.coupling.get i).get j).Contains (D.coupling i j)
  argument : ∀ j, (P.argument.get j : ℝ) = D.argument j

theorem OuterPointBounds.atPoint_encloses (a b η : ℚ) (margins : Vector ℚ 3)
    (roots : Fin 3 → RatBounds) (hroot : (outerParameterCell a b η).rootsOK roots = true) :
    (atPoint a b η margins roots).Encloses (cornerRowCoefficients margins.get a b η) := by
  have hc : (outerParameterCell a b η).Contains a b η :=
    ⟨RatBounds.point_mem _, RatBounds.point_mem _, RatBounds.point_mem _⟩
  obtain ⟨hD, _, hH⟩ := ParameterCell.coefficientValues_mem hc hc hroot
  constructor
  · intro j
    simpa only [atPoint, vector_get_ofFn, cornerRowCoefficients] using
      ((hD j).sub (DyadicBounds.point_mem (margins.get j))).add (outerExponent_mem.mul (hH j j))
  · intro i j
    simpa only [atPoint, vector_get_ofFn, cornerRowCoefficients] using outerExponent_mem.mul (hH i j)
  · intro j
    fin_cases j <;> simp [atPoint, vector_get_ofFn, cornerRowCoefficients, parameterDirection]

theorem OuterPointBounds.Encloses.linearCoeff_mem {P : OuterPointBounds} {D : CornerRowCoefficients}
    (hp : P.Encloses D) (k cross axis : Fin 3) (x : ℚ) :
    (P.linearCoeff k cross axis x).Contains (D.coupling k axis + D.coupling cross axis * (x : ℝ)) :=
  (hp.coupling k axis).add ((hp.coupling cross axis).mul (DyadicBounds.point_mem x))

theorem OuterPointBounds.Encloses.remainderLinear_mem {P : OuterPointBounds} {D : CornerRowCoefficients}
    (hp : P.Encloses D) (k m n : Fin 3) (x y : ℚ) : (P.remainderLinear k m n x y).Contains
      (D.diagonal k + D.coupling m k * (x : ℝ) + D.coupling n k * (y : ℝ)) :=
  ((hp.diagonal k).add ((hp.coupling m k).mul (DyadicBounds.point_mem x))).add
    ((hp.coupling n k).mul (DyadicBounds.point_mem y))

theorem outerSignedNumerator_bound {c : DyadicBounds} {r : ℝ} (hc : c.Contains r)
    (hok : c.ok = true) (axis : RatBounds) :
    if (0 : ℝ) ≤ axis.lo then DyadicBounds.decode (outerSignedNumerator axis c) ≤ r
    else r ≤ DyadicBounds.decode (outerSignedNumerator axis c) := by
  by_cases h : 0 ≤ axis.lo
  · have h' : (0 : ℝ) ≤ axis.lo := by exact_mod_cast h
    simpa [outerSignedNumerator, h, h'] using (hc hok).1
  · have h' : ¬ (0 : ℝ) ≤ axis.lo := by exact_mod_cast h
    simpa [outerSignedNumerator, h, h'] using (hc hok).2

private theorem spanEndpoint_flags {P : OuterPointBounds} {k m n : Fin 3} {U V : RatBounds}
    {x y : Bool} {Au Av : Bool → OuterAxisBounds} {chord : ℚ → ℚ}
    (h : P.spanEndpointOK k m n U V x y Au Av chord = true) :
    let u := outerEndpoint U x
    let v := outerEndpoint V y
    (P.diagonal.get m).ok = true ∧ (P.diagonal.get n).ok = true ∧
      (P.linearCoeff k n m v).ok = true ∧ (P.linearCoeff k m n u).ok = true ∧
      |P.argumentAt k m n u v| ≤ 4 ∧ (P.spanEndpointBound k m n U V x y Au Av chord).lowerOK 0 = true := by
  simpa only [OuterPointBounds.spanEndpointOK, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using h

private theorem span_of_four_checks {margins : Fin 3 → ℚ} {a b η : ℝ} {P : OuterPointBounds}
    (hp : P.Encloses (cornerRowCoefficients margins a b η))
    (k : Fin 3) (U V : RatBounds) {Au Av : Bool → OuterAxisBounds} {chord : ℚ → ℚ}
    (hU : ∀ e, (Au e).EnclosesSpan U e) (hV : ∀ e, (Av e).EnclosesSpan V e)
    (hwU : U.lo < U.hi) (hwV : V.lo < V.hi) (hsU : 0 ≤ U.lo ∨ U.hi ≤ 0) (hsV : 0 ≤ V.lo ∨ V.hi ≤ 0)
    (hchord : ∀ r : ℚ, |r| ≤ 4 → |(r : ℝ)|^criticalQ ≤ (chord r : ℝ))
    (hc : ∀ x y, P.spanEndpointOK k (outerFaceFirst k) (outerFaceSecond k) U V x y Au Av chord = true) :
    ∀ ⦃u v : ℝ⦄, U.Contains u → V.Contains v → CornerMarginAt margins (outerFaceRow k u v) a b η := by
  let m := outerFaceFirst k
  let n := outerFaceSecond k
  let u := outerEndpoint U
  let v := outerEndpoint V
  let D := cornerRowCoefficients margins a b η
  let du := (P.diagonal.get m).lo
  let dv := (P.diagonal.get n).lo
  let cu := fun y => outerSignedNumerator U (P.linearCoeff k n m (v y))
  let cv := fun x => outerSignedNumerator V (P.linearCoeff k m n (u x))
  have castEnd (r : RatBounds) (z : Bool) :
      (outerEndpoint r z : ℝ) = chooseCorner z (r.lo : ℝ) (r.hi : ℝ) := by cases z <;> rfl
  intro u₀ v₀ hu hv
  apply cornerMargin_of_rectangle (du := DyadicBounds.decode du) (dv := DyadicBounds.decode dv)
    (cu := fun y => DyadicBounds.decode (cu y)) (cv := fun x => DyadicBounds.decode (cv x))
    k hu hv (by exact_mod_cast hwU) (by exact_mod_cast hwV) (by exact_mod_cast hsU) (by exact_mod_cast hsV)
  · exact (hp.diagonal m (spanEndpoint_flags (hc false false)).1).1
  · exact (hp.diagonal n (spanEndpoint_flags (hc false false)).2.1).1
  · intro y
    rw [← castEnd]
    exact outerSignedNumerator_bound (hp.linearCoeff_mem k n m (v y))
      (spanEndpoint_flags (hc false y)).2.2.1 U
  · intro x
    rw [← castEnd]
    exact outerSignedNumerator_bound (hp.linearCoeff_mem k m n (u x))
      (spanEndpoint_flags (hc x false)).2.2.2.1 V
  · intro x y
    rw [← castEnd, ← castEnd]
    let r := P.argumentAt k m n (u x) (v y)
    have hr : (r : ℝ) = D.argument k + D.argument m*(u x : ℝ) + D.argument n*(v y : ℝ) := by
      simp only [r, OuterPointBounds.argumentAt, Rat.cast_add, Rat.cast_mul, hp.argument, D]
    have hpow := hchord r (spanEndpoint_flags (hc x y)).2.2.2.2.1
    have hA := OuterAxisBounds.eval_mem_span (hU x) hwU hsU du (cu y)
    have hB := OuterAxisBounds.eval_mem_span (hV y) hwV hsV dv (cv x)
    have hlinear := (hp.remainderLinear_mem k m n (u x) (v y)).sub (DyadicBounds.point_mem (chord r))
    have hsum := (hlinear.add hA).add hB
    have hval := hsum.lower_le (spanEndpoint_flags (hc x y)).2.2.2.2.2
    rw [Rat.cast_zero] at hval
    apply hval.trans
    refine add_le_add (add_le_add ?_ le_rfl) le_rfl
    unfold CornerRowCoefficients.remainder
    exact sub_le_sub le_rfl (by simpa only [hr] using hpow)


theorem outerSpan_of_checks {margins : Fin 3 → ℚ} {a b η : ℝ} {P : OuterPointBounds}
    (hp : P.Encloses (cornerRowCoefficients margins a b η)) (k : Fin 3) (U V : RatBounds)
    {Au Av : Bool → OuterAxisBounds} {chord : ℚ → ℚ}
    (hU : ∀ e, (Au e).EnclosesSpan U e) (hV : ∀ e, (Av e).EnclosesSpan V e)
    (hchord : ∀ r : ℚ, |r| ≤ 4 → |(r : ℝ)|^criticalQ ≤ (chord r : ℝ))
    (hc : P.spanOK k U V Au Av chord = true) :
    ∀ ⦃u v : ℝ⦄, U.Contains u → V.Contains v → CornerMarginAt margins (outerFaceRow k u v) a b η := by
  have hk : outerTransverse k = (outerFaceFirst k, outerFaceSecond k) := by fin_cases k <;> rfl
  simp only [OuterPointBounds.spanOK, hk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hwU,hwV,hsU,hsV⟩, hxy⟩ := hc
  apply span_of_four_checks hp k U V hU hV hwU hwV hsU hsV hchord
  intro x y
  have member (e : Bool) : e ∈ [false,true] := by cases e <;> simp
  exact List.all_eq_true.mp (List.all_eq_true.mp hxy x (member x)) y (member y)

theorem outerRectangle_of_checks {margins : Fin 3 → ℚ} {a b η : ℝ} {P : OuterPointBounds}
    (hp : P.Encloses (cornerRowCoefficients margins a b η))
    (k : Fin 3) (i j : Fin 34) {axes : Fin 34 → Bool → OuterAxisBounds} {chord : ℚ → ℚ}
    (haxes : ∀ l e, (axes l e).Encloses l e)
    (hchord : ∀ r : ℚ, |r| ≤ 4 → |(r : ℝ)|^criticalQ ≤ (chord r : ℝ))
    (hc : ∀ x y, P.endpointOK k (outerFaceFirst k) (outerFaceSecond k) i j x y axes chord = true) :
    OuterRectangleAt margins a b η k i j := by
  have hg : ∀ l : Fin 34, (outerInterval l).lo < (outerInterval l).hi ∧
      (0 ≤ (outerInterval l).lo ∨ (outerInterval l).hi ≤ 0) := by decide +kernel
  exact span_of_four_checks hp k (outerInterval i) (outerInterval j) (haxes i) (haxes j)
    (hg i).1 (hg j).1 (hg i).2 (hg j).2 hchord hc

end
end HlawkaSchatten.BelowExponent.Vertex
