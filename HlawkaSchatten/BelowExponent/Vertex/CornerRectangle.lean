/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CornerMinorants
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCertificates
import all HlawkaSchatten.BelowExponent.Interpolation
import all HlawkaSchatten.BelowExponent.VertexBox
import all HlawkaSchatten.BelowExponent.VertexFeature
import all HlawkaSchatten.BelowExponent.Vertex.CurvatureSound
import Batteries.Tactic.OpenPrivate

/-! Four lower bounds certify the exact corner margin on a closed row rectangle. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

open Set
open private abs_rpow_lerp_le from HlawkaSchatten.BelowExponent.Interpolation
open private interpolate_mem from HlawkaSchatten.BelowExponent.VertexBox
open private interpolate_exists from HlawkaSchatten.BelowExponent.Vertex.CurvatureSound
open private mul_signedPower from HlawkaSchatten.BelowExponent.VertexFeature

noncomputable section

def outerFaceFirst (k : Fin 3) : Fin 3 := ![1,0,0] k
def outerFaceSecond (k : Fin 3) : Fin 3 := ![2,2,1] k

def outerFaceRow (k : Fin 3) (u v : ℝ) : Row :=
  ![![1,u,v], ![u,1,v], ![u,v,1]] k

structure CornerRowCoefficients where
  diagonal : Row
  coupling : Fin 3 → Row
  argument : Row

/-- Diagonal and off-diagonal coefficients of the normalized gap after the margin is charged. -/
def cornerRowCoefficients (margins : Fin 3 → ℚ) (a b η : ℝ) : CornerRowCoefficients :=
  let offset i := 1 - parameterDirection a b i
  let coupling i j := criticalQ * (offset i * parameterWeight a b η j)
  ⟨fun j => parameterD a b η j - margins j + coupling j j, coupling,
    fun j => 1 + 2*η*offset j⟩

namespace CornerRowCoefficients

def firstCoeff (D : CornerRowCoefficients) (k : Fin 3) (v : ℝ) : ℝ :=
  D.coupling k (outerFaceFirst k) + D.coupling (outerFaceSecond k) (outerFaceFirst k)*v

def secondCoeff (D : CornerRowCoefficients) (k : Fin 3) (u : ℝ) : ℝ :=
  D.coupling k (outerFaceSecond k) + D.coupling (outerFaceFirst k) (outerFaceSecond k)*u

def remainder (D : CornerRowCoefficients) (q : ℝ) (k : Fin 3) (u v : ℝ) : ℝ :=
  let m := outerFaceFirst k
  let n := outerFaceSecond k
  D.diagonal k + D.coupling m k*u + D.coupling n k*v -
    |D.argument k + D.argument m*u + D.argument n*v|^q

def firstTerm (D : CornerRowCoefficients) (q : ℝ) (k : Fin 3) (u v : ℝ) : ℝ :=
  D.diagonal (outerFaceFirst k)*|u|^q + D.firstCoeff k v*signedPower q u

def secondTerm (D : CornerRowCoefficients) (q : ℝ) (k : Fin 3) (u v : ℝ) : ℝ :=
  D.diagonal (outerFaceSecond k)*|v|^q + D.secondCoeff k u*signedPower q v

end CornerRowCoefficients

theorem cornerGapOnFace_eq (margins : Fin 3 → ℚ) (a b η : ℝ) (k : Fin 3) (u v : ℝ) :
    let D := cornerRowCoefficients margins a b η
    parameterGap criticalQ (outerFaceRow k u v) a b η -
      (∑ j, (margins j : ℝ)*|outerFaceRow k u v j|^criticalQ) =
    D.remainder criticalQ k u v + D.firstTerm criticalQ k u v + D.secondTerm criticalQ k u v := by
  dsimp only
  have hq : 1 < criticalQ := by linarith only [criticalQ_bracket.1]
  have hOne : signedPower criticalQ 1 = 1 := by simp [signedPower]
  have ha : parameterArgument (outerFaceRow k u v) a b η =
      (cornerRowCoefficients margins a b η).argument k +
        (cornerRowCoefficients margins a b η).argument (outerFaceFirst k)*u +
        (cornerRowCoefficients margins a b η).argument (outerFaceSecond k)*v := by
    fin_cases k <;>
      simp [parameterArgument, argument, linearRow, outerFaceRow, outerFaceFirst, outerFaceSecond,
        cornerRowCoefficients, parameterDirection, Fin.sum_univ_three] <;>
      ring
  rw [parameterGap_eq_linear, ha]
  fin_cases k <;>
    simp [linearFeature, cornerRowCoefficients, CornerRowCoefficients.remainder,
      CornerRowCoefficients.firstTerm, CornerRowCoefficients.secondTerm,
      CornerRowCoefficients.firstCoeff, CornerRowCoefficients.secondCoeff,
      outerFaceRow, outerFaceFirst, outerFaceSecond, Fin.sum_univ_three, hOne, mul_assoc,
      mul_signedPower hq] <;>
    ring

def cornerAxisMinorant (q a c lo hi : ℝ) (i : Bool) : ℝ :=
  cornerAbsMinorant q a lo hi i + cornerSignedMinorant q c lo hi i

private theorem cornerAxisMinorant_le {q t lo hi a c A C : ℝ}
    (hq : 1 < q) (hq₂ : q ≤ 2) (ht : t ∈ Icc 0 1) (hwidth : lo < hi) (hsign : 0 ≤ lo ∨ hi ≤ 0)
    (ha : a ≤ A) (hc : if 0 ≤ lo then c ≤ C else C ≤ c) :
    interpolate t (cornerAxisMinorant q a c lo hi false) (cornerAxisMinorant q a c lo hi true) ≤
      A*|interpolate t lo hi|^q + C*signedPower q (interpolate t lo hi) := by
  have habs := (cornerAbsMinorant_le (c := a) (lo := lo) (hi := hi) hq ht).trans
    (mul_le_mul_of_nonneg_right ha (Real.rpow_nonneg (abs_nonneg _) _))
  have hpow := (cornerSignedMinorant_le (c := c) hq hq₂ hwidth hsign ht).trans
    (signedCoefficient_mul_le hq (interpolate_mem ht hwidth.le) hsign hc)
  convert add_le_add habs hpow using 1
  unfold cornerAxisMinorant interpolate
  ring

private theorem interpolate_mono {w a b x y : ℝ} (hw : w ∈ Icc 0 1) (ha : a ≤ x) (hb : b ≤ y) :
    interpolate w a b ≤ interpolate w x y :=
  add_le_add (mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr hw.2)) (mul_le_mul_of_nonneg_left hb hw.1)

private theorem affinePower_chord {q w lo hi A B C E : ℝ} (hq : 1 ≤ q) (hw : w ∈ Icc 0 1) :
    interpolate w (C+E*lo-|A+B*lo|^q) (C+E*hi-|A+B*hi|^q) ≤
      C+E*interpolate w lo hi-|A+B*interpolate w lo hi|^q := by
  have h := abs_rpow_lerp_le hq hw.1 hw.2 (A+B*lo) (A+B*hi)
  have he : A+B*interpolate w lo hi = (1-w)*(A+B*lo)+w*(A+B*hi) := by unfold interpolate; ring
  rw [he]
  unfold interpolate
  nlinarith only [h]

private theorem CornerRowCoefficients.remainder_first_chord {D : CornerRowCoefficients}
    {q w lo hi v : ℝ} (k : Fin 3) (hq : 1 ≤ q) (hw : w ∈ Icc 0 1) :
    interpolate w (D.remainder q k lo v) (D.remainder q k hi v) ≤
      D.remainder q k (interpolate w lo hi) v := by
  simpa only [CornerRowCoefficients.remainder, add_assoc, add_left_comm, add_comm] using
    (affinePower_chord (A := D.argument k + D.argument (outerFaceSecond k)*v)
      (B := D.argument (outerFaceFirst k)) (C := D.diagonal k + D.coupling (outerFaceSecond k) k*v)
      (E := D.coupling (outerFaceFirst k) k) (lo := lo) (hi := hi) hq hw)

private theorem CornerRowCoefficients.remainder_second_chord {D : CornerRowCoefficients}
    {q w lo hi u : ℝ} (k : Fin 3) (hq : 1 ≤ q) (hw : w ∈ Icc 0 1) :
    interpolate w (D.remainder q k u lo) (D.remainder q k u hi) ≤
      D.remainder q k u (interpolate w lo hi) := by
  exact affinePower_chord (A := D.argument k + D.argument (outerFaceFirst k)*u)
    (B := D.argument (outerFaceSecond k)) (C := D.diagonal k + D.coupling (outerFaceFirst k) k*u)
    (E := D.coupling (outerFaceSecond k) k) hq hw

private def interpolateRectangle (s t : ℝ) (f : Bool → Bool → ℝ) : ℝ :=
  interpolate t (interpolate s (f false false) (f true false)) (interpolate s (f false true) (f true true))

private theorem interpolateRectangle_transpose (s t : ℝ) (f : Bool → Bool → ℝ) :
    interpolateRectangle s t f = interpolateRectangle t s (fun j i => f i j) := by
  unfold interpolateRectangle interpolate
  ring

private theorem CornerRowCoefficients.rectangle_nonneg {D : CornerRowCoefficients}
    {q u v ul uh vl vh : ℝ} (k : Fin 3) (hq : 1 < q) (hq₂ : q ≤ 2)
    (hu : u ∈ Icc ul uh) (hv : v ∈ Icc vl vh)
    (hwu : ul < uh) (hwv : vl < vh) (hsu : 0 ≤ ul ∨ uh ≤ 0) (hsv : 0 ≤ vl ∨ vh ≤ 0)
    {du dv : ℝ} {cu cv : Bool → ℝ}
    (hdu : du ≤ D.diagonal (outerFaceFirst k)) (hdv : dv ≤ D.diagonal (outerFaceSecond k))
    (hcu : ∀ j, if 0 ≤ ul then cu j ≤ D.firstCoeff k (chooseCorner j vl vh)
      else D.firstCoeff k (chooseCorner j vl vh) ≤ cu j)
    (hcv : ∀ i, if 0 ≤ vl then cv i ≤ D.secondCoeff k (chooseCorner i ul uh)
      else D.secondCoeff k (chooseCorner i ul uh) ≤ cv i)
    (hcorners : ∀ i j, 0 ≤ D.remainder q k (chooseCorner i ul uh) (chooseCorner j vl vh) +
      cornerAxisMinorant q du (cu j) ul uh i + cornerAxisMinorant q dv (cv i) vl vh j) :
    0 ≤ D.remainder q k u v + D.firstTerm q k u v + D.secondTerm q k u v := by
  obtain ⟨s, hs, rfl⟩ := interpolate_exists hu
  obtain ⟨t, ht, rfl⟩ := interpolate_exists hv
  let u := interpolate s ul uh
  let v := interpolate t vl vh
  let R i j := D.remainder q k (chooseCorner i ul uh) (chooseCorner j vl vh)
  let M i j := cornerAxisMinorant q du (cu j) ul uh i
  let N i j := cornerAxisMinorant q dv (cv i) vl vh j
  have hr : interpolateRectangle s t R ≤ D.remainder q k u v := by
    have h₀ := D.remainder_first_chord (lo := ul) (hi := uh) (v := vl) k hq.le hs
    have h₁ := D.remainder_first_chord (lo := ul) (hi := uh) (v := vh) k hq.le hs
    exact (interpolate_mono ht h₀ h₁).trans (D.remainder_second_chord k hq.le ht)
  have hm : interpolateRectangle s t M ≤ D.firstTerm q k u v := by
    have h j := cornerAxisMinorant_le hq hq₂ hs hwu hsu hdu (hcu j)
    have he : interpolate t (D.firstTerm q k u vl) (D.firstTerm q k u vh) = D.firstTerm q k u v := by
      unfold CornerRowCoefficients.firstTerm CornerRowCoefficients.firstCoeff v interpolate
      ring
    rw [← he]
    exact interpolate_mono ht (h false) (h true)
  have hn : interpolateRectangle s t N ≤ D.secondTerm q k u v := by
    have h i := cornerAxisMinorant_le hq hq₂ ht hwv hsv hdv (hcv i)
    have he : interpolate s (D.secondTerm q k ul v) (D.secondTerm q k uh v) = D.secondTerm q k u v := by
      unfold CornerRowCoefficients.secondTerm CornerRowCoefficients.secondCoeff u interpolate
      ring
    rw [← he, interpolateRectangle_transpose]
    exact interpolate_mono hs (h false) (h true)
  have htest : 0 ≤ interpolateRectangle s t (fun i j => R i j + M i j + N i j) := by
    have h := interpolate_mono ht (interpolate_mono hs (hcorners false false) (hcorners true false))
      (interpolate_mono hs (hcorners false true) (hcorners true true))
    simpa [interpolateRectangle, interpolate] using h
  have hsum : interpolateRectangle s t (fun i j => R i j + M i j + N i j) =
      interpolateRectangle s t R + interpolateRectangle s t M + interpolateRectangle s t N := by
    unfold interpolateRectangle interpolate
    ring
  rw [hsum] at htest
  exact htest.trans (add_le_add (add_le_add hr hm) hn)

theorem cornerMargin_of_rectangle {margins : Fin 3 → ℚ} {a b η u v ul uh vl vh : ℝ} (k : Fin 3)
    (hu : u ∈ Icc ul uh) (hv : v ∈ Icc vl vh)
    (hwu : ul < uh) (hwv : vl < vh) (hsu : 0 ≤ ul ∨ uh ≤ 0) (hsv : 0 ≤ vl ∨ vh ≤ 0)
    {du dv : ℝ} {cu cv : Bool → ℝ} :
    let D := cornerRowCoefficients margins a b η
    du ≤ D.diagonal (outerFaceFirst k) → dv ≤ D.diagonal (outerFaceSecond k) →
    (∀ j, if 0 ≤ ul then cu j ≤ D.firstCoeff k (chooseCorner j vl vh)
      else D.firstCoeff k (chooseCorner j vl vh) ≤ cu j) →
    (∀ i, if 0 ≤ vl then cv i ≤ D.secondCoeff k (chooseCorner i ul uh)
      else D.secondCoeff k (chooseCorner i ul uh) ≤ cv i) →
    (∀ i j, 0 ≤ D.remainder criticalQ k (chooseCorner i ul uh) (chooseCorner j vl vh) +
      cornerAxisMinorant criticalQ du (cu j) ul uh i + cornerAxisMinorant criticalQ dv (cv i) vl vh j) →
    CornerMarginAt margins (outerFaceRow k u v) a b η := by
  dsimp only
  intro hdu hdv hcu hcv hcorners
  have hq : 1 < criticalQ := by linarith only [criticalQ_bracket.1]
  have hq₂ : criticalQ ≤ 2 := by linarith only [criticalQ_bracket.2]
  apply sub_nonneg.mp
  rw [cornerGapOnFace_eq]
  exact CornerRowCoefficients.rectangle_nonneg k hq hq₂ hu hv hwu hwv hsu hsv hdu hdv hcu hcv hcorners

end

end HlawkaSchatten.BelowExponent.Vertex
