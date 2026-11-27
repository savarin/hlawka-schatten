/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import HlawkaSchatten.BelowExponent.FacetArchive.NearChecker

/-! Exact integer numerators for the F-slab near-equality checks. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FSlabNearInteger

open FacetNumeric

def coeffDen : Nat := 322901021586675
def qLoNum : Int := 511785980078730
def qHiNum : Int := 511786011202725
def c2LoNum : Int := 149687779135809
def c2HiNum : Int := 149687812904175
def c3LoNum : Int := 20708680424425
def c3HiNum : Int := 20708689905540

theorem coeffDen_pos : 0 < coeffDen := by decide

theorem qLo_eq : nearQLo = (qLoNum : ℚ) / coeffDen := by
  norm_num [nearQLo, qLoNum, coeffDen]

theorem qHi_eq : nearQHi = (qHiNum : ℚ) / coeffDen := by
  norm_num [nearQHi, qHiNum, coeffDen]

theorem c2Lo_eq : nearC₂lo = (c2LoNum : ℚ) / coeffDen := by
  norm_num [nearC₂lo, nearQLo, c2LoNum, coeffDen]

theorem c2Hi_eq : nearC₂hi = (c2HiNum : ℚ) / coeffDen := by
  norm_num [nearC₂hi, nearQHi, c2HiNum, coeffDen]

theorem c3Lo_eq : nearC₃lo = (c3LoNum : ℚ) / coeffDen := by
  norm_num [nearC₃lo, nearQLo, nearQHi, c3LoNum, coeffDen]

theorem c3Hi_eq : nearC₃hi = (c3HiNum : ℚ) / coeffDen := by
  norm_num [nearC₃hi, nearQLo, nearQHi, c3HiNum, coeffDen]

def upperNum (D w : Nat) : Int :=
  let n : Int := (w : Int) - D
  let q := if w ≤ D then qLoNum else qHiNum
  let c := if w ≤ D then c3HiNum else c3LoNum
  (coeffDen : Int)*D^2*w^2 + q*n*D*w^2 + c2HiNum*n^2*w^2 - c*n^3*D

theorem upperNum_spec (D w : Nat) (hD : 0 < D) (hw : 0 < w) :
    nearUpper ((w : ℚ)/D - 1) = (upperNum D w : ℚ) / ((coeffDen : ℚ)*D^2*w^2) := by
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD
  have hwq : (0 : ℚ) < w := by exact_mod_cast hw
  have hC : (coeffDen : ℚ) ≠ 0 := by exact_mod_cast coeffDen_pos.ne'
  have hs : (w : ℚ)/D - 1 ≤ 0 ↔ w ≤ D := by
    rw [sub_nonpos, div_le_iff₀ hDq]
    norm_cast
    simp
  by_cases h : w ≤ D
  · rw [nearUpper, ite_eq_left (hs.mpr h), qLo_eq, c2Hi_eq, c3Hi_eq]
    rw [show 1 + ((w : ℚ)/D - 1) = (w : ℚ)/D by ring]
    simp only [upperNum, ite_eq_left h]
    push_cast
    field_simp [hDq.ne', hwq.ne', hC]
    ring
  · rw [nearUpper, ite_eq_right (fun hh => h (hs.mp hh)), qHi_eq, c2Hi_eq, c3Lo_eq]
    rw [show 1 + ((w : ℚ)/D - 1) = (w : ℚ)/D by ring]
    simp only [upperNum, ite_eq_right h]
    push_cast
    field_simp [hDq.ne', hwq.ne', hC]

def tangentNum (R : Int) (S M Da : Nat) : Int :=
  (coeffDen : Int)*S^3*Da - c2LoNum*R^2*S*Da - 2*c3LoNum*R^3*Da +
    (-qHiNum*S^2 + 2*c2LoNum*R*S + 3*c3LoNum*R^2)*S*((Da : Int)-M)

theorem tangentNum_spec (R : Int) (S M Da : Nat) (hS : 0 < S) (hDa : 0 < Da) :
    nearIntercept ((R : ℚ)/S) - nearSlope ((R : ℚ)/S)*((M : ℚ)/Da) =
      (tangentNum R S M Da : ℚ) / ((coeffDen : ℚ)*S^3*Da) := by
  have hSq : (S : ℚ) ≠ 0 := by exact_mod_cast hS.ne'
  have hDq : (Da : ℚ) ≠ 0 := by exact_mod_cast hDa.ne'
  have hC : (coeffDen : ℚ) ≠ 0 := by exact_mod_cast coeffDen_pos.ne'
  simp only [nearIntercept, nearSlope, qHi_eq, c2Lo_eq, c3Lo_eq]
  unfold tangentNum
  push_cast
  field_simp
  ring

def sumAux (D : Nat) : List (Nat × Nat) → Int × Nat → Int × Nat
  | [], acc => acc
  | (p,w)::tail, (n,d) =>
    sumAux D tail (n*(w : Int)^2 + (p : Int)*upperNum D w*d, d*w^2)

def upperSum (D : Nat) (xs : List (Nat × Nat)) : Int × Nat := sumAux D xs (0,1)

theorem sumAux_den_pos (D : Nat) (xs : List (Nat × Nat)) (n : Int) (d : Nat)
    (hd : 0 < d) (hvalid : ∀ x ∈ xs, 0 < x.2) : 0 < (sumAux D xs (n,d)).2 := by
  induction xs generalizing n d with
  | nil => exact hd
  | cons head tail ih =>
    obtain ⟨p,w⟩ := head
    have hw := hvalid (p,w) (by simp)
    have ht : ∀ x ∈ tail, 0 < x.2 := fun x hx => hvalid x (by simp [hx])
    exact ih _ _ (Nat.mul_pos hd (pow_pos hw 2)) ht

theorem sumAux_spec (D : Nat) (hD : 0 < D) (xs : List (Nat × Nat)) (n : Int) (d : Nat)
    (hd : 0 < d) (hvalid : ∀ x ∈ xs, 0 < x.2) :
    ((sumAux D xs (n,d)).1 : ℚ) / ((sumAux D xs (n,d)).2 * (coeffDen : ℚ)*D^2) =
      (n : ℚ) / ((d : ℚ)*coeffDen*D^2) +
        (xs.map fun x => (x.1 : ℚ)*nearUpper ((x.2 : ℚ)/D-1)).sum := by
  induction xs generalizing n d with
  | nil => simp [sumAux]
  | cons head tail ih =>
    obtain ⟨p,w⟩ := head
    have hw := hvalid (p,w) (by simp)
    have ht : ∀ x ∈ tail, 0 < x.2 := fun x hx => hvalid x (by simp [hx])
    have hnext := ih (n*(w : Int)^2 + (p : Int)*upperNum D w*d) (d*w^2)
      (Nat.mul_pos hd (pow_pos hw 2)) ht
    simp only [sumAux]
    rw [hnext]
    simp only [List.map_cons, List.sum_cons]
    rw [upperNum_spec D w hD hw]
    have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
    have hwq : (w : ℚ) ≠ 0 := by exact_mod_cast hw.ne'
    have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
    have hC : (coeffDen : ℚ) ≠ 0 := by exact_mod_cast coeffDen_pos.ne'
    push_cast
    field_simp
    ring

theorem upperSum_spec (D : Nat) (hD : 0 < D) (xs : List (Nat × Nat))
    (hvalid : ∀ x ∈ xs, 0 < x.2) :
    ((upperSum D xs).1 : ℚ) / ((upperSum D xs).2 * (coeffDen : ℚ)*D^2) =
      (xs.map fun x => (x.1 : ℚ)*nearUpper ((x.2 : ℚ)/D-1)).sum := by
  simpa [upperSum] using sumAux_spec D hD xs 0 1 (by decide) hvalid

def inputNum (Da g0 ga gb ma mb : Nat) (r s : ℚ) : Int :=
  2*((g0 : Int)*coeffDen*Da*r.den^3*s.den^3 +
    (ga : Int)*tangentNum r.num r.den ma Da*s.den^3 +
    (gb : Int)*tangentNum s.num s.den mb Da*r.den^3)

theorem inputNum_spec (Da g0 ga gb ma mb : Nat) (hDa : 0 < Da) (r s : ℚ) :
    2*((g0 : ℚ) + ga*(nearIntercept r-nearSlope r*((ma : ℚ)/Da)) +
      gb*(nearIntercept s-nearSlope s*((mb : ℚ)/Da))) =
    (inputNum Da g0 ga gb ma mb r s : ℚ) /
      ((coeffDen : ℚ)*Da*r.den^3*s.den^3) := by
  have hr := tangentNum_spec r.num r.den ma Da r.den_pos hDa
  have hs := tangentNum_spec s.num s.den mb Da s.den_pos hDa
  simp only [Rat.num_div_den] at hr hs
  rw [hr, hs]
  unfold inputNum
  have hDq : (Da : ℚ) ≠ 0 := by exact_mod_cast hDa.ne'
  have hrq : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_pos.ne'
  have hsq : (s.den : ℚ) ≠ 0 := by exact_mod_cast s.den_pos.ne'
  have hC : (coeffDen : ℚ) ≠ 0 := by exact_mod_cast coeffDen_pos.ne'
  push_cast
  field_simp

def groupOK (D Da g0 ga gb ma mb : Nat) (r s : ℚ) (xs : List (Nat × Nat)) : Bool :=
  xs.all (fun x => decide (0 < x.2)) &&
    let v := upperSum D xs
    decide (v.1*Da*r.den^3*s.den^3 ≤ inputNum Da g0 ga gb ma mb r s*v.2*D^2)

theorem groupOK_spec (D Da g0 ga gb ma mb : Nat) (hD : 0 < D) (hDa : 0 < Da)
    (r s : ℚ) (xs : List (Nat × Nat)) :
    groupOK D Da g0 ga gb ma mb r s xs =
      (xs.all (fun x => decide (0 < x.2)) &&
        decide ((xs.map fun x => (x.1 : ℚ)*nearUpper ((x.2 : ℚ)/D-1)).sum ≤
          2*((g0 : ℚ) + ga*(nearIntercept r-nearSlope r*((ma : ℚ)/Da)) +
            gb*(nearIntercept s-nearSlope s*((mb : ℚ)/Da))))) := by
  by_cases hvalid : xs.all (fun x => decide (0 < x.2)) = true
  · have hv : ∀ x ∈ xs, 0 < x.2 := by
      intro x hx
      exact of_decide_eq_true (List.all_eq_true.mp hvalid x hx)
    have hden : 0 < (upperSum D xs).2 :=
      sumAux_den_pos D xs 0 1 (by decide) hv
    have hOut : (0 : ℚ) < (upperSum D xs).2 * (coeffDen : ℚ)*D^2 := by
      have : (0 : ℚ) < (upperSum D xs).2 := by exact_mod_cast hden
      have : (0 : ℚ) < D := by exact_mod_cast hD
      have : (0 : ℚ) < coeffDen := by exact_mod_cast coeffDen_pos
      positivity
    have hIn : (0 : ℚ) < (coeffDen : ℚ)*Da*r.den^3*s.den^3 := by
      have : (0 : ℚ) < coeffDen := by exact_mod_cast coeffDen_pos
      have : (0 : ℚ) < Da := by exact_mod_cast hDa
      have : (0 : ℚ) < r.den := by exact_mod_cast r.den_pos
      have : (0 : ℚ) < s.den := by exact_mod_cast s.den_pos
      positivity
    simp only [groupOK, hvalid, Bool.true_and, decide_eq_decide]
    rw [← upperSum_spec D hD xs hv, inputNum_spec Da g0 ga gb ma mb hDa r s]
    rw [div_le_div_iff₀ hOut hIn]
    rw [← Int.cast_le (R := ℚ)]
    push_cast
    have hC : (0 : ℚ) < coeffDen := by exact_mod_cast coeffDen_pos
    convert (mul_le_mul_iff_left₀ hC (b :=
      ((upperSum D xs).1 : ℚ)*Da*r.den^3*s.den^3) (c :=
      (inputNum Da g0 ga gb ma mb r s : ℚ)*(upperSum D xs).2*D^2)).symm using 1
    ring_nf
  · have hf : xs.all (fun x => decide (0 < x.2)) = false := Bool.eq_false_iff.mpr hvalid
    simp only [groupOK, hf, Bool.false_and]

end HlawkaSchatten.BelowExponent.FSlabNearInteger
