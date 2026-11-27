/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FSlabRows
public import HlawkaSchatten.BelowExponent.FSlabCheck

/-! The integer F witnesses use the exact balanced profiles and weights. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FSlabCheck

open Tangent

noncomputable section

def len (P : Band) : ℝ := (lengthNum P : ℝ) / lengthDen P
def mu (P : Band) : ℝ := (P.weight : ℝ) / 100
def imbalanceAt (P : Band) (edge : Bool) : ℝ := (edgeNum P edge : ℝ) / 4

private theorem length_bounds : ∀ i : Fin 157, 0 < lengthDen ⟨i,0,false⟩ ∧
    2 * lengthNum ⟨i,0,false⟩ ≤ lengthDen ⟨i,0,false⟩ := by decide +kernel

theorem lengthDen_pos (P : Band) : 0 < lengthDen P := (length_bounds P.knot).1
theorem profileDen_pos (P : Band) : 0 < profileDen P := Nat.mul_pos (by decide) (lengthDen_pos P)
theorem commonDen_pos (P : Band) : 0 < commonDen P := Nat.mul_pos (by decide) (lengthDen_pos P)

theorem len_eq (P : Band) : len P = (fSlabKnot P.knot : ℝ) := by
  unfold len lengthNum lengthDen fSlabKnot
  split <;> push_cast <;> rfl

theorem imbalanceAt_low (P : Band) : imbalanceAt P false = if P.high then 1/4 else 0 := by
  cases h : P.high <;> norm_num [imbalanceAt,edgeNum,h]

theorem imbalanceAt_high (P : Band) : imbalanceAt P true = if P.high then 1/2 else 1/4 := by
  cases h : P.high <;> norm_num [imbalanceAt,edgeNum,h]

theorem imbalanceAt_bound (P : Band) (b : Bool) : |imbalanceAt P b| ≤ 1 := by
  cases b <;> cases h : P.high <;> norm_num [imbalanceAt,edgeNum,h]

theorem profile_eq (P : Band) (b : Bool) : vertex (profileDen P) (profile P b) =
    balancedProfile (len P) (imbalanceAt P b) (len P) := by
  have hD : (lengthDen P : ℝ) ≠ 0 := by exact_mod_cast (lengthDen_pos P).ne'
  have hl : 2*lengthNum P ≤ lengthDen P := (length_bounds P.knot).2
  have he : edgeNum P b ≤ 2 := by cases b <;> cases h : P.high <;> norm_num [edgeNum,h]
  have hm₀ : lengthNum P ≤ lengthDen P := by omega
  have hN : edgeNum P b*lengthDen P ≤ 4*(lengthDen P-lengthNum P) := by
    have h := Nat.mul_le_mul_right (lengthDen P) he
    omega
  funext i
  fin_cases i <;> simp [vertex,profile,profileDen,balancedProfile,splitProfile,len,imbalanceAt] <;>
    push_cast [Nat.cast_sub hm₀,Nat.cast_sub hN] <;> field_simp [hD] <;> ring

theorem pi_eq (P : Band) (b : Bool) (hW : P.weight ≤ 100) (j : Fin 4) :
    (((pi P b).getD j.val 0 : Nat) : ℝ) / commonDen P = balancedPi (mu P) (imbalanceAt P b) j := by
  have hD : (lengthDen P : ℝ) ≠ 0 := by exact_mod_cast (lengthDen_pos P).ne'
  have he : edgeNum P b ≤ 4 := by cases b <;> cases h : P.high <;> norm_num [edgeNum,h]
  fin_cases j <;> simp [pi,commonDen,balancedPi,mu,imbalanceAt] <;>
    push_cast [Nat.cast_sub hW,Nat.cast_sub he] <;> field_simp [hD] <;> ring

theorem gamma_eq (P : Band) (hW : P.weight ≤ 100) (j : Fin 3) :
    (((gamma P).getD j.val 0 : Nat) : ℝ) / commonDen P = balancedGamma (mu P) (len P) j := by
  have hD : (lengthDen P : ℝ) ≠ 0 := by exact_mod_cast (lengthDen_pos P).ne'
  have hl : 2*lengthNum P ≤ lengthDen P := (length_bounds P.knot).2
  have hl' : lengthNum P ≤ lengthDen P := by omega
  have hg : P.weight*(lengthDen P-lengthNum P) ≤ 100*lengthDen P :=
    Nat.mul_le_mul hW (Nat.sub_le _ _)
  fin_cases j <;> simp [gamma,commonDen,balancedGamma,mu,len] <;>
    push_cast [Nat.cast_sub hl',Nat.cast_sub hg] <;> field_simp [hD] <;> ring

end

end HlawkaSchatten.BelowExponent.FSlabCheck
