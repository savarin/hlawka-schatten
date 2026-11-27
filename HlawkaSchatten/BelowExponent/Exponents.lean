/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.ConjExponents
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-! The endpoint exponent in the mission and its dual in the scalar row certificate. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

noncomputable def criticalP : ℝ := Real.log 3 / Real.log (3/2)
noncomputable def criticalQ : ℝ := Real.log 3 / Real.log 2

theorem critical_conjugate : criticalP.HolderConjugate criticalQ := by
  have h₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h₃ : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hd : 0 < Real.log (3/2 : ℝ) := Real.log_pos (by norm_num)
  have he : Real.log (3/2 : ℝ) = Real.log 3 - Real.log 2 := Real.log_div (by norm_num) (by norm_num)
  apply Real.holderConjugate_iff.mpr
  constructor
  · exact (one_lt_div hd).2 (by linarith)
  · unfold criticalP criticalQ
    rw [inv_div, inv_div, ← add_div, he]
    rw [sub_add_cancel, div_self h₃.ne']

theorem two_rpow_criticalQ : (2 : ℝ) ^ criticalQ = 3 := by
  have h₂ : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1:ℝ) < 2)).ne'
  rw [criticalQ, Real.rpow_def_of_pos (by norm_num), mul_div_cancel₀ _ h₂, Real.exp_log (by norm_num)]

private theorem rational_lt_criticalQ (a b : ℕ) (hb : 0 < b) (h : (2:ℕ)^a < 3^b) :
    (a:ℝ) / b < criticalQ := by
  have hr : (2:ℝ)^a < 3^b := by exact_mod_cast h
  have H := Real.log_lt_log (pow_pos (by norm_num : (0:ℝ) < 2) _) hr
  rw [Real.log_pow, Real.log_pow] at H
  exact (div_lt_div_iff₀ (by exact_mod_cast hb) (Real.log_pos (by norm_num : (1:ℝ) < 2))).2
    (by linarith)

private theorem criticalQ_lt_rational (a b : ℕ) (hb : 0 < b) (h : (3:ℕ)^b < 2^a) :
    criticalQ < (a:ℝ) / b := by
  have hr : (3:ℝ)^b < 2^a := by exact_mod_cast h
  have H := Real.log_lt_log (pow_pos (by norm_num : (0:ℝ) < 3) _) hr
  rw [Real.log_pow, Real.log_pow] at H
  exact (div_lt_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ) < 2)) (by exact_mod_cast hb)).2
    (by linarith)

theorem criticalQ_bracket : 1054 / 665 < criticalQ ∧ criticalQ < 485 / 306 := by
  exact ⟨rational_lt_criticalQ 1054 665 (by decide) (by decide +kernel),
    criticalQ_lt_rational 485 306 (by decide) (by decide +kernel)⟩

end HlawkaSchatten.BelowExponent
