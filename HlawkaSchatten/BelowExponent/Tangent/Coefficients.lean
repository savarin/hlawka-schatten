/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Tangent.Rectangle
import HlawkaSchatten.BelowExponent.Bulk
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Real power bounds for the integer coefficients and corner checks in `Tangent.Checker`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Tangent

private theorem q_range : 1 < criticalQ ∧ criticalQ < 2 :=
  ⟨by linarith only [criticalQ_bracket.1], by linarith only [criticalQ_bracket.2]⟩

private theorem two_pow_q (n : ℕ) : ((2 : ℝ) ^ n) ^ criticalQ = (3 : ℝ) ^ n := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), mul_comm,
    Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), two_rpow_criticalQ, Real.rpow_natCast]

private theorem four_pow_half_q (n : ℕ) : ((4 : ℝ) ^ n) ^ (criticalQ / 2) = (3 : ℝ) ^ n := by
  rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← pow_mul, mul_comm 2 n, pow_mul,
    ← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 2 ^ n)]
  norm_num only [Nat.cast_ofNat]
  rw [show (2 : ℝ) * (criticalQ / 2) = criticalQ by ring, two_pow_q]

private theorem scaled_q (m e s : ℕ) :
    ((m : ℝ) / (2 : ℝ) ^ e) ^ criticalQ =
      ((m : ℝ) / (2 : ℝ) ^ s) ^ criticalQ * (3 : ℝ) ^ s / (3 : ℝ) ^ e := by
  rw [Real.div_rpow (Nat.cast_nonneg m) (by positivity),
    Real.div_rpow (Nat.cast_nonneg m) (by positivity), two_pow_q, two_pow_q]
  field_simp

private theorem pow_cancel_offset (base : ℝ) (a b : ℕ) (hb : base ≠ 0) :
    base ^ (a - b) / base ^ (b - a) = base ^ a / base ^ b := by
  rcases le_total b a with h | h
  · rw [Nat.sub_eq_zero_of_le h, pow_zero, div_one]
    conv_rhs => rw [← Nat.sub_add_cancel h, pow_add]
    exact (mul_div_cancel_right₀ _ (pow_ne_zero _ hb)).symm
  · rw [Nat.sub_eq_zero_of_le h, pow_zero]
    conv_rhs => rw [← Nat.sub_add_cancel h, pow_add]
    field_simp

private theorem scale_eq (base : ℝ) {m n : ℕ} (h : m ≤ n) :
    base ^ n = base ^ m * base ^ (n - m) := by
  rw [← pow_add, Nat.add_sub_of_le h]

private theorem q_table_bounds {P : TC.Prof} {T : TC.Tab} (hT : TC.tabOK P T = true)
    (hk : 0 < P.k1 ∧ 0 < P.k2) {i : ℕ} (hi : i < 64) (e : ℕ) :
    let m := 64 + i
    let lo := (TC.field T.Qlo T.W i : ℝ) / (2 : ℝ) ^ P.K0 * (3 : ℝ) ^ 6 / (3 : ℝ) ^ e
    let hi := (TC.field T.Qhi T.W i : ℝ) / (2 : ℝ) ^ P.K0 * (3 : ℝ) ^ 7 / (3 : ℝ) ^ e
    lo ≤ ((m : ℝ) / (2 : ℝ) ^ e) ^ criticalQ ∧
      ((m : ℝ) / (2 : ℝ) ^ e) ^ criticalQ ≤ hi := by
  intro m lo up
  have hb := (exponent_bracket_of_tabOK hT hk).1.le
  obtain ⟨hlo, hup⟩ := (TC.tabOK_spec P T hT).2.2.2.2.2.2.2 i hi
  have hml : (1 : ℝ) ≤ (m : ℝ) / 2 ^ (6 : ℕ) := by
    rw [le_div_iff₀ (by positivity)]
    have : (64 : ℝ) ≤ m := by exact_mod_cast (Nat.le_add_right 64 i)
    norm_num at *
    linarith only [this]
  have hmu : (m : ℝ) / 2 ^ (7 : ℕ) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : (m : ℝ) ≤ 128 := by exact_mod_cast (show m ≤ 128 by dsimp [m]; omega)
    norm_num at *
    exact this
  have hnatlo : (TC.field T.Qlo T.W i : ℝ) / (2 : ℝ) ^ P.K0 ≤
      ((m : ℝ) / (2 : ℝ) ^ (6 : ℕ)) ^ ((P.n1 : ℝ) / P.k1) := by
    have h := (le_natRat_rpow_iff (a := m) (b := 2 ^ 6) (c := TC.field T.Qlo T.W i)
      (d := 2 ^ P.K0) (m := P.n1) (by positivity) (by positivity) hk.1).2
        (by simpa only [← pow_mul] using hlo)
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using h
  have hnatup : ((m : ℝ) / (2 : ℝ) ^ (7 : ℕ)) ^ ((P.n1 : ℝ) / P.k1) ≤
      (TC.field T.Qhi T.W i : ℝ) / (2 : ℝ) ^ P.K0 := by
    have h := (natRat_rpow_le_iff (a := m) (b := 2 ^ 7) (c := TC.field T.Qhi T.W i)
      (d := 2 ^ P.K0) (m := P.n1) (by positivity) (by positivity) hk.1).2
        (by simpa only [← pow_mul] using hup)
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using h
  constructor
  · rw [scaled_q m e 6]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hnatlo.trans (Real.rpow_le_rpow_of_exponent_le hml hb)) (by positivity))
      (by positivity)
  · rw [scaled_q m e 7]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      ((Real.rpow_le_rpow_of_exponent_ge (by positivity) hmu hb).trans hnatup) (by positivity))
      (by positivity)

/-- A checked input tangent is a global minorant, including code zero. -/
theorem rowTangent_le_rpow {H : TC.Hdr} (hT : TC.tabOK H.prof H.tab = true)
    (hk : 0 < H.prof.k1 ∧ 0 < H.prof.k2) (code : ℕ) (x : ℝ) :
    rowTangent (TC.mkCtx H) code x ≤ |x| ^ criticalQ := by
  by_cases hc : code = 0
  · simpa [rowTangent, TC.acoef, hc] using Real.rpow_nonneg (abs_nonneg x) criticalQ
  let P := H.prof
  let C := TC.mkCtx H
  let i := (code - 1) % 64
  let m := 64 + i
  let e := 6 + (code - 1) / 64
  let lo := (TC.field H.tab.Qlo H.tab.W i : ℝ) / (2 : ℝ) ^ P.K0 * (3 : ℝ) ^ 6 / (3 : ℝ) ^ e
  let up := (TC.field H.tab.Qhi H.tab.W i : ℝ) / (2 : ℝ) ^ P.K0 * (3 : ℝ) ^ 7 / (3 : ℝ) ^ e
  let a := (m : ℝ) / (2 : ℝ) ^ e
  have htab := TC.tabOK_spec P H.tab hT
  have hbr := exponent_bracket_of_tabOK hT hk
  have hm : 0 < m := by dsimp [m]; omega
  have ha : 0 < a := by dsimp [a]; positivity
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h₁ : (0 : ℝ) < P.k1 := by exact_mod_cast hk.1
  have h₂ : (0 : ℝ) < P.k2 := by exact_mod_cast hk.2
  have hlo₀ : 0 ≤ (P.n1 : ℝ) / P.k1 := by positivity
  have hhi : P.k2 ≤ P.n2 := by
    apply Nat.le_of_lt
    have h := (lt_div_iff₀ h₂).1 (q_range.1.trans hbr.2)
    rw [one_mul] at h
    exact_mod_cast h
  have hhi₀ : 0 ≤ (P.n2 : ℝ) / P.k2 - 1 := by linarith only [q_range.1, hbr.2]
  have he : 6 ≤ e := by dsimp [e]; omega
  have hall : lo ≤ a ^ criticalQ ∧ a ^ criticalQ ≤ up :=
    q_table_bounds hT hk (Nat.mod_lt _ (by decide)) e
  have hs := TC.acoef_spec C code hk.1 hk.2 hc
  change (_ → _) ∧ (_ → _) ∧ _ at hs
  have hCN : ((P.n2 - P.k2 : ℕ) * TC.field H.tab.Qhi H.tab.W i * 3 ^ (7 - e)) <<< (P.K - P.K0) ≤
      (TC.acoef C code).1 * (P.k2 * 3 ^ (e - 7)) := by
    rcases le_or_gt e 7 with hh | hh
    · simpa [C, TC.mkCtx, Nat.sub_eq_zero_of_le hh] using hs.1 hh
    · simpa [C, TC.mkCtx, Nat.sub_eq_zero_of_le hh.le] using hs.2.1 hh
  have hDN : (TC.acoef C code).2 * (P.k1 * m * 3 ^ (e - 6)) ≤
      (P.n1 * TC.field H.tab.Qlo H.tab.W i) <<< (e + (P.K - P.K0)) := hs.2.2
  rw [Nat.shiftLeft_eq] at hCN hDN
  have hCn : ((P.n2 : ℝ) - P.k2) * TC.field H.tab.Qhi H.tab.W i * (3 : ℝ) ^ (7 - e) *
      (2 : ℝ) ^ (P.K - P.K0) ≤ (TC.acoef C code).1 * ((P.k2 : ℝ) * (3 : ℝ) ^ (e - 7)) := by
    exact_mod_cast hCN
  have hDn : ((TC.acoef C code).2 : ℝ) * ((P.k1 : ℝ) * m * (3 : ℝ) ^ (e - 6)) ≤
      (P.n1 : ℝ) * TC.field H.tab.Qlo H.tab.W i * (2 : ℝ) ^ (e + (P.K - P.K0)) := by
    exact_mod_cast hDN
  have hK : P.K0 ≤ P.K := htab.2.2.2.2.2.1
  have hC : ((P.n2 : ℝ) / P.k2 - 1) * up ≤ (TC.acoef C code).1 / (2 : ℝ) ^ C.K := by
    apply (le_div_iff₀ (by positivity)).2
    change _ * _ * (2 : ℝ) ^ P.K ≤ _
    have h := (div_le_iff₀ (by positivity : 0 < (P.k2 : ℝ) * (3 : ℝ) ^ (e - 7))).2 hCn
    refine le_trans (le_of_eq ?_) h
    dsimp [up]
    rw [scale_eq 2 hK, mul_div_assoc _ ((3 : ℝ) ^ 7), ← pow_cancel_offset 3 7 e (by norm_num)]
    field_simp
  have hD : (TC.acoef C code).2 / (2 : ℝ) ^ C.K ≤ ((P.n1 : ℝ) / P.k1) * lo / a := by
    apply (div_le_iff₀ (by positivity)).2
    change _ ≤ _ * (2 : ℝ) ^ P.K
    have h := (le_div_iff₀ (by positivity : 0 < (P.k1 : ℝ) * m * (3 : ℝ) ^ (e - 6))).2 hDn
    refine h.trans (le_of_eq ?_)
    dsimp [lo, a]
    rw [scale_eq 2 hK, mul_div_assoc _ ((3 : ℝ) ^ 6), ← pow_cancel_offset 3 6 e (by norm_num),
      Nat.sub_eq_zero_of_le he, pow_zero, pow_add]
    field_simp
  have hUpper := (mul_le_mul_of_nonneg_left hall.2 hhi₀).trans hC
  have hLower := hD.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hall.1 hlo₀) ha.le)
  have hq₀ : 0 ≤ a ^ criticalQ := Real.rpow_nonneg ha.le _
  have hqC : (criticalQ - 1) * a ^ criticalQ ≤ (TC.acoef C code).1 / (2 : ℝ) ^ C.K :=
    (mul_le_mul_of_nonneg_right (sub_le_sub_right hbr.2.le _) hq₀).trans hUpper
  have hqD : (TC.acoef C code).2 / (2 : ℝ) ^ C.K ≤ criticalQ * a ^ criticalQ / a :=
    hLower.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hbr.1.le hq₀) ha.le)
  calc
    _ = -((TC.acoef C code).1 / (2 : ℝ) ^ C.K) + ((TC.acoef C code).2 / (2 : ℝ) ^ C.K) * |x| := by
      simp only [C, rowTangent, add_div, neg_div, mul_div_right_comm]
    _ ≤ -((criticalQ - 1) * a ^ criticalQ) + (criticalQ * a ^ criticalQ / a) * |x| :=
      add_le_add (neg_le_neg hqC) (mul_le_mul_of_nonneg_right hqD (abs_nonneg x))
    _ = a ^ criticalQ * (1 + criticalQ * (|x| / a - 1)) := by ring
    _ ≤ _ := tangentRatio_le_rpow q_range.1.le ha (abs_nonneg x)

private theorem mhi_eq (P : TC.Prof) (hMR : 4 ≤ P.MR) :
    (2 : ℕ) ^ P.MR = 4 * 2 ^ (P.MR - 2) := by
  calc
    _ = (2 : ℕ) ^ ((P.MR - 2) + 2) := congrArg (fun n : ℕ => (2 : ℕ) ^ n) (by omega)
    _ = _ := by rw [pow_add, mul_comm]; rfl

private theorem r_table_bound {P : TC.Prof} {T : TC.Tab} (hT : TC.tabOK P T = true)
    (hk : 0 < P.k1 ∧ 0 < P.k2) {m : ℕ} (hml : 2 ^ (P.MR - 2) ≤ m) (hmh : m < 2 ^ P.MR)
    (e : ℕ) :
    ((m : ℝ) / (4 : ℝ) ^ e) ^ (criticalQ / 2) ≤
      (TC.field T.P1 T.W (m - 2 ^ (P.MR - 2)) : ℝ) / (2 : ℝ) ^ P.K0 *
        (3 : ℝ) ^ (P.MR / 2) / (3 : ℝ) ^ e := by
  have htab := TC.tabOK_spec P T hT
  have hlo := (exponent_bracket_of_tabOK hT hk).1
  have hevenN : (P.n1 : ℝ) = (↑(P.n1 / 2 : ℕ) : ℝ) * 2 := by
    have hn := htab.2.2.1
    exact_mod_cast (show P.n1 = (P.n1 / 2) * 2 by omega)
  have hr := htab.2.2.2.1
  have hmr : 4 ≤ P.MR := htab.2.2.2.2.1
  have pows : (2 : ℝ) ^ P.MR = (4 : ℝ) ^ (P.MR / 2) := by
    conv_lhs => rw [show P.MR = 2 * (P.MR / 2) by omega, pow_mul]
    norm_num
  have hs := htab.2.2.2.2.2.2.1 (m - 2 ^ (P.MR - 2)) (by rw [mhi_eq P hmr] at hmh; omega)
  rw [show (2 : ℕ) ^ (P.MR - 2) + (m - 2 ^ (P.MR - 2)) = m by omega] at hs
  have hrational : ((m : ℝ) / (2 : ℝ) ^ P.MR) ^ ((↑(P.n1 / 2 : ℕ) : ℝ) / P.k1) ≤
      (TC.field T.P1 T.W (m - 2 ^ (P.MR - 2)) : ℝ) / (2 : ℝ) ^ P.K0 := by
    have h := (natRat_rpow_le_iff (a := m) (b := 2 ^ P.MR) (d := 2 ^ P.K0)
      (m := P.n1 / 2) (by positivity) (by positivity) hk.1).2
        (by simpa only [← pow_mul] using hs.2)
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using h
  have hm₀ : 0 < m := (Nat.pow_pos (by decide)).trans_le hml
  have hm₁ : (m : ℝ) / (2 : ℝ) ^ P.MR ≤ 1 := (div_le_one (by positivity)).2 (by exact_mod_cast hmh.le)
  have hExp : (↑(P.n1 / 2 : ℕ) : ℝ) / P.k1 ≤ criticalQ / 2 := by
    rw [hevenN] at hlo
    linarith only [show ((↑(P.n1 / 2 : ℕ) : ℝ) * 2) / P.k1 = 2 * ((↑(P.n1 / 2 : ℕ) : ℝ) / P.k1) by ring, hlo]
  have hnorm := (Real.rpow_le_rpow_of_exponent_ge
    (div_pos (by exact_mod_cast hm₀) (by positivity)) hm₁ hExp).trans hrational
  calc
    _ = ((m : ℝ) / (2 : ℝ) ^ P.MR) ^ (criticalQ / 2) *
        (3 : ℝ) ^ (P.MR / 2) / (3 : ℝ) ^ e := by
      rw [pows, Real.div_rpow (Nat.cast_nonneg m) (by positivity),
        Real.div_rpow (Nat.cast_nonneg m) (by positivity), four_pow_half_q, four_pow_half_q]
      field_simp
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hnorm (by positivity)) (by positivity)

private theorem rcoef_bounds {H : TC.Hdr} (hT : TC.tabOK H.prof H.tab = true)
    (hk : 0 < H.prof.k1 ∧ 0 < H.prof.k2) (p m e : ℕ) (hm : 0 < m) :
    let P := H.prof
    let C := TC.mkCtx H
    let r := (m : ℝ) / (4 : ℝ) ^ e
    let R := (p : ℝ) / (2 : ℝ) ^ P.K0 * (3 : ℝ) ^ (P.MR / 2) / (3 : ℝ) ^ e
    (1 - (↑(P.n1 / 2 : ℕ) : ℝ) / P.k1) * R ≤ (TC.rcoef C p m e).1 / (2 : ℝ) ^ C.K ∧
      ((P.n2 : ℝ) / (2 * P.k2)) * R / r ≤ (TC.rcoef C p m e).2 / (2 : ℝ) ^ C.K := by
  intro P C r R
  let h := P.MR / 2
  have htab := TC.tabOK_spec P H.tab hT
  have hkR : P.K0 ≤ P.K := htab.2.2.2.2.2.1
  have h₁ : (0 : ℝ) < P.k1 := by exact_mod_cast hk.1
  have h₂ : (0 : ℝ) < P.k2 := by exact_mod_cast hk.2
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hEven : P.n1 = (P.n1 / 2) * 2 := by have := htab.2.2.1; omega
  have hEven' : (P.n1 : ℝ) = (↑(P.n1 / 2 : ℕ) : ℝ) * 2 := by exact_mod_cast hEven
  have hHalf : P.n1 / 2 ≤ P.k1 := by
    have hb := (exponent_bracket_of_tabOK hT hk).1.trans q_range.2
    have hb' := (div_lt_iff₀ h₁).1 hb
    rw [hEven'] at hb'
    have hc : (↑(P.n1 / 2 : ℕ) : ℝ) ≤ P.k1 := by linarith only [hb']
    exact_mod_cast hc
  have hs := TC.rcoef_spec C p m e hk.1 (Nat.mul_pos (by decide) hk.2) hm
  have hA : p * 3 ^ (h - e) * ((P.k1 - P.n1 / 2) * 2 ^ (P.K - P.K0)) ≤
      (TC.rcoef C p m e).1 * (P.k1 * 3 ^ (e - h)) := by
    rcases le_or_gt e h with hh | hh
    · simpa [C, TC.mkCtx, h, Nat.sub_eq_zero_of_le hh] using hs.1 hh |>.1
    · simpa [C, TC.mkCtx, h, Nat.sub_eq_zero_of_le hh.le] using hs.2 hh |>.1
  have hB : (p * 3 ^ (h - e) * (P.n2 * 2 ^ (P.K - P.K0))) <<< (2 * e) ≤
      (TC.rcoef C p m e).2 * (2 * P.k2 * m * 3 ^ (e - h)) := by
    rcases le_or_gt e h with hh | hh
    · simpa [C, TC.mkCtx, h, Nat.sub_eq_zero_of_le hh] using hs.1 hh |>.2
    · simpa [C, TC.mkCtx, h, Nat.sub_eq_zero_of_le hh.le] using hs.2 hh |>.2
  rw [Nat.shiftLeft_eq] at hB
  have hA' : (p : ℝ) * 3 ^ (h - e) * (((P.k1 : ℝ) - ↑(P.n1 / 2 : ℕ)) * 2 ^ (P.K - P.K0)) ≤
      (TC.rcoef C p m e).1 * ((P.k1 : ℝ) * 3 ^ (e - h)) := by exact_mod_cast hA
  have hB' : (p : ℝ) * 3 ^ (h - e) * ((P.n2 : ℝ) * 2 ^ (P.K - P.K0)) * 2 ^ (2 * e) ≤
      (TC.rcoef C p m e).2 * (2 * (P.k2 : ℝ) * m * 3 ^ (e - h)) := by exact_mod_cast hB
  constructor
  · apply (le_div_iff₀ (by positivity)).2
    have hq := (div_le_iff₀ (by positivity : 0 < (P.k1 : ℝ) * (3 : ℝ) ^ (e - h))).2 hA'
    refine le_trans (le_of_eq ?_) hq
    dsimp [R, C, TC.mkCtx]
    change _ * ((p : ℝ) / 2 ^ P.K0 * 3 ^ h / 3 ^ e) * 2 ^ P.K = _
    rw [scale_eq 2 hkR, mul_div_assoc _ ((3 : ℝ) ^ h), ← pow_cancel_offset 3 h e (by norm_num)]
    field_simp
  · apply (le_div_iff₀ (by positivity)).2
    have hq := (div_le_iff₀ (by positivity : 0 < 2 * (P.k2 : ℝ) * m * (3 : ℝ) ^ (e - h))).2 hB'
    refine le_trans (le_of_eq ?_) hq
    dsimp [R, r, C, TC.mkCtx]
    change _ * ((p : ℝ) / 2 ^ P.K0 * 3 ^ h / 3 ^ e) / ((m : ℝ) / 4 ^ e) * 2 ^ P.K = _
    rw [scale_eq 2 hkR, mul_div_assoc _ ((3 : ℝ) ^ h), ← pow_cancel_offset 3 h e (by norm_num), pow_mul]
    norm_num
    field_simp

private theorem rpow_le_rcoef {H : TC.Hdr} (hT : TC.tabOK H.prof H.tab = true)
    (hk : 0 < H.prof.k1 ∧ 0 < H.prof.k2) {m : ℕ}
    (hml : 2 ^ (H.prof.MR - 2) ≤ m) (hmh : m < 2 ^ H.prof.MR)
    (e : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    let C := TC.mkCtx H
    let c := TC.rcoef C (TC.field C.P1 C.W (m - C.mlo)) m e
    y ^ (criticalQ / 2) ≤ (c.1 : ℝ) / (2 : ℝ) ^ C.K + (c.2 : ℝ) / (2 : ℝ) ^ C.K * y := by
  intro C c
  let P := H.prof
  let p := TC.field C.P1 C.W (m - C.mlo)
  let r := (m : ℝ) / (4 : ℝ) ^ e
  let α := criticalQ / 2
  let a := (↑(P.n1 / 2 : ℕ) : ℝ) / P.k1
  let b := (P.n2 : ℝ) / (2 * P.k2)
  let R := (p : ℝ) / (2 : ℝ) ^ P.K0 * (3 : ℝ) ^ (P.MR / 2) / (3 : ℝ) ^ e
  have hm : 0 < m := (Nat.pow_pos (by decide)).trans_le hml
  have hr : 0 < r := div_pos (by exact_mod_cast hm) (by positivity)
  have hα₀ : 0 ≤ α := by dsimp [α]; linarith only [q_range.1]
  have hα₁ : α ≤ 1 := by dsimp [α]; linarith only [q_range.2]
  have htab := TC.tabOK_spec P H.tab hT
  have hbr := exponent_bracket_of_tabOK hT hk
  have hab : a ≤ α ∧ α ≤ b := by
    have heven := htab.2.2.1
    have hn : (P.n1 : ℝ) = (↑(P.n1 / 2 : ℕ) : ℝ) * 2 := by
      exact_mod_cast (show P.n1 = (P.n1 / 2) * 2 by omega)
    have hlo : (P.n1 : ℝ) / P.k1 < criticalQ := hbr.1
    have hup : criticalQ < (P.n2 : ℝ) / P.k2 := hbr.2
    have hEq : (P.n1 : ℝ) / P.k1 = 2 * a := by dsimp [a]; rw [hn]; ring
    rw [hEq] at hlo
    constructor
    · dsimp [α]; linarith only [hlo]
    · dsimp [α, b]
      rw [mul_comm (2 : ℝ), ← div_div]
      linarith only [hup]
  have hR : r ^ α ≤ R := r_table_bound hT hk hml hmh e
  have hc := rcoef_bounds hT hk p m e hm
  change (1 - a) * R ≤ (c.1 : ℝ) / (2 : ℝ) ^ C.K ∧ b * R / r ≤ (c.2 : ℝ) / (2 : ℝ) ^ C.K at hc
  have ha₀ : 0 ≤ 1 - a := sub_nonneg.mpr (hab.1.trans hα₁)
  have hb₀ : 0 ≤ b := hα₀.trans hab.2
  have hp₀ : 0 ≤ r ^ α := Real.rpow_nonneg hr.le _
  have hA := ((mul_le_mul_of_nonneg_right (sub_le_sub_left hab.1 _) hp₀).trans
    (mul_le_mul_of_nonneg_left hR ha₀)).trans hc.1
  have hB := (div_le_div_of_nonneg_right ((mul_le_mul_of_nonneg_right hab.2 hp₀).trans
    (mul_le_mul_of_nonneg_left hR hb₀)) hr.le).trans hc.2
  have hBern := rpow_one_add_le_one_add_mul_self
    (show -1 ≤ y / r - 1 by linarith only [div_nonneg hy hr.le]) hα₀ hα₁
  rw [show 1 + (y / r - 1) = y / r by ring, Real.div_rpow hy hr.le] at hBern
  calc
    _ ≤ (1 + α * (y / r - 1)) * r ^ α := (div_le_iff₀ (Real.rpow_pos_of_pos hr _)).1 hBern
    _ = (1 - α) * r ^ α + (α * r ^ α / r) * y := by ring
    _ ≤ _ := add_le_add hA (mul_le_mul_of_nonneg_right hB hy)

/-- The checked output term bounds the real half power after dividing by its scale and denominator. -/
theorem rpow_le_termL {H : TC.Hdr} (hT : TC.tabOK H.prof H.tab = true)
    (hk : 0 < H.prof.k1 ∧ 0 < H.prof.k2) (X : ℕ) {Y : ℕ} (hY : 0 < Y) :
    let C := TC.mkCtx H
    ((X : ℝ) / Y) ^ (criticalQ / 2) ≤ (TC.termL C X Y : ℝ) / ((2 : ℝ) ^ C.K * Y) := by
  intro C
  by_cases hX : X = 0
  · have hq : criticalQ / 2 ≠ 0 := by linarith only [q_range.1]
    simp [hX, TC.termL, Real.zero_rpow hq]
  have hXb : Nat.beq X 0 = false := by
    cases h : Nat.beq X 0
    · rfl
    · exact (hX (Nat.beq_eq.mp h)).elim
  have h4 := (TC.tabOK_spec H.prof H.tab hT).2.2.2.2.1
  have hm : C.mlo < C.mhi := by
    change 2 ^ (H.prof.MR - 2) < 2 ^ H.prof.MR
    rw [mhi_eq _ h4]
    have hpos : 0 < (2 : ℕ) ^ (H.prof.MR - 2) := by positivity
    omega
  obtain ⟨hl, hu⟩ := TC.node_range C X Y hm
  have h := rpow_le_rcoef hT hk hl hu (TC.node C X Y).2 (y := (X : ℝ) / Y) (by positivity)
  let c := TC.rcoef C (TC.field C.P1 C.W ((TC.node C X Y).1 - C.mlo))
    (TC.node C X Y).1 (TC.node C X Y).2
  change _ ≤ (c.1 : ℝ) / (2 : ℝ) ^ C.K + (c.2 : ℝ) / (2 : ℝ) ^ C.K * ((X : ℝ) / Y) at h
  have hTerm : TC.termL C X Y = c.1 * Y + c.2 * X := by simp [TC.termL, hXb, c]
  rw [hTerm, Nat.cast_add, Nat.cast_mul, Nat.cast_mul]
  have hY' : (Y : ℝ) ≠ 0 := by exact_mod_cast hY.ne'
  refine h.trans (le_of_eq ?_)
  field_simp

private def shiftedMag (C : TC.Ctx) (A : ℕ) : ℕ :=
  bif Nat.ble C.Da A then A - C.Da else C.Da - A

private theorem signed_mag (C : TC.Ctx) (A : ℕ) :
    (TC.sgn (Nat.ble C.Da A) : ℝ) * (shiftedMag C A : ℝ) = (A : ℝ) - C.Da := by
  rcases le_or_gt C.Da A with h | h
  · simp [shiftedMag, TC.ble_dec, TC.sgn, h, Nat.cast_sub h]
  · simp [shiftedMag, TC.ble_dec, TC.sgn, h.not_ge, Nat.cast_sub h.le]

private theorem abs_chartCoord {C : TC.Ctx} (hDa : 0 < C.Da) (A : ℕ) :
    |chartCoord C A| = (shiftedMag C A : ℝ) / C.Da := by
  have hDa' : (0 : ℝ) < C.Da := by exact_mod_cast hDa
  have h := congrArg abs (signed_mag C A)
  have hsgn : |(TC.sgn (Nat.ble C.Da A) : ℝ)| = 1 := by
    cases Nat.ble C.Da A <;> norm_num [TC.sgn]
  rw [abs_mul, hsgn, one_mul, abs_of_nonneg (Nat.cast_nonneg _)] at h
  unfold chartCoord
  rw [← div_self hDa'.ne', ← sub_div, abs_div, abs_of_pos hDa', ← h]

private theorem gInt_cast_chart (C : TC.Ctx) (A B : ℕ) (t : TC.Tm) :
    (TC.gInt t (Nat.ble C.Da A) (shiftedMag C A) (Nat.ble C.Da B) (shiftedMag C B) : ℝ) =
    (TC.sgn t.s0 : ℝ) * t.c0 + (TC.sgn t.s1 : ℝ) * t.c1 * ((A : ℝ) - C.Da) +
      (TC.sgn t.s2 : ℝ) * t.c2 * ((B : ℝ) - C.Da) := by
  rw [← signed_mag C A, ← signed_mag C B]
  simp only [TC.gInt, TC.sgn_beqB, Int.cast_add, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
  ring

private theorem sgn_chiPos (j : Fin 3) (s : Fin 4) :
    (TC.sgn (TC.chiPos s.val j.val) : ℝ) = sign j s := by
  fin_cases j <;> fin_cases s <;> norm_num [TC.chiPos, TC.sgn, sign, partner]

private theorem wv_ratio (D : ℕ) (v : TC.V4) (j : Fin 3) (s : Fin 4) :
    (TC.wv v j.val s.val : ℝ) / D = vertex D v s + vertex D v (partner j s) := by
  fin_cases j <;> fin_cases s <;> simp [TC.wv, vertex, partner, Nat.cast_add, add_div]

private theorem rowEval_mkTm {C : TC.Ctx} {D : ℕ} (hD : 0 < D) (hDa : 0 < C.Da)
    (v : TC.V4) (j : Fin 3) (s : Fin 4) (A B p : ℕ) :
    (TC.gInt (TC.mkTm C.Da v j.val (chartA j).val (chartB j).val s.val p)
      (Nat.ble C.Da A) (shiftedMag C A) (Nat.ble C.Da B) (shiftedMag C B) : ℝ) /
        ((D : ℝ) * C.Da) = rowEval (vertex D v) s (chartRow j (chartCoord C A) (chartCoord C B)) := by
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hDa' : (C.Da : ℝ) ≠ 0 := by exact_mod_cast hDa.ne'
  have hrow (a b : ℝ) : rowEval (vertex D v) s (chartRow j a b) =
      sign j s * (vertex D v s + vertex D v (partner j s)) +
      sign (chartA j) s * (vertex D v s + vertex D v (partner (chartA j) s)) * a +
      sign (chartB j) s * (vertex D v s + vertex D v (partner (chartB j) s)) * b := by
    fin_cases j <;> simp [rowEval, Fin.sum_univ_three, chartRow, chartA, chartB] <;> ring
  rw [gInt_cast_chart, hrow]
  simp only [TC.mkTm, Nat.cast_mul, sgn_chiPos, ← wv_ratio, chartCoord]
  field_simp [hD', hDa']

private theorem power_term_le {H : TC.Hdr} (hT : TC.tabOK H.prof H.tab = true)
    (hk : 0 < H.prof.k1 ∧ 0 < H.prof.k2) {d : ℕ} (hd : 0 < d)
    (sa : Bool) (ua : ℕ) (sb : Bool) (ub : ℕ) (t : TC.Tm) :
    let C := TC.mkCtx H
    let g := TC.agOf t sa ua sb ub
    |(TC.gInt t sa ua sb ub : ℝ) / d| ^ criticalQ ≤
      (TC.termL C (g * g) (d ^ 2) : ℝ) / ((2 : ℝ) ^ C.K * (d : ℝ) ^ 2) := by
  intro C g
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hg : (g : ℝ) = |(TC.gInt t sa ua sb ub : ℝ)| := by
    have ha : g = (TC.gInt t sa ua sb ub).natAbs := by exact_mod_cast TC.ag_spec t sa ua sb ub
    rw [ha, Nat.cast_natAbs, Int.cast_abs]
  have hsq : ((↑(g * g : ℕ) : ℝ) / ↑(d ^ 2 : ℕ)) ^ (criticalQ / 2) =
      |(TC.gInt t sa ua sb ub : ℝ) / d| ^ criticalQ := by
    rw [Nat.cast_mul, Nat.cast_pow, ← pow_two, hg, ← div_pow, ← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity), abs_div, abs_of_pos hd']
    congr 1
    push_cast
    ring
  have h := rpow_le_termL hT hk (g * g) (pow_pos hd 2)
  dsimp only at h
  rw [hsq, Nat.cast_pow] at h
  exact h

private theorem powers_le_lint {H : TC.Hdr} (hT : TC.tabOK H.prof H.tab = true)
    (hk : 0 < H.prof.k1 ∧ 0 < H.prof.k2) {d : ℕ} (hd : 0 < d)
    (sa : Bool) (ua : ℕ) (sb : Bool) (ub : ℕ) (ts : List TC.Tm) :
    let C := TC.mkCtx H
    (ts.map fun t => (t.p : ℝ) * |(TC.gInt t sa ua sb ub : ℝ) / d| ^ criticalQ).sum ≤
      (TC.lint C (d ^ 2) sa ua sb ub ts : ℝ) / ((2 : ℝ) ^ C.K * (d : ℝ) ^ 2) := by
  intro C
  induction ts with
  | nil => simp [TC.lint]
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons, TC.lint_cons_eq_reference, TC.tmVal_eq, Nat.cast_add, add_div, Nat.cast_mul]
    refine add_le_add ?_ ih
    exact (mul_le_mul_of_nonneg_left (power_term_le hT hk hd sa ua sb ub t) (Nat.cast_nonneg _)).trans_eq
      (by ring)

private theorem mkTm_p (Da : ℕ) (v : TC.V4) (j k l s p : ℕ) : (TC.mkTm Da v j k l s p).p = p := rfl

private theorem rawCornerOutput_eq {C : TC.Ctx} {D : ℕ} (hD : 0 < D) (hDa : 0 < C.Da)
    (v : TC.V4) (j : Fin 3) {ps : List ℕ} (hp : ps.length = 4) (A B : ℕ) :
    ((TC.mkTms C.Da j.val (chartA j).val (chartB j).val ps v).map fun t =>
      (t.p : ℝ) * |(TC.gInt t (Nat.ble C.Da A) (shiftedMag C A) (Nat.ble C.Da B) (shiftedMag C B) : ℝ) /
        ↑(D * C.Da : ℕ)| ^ criticalQ).sum =
    cornerOutput criticalQ (vertex D v) (fun s => (ps.getD s.val 0 : ℝ))
      (chartRow j (chartCoord C A) (chartCoord C B)) := by
  obtain ⟨p₀, p₁, p₂, p₃, rfl⟩ := List.length_eq_four.mp hp
  simp [TC.mkTms, mkTm_p, cornerOutput, Fin.sum_univ_four, Nat.cast_mul]
  have hrow (s : Fin 4) (i p : ℕ) (hi : s.val = i) :
      (TC.gInt (TC.mkTm C.Da v j.val (chartA j).val (chartB j).val i p)
        (Nat.ble C.Da A) (shiftedMag C A) (Nat.ble C.Da B) (shiftedMag C B) : ℝ) /
        ((D : ℝ) * C.Da) = rowEval (vertex D v) s (chartRow j (chartCoord C A) (chartCoord C B)) :=
    hi ▸ rowEval_mkTm hD hDa v j s A B p
  rw [hrow 0 0 p₀ rfl, hrow 1 1 p₁ rfl, hrow 2 2 p₂ rfl, hrow 3 3 p₃ rfl]
  ring

/-- Checked integer corners imply the compensated real comparisons at every represented vertex.
The positive common weight denominator can include any profile-dependent scale. -/
theorem cornerSound_mkFace {H : TC.Hdr} (hT : TC.tabOK H.prof H.tab = true)
    (hk : 0 < H.prof.k1 ∧ 0 < H.prof.k2) (j : Fin 3)
    {V : List TC.V4} {v : TC.V4} (hv : v ∈ V) {D W : ℕ} (hD : 0 < D) (hW : 0 < W)
    {ps gs : List ℕ} (hp : ps.length = 4) :
    let C := TC.mkCtx H
    CornerSound criticalQ C (TC.mkFace C V D ps gs j.val (chartA j).val (chartB j).val)
      j (vertex D v) (fun s => (ps.getD s.val 0 : ℝ) / W) (fun i => (gs.getD i.val 0 : ℝ) / W) := by
  intro C ca cb A B
  dsimp only
  let F := TC.mkFace C V D ps gs j.val (chartA j).val (chartB j).val
  let out := cornerOutput criticalQ (vertex D v) (fun s => (ps.getD s.val 0 : ℝ))
    (chartRow j (chartCoord C A) (chartCoord C B))
  let inp := cornerInput (fun i => (gs.getD i.val 0 : ℝ)) j (rowTangent C ca) (rowTangent C cb)
    (chartCoord C A) (chartCoord C B)
  let L := (F.gk * (TC.acoef C ca).1 + F.gl * (TC.acoef C cb).1) * C.Da * F.F
  let U := F.gj2K + F.gk * (TC.acoef C ca).2 * shiftedMag C A + F.gl * (TC.acoef C cb).2 * shiftedMag C B
  let S := (2 : ℝ) ^ C.K * ((D : ℝ) * C.Da) ^ 2
  change TC.cornerOK C F L (TC.acoef C ca).2 (TC.acoef C cb).2 A B (TC.lmaxAt C F A B) = true → _
  intro h
  have hDa : 0 < C.Da := by change 0 < (2 : ℕ) ^ H.KBOX; positivity
  have hDa' : (0 : ℝ) < C.Da := by exact_mod_cast hDa
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hS : 0 < S := by dsimp [S]; positivity
  have hInt : TC.lmaxAt C F A B + L ≤ U * F.F := (TC.cornerOK_spec _ _ _ _ _ _ _ _).1 h
  have hReal : (TC.lmaxAt C F A B : ℝ) + L ≤ (U : ℝ) * F.F := by exact_mod_cast hInt
  let ts := TC.mkTms C.Da j.val (chartA j).val (chartB j).val ps v
  have hm : ts ∈ F.terms := List.mem_map_of_mem hv
  have hy : F.Y = (D * C.Da) ^ 2 := rfl
  have hmax : TC.lint C F.Y (Nat.ble C.Da A) (shiftedMag C A) (Nat.ble C.Da B) (shiftedMag C B) ts ≤
      TC.lmaxAt C F A B := TC.lmaxV_ge _ _ _ _ _ _ _ _ hm
  have hout : out ≤ (TC.lmaxAt C F A B : ℝ) / S := by
    have hsum := powers_le_lint hT hk (Nat.mul_pos hD hDa) (Nat.ble C.Da A) (shiftedMag C A)
      (Nat.ble C.Da B) (shiftedMag C B) ts
    dsimp only at hsum
    rw [rawCornerOutput_eq hD hDa v j hp A B, Nat.cast_mul, ← hy] at hsum
    exact hsum.trans (div_le_div_of_nonneg_right (by exact_mod_cast hmax) hS.le)
  have hEq : inp * S = (U : ℝ) * F.F - L := by
    simp only [inp, S, U, L, F, TC.mkFace, cornerInput, rowTangent, abs_chartCoord hDa,
      Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    field_simp [hDa'.ne']
    ring
  have hin : (TC.lmaxAt C F A B : ℝ) / S ≤ inp := by
    apply (div_le_iff₀ hS).2
    rw [hEq]
    exact (le_sub_iff_add_le).2 hReal
  calc
    _ = out / W := by simp [out, cornerOutput, Finset.sum_div, div_mul_eq_mul_div]
    _ ≤ inp / W := div_le_div_of_nonneg_right (hout.trans hin) hW'.le
    _ = _ := by simp [inp, cornerInput, add_div, mul_div_right_comm]

end HlawkaSchatten.BelowExponent.Tangent
