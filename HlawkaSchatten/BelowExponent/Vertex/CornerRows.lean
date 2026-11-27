/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCertificates
public import HlawkaSchatten.BelowExponent.Vertex.SideConeJoin

/-! Corner margin inequalities on the three bounded row charts. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

theorem CornerMarginAt.scale_iff {margins : Fin 3 → ℚ} {z : Row} {a b η ρ : ℝ}
    (hρ : ρ ≠ 0) :
    CornerMarginAt margins (fun j => ρ * z j) a b η ↔ CornerMarginAt margins z a b η := by
  have hq : 1 < criticalQ := by linarith only [criticalQ_bracket.1]
  have hp (x : ℝ) : |ρ*x|^criticalQ = |ρ|^criticalQ * |x|^criticalQ := by
    rw [abs_mul, Real.mul_rpow (abs_nonneg ρ) (abs_nonneg x)]
  simp only [CornerMarginAt, hp, parameterGap_scale hq hρ]
  simp_rw [mul_left_comm _ (|ρ|^criticalQ), ← Finset.mul_sum]
  exact mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos (abs_pos.mpr hρ) criticalQ)

theorem inSideNearCone_scale_iff {ρ : ℝ} (hρ : ρ ≠ 0) (z : Row) :
    InSideNearCone (fun j => ρ*z j) ↔ InSideNearCone z := by
  have hratio (j : Fin 3) : -(ρ*z j)/(ρ*z 0) = -z j/z 0 := by
    rw [← mul_neg]
    exact mul_div_mul_left _ _ hρ
  simp only [InSideNearCone, hratio, ne_eq, mul_eq_zero, hρ, false_or]

theorem cornerMargin_of_charts {margins : Fin 3 → ℚ} {a b η : ℝ} {applies : Row → Prop}
    (hscale : ∀ {ρ : ℝ} {z : Row}, ρ ≠ 0 → applies z → applies (fun j => ρ*z j))
    (hchart : ∀ k : Fin 3, ∀ z : Row, z k = 1 → (∀ j, |z j| ≤ 1) →
      applies z → CornerMarginAt margins z a b η) (z : Row) (hz : applies z) :
    CornerMarginAt margins z a b η := by
  by_cases hzero : z = 0
  · subst z
    have hq : criticalQ ≠ 0 := by linarith only [criticalQ_bracket.1]
    simp [CornerMarginAt, parameterGap_eq_linear, parameterArgument, argument, linearRow,
      linearFeature, Real.zero_rpow hq]
  obtain ⟨k, _, hmax⟩ := Finset.exists_max_image Finset.univ (fun j => |z j|) Finset.univ_nonempty
  have hk : z k ≠ 0 := by
    intro hk0
    apply hzero
    funext j
    exact abs_eq_zero.mp (le_antisymm (by simpa [hk0] using hmax j (Finset.mem_univ j)) (abs_nonneg _))
  have hρ : (z k)⁻¹ ≠ 0 := inv_ne_zero hk
  apply (CornerMarginAt.scale_iff (ρ := (z k)⁻¹) hρ).mp
  apply hchart k
  · simp [hk]
  · intro j
    simpa only [abs_mul, abs_inv, div_eq_inv_mul] using
      (div_le_one₀ (abs_pos.mpr hk)).mpr (hmax j (Finset.mem_univ j))
  · exact hscale hρ hz

end HlawkaSchatten.BelowExponent.Vertex
