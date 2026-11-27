/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.SideConeNormalize
public import HlawkaSchatten.BelowExponent.Vertex.SideConeParameterGrid
public import HlawkaSchatten.BelowExponent.Vertex.SideConeReplay

/-! The exact row and parameter covers give the near-cone input to the vertex-side region. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

noncomputable section

def InSideNearCone (z : Row) : Prop :=
  let u := -z 1/z 0-1
  let v := -z 2/z 0-1
  z 0 ≠ 0 ∧ -5/8 ≤ u ∧ u ≤ 2 ∧ -3/4 ≤ v ∧ v ≤ 3 ∧ -5/8 ≤ u+v

theorem scNearGap_of_parameterGrid
    (hgrid : ∀ c ∈ scParameterGrid, ∀ ij ∈ sideRowGrid,
      SideConeOn c (sideURange ij.1) (sideVRange ij.2))
    {a b η : ℝ} {z : Row} (ha : 0 ≤ a) (ha₁ : a ≤ 1/40)
    (hb : b ≤ 1-a-b) (hab : 1/5 ≤ a+b) (hη : 0 ≤ η) (hη₁ : η ≤ 1/6)
    (hz : InSideNearCone z) : 0 ≤ parameterGap criticalQ z a b η := by
  have hb₁ : b ≤ 1/2 := by linarith only [ha,hb]
  obtain ⟨c,hc,hp⟩ := scParameterGrid_cover ha ha₁ hb₁ hab hη hη₁
  obtain ⟨hnz,hu₀,hu₁,hv₀,hv₁,hcut⟩ := hz
  have hq : 1 < criticalQ := by linarith only [criticalQ_bracket.1]
  exact parameterGap_of_near_ratios hq hnz
    (sideConeOn_of_rowGrid (hgrid c hc) hp hu₀ hu₁ hv₀ hv₁ hcut)

end

end HlawkaSchatten.BelowExponent.Vertex
