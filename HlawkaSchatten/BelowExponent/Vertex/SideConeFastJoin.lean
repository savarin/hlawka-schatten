/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.SideConeJoin
public import HlawkaSchatten.BelowExponent.Vertex.SideConeFastTree

/-! Assemble cell certificates on the original closed SC parameter grid. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

structure SideFastCellCertificate where
  cell : ParameterCell
  rows : ∀ row ∈ sideRowGrid, SideConeOn cell (sideURange row.1) (sideVRange row.2)

theorem sideFastFamily_sound {family : List SideFastCellCertificate}
    (hmatch : family.map SideFastCellCertificate.cell = scParameterGrid) :
    ∀ c ∈ scParameterGrid, ∀ row ∈ sideRowGrid, SideConeOn c (sideURange row.1) (sideVRange row.2) := by
  intro c hc
  rw [← hmatch] at hc
  obtain ⟨P, _, hp⟩ := List.mem_map.mp hc
  subst c
  exact P.rows

theorem sideFastCone_sound {family : List SideFastCellCertificate}
    (hmatch : family.map SideFastCellCertificate.cell = scParameterGrid)
    {a b η : ℝ} {z : Row} (ha : 0 ≤ a) (ha₁ : a ≤ 1/40)
    (hb : b ≤ 1-a-b) (hab : 1/5 ≤ a+b) (hη : 0 ≤ η) (hη₁ : η ≤ 1/6)
    (hz : InSideNearCone z) : 0 ≤ parameterGap criticalQ z a b η :=
  scNearGap_of_parameterGrid (sideFastFamily_sound hmatch) ha ha₁ hb hab hη hη₁ hz

theorem sideFastCover_sound {family : List SideFastCellCertificate}
    (hcover : scParameterGrid.all (fun c => family.any (fun P => c.containedIn P.cell)) = true) :
    ∀ c ∈ scParameterGrid, ∀ row ∈ sideRowGrid, SideConeOn c (sideURange row.1) (sideVRange row.2) := by
  intro c hc row hr a b η u v hp hu hv
  obtain ⟨P, _, hP⟩ := List.any_eq_true.mp (List.all_eq_true.mp hcover c hc)
  exact P.rows row hr (ParameterCell.containedIn_sound hP hp) hu hv

end HlawkaSchatten.BelowExponent.Vertex
