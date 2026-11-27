/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Tangent.Real
import HlawkaSchatten.BelowExponent.BulkGeometry
import Mathlib.Data.List.GetD

/-! Real barycentric coordinates for a checked truncated cone cell. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Tangent

open Set

noncomputable section

/-- The geometry needed to interpret the integer vertex list as a truncated cone. -/
structure CellGeometry (G : TC.Geom) : Prop where
  length_base : G.b.length = 3
  base_pos : 0 < G.Db
  lower_pos : 0 < G.l1d
  upper_pos : 0 < G.l2d
  ordered : G.l1n * G.l2d ≤ G.l2n * G.l1d
  upper_le_one : G.l2n ≤ G.l2d

theorem CellGeometry.vertexDen_pos {G : TC.Geom} (h : CellGeometry G) : 0 < (TC.cellVerts G).2 := by
  change 0 < 4 * G.Db * G.l1d * G.l2d
  exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) h.base_pos) h.lower_pos) h.upper_pos

def lowerLevel (G : TC.Geom) : ℝ := (G.l1n : ℝ) / G.l1d

def upperLevel (G : TC.Geom) : ℝ := (G.l2n : ℝ) / G.l2d

theorem CellGeometry.level_order {G : TC.Geom} (h : CellGeometry G) : lowerLevel G ≤ upperLevel G := by
  have h₀ : (0 : ℝ) < G.l1d := by exact_mod_cast h.lower_pos
  have h₁ : (0 : ℝ) < G.l2d := by exact_mod_cast h.upper_pos
  exact (div_le_div_iff₀ h₀ h₁).2 (by exact_mod_cast h.ordered)

private theorem CellGeometry.lower_le_one {G : TC.Geom} (h : CellGeometry G) : G.l1n ≤ G.l1d := by
  have h₀ : (0 : ℝ) < G.l1d := by exact_mod_cast h.lower_pos
  have h₁ : (0 : ℝ) < G.l2d := by exact_mod_cast h.upper_pos
  have hUpper : upperLevel G ≤ 1 := (div_le_one₀ h₁).2 (by exact_mod_cast h.upper_le_one)
  have hLower := (div_le_one₀ h₀).1 (h.level_order.trans hUpper)
  exact_mod_cast hLower

def basePoint (den : ℕ) (b : TC.P3) : Profile :=
  ![(b.1 : ℝ) / den, (b.2.1 : ℝ) / den, (b.2.2 : ℝ) / den, 0]

def cellBase (G : TC.Geom) (i : Fin 3) : Profile := basePoint G.Db (G.b.getD i.val (0, 0, 0))

private def radialPoint (r : ℝ) (b : Profile) : Profile := (1 - r) • centerProfile + r • b

private theorem vertex_vtx {Db o d n : ℕ} (hDb : 0 < Db) (ho : 0 < o) (hd : 0 < d) (hn : n ≤ d)
    (b : TC.P3) : vertex (4 * Db * o * d) (TC.vtx Db o d n b) = radialPoint ((n : ℝ) / d) (basePoint Db b) := by
  have hDb' : (Db : ℝ) ≠ 0 := by exact_mod_cast hDb.ne'
  have ho' : (o : ℝ) ≠ 0 := by exact_mod_cast ho.ne'
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  funext j
  fin_cases j <;>
    simp [vertex, TC.vtx, radialPoint, basePoint, centerProfile, Nat.cast_sub hn, smul_eq_mul] <;>
    field_simp [hDb', ho', hd']

private theorem lowerVtx_eq {G : TC.Geom} (h : CellGeometry G) (b : TC.P3) :
    vertex (TC.cellVerts G).2 (TC.vtx G.Db G.l2d G.l1d G.l1n b) = radialPoint (lowerLevel G) (basePoint G.Db b) := by
  change vertex (4 * G.Db * G.l1d * G.l2d) _ = _
  rw [mul_right_comm (4 * G.Db)]
  exact vertex_vtx h.base_pos h.upper_pos h.lower_pos h.lower_le_one b

private theorem upperVtx_eq {G : TC.Geom} (h : CellGeometry G) (b : TC.P3) :
    vertex (TC.cellVerts G).2 (TC.vtx G.Db G.l1d G.l2d G.l2n b) = radialPoint (upperLevel G) (basePoint G.Db b) :=
  vertex_vtx h.base_pos h.lower_pos h.upper_pos h.upper_le_one b

private theorem baseGetD_mem {G : TC.Geom} (hG : CellGeometry G) (i : Fin 3) :
    G.b.getD i.val (0, 0, 0) ∈ G.b := by
  have hi : i.val < G.b.length := hG.length_base.symm ▸ i.isLt
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem _

private theorem baseGetD_of_mem {G : TC.Geom} (hG : CellGeometry G) {b : TC.P3} (hb : b ∈ G.b) :
    ∃ i : Fin 3, G.b.getD i.val (0, 0, 0) = b := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hb
  refine ⟨⟨i, hG.length_base ▸ hi⟩, ?_⟩
  exact List.getD_eq_getElem _ _ hi

private theorem lowerPoint_mem {G : TC.Geom} (hG : CellGeometry G) (i : Fin 3) :
    radialPoint (lowerLevel G) (cellBase G i) ∈ cellSet G := by
  apply subset_convexHull ℝ _
  by_cases h : G.l1n = 0
  · refine ⟨TC.vtx G.Db G.l2d G.l1d G.l1n (0, 0, 0), ?_, ?_⟩
    · simp [TC.cellVerts, h]
    · rw [lowerVtx_eq hG]
      simp [lowerLevel, h, radialPoint]
  · let b := G.b.getD i.val (0, 0, 0)
    refine ⟨TC.vtx G.Db G.l2d G.l1d G.l1n b, ?_, (lowerVtx_eq hG b).symm⟩
    exact List.mem_append_left _ (by simpa only [TC.cellVerts, ite_eq_right h] using
      (List.mem_map_of_mem (f := TC.vtx G.Db G.l2d G.l1d G.l1n) (baseGetD_mem hG i)))

private theorem upperPoint_mem {G : TC.Geom} (hG : CellGeometry G) (i : Fin 3) :
    radialPoint (upperLevel G) (cellBase G i) ∈ cellSet G := by
  apply subset_convexHull ℝ _
  let b := G.b.getD i.val (0, 0, 0)
  refine ⟨TC.vtx G.Db G.l1d G.l2d G.l2n b,
    List.mem_append_right _ (List.mem_map_of_mem (baseGetD_mem hG i)), (upperVtx_eq hG b).symm⟩

private theorem vertex_endpoint {G : TC.Geom} (hG : CellGeometry G) {v : TC.V4} (hv : v ∈ (TC.cellVerts G).1) :
    ∃ i : Fin 3, vertex (TC.cellVerts G).2 v = radialPoint (lowerLevel G) (cellBase G i) ∨
      vertex (TC.cellVerts G).2 v = radialPoint (upperLevel G) (cellBase G i) := by
  simp only [TC.cellVerts, List.mem_append] at hv
  rcases hv with hv | hv
  · by_cases h : G.l1n = 0
    · rw [ite_eq_left h, List.mem_singleton] at hv
      refine ⟨0, Or.inl ?_⟩
      rw [hv, ← h, lowerVtx_eq hG]
      simp [lowerLevel, h, radialPoint]
    · rw [ite_eq_right h, List.mem_map] at hv
      obtain ⟨b, hb, rfl⟩ := hv
      obtain ⟨i, hi⟩ := baseGetD_of_mem hG hb
      exact ⟨i, Or.inl (by rw [lowerVtx_eq hG, cellBase, hi])⟩
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hv
    obtain ⟨i, hi⟩ := baseGetD_of_mem hG hb
    exact ⟨i, Or.inr (by rw [upperVtx_eq hG, cellBase, hi])⟩

/-- Cone coefficients attach each nonnegative mass directly to its base vertex.
Their sum is the radial coordinate. This representation includes the apex. -/
def coneSum (B : Fin 3 → Profile) (w : Row) : Profile :=
  (1 - ∑ i, w i) • centerProfile + ∑ i, w i • B i

private theorem coneSum_combo (B : Fin 3 → Profile) (x y : Row) {a b : ℝ} (hab : a + b = 1) :
    coneSum B (fun i => a * x i + b * y i) = a • coneSum B x + b • coneSum B y := by
  have hb : b = 1 - a := by linarith only [hab]
  funext j
  simp only [coneSum, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hb]
  ring

private theorem coneSum_single (B : Fin 3 → Profile) (i : Fin 3) (r : ℝ) :
    coneSum B (fun j => if j = i then r else 0) = radialPoint r (B i) := by
  funext j
  fin_cases i <;> norm_num [coneSum, radialPoint, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

private theorem coneSum_scaled (B : Fin 3 → Profile) {w : Row} (hw : ∑ i, w i = 1) (r : ℝ) :
    coneSum B (fun i => r * w i) = ∑ i, w i • radialPoint r (B i) := by
  have hs : w 0 + w 1 + w 2 = 1 := by simpa only [Fin.sum_univ_three] using hw
  have h₂ : w 2 = 1 - w 0 - w 1 := by linarith only [hs]
  funext j
  simp only [coneSum, radialPoint, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [h₂]
  ring

private def coneSet (G : TC.Geom) : Set Profile :=
  {t | ∃ w : Row, (∀ i, 0 ≤ w i) ∧ (∑ i, w i) ∈ Icc (lowerLevel G) (upperLevel G) ∧
    t = coneSum (cellBase G) w}

private theorem coneSet_convex (G : TC.Geom) : Convex ℝ (coneSet G) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨u, hu, hU, rfl⟩ := hx
  obtain ⟨v, hv, hV, rfl⟩ := hy
  refine ⟨fun i => a * u i + b * v i, fun i => add_nonneg (mul_nonneg ha (hu i)) (mul_nonneg hb (hv i)),
    ?_, (coneSum_combo (cellBase G) u v hab).symm⟩
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  exact (convex_Icc (lowerLevel G) (upperLevel G)) hU hV ha hb hab

private theorem cellSet_subset_coneSet {G : TC.Geom} (hG : CellGeometry G) : cellSet G ⊆ coneSet G := by
  apply convexHull_min _ (coneSet_convex G)
  rintro _ ⟨v, hv, rfl⟩
  obtain ⟨i, h | h⟩ := vertex_endpoint hG hv
  · refine ⟨fun j => if j = i then lowerLevel G else 0, ?_, ?_, h.trans (coneSum_single _ _ _).symm⟩
    · intro j
      change 0 ≤ if j = i then lowerLevel G else 0
      split
      · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      · exact le_rfl
    · simpa using (show lowerLevel G ∈ Icc (lowerLevel G) (upperLevel G) from ⟨le_rfl, hG.level_order⟩)
  · refine ⟨fun j => if j = i then upperLevel G else 0, ?_, ?_, h.trans (coneSum_single _ _ _).symm⟩
    · intro j
      change 0 ≤ if j = i then upperLevel G else 0
      split
      · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      · exact le_rfl
    · simpa using (show upperLevel G ∈ Icc (lowerLevel G) (upperLevel G) from ⟨hG.level_order, le_rfl⟩)

private theorem coneSet_subset_cellSet {G : TC.Geom} (hG : CellGeometry G) : coneSet G ⊆ cellSet G := by
  rintro _ ⟨w, hw, ⟨hlo, hhi⟩, rfl⟩
  have hConv : Convex ℝ (cellSet G) := convex_convexHull ℝ _
  let mass := ∑ i, w i
  have hmass : 0 ≤ mass := Finset.sum_nonneg fun i _ => hw i
  rcases eq_or_lt_of_le hmass with hzero | hpos
  · have hw₀ (i : Fin 3) : w i = 0 := by
      have h := Finset.single_le_sum (f := w) (fun i _ => hw i) (Finset.mem_univ i)
      have hz : (∑ i, w i) = 0 := hzero.symm
      linarith only [h, hz, hw i]
    have hl₀ : 0 ≤ lowerLevel G := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hl : lowerLevel G = 0 := le_antisymm (hlo.trans hzero.symm.le) hl₀
    simpa [coneSum, hw₀, hl, radialPoint] using lowerPoint_mem hG 0
  · let u : Row := fun i => w i / mass
    have hu : ∀ i, 0 ≤ u i := fun i => div_nonneg (hw i) hmass
    have hsum : ∑ i, u i = 1 := by
      change ∑ i, w i / mass = 1
      rw [← Finset.sum_div, div_self hpos.ne']
    have hLower : coneSum (cellBase G) (fun i => lowerLevel G * u i) ∈ cellSet G := by
      rw [coneSum_scaled _ hsum]
      exact hConv.sum_mem (fun i _ => hu i) hsum (fun i _ => lowerPoint_mem hG i)
    have hUpper : coneSum (cellBase G) (fun i => upperLevel G * u i) ∈ cellSet G := by
      rw [coneSum_scaled _ hsum]
      exact hConv.sum_mem (fun i _ => hu i) hsum (fun i _ => upperPoint_mem hG i)
    obtain ⟨a, ha, hg⟩ := exists_interval_lerp (x := mass) hlo hhi
    have hw' : w = fun i => (1 - a) * (lowerLevel G * u i) + a * (upperLevel G * u i) := by
      funext i
      calc
        w i = mass * u i := (mul_div_cancel₀ _ hpos.ne').symm
        _ = _ := by rw [hg]; ring
    rw [hw', coneSum_combo _ _ _ (sub_add_cancel 1 a)]
    exact hConv hLower hUpper (sub_nonneg.mpr ha.2) ha.1 (sub_add_cancel 1 a)

/-- The real hull of the integer vertices is precisely the radial band of nonnegative base masses. -/
theorem mem_cellSet_iff_coefficients {G : TC.Geom} (hG : CellGeometry G) {t : Profile} :
    t ∈ cellSet G ↔ ∃ w : Row, (∀ i, 0 ≤ w i) ∧ (∑ i, w i) ∈ Icc (lowerLevel G) (upperLevel G) ∧
      t = coneSum (cellBase G) w := by
  change t ∈ cellSet G ↔ t ∈ coneSet G
  exact ⟨fun h => cellSet_subset_coneSet hG h, fun h => coneSet_subset_cellSet hG h⟩

end

end HlawkaSchatten.BelowExponent.Tangent
