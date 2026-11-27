/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Tangent.CellGeometry
import Mathlib.Data.List.GetD

/-! Each successful radial or tangential split covers the parent hull by two closed child hulls. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Tangent

noncomputable section

theorem radialSplit_cover {G : TC.Geom} (hG : CellGeometry G) {p q : ℕ} (hq : 0 < q)
    (hl : G.l1n * q < p * G.l1d) (hr : p * G.l2d < G.l2n * q) :
    let L := { G with l2n := p, l2d := q }
    let R := { G with l1n := p, l1d := q }
    CellGeometry L ∧ CellGeometry R ∧ cellSet G ⊆ cellSet L ∪ cellSet R := by
  intro L R
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hG₂ : (0 : ℝ) < G.l2d := by exact_mod_cast hG.upper_pos
  have hRight : (p : ℝ) / q ≤ upperLevel G := (div_le_div_iff₀ hq' hG₂).2 (by exact_mod_cast hr.le)
  have hOne : upperLevel G ≤ 1 := (div_le_one₀ hG₂).2 (by exact_mod_cast hG.upper_le_one)
  have hpq : p ≤ q := by exact_mod_cast (div_le_one₀ hq').1 (hRight.trans hOne)
  have hL : CellGeometry L := ⟨hG.length_base, hG.base_pos, hG.lower_pos, hq, hl.le, hpq⟩
  have hR : CellGeometry R := ⟨hG.length_base, hG.base_pos, hq, hG.upper_pos, hr.le, hG.upper_le_one⟩
  refine ⟨hL, hR, ?_⟩
  intro t ht
  obtain ⟨w, hw, hmass, hrepr⟩ := (mem_cellSet_iff_coefficients hG).1 ht
  rcases le_total (∑ i, w i) ((p : ℝ) / q) with h | h
  · exact Or.inl ((mem_cellSet_iff_coefficients hL).2 ⟨w, hw, ⟨hmass.1, h⟩, hrepr⟩)
  · exact Or.inr ((mem_cellSet_iff_coefficients hR).2 ⟨w, hw, ⟨h, hmass.2⟩, hrepr⟩)

private theorem basePoint_double {d : ℕ} (hd : 0 < d) (b : TC.P3) :
    basePoint (2 * d) (TC.p3dbl b) = basePoint d b := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  funext k
  fin_cases k <;> norm_num [basePoint, TC.p3dbl, Nat.cast_mul] <;> field_simp

private theorem basePoint_midpoint {d : ℕ} (hd : 0 < d) (a b : TC.P3) :
    basePoint (2 * d) (TC.p3add a b) = (1 / 2 : ℝ) • (basePoint d a + basePoint d b) := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  funext k
  fin_cases k <;> norm_num [basePoint, TC.p3add, Nat.cast_add, Nat.cast_mul, smul_eq_mul] <;> field_simp

private theorem p3double_half {b : TC.P3} (hb : TC.p3even b = true) : TC.p3dbl (TC.p3half b) = b := by
  obtain ⟨a, b, c⟩ := b
  simp only [TC.p3even, Bool.and_eq_true, beq_iff_eq] at hb
  simp only [TC.p3dbl, TC.p3half, Prod.mk.injEq]
  exact ⟨by omega, by omega, by omega⟩

private theorem getD_set_base {l : List TC.P3} {i j : ℕ} (hj : j < l.length) (b : TC.P3) :
    (l.set i b).getD j (0, 0, 0) = if j = i then b else l.getD j (0, 0, 0) := by
  have hj' : j < (l.set i b).length := by simpa only [List.length_set] using hj
  rw [List.getD_eq_getElem _ _ hj', List.getD_eq_getElem _ _ hj, List.getElem_set]
  simp [eq_comm]

private def tangentialChild (G : TC.Geom) (i : ℕ) (mid : TC.P3) : TC.Geom :=
  let even := TC.p3even mid
  let W := if even then G.b else G.b.map TC.p3dbl
  let m := if even then TC.p3half mid else mid
  let Db := if even then G.Db else 2 * G.Db
  { G with b := TC.setAt W i m, Db := Db }

private theorem tangentialChild_geometry {G : TC.Geom} (hG : CellGeometry G) (i : ℕ) (m : TC.P3) :
    CellGeometry (tangentialChild G i m) := by
  constructor
  · simp only [tangentialChild, TC.setAt, List.length_set]
    split <;> simp [hG.length_base]
  · simp only [tangentialChild]
    split
    · exact hG.base_pos
    · exact Nat.mul_pos (by decide) hG.base_pos
  · exact hG.lower_pos
  · exact hG.upper_pos
  · exact hG.ordered
  · exact hG.upper_le_one

private theorem tangentialChild_base {G : TC.Geom} (hG : CellGeometry G) (i j : Fin 3) :
    let mid := TC.p3add (G.b.getD i.val (0, 0, 0)) (G.b.getD j.val (0, 0, 0))
    cellBase (tangentialChild G i.val mid) =
      Function.update (cellBase G) i ((1 / 2 : ℝ) • (cellBase G i + cellBase G j)) := by
  intro mid
  let even := TC.p3even mid
  let W := if even then G.b else G.b.map TC.p3dbl
  let m := if even then TC.p3half mid else mid
  let d := if even then G.Db else 2 * G.Db
  have hW : W.length = 3 := by dsimp [W]; split <;> simp [hG.length_base]
  have hscale (k : Fin 3) : basePoint d (W.getD k.val (0, 0, 0)) = cellBase G k := by
    by_cases h : even = true
    · simp [d, W, h, cellBase]
    · have hm : (G.b.map TC.p3dbl).getD k.val (0, 0, 0) = TC.p3dbl (G.b.getD k.val (0, 0, 0)) :=
        List.getD_map G.b (0, 0, 0) TC.p3dbl
      simpa only [d, W, ite_eq_right h, hm, cellBase] using
        basePoint_double hG.base_pos (G.b.getD k.val (0, 0, 0))
  have hmid : basePoint d m = (1 / 2 : ℝ) • (cellBase G i + cellBase G j) := by
    by_cases h : even = true
    · simp only [d, m, ite_eq_left h]
      rw [← basePoint_double hG.base_pos (TC.p3half mid), p3double_half h]
      exact basePoint_midpoint hG.base_pos _ _
    · simp only [d, m, ite_eq_right h]
      exact basePoint_midpoint hG.base_pos _ _
  funext k
  change basePoint d ((W.set i.val m).getD k.val (0, 0, 0)) = _
  rw [getD_set_base (hW.symm ▸ k.isLt)]
  by_cases hk : k = i
  · subst k
    rw [ite_eq_left (rfl : i.val = i.val), Function.update_self]
    exact hmid
  · have hk' : k.val ≠ i.val := fun h => hk (Fin.ext h)
    simpa only [ite_eq_right hk', Function.update_of_ne hk] using hscale k

private theorem p3add_comm (a b : TC.P3) : TC.p3add a b = TC.p3add b a := by simp [TC.p3add, Nat.add_comm]

private theorem reweight_midpoint {B : Fin 3 → Profile} {i j : Fin 3} (hne : i ≠ j)
    {w : Row} (hw : ∀ k, 0 ≤ w k) (hij : w i ≤ w j) :
    ∃ u : Row, (∀ k, 0 ≤ u k) ∧ (∑ k, u k) = ∑ k, w k ∧
      coneSum (Function.update B i ((1 / 2 : ℝ) • (B i + B j))) u = coneSum B w := by
  let u : Row := fun k => if k = i then 2 * w i else if k = j then w j - w i else w k
  have hsum : (∑ k, u k) = ∑ k, w k := by
    fin_cases i <;> fin_cases j <;> norm_num at hne
    all_goals (norm_num [u, Fin.sum_univ_three]; ring)
  refine ⟨u, ?_, hsum, ?_⟩
  · intro k
    by_cases hki : k = i
    · simp [u, hki, hw]
    by_cases hkj : k = j
    · subst k
      simp [u, hne.symm, sub_nonneg.mpr hij]
    · simp [u, hki, hkj, hw]
  · unfold coneSum
    rw [hsum]
    congr 1
    funext s
    fin_cases i <;> fin_cases j <;> norm_num at hne
    all_goals
      (norm_num [u, Function.update, Fin.sum_univ_three, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
       ring)

/-- A successful integer tangential split gives two admissible hulls whose union covers the original. -/
theorem tangentialSplit_cover {G L R : TC.Geom} (hG : CellGeometry G) {i j : ℕ}
    (hs : TC.tsplit G i j = some (L, R)) :
    CellGeometry L ∧ CellGeometry R ∧ cellSet G ⊆ cellSet L ∪ cellSet R := by
  unfold TC.tsplit at hs
  split at hs
  · rename_i hvalid
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, beq_iff_eq] at hvalid
    obtain ⟨⟨⟨hi, hj⟩, hne⟩, _⟩ := hvalid
    let I : Fin 3 := ⟨i, hi⟩
    let J : Fin 3 := ⟨j, hj⟩
    have hIJ : I ≠ J := fun h => hne (congrArg Fin.val h)
    let m := TC.p3add (G.b.getD i (0, 0, 0)) (G.b.getD j (0, 0, 0))
    change some (tangentialChild G i m, tangentialChild G j m) = some (L, R) at hs
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hs)
    have hL := tangentialChild_geometry hG i m
    have hR := tangentialChild_geometry hG j m
    have hBaseL : cellBase (tangentialChild G i m) =
        Function.update (cellBase G) I ((1 / 2 : ℝ) • (cellBase G I + cellBase G J)) :=
      tangentialChild_base hG I J
    have hBaseR : cellBase (tangentialChild G j m) =
        Function.update (cellBase G) J ((1 / 2 : ℝ) • (cellBase G J + cellBase G I)) := by
      dsimp only [m]
      rw [p3add_comm]
      exact tangentialChild_base hG J I
    refine ⟨hL, hR, ?_⟩
    intro t ht
    obtain ⟨w, hw, hmass, hrepr⟩ := (mem_cellSet_iff_coefficients hG).1 ht
    rcases le_total (w I) (w J) with h | h
    · obtain ⟨u, hu, hsum, he⟩ := reweight_midpoint (B := cellBase G) hIJ hw h
      refine Or.inl ((mem_cellSet_iff_coefficients hL).2 ⟨u, hu, ?_, ?_⟩)
      · rw [hsum]
        exact hmass
      · rw [hBaseL, he, hrepr]
    · obtain ⟨u, hu, hsum, he⟩ := reweight_midpoint (B := cellBase G) hIJ.symm hw h
      refine Or.inr ((mem_cellSet_iff_coefficients hR).2 ⟨u, hu, ?_, ?_⟩)
      · rw [hsum]
        exact hmass
      · rw [hBaseR, he, hrepr]
  · contradiction

end

end HlawkaSchatten.BelowExponent.Tangent
