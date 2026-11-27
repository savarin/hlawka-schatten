/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.SideConeBounds

/-! The 954 signed row rectangles that cover the closed SC near cone. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

def sideUNodes : Vector ℚ 28 := #v[-5/8, -1/2, -3/8, -1/4, -1/8, -1/16, -1/32, -1/64,
  0, 1/64, 1/32, 1/16, 1/8, 1/4, 3/8, 1/2, 5/8, 3/4, 7/8, 1, 9/8, 5/4,
  11/8, 3/2, 13/8, 7/4, 15/8, 2]

def sideVNodes : Vector ℚ 37 := #v[-3/4, -5/8, -1/2, -3/8, -1/4, -1/8, -1/16, -1/32,
  -1/64, 0, 1/64, 1/32, 1/16, 1/8, 1/4, 3/8, 1/2, 5/8, 3/4, 7/8, 1, 9/8, 5/4,
  11/8, 3/2, 13/8, 7/4, 15/8, 2, 17/8, 9/4, 19/8, 5/2, 21/8, 11/4, 23/8, 3]

def sideRowInterval {n : ℕ} (nodes : Vector ℚ (n+1)) (i : Fin n) : RatBounds :=
  ⟨nodes.get i.castSucc, nodes.get i.succ⟩

def sideURange := sideRowInterval sideUNodes
def sideVRange := sideRowInterval sideVNodes

def sideKeepRow (i : Fin 27) (j : Fin 36) : Bool :=
  decide (-5/8 < (sideURange i).hi + (sideVRange j).hi)

def sideRowGrid : List (Fin 27 × Fin 36) :=
  ((List.finRange 27).flatMap fun i => (List.finRange 36).map fun j => (i,j)).filter
    (fun ij => sideKeepRow ij.1 ij.2)

theorem sideRowGrid_length : sideRowGrid.length = 954 := by decide +kernel

private theorem adjacent_strict (f : ℕ → ℝ) (x : ℝ) (h₀ : f 0 ≤ x) (n : ℕ)
    (hn : x < f (n+1)) : ∃ i ≤ n, f i ≤ x ∧ x < f (i+1) := by
  induction n with
  | zero => exact ⟨0, le_rfl, h₀, hn⟩
  | succ n ih =>
    rcases lt_or_ge x (f (n+1)) with h | h
    · obtain ⟨i, hi, hlo, hhi⟩ := ih h
      exact ⟨i, hi.trans (Nat.le_succ n), hlo, hhi⟩
    · exact ⟨n+1, le_rfl, h, hn⟩

private theorem sideRowInterval_cover {n : ℕ} (nodes : Vector ℚ (n+2)) (x : ℝ)
    (h₀ : (nodes.get 0 : ℝ) ≤ x) (h₁ : x ≤ (nodes.get (Fin.last (n+1)) : ℝ))
    (hlast : nodes.get (Fin.last n).castSucc ≤ nodes.get (Fin.last (n+1))) :
    ∃ i : Fin (n+1), (sideRowInterval nodes i).Contains x ∧
      (x < (nodes.get (Fin.last (n+1)) : ℝ) → x < ((sideRowInterval nodes i).hi : ℝ)) := by
  obtain heq | hlt := h₁.eq_or_lt
  · refine ⟨Fin.last n, ⟨?_, h₁⟩, fun h => False.elim (h.ne heq)⟩
    have hlastR : (nodes.get (Fin.last n).castSucc : ℝ) ≤ nodes.get (Fin.last (n+1)) := by
      exact_mod_cast hlast
    exact hlastR.trans_eq heq.symm
  · let f (k : ℕ) : ℝ := if hk : k < n+2 then (nodes.get ⟨k,hk⟩ : ℝ) else 0
    have hfirst : f 0 ≤ x := by
      rw [show f 0 = (nodes.get 0 : ℝ) by simp only [f, dite_eq_left (by omega : 0 < n+2)]; rfl]
      exact h₀
    have hfinal : x < f (n+1) := by
      rw [show f (n+1) = (nodes.get (Fin.last (n+1)) : ℝ) by
        simp only [f, dite_eq_left (by omega : n+1 < n+2)]; rfl]
      exact hlt
    obtain ⟨i, hi, hlo, hhi⟩ := adjacent_strict f x hfirst n hfinal
    have i_lt : i < n+1 := Nat.lt_succ_of_le hi
    have i0 : i < n+2 := by omega
    have i1 : i+1 < n+2 := by omega
    have e0 : (⟨i, i0⟩ : Fin (n+2)) = (⟨i, i_lt⟩ : Fin (n+1)).castSucc := by
      apply Fin.ext
      rfl
    have e1 : (⟨i+1, i1⟩ : Fin (n+2)) = (⟨i, i_lt⟩ : Fin (n+1)).succ := by
      apply Fin.ext
      rfl
    refine ⟨⟨i, i_lt⟩, ⟨?_, ?_⟩, fun _ => ?_⟩
    · simpa only [f, dite_eq_left i0, sideRowInterval, e0] using hlo
    · simpa only [f, dite_eq_left i1, sideRowInterval, e1] using hhi.le
    · simpa only [f, dite_eq_left i1, sideRowInterval, e1] using hhi

theorem sideRowGrid_cover {u v : ℝ} (hu₀ : -5/8 ≤ u) (hu₁ : u ≤ 2)
    (hv₀ : -3/4 ≤ v) (hv₁ : v ≤ 3) (hcut : -5/8 ≤ u+v) :
    ∃ ij ∈ sideRowGrid, (sideURange ij.1).Contains u ∧ (sideVRange ij.2).Contains v := by
  have uminQ : sideUNodes.get 0 = -5/8 := by decide +kernel
  have umaxQ : sideUNodes.get (Fin.last 27) = 2 := by decide +kernel
  have vminQ : sideVNodes.get 0 = -3/4 := by decide +kernel
  have vmaxQ : sideVNodes.get (Fin.last 36) = 3 := by decide +kernel
  have hu0 : (sideUNodes.get 0 : ℝ) ≤ u := by simpa only [uminQ, Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using hu₀
  have hu1 : u ≤ (sideUNodes.get (Fin.last 27) : ℝ) := by simpa only [umaxQ, Rat.cast_ofNat] using hu₁
  have hv0 : (sideVNodes.get 0 : ℝ) ≤ v := by simpa only [vminQ, Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using hv₀
  have hv1 : v ≤ (sideVNodes.get (Fin.last 36) : ℝ) := by simpa only [vmaxQ, Rat.cast_ofNat] using hv₁
  obtain ⟨i, hi, hip⟩ := sideRowInterval_cover sideUNodes u hu0 hu1 (by decide +kernel)
  obtain ⟨j, hj, hjp⟩ := sideRowInterval_cover sideVNodes v hv0 hv1 (by decide +kernel)
  have hret : (-5/8 : ℝ) < ((sideURange i).hi : ℝ) + ((sideVRange j).hi : ℝ) := by
    rcases hu1.eq_or_lt with he | he
    · rcases hv1.eq_or_lt with hf | hf
      · have heq : u = 2 := by simpa only [umaxQ, Rat.cast_ofNat] using he
        have hfq : v = 3 := by simpa only [vmaxQ, Rat.cast_ofNat] using hf
        have hu : u ≤ ((sideURange i).hi : ℝ) := hi.2
        have hv : v ≤ ((sideVRange j).hi : ℝ) := hj.2
        linarith only [hu, hv, heq, hfq]
      · exact hcut.trans_lt (add_lt_add_of_le_of_lt hi.2 (hjp hf))
    · exact hcut.trans_lt (add_lt_add_of_lt_of_le (hip he) hj.2)
  have hqr : (-5/8 : ℚ) < (sideURange i).hi + (sideVRange j).hi := by exact_mod_cast hret
  refine ⟨(i,j), List.mem_filter.mpr ⟨?_, decide_eq_true hqr⟩, hi, hj⟩
  exact List.mem_flatMap.mpr ⟨i, by simp, List.mem_map.mpr ⟨j, by simp, rfl⟩⟩

end HlawkaSchatten.BelowExponent.Vertex
