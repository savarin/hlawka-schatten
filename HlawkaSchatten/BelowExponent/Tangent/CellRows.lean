/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Tangent.Rectangle
public import HlawkaSchatten.BelowExponent.Tangent.Coefficients

/-! Assemble the three checked row faces of an E2 cell and interpolate its profile vertices. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Tangent

def cellFace (H : TC.Hdr) (G : TC.Geom) (D : TC.CellData) (j : Fin 3) : TC.Face :=
  TC.mkFace (TC.mkCtx H) (TC.cellVerts G).1 (TC.cellVerts G).2 D.p D.g j.val
    (chartA j).val (chartB j).val

/-- Common arithmetic at the profile vertices implies the full real theorem throughout the cell. -/
theorem rowAt_of_cell_tangents {H : TC.Hdr} {G : TC.Geom} {D : TC.CellData} {q : ℝ}
    (hq : 1 ≤ q) (hcell : TC.cellOK H G D = true)
    (htan : ∀ code x, rowTangent (TC.mkCtx H) code x ≤ |x|^q)
    (hc : ∀ v ∈ (TC.cellVerts G).1, ∀ j : Fin 3,
      CornerSound q (TC.mkCtx H) (cellFace H G D j) j (vertex (TC.cellVerts G).2 v)
        (profileWeight H D) (rowWeight H D)) {t : Profile} (ht : t ∈ cellSet G) :
    RowAt q t := by
  have hD : 0 < (TC.mkCtx H).Da := by
    change 0 < 2 ^ H.KBOX
    positivity
  obtain ⟨hπ, hγ, _⟩ := weights_of_cellOK hcell
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, f₀, f₁, f₂⟩ := TC.cellOK_spec H G D hcell
  have cover (j : Fin 3) : TC.BoxCover (TC.LeafP (TC.mkCtx H) (cellFace H G D j))
      0 (2*(TC.mkCtx H).Da) 0 (2*(TC.mkCtx H).Da) := by
    fin_cases j
    · exact f₀
    · exact f₁
    · exact f₂
  apply rowAt_of_cell_vertices hcell hq _ ht
  intro v hv x
  apply weightedRow_of_chart_squares (lt_of_lt_of_le zero_lt_one hq) _ x
  intro j a b ha hb
  obtain ⟨A, hA, rfl⟩ := signed_coord_to_offset hD ha
  obtain ⟨B, hB, rfl⟩ := signed_coord_to_offset hD hb
  apply weightedRow_of_face_cover hq hD hπ.1 hγ htan (hc v hv j) (cover j)
  · exact_mod_cast hA
  · exact_mod_cast hB

theorem cellDen_pos_of_geomOK {G : TC.Geom} (hg : TC.geomOK G = true) :
    0 < (TC.cellVerts G).2 := by
  simp only [TC.geomOK, Bool.and_eq_true, TC.blt_true] at hg
  obtain ⟨⟨⟨⟨⟨⟨_, db⟩, dl⟩, dr⟩, _⟩, _⟩, _⟩ := hg
  change 0 < 4 * G.Db * G.l1d * G.l2d
  positivity

/-- A passing cell and its power table imply all physical real rows on its convex hull. -/
theorem rowAt_of_cellOK {H : TC.Hdr} {G : TC.Geom} {D : TC.CellData}
    (hT : TC.tabOK H.prof H.tab = true) (hk : 0 < H.prof.k1 ∧ 0 < H.prof.k2)
    (hc : TC.cellOK H G D = true) {t : Profile} (ht : t ∈ cellSet G) : RowAt criticalQ t := by
  apply rowAt_of_cell_tangents ((by norm_num : (1:ℝ) ≤ 1054/665).trans criticalQ_bracket.1.le)
    hc (rowTangent_le_rpow hT hk) _ ht
  obtain ⟨_, _, _, _, _, _, _, hp, _, hw, _, _, hg, _⟩ := TC.cellOK_spec H G D hc
  intro v hv j
  exact cornerSound_mkFace hT hk j hv (cellDen_pos_of_geomOK hg) hw (by simp [hp])

end HlawkaSchatten.BelowExponent.Tangent
