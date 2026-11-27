/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.SideOuterCheck
public import HlawkaSchatten.BelowExponent.Vertex.OuterRowSound
public import HlawkaSchatten.BelowExponent.Vertex.SideCornerLinks

/-! Reflect the finite row checks at one shared SC parameter corner. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxHeartbeats 0 in
theorem scOuterSkips_eq : ∀ k i j, scOuterSkips k i j = outerSideSkip k i j := by decide +kernel

set_option maxHeartbeats 0 in
theorem scOuterAxes_eq : ∀ i e, scOuterAxes i e =
    outerAxisBounds i e (outerEndpointAbsQ i e) (outerEndpointSigned i e)
      (outerMidAbsQ i) (outerMidSigned i) (outerMidSlope i) := by decide +kernel

theorem scOuterAxes_encloses (i : Fin 34) (e : Bool) : (scOuterAxes i e).Encloses i e := by
  rw [scOuterAxes_eq]
  exact outerAxisBounds_encloses i e (outerEndpointAbsQ_sound i e) (outerEndpointSigned_sound i e)
    (outerMidAbsQ_sound i) (outerMidSigned_sound i) (outerMidSlope_sound i)

theorem scOuterPoint_of_faces {p : SideCornerEntry} {P : OuterPointBounds}
    (hp : P.Encloses (cornerRowCoefficients p.margin.get p.a p.b p.eta))
    (hfaces : ∀ k, scOuterFaceOK P k = true) : p.Valid := by
  intro z hz
  apply cornerMargin_of_sc_grid _ z hz
  intro k i j hkeep
  have hi : i ∈ List.finRange 34 := List.mem_finRange i
  have hj : j ∈ List.finRange 34 := List.mem_finRange j
  have hh := List.all_eq_true.mp (List.all_eq_true.mp (hfaces k) i hi) j hj
  simp only [scOuterSkips_eq, hkeep, Bool.false_or] at hh
  apply outerRectangle_of_checks hp k i j scOuterAxes_encloses (fun _ => outerRpowChordUpper_sound)
  intro x y
  have hm (e : Bool) : e ∈ [false,true] := by cases e <;> decide
  exact List.all_eq_true.mp (List.all_eq_true.mp hh x (hm x)) y (hm y)

theorem scOuterPoint_of_checked_bounds {p : SideCornerEntry} {P : OuterPointBounds}
    {roots : Fin 3 → RatBounds} (hr : p.cell.rootsOK roots = true)
    (hp : P = .atPoint p.a p.b p.eta p.margin roots)
    (hfaces : ∀ k, scOuterFaceOK P k = true) : p.Valid :=
  scOuterPoint_of_faces (hp.symm ▸ OuterPointBounds.atPoint_encloses p.a p.b p.eta p.margin roots hr) hfaces

end HlawkaSchatten.BelowExponent.Vertex
