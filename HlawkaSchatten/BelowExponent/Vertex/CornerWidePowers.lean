/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CornerWidePowerValues
public import HlawkaSchatten.BelowExponent.Vertex.CornerPowers

/-! Sound power enclosures for every half-grid point needed by the coarse rectangles. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem outerWideAxisQTable_ok :
    (List.range 513).all (fun i => outerAbsQOK (outerWideAxisNode i) (outerWideAxisSample i)) = true :=
  by decide +kernel

theorem outerWideAxisQAt_sound {x : ℚ} (hx : outerWideAxisReady x = true) :
    (outerWideAxisQAt x).Contains (|(x : ℝ)|^criticalQ) := by
  obtain ⟨hi, he⟩ := of_decide_eq_true hx
  have hh := List.all_eq_true.mp outerWideAxisQTable_ok (outerWideAxisIndex x)
    (List.mem_range.mpr (by omega : outerWideAxisIndex x < 513))
  have hcast : (outerWideAxisNode (outerWideAxisIndex x) : ℝ) = |(x : ℝ)| := by
    rw [he, Rat.cast_abs]
  simpa only [outerWideAxisQAt, hcast, abs_abs] using (outerAbsQOK_sound hh)

theorem outerWideAxisReady_node (i : Fin 35) : outerWideAxisReady (outerNodes.get i) = true :=
  (by decide +kernel : ∀ j : Fin 35, outerWideAxisReady (outerNodes.get j) = true) i

set_option maxHeartbeats 0 in
theorem outerWideAxisReady_midpoint (i j : Fin 35) :
    outerWideAxisReady ((outerNodes.get i + outerNodes.get j)/2) = true :=
  (by decide +kernel : ∀ i j : Fin 35,
    outerWideAxisReady ((outerNodes.get i + outerNodes.get j)/2) = true) i j

theorem outerWideAxis_abs_sound {x : ℚ} (hx : outerWideAxisReady x = true) :
    (DyadicBounds.ofRat (outerWideAxisQAt x)).Contains (|(x : ℝ)|^criticalQ) :=
  DyadicBounds.ofRat_mem (outerWideAxisQAt_sound hx)

theorem outerWideAxis_signed_sound {x : ℚ} (hx : outerWideAxisReady x = true) :
    (outerSignedFromQ x (outerWideAxisQAt x)).Contains (signedPower criticalQ x) :=
  outerSignedFromQ_sound (outerWideAxisQAt_sound hx)

theorem outerWideAxis_slope_sound {x : ℚ} (hx : outerWideAxisReady x = true) (h₀ : x ≠ 0) :
    (outerSlopeFromQ x (outerWideAxisQAt x)).Contains (|(x : ℝ)|^(criticalQ-2)) :=
  outerSlopeFromQ_sound h₀ (outerWideAxisQAt_sound hx)

end HlawkaSchatten.BelowExponent.Vertex
