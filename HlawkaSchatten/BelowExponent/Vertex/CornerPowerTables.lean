/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CornerPowers
public import HlawkaSchatten.BelowExponent.Vertex.CornerPowerData.Axis
public import HlawkaSchatten.BelowExponent.Vertex.CornerPowerData.Chord

/-! Checked powers shared by all VC and SC corner rectangle certificates. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem outerChordQTable_ok : outerUpperTableOK outerChordQTable = true := by decide +kernel

def outerRpowChordUpper (x : ℚ) : ℚ := outerRpowChord outerChordQTable x

theorem outerRpowChordUpper_sound {x : ℚ} (hx : |x| ≤ 4) :
    |(x : ℝ)| ^ criticalQ ≤ (outerRpowChordUpper x : ℝ) :=
  outerRpowChord_sound outerChordQTable_ok hx

set_option maxHeartbeats 0 in
theorem outerNodeQTable_ok :
    (List.finRange 35).all (fun i => outerAbsQOK (outerNodes.get i) (outerNodeQTable.get i)) = true :=
  by decide +kernel

set_option maxHeartbeats 0 in
theorem outerMidpointQTable_ok :
    (List.finRange 34).all (fun i =>
      outerAbsQOK (outerAxisMidpoint i) (outerMidpointQTable.get i)) = true :=
  by decide +kernel

def outerEndpointCoord (i : Fin 34) (endpoint : Bool) : ℚ :=
  outerEndpoint (outerInterval i) endpoint

def outerEndpointQWitness (i : Fin 34) (endpoint : Bool) : RatBounds :=
  outerNodeQTable.get (if endpoint then i.succ else i.castSucc)

private theorem outerEndpointQWitness_sound (i : Fin 34) (endpoint : Bool) :
    (outerEndpointQWitness i endpoint).Contains (|(outerEndpointCoord i endpoint : ℝ)| ^ criticalQ) := by
  have h (j : Fin 35) := outerAbsQOK_sound
    (List.all_eq_true.mp outerNodeQTable_ok j (List.mem_finRange j))
  cases endpoint
  · exact h i.castSucc
  · exact h i.succ

private theorem outerMidQWitness_sound (i : Fin 34) :
    (outerMidpointQTable.get i).Contains (|(outerAxisMidpoint i : ℝ)| ^ criticalQ) :=
  outerAbsQOK_sound (List.all_eq_true.mp outerMidpointQTable_ok i (List.mem_finRange i))

private theorem outerAxisMidpoint_ne_zero (i : Fin 34) : outerAxisMidpoint i ≠ 0 := by
  have h : (List.finRange 34).all (fun j => decide (outerAxisMidpoint j ≠ 0)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i (List.mem_finRange i))

def outerEndpointAbsQ (i : Fin 34) (endpoint : Bool) : DyadicBounds :=
  .ofRat (outerEndpointQWitness i endpoint)

theorem outerEndpointAbsQ_sound (i : Fin 34) (endpoint : Bool) :
    (outerEndpointAbsQ i endpoint).Contains (|(outerEndpointCoord i endpoint : ℝ)| ^ criticalQ) :=
  DyadicBounds.ofRat_mem (outerEndpointQWitness_sound i endpoint)

def outerEndpointSigned (i : Fin 34) (endpoint : Bool) : DyadicBounds :=
  outerSignedFromQ (outerEndpointCoord i endpoint) (outerEndpointQWitness i endpoint)

theorem outerEndpointSigned_sound (i : Fin 34) (endpoint : Bool) :
    (outerEndpointSigned i endpoint).Contains (signedPower criticalQ (outerEndpointCoord i endpoint : ℝ)) :=
  outerSignedFromQ_sound (outerEndpointQWitness_sound i endpoint)

def outerMidAbsQ (i : Fin 34) : DyadicBounds := .ofRat (outerMidpointQTable.get i)

theorem outerMidAbsQ_sound (i : Fin 34) :
    (outerMidAbsQ i).Contains (|(outerAxisMidpoint i : ℝ)| ^ criticalQ) :=
  DyadicBounds.ofRat_mem (outerMidQWitness_sound i)

def outerMidSigned (i : Fin 34) : DyadicBounds :=
  outerSignedFromQ (outerAxisMidpoint i) (outerMidpointQTable.get i)

theorem outerMidSigned_sound (i : Fin 34) :
    (outerMidSigned i).Contains (signedPower criticalQ (outerAxisMidpoint i : ℝ)) :=
  outerSignedFromQ_sound (outerMidQWitness_sound i)

def outerMidSlope (i : Fin 34) : DyadicBounds :=
  outerSlopeFromQ (outerAxisMidpoint i) (outerMidpointQTable.get i)

theorem outerMidSlope_sound (i : Fin 34) :
    (outerMidSlope i).Contains (|(outerAxisMidpoint i : ℝ)| ^ (criticalQ-2)) :=
  outerSlopeFromQ_sound (outerAxisMidpoint_ne_zero i) (outerMidQWitness_sound i)

end HlawkaSchatten.BelowExponent.Vertex
