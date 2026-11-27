/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.SideOuterWideCheck
public import HlawkaSchatten.BelowExponent.Vertex.SideOuterWideCover
public import HlawkaSchatten.BelowExponent.Vertex.CornerWidePowers
public import HlawkaSchatten.BelowExponent.Vertex.CornerPowerTables
public import HlawkaSchatten.BelowExponent.Vertex.OuterRowSound
public import HlawkaSchatten.BelowExponent.Vertex.SideOuterProof

/-! Connect the shared arbitrary-span comparator to each retained SC row rectangle. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxHeartbeats 0 in
theorem outerWideAxisBank_checked :
    (List.finRange 35).all (fun lo => (outerWideAxisBank.get lo).all fun row =>
      [false,true].all fun e => decide (row.2.get (outerWideEndpointIndex e) =
        outerWideSpanAxesCanonical ⟨lo,row.1⟩ e)) = true := by decide +kernel

theorem outerWideSpanAxes_eq (S : SideOuterSpan) (e : Bool) :
    outerWideSpanAxes S e = outerWideSpanAxesCanonical S e := by
  unfold outerWideSpanAxes
  cases hf : (outerWideAxisBank.get S.lo).find? (fun row => decide (row.1 = S.hi)) with
  | none => rfl
  | some row =>
    have hm := List.mem_of_find?_eq_some hf
    have he : row.1 = S.hi := by
      apply of_decide_eq_true
      exact @List.find?_some _ (fun value => decide (value.1 = S.hi)) row _ hf
    have hE : e ∈ [false,true] := by cases e <;> decide
    have h₀ := List.all_eq_true.mp outerWideAxisBank_checked S.lo (List.mem_finRange S.lo)
    have h₁ := List.all_eq_true.mp h₀ row hm
    have h₂ := of_decide_eq_true (List.all_eq_true.mp h₁ e hE)
    rw [he] at h₂
    exact h₂

theorem outerWideSpanAxes_encloses (S : SideOuterSpan) (e : Bool)
    (hwidth : S.bounds.lo < S.bounds.hi) (hsign : 0 ≤ S.bounds.lo ∨ S.bounds.hi ≤ 0) :
    (outerWideSpanAxes S e).EnclosesSpan S.bounds e := by
  have hE : outerWideAxisReady (outerEndpoint S.bounds e) = true := by
    cases e
    · exact outerWideAxisReady_node S.lo
    · exact outerWideAxisReady_node S.hi
  have hM : outerWideAxisReady (outerSpanMidpoint S.bounds) = true :=
    outerWideAxisReady_midpoint S.lo S.hi
  have h0 : outerSpanMidpoint S.bounds ≠ 0 := by
    unfold outerSpanMidpoint
    rcases hsign with hs | hs <;> intro he <;> linarith only [hs, hwidth, he]
  rw [outerWideSpanAxes_eq]
  exact outerSpanAxisBounds_encloses S.bounds e (outerWideAxis_abs_sound hE)
    (outerWideAxis_signed_sound hE) (outerWideAxis_abs_sound hM) (outerWideAxis_signed_sound hM)
    (outerWideAxis_slope_sound hM h0)

theorem outerWideRectOK_sound {P : OuterPointBounds} {p : SideCornerEntry}
    (hp : P.Encloses (cornerRowCoefficients p.margin.get p.a p.b p.eta))
    (k : Fin 3) (U V : SideOuterSpan) (hc : outerWideRectOK P k U V = true) :
    SideOuterWideAt p k U V := by
  rw [outerWideRectOK_eq_rat] at hc
  have ht := hc
  simp only [outerWideRectOKRat, OuterPointBounds.spanOK, Bool.and_eq_true, decide_eq_true_eq] at ht
  have hw := ht.1
  exact outerSpan_of_checks hp k U.bounds V.bounds
    (fun e => outerWideSpanAxes_encloses U e hw.1 hw.2.2.1)
    (fun e => outerWideSpanAxes_encloses V e hw.2.1 hw.2.2.2)
    (fun _ => outerRpowChordUpper_sound) hc

theorem outerWideRect_of_bounds {P : OuterPointBounds} {p : SideCornerEntry} {roots : Fin 3 → RatBounds}
    (hr : p.cell.rootsOK roots = true) (hp : P = .atPoint p.a p.b p.eta p.margin roots) :
    ∀ k U V, outerWideRectOK P k U V = true → SideOuterWideAt p k U V :=
  outerWideRectOK_sound (hp.symm ▸ OuterPointBounds.atPoint_encloses p.a p.b p.eta p.margin roots hr)

theorem scOuterPoint_of_checked_trees {P : OuterPointBounds} {p : SideCornerEntry}
    {roots : Fin 3 → RatBounds} {trees : Fin 3 → Bool → Bool → SideOuterTree}
    (hr : p.cell.rootsOK roots = true) (hp : P = .atPoint p.a p.b p.eta p.margin roots)
    (h : ∀ k s t, (trees k s t).check (outerWideRectOK P) scOuterSkips k
      (sideOuterStart s) (sideOuterStart t) = true) : p.Valid :=
  sideOuterPoint_of_trees scOuterSkips_eq (outerWideRect_of_bounds hr hp) h

theorem vcOuterPoint_of_checked_trees {P : OuterPointBounds} {p : SideCornerEntry}
    {roots : Fin 3 → RatBounds} {trees : Fin 3 → Bool → Bool → SideOuterTree}
    (hr : p.cell.rootsOK roots = true) (hp : P = .atPoint p.a p.b p.eta p.margin roots)
    (h : ∀ k s t, (trees k s t).check (outerWideRectOK P) (fun _ _ _ => false) k
      (sideOuterStart s) (sideOuterStart t) = true) : p.ValidFor (fun _ => True) :=
  vcOuterPoint_of_trees (outerWideRect_of_bounds hr hp) h

end HlawkaSchatten.BelowExponent.Vertex
