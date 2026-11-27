/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FSlabCheckGeometry
public import Mathlib.Data.List.GetD
import all HlawkaSchatten.BelowExponent.Tangent.Coefficients
import all HlawkaSchatten.BelowExponent.FacetTangentArithmetic
import Batteries.Tactic.OpenPrivate

/-! Soundness of the grouped comparisons for a balanced F row corner. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FSlabCheck

open Tangent
open FacetNumeric (ctx nearShiftedMag)
open private shiftedMag abs_chartCoord powers_le_lint rawCornerOutput_eq from HlawkaSchatten.BelowExponent.Tangent.Coefficients
open private finePrismHeader finePrismHeader_ok finePrismHeader_pos from HlawkaSchatten.BelowExponent.FacetTangentArithmetic

noncomputable section

def rawPowers (P : Band) (A B : ℕ) (ts : List TC.Tm) : ℝ :=
  (ts.map fun t => (t.p : ℝ) *
    |(TC.gInt t (Nat.ble ctx.Da A) (nearShiftedMag A) (Nat.ble ctx.Da B) (nearShiftedMag B) : ℝ) /
      ↑(profileDen P*ctx.Da : ℕ)|^criticalQ).sum

private theorem rawPowers_append (P : Band) (A B : ℕ) (ts us : List TC.Tm) :
    rawPowers P A B (ts++us) = rawPowers P A B ts + rawPowers P A B us := by
  simp [rawPowers]

private theorem rawPowers_terms (P : Band) (hW : P.weight ≤ 100) (j : Fin 3) (A B : ℕ) (v p : Bool) :
    rawPowers P A B (terms P j v p) = (commonDen P : ℝ) * weightedOutput criticalQ
      (balancedProfile (len P) (imbalanceAt P v) (len P)) (balancedPi (mu P) (imbalanceAt P p))
      (chartRow j (chartCoord ctx A) (chartCoord ctx B)) := by
  have hd : (commonDen P : ℝ) ≠ 0 := by exact_mod_cast (commonDen_pos P).ne'
  have hg (i : Fin 4) : ((pi P p).getD i.val 0 : ℝ) =
      (commonDen P : ℝ) * balancedPi (mu P) (imbalanceAt P p) i := by
    rw [mul_comm]
    exact (div_eq_iff hd).mp (pi_eq P p hW i)
  calc
    _ = cornerOutput criticalQ (vertex (profileDen P) (profile P v))
        (fun s => ((pi P p).getD s.val 0 : ℝ)) (chartRow j (chartCoord ctx A) (chartCoord ctx B)) :=
      rawCornerOutput_eq (C := ctx) (profileDen_pos P) (by decide) (profile P v) j
        (by simp [pi]) A B
    _ = _ := by
      rw [profile_eq]
      unfold cornerOutput weightedOutput
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by dsimp only; rw [hg]; ring

theorem rawPowers_groups (P : Band) (hW : P.weight ≤ 100) (j : Fin 3) (A B : ℕ) (i : Fin 3) :
    rawPowers P A B (groups P j i) = (commonDen P : ℝ) *
      fPairOutput (len P) (mu P) (imbalanceAt P false) (imbalanceAt P true) i
        (chartRow j (chartCoord ctx A) (chartCoord ctx B)) := by
  fin_cases i <;> simp [groups,rawPowers_append,rawPowers_terms P hW,fPairOutput,mul_add]

private theorem gamma_double_get (P : Band) (i : Fin 3) :
    ((gamma P).map (2*·)).getD i.val 0 = 2*(gamma P).getD i.val 0 := by
  fin_cases i <;> rfl

theorem rawGamma_agrees (P : Band) (hW : P.weight ≤ 100) (i : Fin 3) :
    (2 : ℝ) * ((gamma P).getD i.val 0 : ℝ) = (commonDen P : ℝ) * fDoubleGamma (mu P) (len P) i := by
  have hD : (commonDen P : ℝ) ≠ 0 := by exact_mod_cast (commonDen_pos P).ne'
  have hz := (div_eq_iff hD).mp (gamma_eq P hW i)
  unfold fDoubleGamma
  rw [hz]
  ring

def FCornerSound (P : Band) (j : Fin 3) : Prop :=
  ∀ (ca cb A B : ℕ),
    let F := face P j
    let add := (F.gk * (TC.acoef ctx ca).1 + F.gl * (TC.acoef ctx cb).1) * ctx.Da * F.F
    TC.cornerOK ctx F add (TC.acoef ctx ca).2 (TC.acoef ctx cb).2 A B (TC.lmaxAt ctx F A B) = true →
      ∀ i, fPairOutput (len P) (mu P) (imbalanceAt P false) (imbalanceAt P true) i
          (chartRow j (chartCoord ctx A) (chartCoord ctx B)) ≤
        cornerInput (fDoubleGamma (mu P) (len P)) j (rowTangent ctx ca) (rowTangent ctx cb)
          (chartCoord ctx A) (chartCoord ctx B)

theorem fCornerSound (P : Band) (hW : P.weight ≤ 100) (j : Fin 3) : FCornerSound P j := by
  intro ca cb A B F L h i
  let C := FacetNumeric.ctx
  let S := (2 : ℝ)^C.K*((profileDen P : ℝ)*C.Da)^2
  let U := F.gj2K + F.gk*(TC.acoef C ca).2*nearShiftedMag A + F.gl*(TC.acoef C cb).2*nearShiftedMag B
  let I := cornerInput (fDoubleGamma (mu P) (len P)) j (rowTangent C ca) (rowTangent C cb)
    (chartCoord C A) (chartCoord C B)
  have hDa : 0 < C.Da := by decide
  have hDa' : (C.Da : ℝ) ≠ 0 := by exact_mod_cast hDa.ne'
  have hD : 0 < (profileDen P : ℝ) := by exact_mod_cast profileDen_pos P
  have hW' : 0 < (commonDen P : ℝ) := by exact_mod_cast commonDen_pos P
  have hS : 0 < S := by dsimp [S]; positivity
  have hInt : TC.lmaxAt C F A B + L ≤ U * F.F := (TC.cornerOK_spec _ _ _ _ _ _ _ _).1 h
  have hn : (TC.lmaxAt C F A B : ℝ) + L ≤ (U : ℝ) * F.F := by exact_mod_cast hInt
  have hmem : groups P j i ∈ F.terms := List.mem_map.mpr ⟨i, List.mem_finRange _, rfl⟩
  have hY : F.Y = (profileDen P*C.Da)^2 := rfl
  have hmax : TC.lint C F.Y (Nat.ble C.Da A) (nearShiftedMag A)
      (Nat.ble C.Da B) (nearShiftedMag B) (groups P j i) ≤ TC.lmaxAt C F A B :=
    TC.lmaxV_ge _ _ _ _ _ _ _ _ hmem
  have hupper : rawPowers P A B (groups P j i) ≤ (TC.lmaxAt C F A B : ℝ)/S := by
    have hPow := powers_le_lint finePrismHeader_ok finePrismHeader_pos (Nat.mul_pos (profileDen_pos P) hDa)
      (Nat.ble C.Da A) (nearShiftedMag A) (Nat.ble C.Da B) (nearShiftedMag B) (groups P j i)
    dsimp only at hPow
    rw [show TC.mkCtx finePrismHeader = C from rfl] at hPow
    have hPow' : rawPowers P A B (groups P j i) ≤
      (TC.lint C ((profileDen P*C.Da)^2) (Nat.ble C.Da A) (nearShiftedMag A)
        (Nat.ble C.Da B) (nearShiftedMag B) (groups P j i) : ℝ)/S := by
      simpa only [rawPowers, Nat.cast_mul, S, C] using hPow
    rw [← hY] at hPow'
    exact hPow'.trans (div_le_div_of_nonneg_right (by exact_mod_cast hmax) hS.le)
  have hgamma' (k : Fin 3) : ((gamma P).map (2*·)).getD k.val 0 = 2*(gamma P).getD k.val 0 :=
    gamma_double_get P k
  have hmag (A : ℕ) : |chartCoord C A| = (nearShiftedMag A : ℝ)/C.Da := abs_chartCoord hDa A
  have heq : ((commonDen P : ℝ)*I)*S = (U : ℝ)*F.F - L := by
    simp only [I,S,U,L,F,face,TC.mkFace,cornerInput,rowTangent,hmag,hgamma',
      Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    rw [rawGamma_agrees P hW, rawGamma_agrees P hW, rawGamma_agrees P hW]
    field_simp [hDa']
    ring
  have hinput : (TC.lmaxAt C F A B : ℝ)/S ≤ (commonDen P : ℝ)*I := by
    apply (div_le_iff₀ hS).2
    rw [heq]
    exact (le_sub_iff_add_le).2 hn
  have hbound := hupper.trans hinput
  rw [rawPowers_groups P hW] at hbound
  exact (mul_le_mul_iff_right₀ hW').mp hbound

end

end HlawkaSchatten.BelowExponent.FSlabCheck
