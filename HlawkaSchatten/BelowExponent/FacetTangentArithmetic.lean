/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetTangent
public import HlawkaSchatten.BelowExponent.Tangent.Coefficients

/-! The certified fine table supplies the real tangent inputs for all F and G2 prisms. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

private def finePrismHeader : TC.Hdr := {
  prof := TC.fine_prof, tab := TC.fine_tab, Dw := 2 ^ 30, KBOX := 30, CB := 10,
  rcN := 1, rcD := 500, etaN := 1, etaD := 500 }

private theorem finePrismHeader_ok : TC.tabOK finePrismHeader.prof finePrismHeader.tab = true :=
  TC.fine_tab_ok

private theorem finePrismHeader_pos : 0 < finePrismHeader.prof.k1 ∧ 0 < finePrismHeader.prof.k2 :=
  by decide

theorem facetRowTangent_le (code : ℕ) (x : ℝ) : Tangent.rowTangent ctx code x ≤ |x| ^ criticalQ :=
  Tangent.rowTangent_le_rpow finePrismHeader_ok finePrismHeader_pos code x

theorem prismCornerSound_of_numeric {P : Prism} (h : dataOK P = true) : PrismCornerSound P := by
  intro i cap j
  let v := vertexAt P i cap
  let ps := P.pi.map (· * P.profileDen)
  let gs := (vertexInputs P v).map Int.toNat
  let W := weightDen * P.profileDen
  have hv := vertexAt_mem h i cap
  have hp : ps.length = 4 := by simpa only [ps, List.length_map] using pi_length h
  have hd := profileDen_pos h
  have hW : 0 < W := Nat.mul_pos (by decide) hd
  have hc := Tangent.cornerSound_mkFace finePrismHeader_ok finePrismHeader_pos j
    (V := [v]) (v := v) (by simp) hd hW (ps := ps) (gs := gs) hp
  have hπ : (fun s : Fin 4 => (ps.getD s.val 0 : ℝ) / W) = realPi P :=
    funext fun s => (realPi_faceWeights h s).symm
  have hγ : (fun k : Fin 3 => (gs.getD k.val 0 : ℝ) / W) = realGamma P i cap :=
    funext fun k => (realInput_faceWeights h hv k).symm
  rw [hπ, hγ] at hc
  exact hc

end HlawkaSchatten.BelowExponent.FacetNumeric
