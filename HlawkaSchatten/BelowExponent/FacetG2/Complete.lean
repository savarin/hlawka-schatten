/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetG2.Cover
public import HlawkaSchatten.BelowExponent.FacetTangentArithmetic

/-! Discharge the cap and noncone row premises of the adaptive G2 cover. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

public section

namespace HlawkaSchatten.BelowExponent

open FacetNumeric

private theorem g2CheckedRows {P : Prism} {b : Fin 3 → Row} {π : Profile} {slope : Row} {ρ : ℝ}
    (hdata : dataOK P = true) (trees : Fin 3 → RowTree)
    (hcharts : ∀ j : Fin 3, checkChart P j.val (Tangent.chartA j).val (Tangent.chartB j).val (trees j) = true)
    (hradius : (P.radiusNum : ℝ) / P.radiusDen = ρ)
    (hcap : ∀ i, (vertexAt P i true).v3 ≠ 0)
    (hvertex : ∀ i cap, realVertex P i cap = facetCap (b i) (if cap then 1 / 500 else 0))
    (hπ : realPi P = π)
    (hγ : ∀ i cap, realGamma P i cap = prismWeight π slope (facetCap (b i) (if cap then 1 / 500 else 0)))
    (hcone : ∀ i x, FacetRatioCone ρ x → WeightedRow criticalQ (facetBase (b i)) π (facetWeight π (b i)) x) :
    ∀ i cap x, WeightedRow criticalQ (realVertex P i cap) (realPi P) (realGamma P i cap) x := by
  apply prismRows_of_numeric hdata trees hcharts facetRowTangent_le (prismCornerSound_of_numeric hdata)
  intro i cap hv x hx
  rw [hradius] at hx
  cases cap
  · have hb : facetCap (b i) 0 = facetBase (b i) := by
      funext s
      fin_cases s <;> simp [facetCap, facetBase]
    have hg : prismWeight π slope (facetCap (b i) 0) = facetWeight π (b i) := by
      funext j
      fin_cases j <;> simp [prismWeight, facetWeight, facetCap, Fin.castSucc]
    rw [hvertex, hπ, hγ]
    change WeightedRow criticalQ (facetCap (b i) 0) π (prismWeight π slope (facetCap (b i) 0)) x
    rw [hg, hb]
    exact hcone i x hx
  · exact (hcap i hv).elim

set_option maxHeartbeats 0 in
theorem g2NumericRows_checked (prism : Fin 39) : G2NumericRows prism := by
  fin_cases prism
  · intro v cap x _
    refine g2CheckedRows (P := g2Tip0) (b := g2Tip0Base) (π := g2Tip0Pi)
      (slope := g2Tip0Slope) (ρ := g2PrismRadius 0) g2Tip0_data_ok ![g2Tip0Chart0, g2Tip0Chart1, g2Tip0Chart2] ?_ ?_ ?_
      g2Tip0_vertices_agree g2Tip0_pi_agrees g2Tip0_gamma_agrees ?_ v cap x
    · intro j
      fin_cases j
      · exact g2Tip0Chart0_ok
      · exact g2Tip0Chart1_ok
      · exact g2Tip0Chart2_ok
    · norm_num [g2Tip0, g2PrismRadius]
    · intro j
      fin_cases j <;> decide
    · intro j y hy
      exact g2Tip0_cone j hy
  · intro v cap x _
    refine g2CheckedRows (P := g2Tip1) (b := g2Tip1Base) (π := g2Tip1Pi)
      (slope := g2Tip1Slope) (ρ := g2PrismRadius 1) g2Tip1_data_ok ![g2Tip1Chart0, g2Tip1Chart1, g2Tip1Chart2] ?_ ?_ ?_
      g2Tip1_vertices_agree g2Tip1_pi_agrees g2Tip1_gamma_agrees ?_ v cap x
    · intro j
      fin_cases j
      · exact g2Tip1Chart0_ok
      · exact g2Tip1Chart1_ok
      · exact g2Tip1Chart2_ok
    · norm_num [g2Tip1, g2PrismRadius]
    · intro j
      fin_cases j <;> decide
    · intro j y hy
      exact g2Tip1_cone j hy
  · intro v cap x _
    refine g2CheckedRows (P := g2Upper0) (b := g2Upper0Base) (π := g2Upper0Pi)
      (slope := g2Upper0Slope) (ρ := g2PrismRadius 2) g2Upper0_data_ok ![g2Upper0Chart0, g2Upper0Chart1, g2Upper0Chart2] ?_ ?_ ?_
      g2Upper0_vertices_agree g2Upper0_pi_agrees g2Upper0_gamma_agrees ?_ v cap x
    · intro j
      fin_cases j
      · exact g2Upper0Chart0_ok
      · exact g2Upper0Chart1_ok
      · exact g2Upper0Chart2_ok
    · norm_num [g2Upper0, g2PrismRadius]
    · intro j
      fin_cases j <;> decide
    · intro j y hy
      exact g2Upper0_cone j hy
  · intro v cap x _
    refine g2CheckedRows (P := g2Upper1) (b := g2Upper1Base) (π := g2Upper1Pi)
      (slope := g2Upper1Slope) (ρ := g2PrismRadius 3) g2Upper1_data_ok ![g2Upper1Chart0, g2Upper1Chart1, g2Upper1Chart2] ?_ ?_ ?_
      g2Upper1_vertices_agree g2Upper1_pi_agrees g2Upper1_gamma_agrees ?_ v cap x
    · intro j
      fin_cases j
      · exact g2Upper1Chart0_ok
      · exact g2Upper1Chart1_ok
      · exact g2Upper1Chart2_ok
    · norm_num [g2Upper1, g2PrismRadius]
    · intro j
      fin_cases j <;> decide
    · intro j y hy
      exact g2Upper1_cone j hy
  · intro v cap x _
    refine g2CheckedRows (P := g2Upper2) (b := g2Upper2Base) (π := g2Upper2Pi)
      (slope := g2Upper2Slope) (ρ := g2PrismRadius 4) g2Upper2_data_ok ![g2Upper2Chart0, g2Upper2Chart1, g2Upper2Chart2] ?_ ?_ ?_
      g2Upper2_vertices_agree g2Upper2_pi_agrees g2Upper2_gamma_agrees ?_ v cap x
    · intro j
      fin_cases j
      · exact g2Upper2Chart0_ok
      · exact g2Upper2Chart1_ok
      · exact g2Upper2Chart2_ok
    · norm_num [g2Upper2, g2PrismRadius]
    · intro j
      fin_cases j <;> decide
    · intro j y hy
      exact g2Upper2_cone j hy
  · intro v cap x _
    refine g2CheckedRows (P := g2Upper3) (b := g2Upper3Base) (π := g2Upper3Pi)
      (slope := g2Upper3Slope) (ρ := g2PrismRadius 5) g2Upper3_data_ok ![g2Upper3Chart0, g2Upper3Chart1, g2Upper3Chart2] ?_ ?_ ?_
      g2Upper3_vertices_agree g2Upper3_pi_agrees g2Upper3_gamma_agrees ?_ v cap x
    · intro j
      fin_cases j
      · exact g2Upper3Chart0_ok
      · exact g2Upper3Chart1_ok
      · exact g2Upper3Chart2_ok
    · norm_num [g2Upper3, g2PrismRadius]
    · intro j
      fin_cases j <;> decide
    · intro j y hy
      exact g2Upper3_cone j hy
  · intro v cap x _
    refine g2CheckedRows (P := g2Upper4) (b := g2Upper4Base) (π := g2Upper4Pi)
      (slope := g2Upper4Slope) (ρ := g2PrismRadius 6) g2Upper4_data_ok ![g2Upper4Chart0, g2Upper4Chart1, g2Upper4Chart2] ?_ ?_ ?_
      g2Upper4_vertices_agree g2Upper4_pi_agrees g2Upper4_gamma_agrees ?_ v cap x
    · intro j
      fin_cases j
      · exact g2Upper4Chart0_ok
      · exact g2Upper4Chart1_ok
      · exact g2Upper4Chart2_ok
    · norm_num [g2Upper4, g2PrismRadius]
    · intro j
      fin_cases j <;> decide
    · intro j y hy
      exact g2Upper4_cone j hy
  · intro v cap x _
    refine g2CheckedRows (P := g2Upper5) (b := g2Upper5Base) (π := g2Upper5Pi)
      (slope := g2Upper5Slope) (ρ := g2PrismRadius 7) g2Upper5_data_ok ![g2Upper5Chart0, g2Upper5Chart1, g2Upper5Chart2] ?_ ?_ ?_
      g2Upper5_vertices_agree g2Upper5_pi_agrees g2Upper5_gamma_agrees ?_ v cap x
    · intro j
      fin_cases j
      · exact g2Upper5Chart0_ok
      · exact g2Upper5Chart1_ok
      · exact g2Upper5Chart2_ok
    · norm_num [g2Upper5, g2PrismRadius]
    · intro j
      fin_cases j <;> decide
    · intro j y hy
      exact g2Upper5_cone j hy
  · intro v cap x _
    refine g2CheckedRows (P := g2Upper6) (b := g2Upper6Base) (π := g2Upper6Pi)
      (slope := g2Upper6Slope) (ρ := g2PrismRadius 8) g2Upper6_data_ok ![g2Upper6Chart0, g2Upper6Chart1, g2Upper6Chart2] ?_ ?_ ?_
      g2Upper6_vertices_agree g2Upper6_pi_agrees g2Upper6_gamma_agrees ?_ v cap x
    · intro j
      fin_cases j
      · exact g2Upper6Chart0_ok
      · exact g2Upper6Chart1_ok
      · exact g2Upper6Chart2_ok
    · norm_num [g2Upper6, g2PrismRadius]
    · intro j
      fin_cases j <;> decide
    · intro j y hy
      exact g2Upper6_cone j hy
  · intro v cap x _
    refine g2CheckedRows (P := g2Upper7) (b := g2Upper7Base) (π := g2Upper7Pi)
      (slope := g2Upper7Slope) (ρ := g2PrismRadius 9) g2Upper7_data_ok ![g2Upper7Chart0, g2Upper7Chart1, g2Upper7Chart2] ?_ ?_ ?_
      g2Upper7_vertices_agree g2Upper7_pi_agrees g2Upper7_gamma_agrees ?_ v cap x
    · intro j
      fin_cases j
      · exact g2Upper7Chart0_ok
      · exact g2Upper7Chart1_ok
      · exact g2Upper7Chart2_ok
    · norm_num [g2Upper7, g2PrismRadius]
    · intro j
      fin_cases j <;> decide
    · intro j y hy
      exact g2Upper7_cone j hy
  · intro v cap x _
    refine g2CheckedRows (P := g2Upper8) (b := g2Upper8Base) (π := g2Upper8Pi)
      (slope := g2Upper8Slope) (ρ := g2PrismRadius 10) g2Upper8_data_ok ![g2Upper8Chart0, g2Upper8Chart1, g2Upper8Chart2] ?_ ?_ ?_
      g2Upper8_vertices_agree g2Upper8_pi_agrees g2Upper8_gamma_agrees ?_ v cap x
    · intro j
      fin_cases j
      · exact g2Upper8Chart0_ok
      · exact g2Upper8Chart1_ok
      · exact g2Upper8Chart2_ok
    · norm_num [g2Upper8, g2PrismRadius]
    · intro j
      fin_cases j <;> decide
    · intro j y hy
      exact g2Upper8_cone j hy
  · intro v cap x _
    refine g2CheckedRows (P := g2Upper9) (b := g2Upper9Base) (π := g2Upper9Pi)
      (slope := g2Upper9Slope) (ρ := g2PrismRadius 11) g2Upper9_data_ok ![g2Upper9Chart0, g2Upper9Chart1, g2Upper9Chart2] ?_ ?_ ?_
      g2Upper9_vertices_agree g2Upper9_pi_agrees g2Upper9_gamma_agrees ?_ v cap x
    · intro j
      fin_cases j
      · exact g2Upper9Chart0_ok
      · exact g2Upper9Chart1_ok
      · exact g2Upper9Chart2_ok
    · norm_num [g2Upper9, g2PrismRadius]
    · intro j
      fin_cases j <;> decide
    · intro j y hy
      exact g2Upper9_cone j hy
  · intro v cap x _
    refine g2CheckedRows (P := g2Upper10) (b := g2Upper10Base) (π := g2Upper10Pi)
      (slope := g2Upper10Slope) (ρ := g2PrismRadius 12) g2Upper10_data_ok ![g2Upper10Chart0, g2Upper10Chart1, g2Upper10Chart2] ?_ ?_ ?_
      g2Upper10_vertices_agree g2Upper10_pi_agrees g2Upper10_gamma_agrees ?_ v cap x
    · intro j
      fin_cases j
      · exact g2Upper10Chart0_ok
      · exact g2Upper10Chart1_ok
      · exact g2Upper10Chart2_ok
    · norm_num [g2Upper10, g2PrismRadius]
    · intro j
      fin_cases j <;> decide
    · intro j y hy
      exact g2Upper10_cone j hy
  · intro v cap x _
    refine g2CheckedRows (P := g2Upper11) (b := g2Upper11Base) (π := g2Upper11Pi)
      (slope := g2Upper11Slope) (ρ := g2PrismRadius 13) g2Upper11_data_ok ![g2Upper11Chart0, g2Upper11Chart1, g2Upper11Chart2] ?_ ?_ ?_
      g2Upper11_vertices_agree g2Upper11_pi_agrees g2Upper11_gamma_agrees ?_ v cap x
    · intro j
      fin_cases j
      · exact g2Upper11Chart0_ok
      · exact g2Upper11Chart1_ok
      · exact g2Upper11Chart2_ok
    · norm_num [g2Upper11, g2PrismRadius]
    · intro j
      fin_cases j <;> decide
    · intro j y hy
      exact g2Upper11_cone j hy
  · intro v cap x _
    refine g2CheckedRows (P := g2Upper12) (b := g2Upper12Base) (π := g2Upper12Pi)
      (slope := g2Upper12Slope) (ρ := g2PrismRadius 14) g2Upper12_data_ok ![g2Upper12Chart0, g2Upper12Chart1, g2Upper12Chart2] ?_ ?_ ?_
      g2Upper12_vertices_agree g2Upper12_pi_agrees g2Upper12_gamma_agrees ?_ v cap x
    · intro j
      fin_cases j
      · exact g2Upper12Chart0_ok
      · exact g2Upper12Chart1_ok
      · exact g2Upper12Chart2_ok
    · norm_num [g2Upper12, g2PrismRadius]
    · intro j
      fin_cases j <;> decide
    · intro j y hy
      exact g2Upper12_cone j hy
  · intro v cap x _
    refine g2CheckedRows (P := g2Upper13) (b := g2Upper13Base) (π := g2Upper13Pi)
      (slope := g2Upper13Slope) (ρ := g2PrismRadius 15) g2Upper13_data_ok ![g2Upper13Chart0, g2Upper13Chart1, g2Upper13Chart2] ?_ ?_ ?_
      g2Upper13_vertices_agree g2Upper13_pi_agrees g2Upper13_gamma_agrees ?_ v cap x
    · intro j
      fin_cases j
      · exact g2Upper13Chart0_ok
      · exact g2Upper13Chart1_ok
      · exact g2Upper13Chart2_ok
    · norm_num [g2Upper13, g2PrismRadius]
    · intro j
      fin_cases j <;> decide
    · intro j y hy
      exact g2Upper13_cone j hy
  · intro v cap x _
    refine g2CheckedRows (P := g2Upper14) (b := g2Upper14Base) (π := g2Upper14Pi)
      (slope := g2Upper14Slope) (ρ := g2PrismRadius 16) g2Upper14_data_ok ![g2Upper14Chart0, g2Upper14Chart1, g2Upper14Chart2] ?_ ?_ ?_
      g2Upper14_vertices_agree g2Upper14_pi_agrees g2Upper14_gamma_agrees ?_ v cap x
    · intro j
      fin_cases j
      · exact g2Upper14Chart0_ok
      · exact g2Upper14Chart1_ok
      · exact g2Upper14Chart2_ok
    · norm_num [g2Upper14, g2PrismRadius]
    · intro j
      fin_cases j <;> decide
    · intro j y hy
      exact g2Upper14_cone j hy
  · intro v cap x _
    refine g2CheckedRows (P := g2Upper15) (b := g2Upper15Base) (π := g2Upper15Pi)
      (slope := g2Upper15Slope) (ρ := g2PrismRadius 17) g2Upper15_data_ok ![g2Upper15Chart0, g2Upper15Chart1, g2Upper15Chart2] ?_ ?_ ?_
      g2Upper15_vertices_agree g2Upper15_pi_agrees g2Upper15_gamma_agrees ?_ v cap x
    · intro j
      fin_cases j
      · exact g2Upper15Chart0_ok
      · exact g2Upper15Chart1_ok
      · exact g2Upper15Chart2_ok
    · norm_num [g2Upper15, g2PrismRadius]
    · intro j
      fin_cases j <;> decide
    · intro j y hy
      exact g2Upper15_cone j hy
  · intro v cap x _
    refine g2CheckedRows (P := g2Upper16) (b := g2Upper16Base) (π := g2Upper16Pi)
      (slope := g2Upper16Slope) (ρ := g2PrismRadius 18) g2Upper16_data_ok ![g2Upper16Chart0, g2Upper16Chart1, g2Upper16Chart2] ?_ ?_ ?_
      g2Upper16_vertices_agree g2Upper16_pi_agrees g2Upper16_gamma_agrees ?_ v cap x
    · intro j
      fin_cases j
      · exact g2Upper16Chart0_ok
      · exact g2Upper16Chart1_ok
      · exact g2Upper16Chart2_ok
    · norm_num [g2Upper16, g2PrismRadius]
    · intro j
      fin_cases j <;> decide
    · intro j y hy
      exact g2Upper16_cone j hy
  · intro v cap x _
    refine g2CheckedRows (P := g2Upper17) (b := g2Upper17Base) (π := g2Upper17Pi)
      (slope := g2Upper17Slope) (ρ := g2PrismRadius 19) g2Upper17_data_ok ![g2Upper17Chart0, g2Upper17Chart1, g2Upper17Chart2] ?_ ?_ ?_
      g2Upper17_vertices_agree g2Upper17_pi_agrees g2Upper17_gamma_agrees ?_ v cap x
    · intro j
      fin_cases j
      · exact g2Upper17Chart0_ok
      · exact g2Upper17Chart1_ok
      · exact g2Upper17Chart2_ok
    · norm_num [g2Upper17, g2PrismRadius]
    · intro j
      fin_cases j <;> decide
    · intro j y hy
      exact g2Upper17_cone j hy
  · intro v cap x _
    refine g2CheckedRows (P := g2Upper18) (b := g2Upper18Base) (π := g2Upper18Pi)
      (slope := g2Upper18Slope) (ρ := g2PrismRadius 20) g2Upper18_data_ok ![g2Upper18Chart0, g2Upper18Chart1, g2Upper18Chart2] ?_ ?_ ?_
      g2Upper18_vertices_agree g2Upper18_pi_agrees g2Upper18_gamma_agrees ?_ v cap x
    · intro j
      fin_cases j
      · exact g2Upper18Chart0_ok
      · exact g2Upper18Chart1_ok
      · exact g2Upper18Chart2_ok
    · norm_num [g2Upper18, g2PrismRadius]
    · intro j
      fin_cases j <;> decide
    · intro j y hy
      exact g2Upper18_cone j hy
  · intro v cap x _
    refine g2CheckedRows (P := g2Upper19) (b := g2Upper19Base) (π := g2Upper19Pi)
      (slope := g2Upper19Slope) (ρ := g2PrismRadius 21) g2Upper19_data_ok ![g2Upper19Chart0, g2Upper19Chart1, g2Upper19Chart2] ?_ ?_ ?_
      g2Upper19_vertices_agree g2Upper19_pi_agrees g2Upper19_gamma_agrees ?_ v cap x
    · intro j
      fin_cases j
      · exact g2Upper19Chart0_ok
      · exact g2Upper19Chart1_ok
      · exact g2Upper19Chart2_ok
    · norm_num [g2Upper19, g2PrismRadius]
    · intro j
      fin_cases j <;> decide
    · intro j y hy
      exact g2Upper19_cone j hy
  · intro v cap x _
    refine g2CheckedRows (P := g2Upper20) (b := g2Upper20Base) (π := g2Upper20Pi)
      (slope := g2Upper20Slope) (ρ := g2PrismRadius 22) g2Upper20_data_ok ![g2Upper20Chart0, g2Upper20Chart1, g2Upper20Chart2] ?_ ?_ ?_
      g2Upper20_vertices_agree g2Upper20_pi_agrees g2Upper20_gamma_agrees ?_ v cap x
    · intro j
      fin_cases j
      · exact g2Upper20Chart0_ok
      · exact g2Upper20Chart1_ok
      · exact g2Upper20Chart2_ok
    · norm_num [g2Upper20, g2PrismRadius]
    · intro j
      fin_cases j <;> decide
    · intro j y hy
      exact g2Upper20_cone j hy
  · intro v cap x _
    refine g2CheckedRows (P := g2Upper21) (b := g2Upper21Base) (π := g2Upper21Pi)
      (slope := g2Upper21Slope) (ρ := g2PrismRadius 23) g2Upper21_data_ok ![g2Upper21Chart0, g2Upper21Chart1, g2Upper21Chart2] ?_ ?_ ?_
      g2Upper21_vertices_agree g2Upper21_pi_agrees g2Upper21_gamma_agrees ?_ v cap x
    · intro j
      fin_cases j
      · exact g2Upper21Chart0_ok
      · exact g2Upper21Chart1_ok
      · exact g2Upper21Chart2_ok
    · norm_num [g2Upper21, g2PrismRadius]
    · intro j
      fin_cases j <;> decide
    · intro j y hy
      exact g2Upper21_cone j hy
  · intro v cap x _
    refine g2CheckedRows (P := g2Upper22) (b := g2Upper22Base) (π := g2Upper22Pi)
      (slope := g2Upper22Slope) (ρ := g2PrismRadius 24) g2Upper22_data_ok ![g2Upper22Chart0, g2Upper22Chart1, g2Upper22Chart2] ?_ ?_ ?_
      g2Upper22_vertices_agree g2Upper22_pi_agrees g2Upper22_gamma_agrees ?_ v cap x
    · intro j
      fin_cases j
      · exact g2Upper22Chart0_ok
      · exact g2Upper22Chart1_ok
      · exact g2Upper22Chart2_ok
    · norm_num [g2Upper22, g2PrismRadius]
    · intro j
      fin_cases j <;> decide
    · intro j y hy
      exact g2Upper22_cone j hy
  · intro v cap x _
    refine g2CheckedRows (P := g2Upper23) (b := g2Upper23Base) (π := g2Upper23Pi)
      (slope := g2Upper23Slope) (ρ := g2PrismRadius 25) g2Upper23_data_ok ![g2Upper23Chart0, g2Upper23Chart1, g2Upper23Chart2] ?_ ?_ ?_
      g2Upper23_vertices_agree g2Upper23_pi_agrees g2Upper23_gamma_agrees ?_ v cap x
    · intro j
      fin_cases j
      · exact g2Upper23Chart0_ok
      · exact g2Upper23Chart1_ok
      · exact g2Upper23Chart2_ok
    · norm_num [g2Upper23, g2PrismRadius]
    · intro j
      fin_cases j <;> decide
    · intro j y hy
      exact g2Upper23_cone j hy
  · intro v cap x _
    refine g2CheckedRows (P := g2Upper24) (b := g2Upper24Base) (π := g2Upper24Pi)
      (slope := g2Upper24Slope) (ρ := g2PrismRadius 26) g2Upper24_data_ok ![g2Upper24Chart0, g2Upper24Chart1, g2Upper24Chart2] ?_ ?_ ?_
      g2Upper24_vertices_agree g2Upper24_pi_agrees g2Upper24_gamma_agrees ?_ v cap x
    · intro j
      fin_cases j
      · exact g2Upper24Chart0_ok
      · exact g2Upper24Chart1_ok
      · exact g2Upper24Chart2_ok
    · norm_num [g2Upper24, g2PrismRadius]
    · intro j
      fin_cases j <;> decide
    · intro j y hy
      exact g2Upper24_cone j hy
  · intro v cap x _
    refine g2CheckedRows (P := g2Upper25) (b := g2Upper25Base) (π := g2Upper25Pi)
      (slope := g2Upper25Slope) (ρ := g2PrismRadius 27) g2Upper25_data_ok ![g2Upper25Chart0, g2Upper25Chart1, g2Upper25Chart2] ?_ ?_ ?_
      g2Upper25_vertices_agree g2Upper25_pi_agrees g2Upper25_gamma_agrees ?_ v cap x
    · intro j
      fin_cases j
      · exact g2Upper25Chart0_ok
      · exact g2Upper25Chart1_ok
      · exact g2Upper25Chart2_ok
    · norm_num [g2Upper25, g2PrismRadius]
    · intro j
      fin_cases j <;> decide
    · intro j y hy
      exact g2Upper25_cone j hy
  · intro v cap x _
    refine g2CheckedRows (P := g2Upper26) (b := g2Upper26Base) (π := g2Upper26Pi)
      (slope := g2Upper26Slope) (ρ := g2PrismRadius 28) g2Upper26_data_ok ![g2Upper26Chart0, g2Upper26Chart1, g2Upper26Chart2] ?_ ?_ ?_
      g2Upper26_vertices_agree g2Upper26_pi_agrees g2Upper26_gamma_agrees ?_ v cap x
    · intro j
      fin_cases j
      · exact g2Upper26Chart0_ok
      · exact g2Upper26Chart1_ok
      · exact g2Upper26Chart2_ok
    · norm_num [g2Upper26, g2PrismRadius]
    · intro j
      fin_cases j <;> decide
    · intro j y hy
      exact g2Upper26_cone j hy
  · intro v cap x _
    refine g2CheckedRows (P := g2Upper27) (b := g2Upper27Base) (π := g2Upper27Pi)
      (slope := g2Upper27Slope) (ρ := g2PrismRadius 29) g2Upper27_data_ok ![g2Upper27Chart0, g2Upper27Chart1, g2Upper27Chart2] ?_ ?_ ?_
      g2Upper27_vertices_agree g2Upper27_pi_agrees g2Upper27_gamma_agrees ?_ v cap x
    · intro j
      fin_cases j
      · exact g2Upper27Chart0_ok
      · exact g2Upper27Chart1_ok
      · exact g2Upper27Chart2_ok
    · norm_num [g2Upper27, g2PrismRadius]
    · intro j
      fin_cases j <;> decide
    · intro j y hy
      exact g2Upper27_cone j hy
  · intro v cap x _
    refine g2CheckedRows (P := g2Upper28) (b := g2Upper28Base) (π := g2Upper28Pi)
      (slope := g2Upper28Slope) (ρ := g2PrismRadius 30) g2Upper28_data_ok ![g2Upper28Chart0, g2Upper28Chart1, g2Upper28Chart2] ?_ ?_ ?_
      g2Upper28_vertices_agree g2Upper28_pi_agrees g2Upper28_gamma_agrees ?_ v cap x
    · intro j
      fin_cases j
      · exact g2Upper28Chart0_ok
      · exact g2Upper28Chart1_ok
      · exact g2Upper28Chart2_ok
    · norm_num [g2Upper28, g2PrismRadius]
    · intro j
      fin_cases j <;> decide
    · intro j y hy
      exact g2Upper28_cone j hy
  · intro v cap x _
    refine g2CheckedRows (P := g2Upper29) (b := g2Upper29Base) (π := g2Upper29Pi)
      (slope := g2Upper29Slope) (ρ := g2PrismRadius 31) g2Upper29_data_ok ![g2Upper29Chart0, g2Upper29Chart1, g2Upper29Chart2] ?_ ?_ ?_
      g2Upper29_vertices_agree g2Upper29_pi_agrees g2Upper29_gamma_agrees ?_ v cap x
    · intro j
      fin_cases j
      · exact g2Upper29Chart0_ok
      · exact g2Upper29Chart1_ok
      · exact g2Upper29Chart2_ok
    · norm_num [g2Upper29, g2PrismRadius]
    · intro j
      fin_cases j <;> decide
    · intro j y hy
      exact g2Upper29_cone j hy
  · intro v cap x _
    refine g2CheckedRows (P := g2Upper30) (b := g2Upper30Base) (π := g2Upper30Pi)
      (slope := g2Upper30Slope) (ρ := g2PrismRadius 32) g2Upper30_data_ok ![g2Upper30Chart0, g2Upper30Chart1, g2Upper30Chart2] ?_ ?_ ?_
      g2Upper30_vertices_agree g2Upper30_pi_agrees g2Upper30_gamma_agrees ?_ v cap x
    · intro j
      fin_cases j
      · exact g2Upper30Chart0_ok
      · exact g2Upper30Chart1_ok
      · exact g2Upper30Chart2_ok
    · norm_num [g2Upper30, g2PrismRadius]
    · intro j
      fin_cases j <;> decide
    · intro j y hy
      exact g2Upper30_cone j hy
  · intro v cap x _
    refine g2CheckedRows (P := g2Upper31) (b := g2Upper31Base) (π := g2Upper31Pi)
      (slope := g2Upper31Slope) (ρ := g2PrismRadius 33) g2Upper31_data_ok ![g2Upper31Chart0, g2Upper31Chart1, g2Upper31Chart2] ?_ ?_ ?_
      g2Upper31_vertices_agree g2Upper31_pi_agrees g2Upper31_gamma_agrees ?_ v cap x
    · intro j
      fin_cases j
      · exact g2Upper31Chart0_ok
      · exact g2Upper31Chart1_ok
      · exact g2Upper31Chart2_ok
    · norm_num [g2Upper31, g2PrismRadius]
    · intro j
      fin_cases j <;> decide
    · intro j y hy
      exact g2Upper31_cone j hy
  · intro v cap x _
    refine g2CheckedRows (P := g2Upper32) (b := g2Upper32Base) (π := g2Upper32Pi)
      (slope := g2Upper32Slope) (ρ := g2PrismRadius 34) g2Upper32_data_ok ![g2Upper32Chart0, g2Upper32Chart1, g2Upper32Chart2] ?_ ?_ ?_
      g2Upper32_vertices_agree g2Upper32_pi_agrees g2Upper32_gamma_agrees ?_ v cap x
    · intro j
      fin_cases j
      · exact g2Upper32Chart0_ok
      · exact g2Upper32Chart1_ok
      · exact g2Upper32Chart2_ok
    · norm_num [g2Upper32, g2PrismRadius]
    · intro j
      fin_cases j <;> decide
    · intro j y hy
      exact g2Upper32_cone j hy
  · intro v cap x _
    refine g2CheckedRows (P := g2Upper33) (b := g2Upper33Base) (π := g2Upper33Pi)
      (slope := g2Upper33Slope) (ρ := g2PrismRadius 35) g2Upper33_data_ok ![g2Upper33Chart0, g2Upper33Chart1, g2Upper33Chart2] ?_ ?_ ?_
      g2Upper33_vertices_agree g2Upper33_pi_agrees g2Upper33_gamma_agrees ?_ v cap x
    · intro j
      fin_cases j
      · exact g2Upper33Chart0_ok
      · exact g2Upper33Chart1_ok
      · exact g2Upper33Chart2_ok
    · norm_num [g2Upper33, g2PrismRadius]
    · intro j
      fin_cases j <;> decide
    · intro j y hy
      exact g2Upper33_cone j hy
  · intro v cap x _
    refine g2CheckedRows (P := g2Upper34) (b := g2Upper34Base) (π := g2Upper34Pi)
      (slope := g2Upper34Slope) (ρ := g2PrismRadius 36) g2Upper34_data_ok ![g2Upper34Chart0, g2Upper34Chart1, g2Upper34Chart2] ?_ ?_ ?_
      g2Upper34_vertices_agree g2Upper34_pi_agrees g2Upper34_gamma_agrees ?_ v cap x
    · intro j
      fin_cases j
      · exact g2Upper34Chart0_ok
      · exact g2Upper34Chart1_ok
      · exact g2Upper34Chart2_ok
    · norm_num [g2Upper34, g2PrismRadius]
    · intro j
      fin_cases j <;> decide
    · intro j y hy
      exact g2Upper34_cone j hy
  · intro v cap x _
    refine g2CheckedRows (P := g2Upper35) (b := g2Upper35Base) (π := g2Upper35Pi)
      (slope := g2Upper35Slope) (ρ := g2PrismRadius 37) g2Upper35_data_ok ![g2Upper35Chart0, g2Upper35Chart1, g2Upper35Chart2] ?_ ?_ ?_
      g2Upper35_vertices_agree g2Upper35_pi_agrees g2Upper35_gamma_agrees ?_ v cap x
    · intro j
      fin_cases j
      · exact g2Upper35Chart0_ok
      · exact g2Upper35Chart1_ok
      · exact g2Upper35Chart2_ok
    · norm_num [g2Upper35, g2PrismRadius]
    · intro j
      fin_cases j <;> decide
    · intro j y hy
      exact g2Upper35_cone j hy
  · intro v cap x _
    refine g2CheckedRows (P := g2Upper36) (b := g2Upper36Base) (π := g2Upper36Pi)
      (slope := g2Upper36Slope) (ρ := g2PrismRadius 38) g2Upper36_data_ok ![g2Upper36Chart0, g2Upper36Chart1, g2Upper36Chart2] ?_ ?_ ?_
      g2Upper36_vertices_agree g2Upper36_pi_agrees g2Upper36_gamma_agrees ?_ v cap x
    · intro j
      fin_cases j
      · exact g2Upper36Chart0_ok
      · exact g2Upper36Chart1_ok
      · exact g2Upper36Chart2_ok
    · norm_num [g2Upper36, g2PrismRadius]
    · intro j
      fin_cases j <;> decide
    · intro j y hy
      exact g2Upper36_cone j hy


/-- The adaptive deep-facet G2 certificate with every real vertex row discharged. -/
theorem rowAt_deepFacet_adaptive {t : Profile} (ht : OrderedInterior t) (hd : t 3 ≤ 1 / 500)
    (hf : facetCoord t ≤ 1 / 20) (hε : 1 / 8 ≤ vertexDepth t)
    (hσ : 1 / 5 ≤ sigma t) : RowAt criticalQ t :=
  rowAt_deepFacet_of_adaptive_prisms g2NumericRows_checked ht hd hf hε hσ

end HlawkaSchatten.BelowExponent
