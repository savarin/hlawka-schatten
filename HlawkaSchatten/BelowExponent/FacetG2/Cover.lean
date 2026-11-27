/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetG2.TriangleSplit
public import HlawkaSchatten.BelowExponent.FacetG2.Tip0Real
public import HlawkaSchatten.BelowExponent.FacetG2.Tip1Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper0Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper1Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper2Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper3Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper4Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper5Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper6Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper7Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper8Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper9Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper10Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper11Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper12Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper13Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper14Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper15Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper16Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper17Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper18Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper19Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper20Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper21Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper22Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper23Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper24Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper25Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper26Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper27Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper28Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper29Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper30Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper31Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper32Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper33Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper34Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper35Real
public import HlawkaSchatten.BelowExponent.FacetG2.Upper36Real

/-! Certificate data for the G2 facet triangles: `Cover`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open FacetNumeric

noncomputable section

set_option maxRecDepth 20000
set_option maxHeartbeats 0

def g2PrismBase (i : Fin 39) : Fin 3 → Row :=
  match i.val with
  | 0 => g2Tip0Base
  | 1 => g2Tip1Base
  | 2 => g2Upper0Base
  | 3 => g2Upper1Base
  | 4 => g2Upper2Base
  | 5 => g2Upper3Base
  | 6 => g2Upper4Base
  | 7 => g2Upper5Base
  | 8 => g2Upper6Base
  | 9 => g2Upper7Base
  | 10 => g2Upper8Base
  | 11 => g2Upper9Base
  | 12 => g2Upper10Base
  | 13 => g2Upper11Base
  | 14 => g2Upper12Base
  | 15 => g2Upper13Base
  | 16 => g2Upper14Base
  | 17 => g2Upper15Base
  | 18 => g2Upper16Base
  | 19 => g2Upper17Base
  | 20 => g2Upper18Base
  | 21 => g2Upper19Base
  | 22 => g2Upper20Base
  | 23 => g2Upper21Base
  | 24 => g2Upper22Base
  | 25 => g2Upper23Base
  | 26 => g2Upper24Base
  | 27 => g2Upper25Base
  | 28 => g2Upper26Base
  | 29 => g2Upper27Base
  | 30 => g2Upper28Base
  | 31 => g2Upper29Base
  | 32 => g2Upper30Base
  | 33 => g2Upper31Base
  | 34 => g2Upper32Base
  | 35 => g2Upper33Base
  | 36 => g2Upper34Base
  | 37 => g2Upper35Base
  | _ => g2Upper36Base

def g2PrismData (i : Fin 39) : Prism :=
  match i.val with
  | 0 => g2Tip0
  | 1 => g2Tip1
  | 2 => g2Upper0
  | 3 => g2Upper1
  | 4 => g2Upper2
  | 5 => g2Upper3
  | 6 => g2Upper4
  | 7 => g2Upper5
  | 8 => g2Upper6
  | 9 => g2Upper7
  | 10 => g2Upper8
  | 11 => g2Upper9
  | 12 => g2Upper10
  | 13 => g2Upper11
  | 14 => g2Upper12
  | 15 => g2Upper13
  | 16 => g2Upper14
  | 17 => g2Upper15
  | 18 => g2Upper16
  | 19 => g2Upper17
  | 20 => g2Upper18
  | 21 => g2Upper19
  | 22 => g2Upper20
  | 23 => g2Upper21
  | 24 => g2Upper22
  | 25 => g2Upper23
  | 26 => g2Upper24
  | 27 => g2Upper25
  | 28 => g2Upper26
  | 29 => g2Upper27
  | 30 => g2Upper28
  | 31 => g2Upper29
  | 32 => g2Upper30
  | 33 => g2Upper31
  | 34 => g2Upper32
  | 35 => g2Upper33
  | 36 => g2Upper34
  | 37 => g2Upper35
  | _ => g2Upper36

def g2PrismRadius (i : Fin 39) : ℝ :=
  match i.val with
  | 0 => 1/16
  | 1 => 1/16
  | 2 => 1/16
  | 3 => 1/16
  | 4 => 1/16
  | 5 => 1/16
  | 6 => 1/16
  | 7 => 1/16
  | 8 => 1/16
  | 9 => 1/16
  | 10 => 1/16
  | 11 => 1/16
  | 12 => 1/16
  | 13 => 1/16
  | 14 => 1/16
  | 15 => 1/16
  | 16 => 1/16
  | 17 => 1/16
  | 18 => 1/16
  | 19 => 1/16
  | 20 => 1/16
  | 21 => 1/16
  | 22 => 1/16
  | 23 => 1/16
  | 24 => 1/16
  | 25 => 1/16
  | 26 => 1/32
  | 27 => 1/32
  | 28 => 1/16
  | 29 => 1/16
  | 30 => 1/16
  | 31 => 1/16
  | 32 => 1/16
  | 33 => 1/16
  | 34 => 1/16
  | 35 => 1/16
  | 36 => 1/16
  | 37 => 1/16
  | _ => 1/16

def G2NumericRows (p : Fin 39) : Prop :=
  ∀ (i : Fin 3) (cap : Bool) (x : Row),
    (cap = true ∨ ¬ FacetRatioCone (g2PrismRadius p) x) →
    WeightedRow criticalQ (realVertex (g2PrismData p) i cap) (realPi (g2PrismData p))
      (realGamma (g2PrismData p) i cap) x

theorem g2PrismRows_of_numeric (h : ∀ p, G2NumericRows p) (p : Fin 39) :
    G2TriangleRows criticalQ (g2PrismBase p) := by
  fin_cases p
  · apply g2TriangleRows_of_weights
    intro w d hw hs hd₀ hd
    exact rowAt_g2Tip0_of_numeric_rows (h 0) hw hs hd₀ hd
  · apply g2TriangleRows_of_weights
    intro w d hw hs hd₀ hd
    exact rowAt_g2Tip1_of_numeric_rows (h 1) hw hs hd₀ hd
  · apply g2TriangleRows_of_weights
    intro w d hw hs hd₀ hd
    exact rowAt_g2Upper0_of_numeric_rows (h 2) hw hs hd₀ hd
  · apply g2TriangleRows_of_weights
    intro w d hw hs hd₀ hd
    exact rowAt_g2Upper1_of_numeric_rows (h 3) hw hs hd₀ hd
  · apply g2TriangleRows_of_weights
    intro w d hw hs hd₀ hd
    exact rowAt_g2Upper2_of_numeric_rows (h 4) hw hs hd₀ hd
  · apply g2TriangleRows_of_weights
    intro w d hw hs hd₀ hd
    exact rowAt_g2Upper3_of_numeric_rows (h 5) hw hs hd₀ hd
  · apply g2TriangleRows_of_weights
    intro w d hw hs hd₀ hd
    exact rowAt_g2Upper4_of_numeric_rows (h 6) hw hs hd₀ hd
  · apply g2TriangleRows_of_weights
    intro w d hw hs hd₀ hd
    exact rowAt_g2Upper5_of_numeric_rows (h 7) hw hs hd₀ hd
  · apply g2TriangleRows_of_weights
    intro w d hw hs hd₀ hd
    exact rowAt_g2Upper6_of_numeric_rows (h 8) hw hs hd₀ hd
  · apply g2TriangleRows_of_weights
    intro w d hw hs hd₀ hd
    exact rowAt_g2Upper7_of_numeric_rows (h 9) hw hs hd₀ hd
  · apply g2TriangleRows_of_weights
    intro w d hw hs hd₀ hd
    exact rowAt_g2Upper8_of_numeric_rows (h 10) hw hs hd₀ hd
  · apply g2TriangleRows_of_weights
    intro w d hw hs hd₀ hd
    exact rowAt_g2Upper9_of_numeric_rows (h 11) hw hs hd₀ hd
  · apply g2TriangleRows_of_weights
    intro w d hw hs hd₀ hd
    exact rowAt_g2Upper10_of_numeric_rows (h 12) hw hs hd₀ hd
  · apply g2TriangleRows_of_weights
    intro w d hw hs hd₀ hd
    exact rowAt_g2Upper11_of_numeric_rows (h 13) hw hs hd₀ hd
  · apply g2TriangleRows_of_weights
    intro w d hw hs hd₀ hd
    exact rowAt_g2Upper12_of_numeric_rows (h 14) hw hs hd₀ hd
  · apply g2TriangleRows_of_weights
    intro w d hw hs hd₀ hd
    exact rowAt_g2Upper13_of_numeric_rows (h 15) hw hs hd₀ hd
  · apply g2TriangleRows_of_weights
    intro w d hw hs hd₀ hd
    exact rowAt_g2Upper14_of_numeric_rows (h 16) hw hs hd₀ hd
  · apply g2TriangleRows_of_weights
    intro w d hw hs hd₀ hd
    exact rowAt_g2Upper15_of_numeric_rows (h 17) hw hs hd₀ hd
  · apply g2TriangleRows_of_weights
    intro w d hw hs hd₀ hd
    exact rowAt_g2Upper16_of_numeric_rows (h 18) hw hs hd₀ hd
  · apply g2TriangleRows_of_weights
    intro w d hw hs hd₀ hd
    exact rowAt_g2Upper17_of_numeric_rows (h 19) hw hs hd₀ hd
  · apply g2TriangleRows_of_weights
    intro w d hw hs hd₀ hd
    exact rowAt_g2Upper18_of_numeric_rows (h 20) hw hs hd₀ hd
  · apply g2TriangleRows_of_weights
    intro w d hw hs hd₀ hd
    exact rowAt_g2Upper19_of_numeric_rows (h 21) hw hs hd₀ hd
  · apply g2TriangleRows_of_weights
    intro w d hw hs hd₀ hd
    exact rowAt_g2Upper20_of_numeric_rows (h 22) hw hs hd₀ hd
  · apply g2TriangleRows_of_weights
    intro w d hw hs hd₀ hd
    exact rowAt_g2Upper21_of_numeric_rows (h 23) hw hs hd₀ hd
  · apply g2TriangleRows_of_weights
    intro w d hw hs hd₀ hd
    exact rowAt_g2Upper22_of_numeric_rows (h 24) hw hs hd₀ hd
  · apply g2TriangleRows_of_weights
    intro w d hw hs hd₀ hd
    exact rowAt_g2Upper23_of_numeric_rows (h 25) hw hs hd₀ hd
  · apply g2TriangleRows_of_weights
    intro w d hw hs hd₀ hd
    exact rowAt_g2Upper24_of_numeric_rows (h 26) hw hs hd₀ hd
  · apply g2TriangleRows_of_weights
    intro w d hw hs hd₀ hd
    exact rowAt_g2Upper25_of_numeric_rows (h 27) hw hs hd₀ hd
  · apply g2TriangleRows_of_weights
    intro w d hw hs hd₀ hd
    exact rowAt_g2Upper26_of_numeric_rows (h 28) hw hs hd₀ hd
  · apply g2TriangleRows_of_weights
    intro w d hw hs hd₀ hd
    exact rowAt_g2Upper27_of_numeric_rows (h 29) hw hs hd₀ hd
  · apply g2TriangleRows_of_weights
    intro w d hw hs hd₀ hd
    exact rowAt_g2Upper28_of_numeric_rows (h 30) hw hs hd₀ hd
  · apply g2TriangleRows_of_weights
    intro w d hw hs hd₀ hd
    exact rowAt_g2Upper29_of_numeric_rows (h 31) hw hs hd₀ hd
  · apply g2TriangleRows_of_weights
    intro w d hw hs hd₀ hd
    exact rowAt_g2Upper30_of_numeric_rows (h 32) hw hs hd₀ hd
  · apply g2TriangleRows_of_weights
    intro w d hw hs hd₀ hd
    exact rowAt_g2Upper31_of_numeric_rows (h 33) hw hs hd₀ hd
  · apply g2TriangleRows_of_weights
    intro w d hw hs hd₀ hd
    exact rowAt_g2Upper32_of_numeric_rows (h 34) hw hs hd₀ hd
  · apply g2TriangleRows_of_weights
    intro w d hw hs hd₀ hd
    exact rowAt_g2Upper33_of_numeric_rows (h 35) hw hs hd₀ hd
  · apply g2TriangleRows_of_weights
    intro w d hw hs hd₀ hd
    exact rowAt_g2Upper34_of_numeric_rows (h 36) hw hs hd₀ hd
  · apply g2TriangleRows_of_weights
    intro w d hw hs hd₀ hd
    exact rowAt_g2Upper35_of_numeric_rows (h 37) hw hs hd₀ hd
  · apply g2TriangleRows_of_weights
    intro w d hw hs hd₀ hd
    exact rowAt_g2Upper36_of_numeric_rows (h 38) hw hs hd₀ hd

theorem g2TriangleRoots_of_prisms (rows : ∀ p : Fin 39, G2TriangleRows criticalQ (g2PrismBase p)) :
    ∀ upper side, G2TriangleRows criticalQ (g2SliceRoot upper side) := by
  intro upper side
  cases upper <;> cases side
  · have geometry : g2PrismBase 0 = g2SliceRoot false false := by
      funext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [g2PrismBase, g2Tip0Base, g2SliceRoot, g2Root,
          g2Point, g2Lower, g2Upper, g2SplitTriangle, Function.update,
          Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    rw [← geometry]
    exact @rows 0
  · have geometry : g2PrismBase 1 = g2SliceRoot false true := by
      funext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [g2PrismBase, g2Tip1Base, g2SliceRoot, g2Root,
          g2Point, g2Lower, g2Upper, g2SplitTriangle, Function.update,
          Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    rw [← geometry]
    exact @rows 1
  · refine g2TriangleRows_of_bisect (i := 1) (j := 2) (by decide) ?_ ?_
    · refine g2TriangleRows_of_bisect (i := 0) (j := 2) (by decide) ?_ ?_
      · refine g2TriangleRows_of_bisect (i := 1) (j := 2) (by decide) ?_ ?_
        · refine g2TriangleRows_of_bisect (i := 0) (j := 2) (by decide) ?_ ?_
          · have geometry : g2PrismBase 22 = g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SliceRoot true false) 1 2) 0 2) 1 2) 0 2 := by
              funext i j
              fin_cases i <;> fin_cases j <;>
                norm_num [g2PrismBase, g2Upper20Base, g2SliceRoot, g2Root,
                  g2Point, g2Lower, g2Upper, g2SplitTriangle, Function.update,
                  Pi.smul_apply, Pi.add_apply, smul_eq_mul]
            rw [← geometry]
            exact @rows 22
          · have geometry : g2PrismBase 23 = g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SliceRoot true false) 1 2) 0 2) 1 2) 2 0 := by
              funext i j
              fin_cases i <;> fin_cases j <;>
                norm_num [g2PrismBase, g2Upper21Base, g2SliceRoot, g2Root,
                  g2Point, g2Lower, g2Upper, g2SplitTriangle, Function.update,
                  Pi.smul_apply, Pi.add_apply, smul_eq_mul]
            rw [← geometry]
            exact @rows 23
        · have geometry : g2PrismBase 24 = g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SliceRoot true false) 1 2) 0 2) 2 1 := by
            funext i j
            fin_cases i <;> fin_cases j <;>
              norm_num [g2PrismBase, g2Upper22Base, g2SliceRoot, g2Root,
                g2Point, g2Lower, g2Upper, g2SplitTriangle, Function.update,
                Pi.smul_apply, Pi.add_apply, smul_eq_mul]
          rw [← geometry]
          exact @rows 24
      · refine g2TriangleRows_of_bisect (i := 0) (j := 2) (by decide) ?_ ?_
        · refine g2TriangleRows_of_bisect (i := 0) (j := 2) (by decide) ?_ ?_
          · have geometry : g2PrismBase 25 = g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SliceRoot true false) 1 2) 2 0) 0 2) 0 2 := by
              funext i j
              fin_cases i <;> fin_cases j <;>
                norm_num [g2PrismBase, g2Upper23Base, g2SliceRoot, g2Root,
                  g2Point, g2Lower, g2Upper, g2SplitTriangle, Function.update,
                  Pi.smul_apply, Pi.add_apply, smul_eq_mul]
            rw [← geometry]
            exact @rows 25
          · have geometry : g2PrismBase 26 = g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SliceRoot true false) 1 2) 2 0) 0 2) 2 0 := by
              funext i j
              fin_cases i <;> fin_cases j <;>
                norm_num [g2PrismBase, g2Upper24Base, g2SliceRoot, g2Root,
                  g2Point, g2Lower, g2Upper, g2SplitTriangle, Function.update,
                  Pi.smul_apply, Pi.add_apply, smul_eq_mul]
            rw [← geometry]
            exact @rows 26
        · refine g2TriangleRows_of_bisect (i := 0) (j := 1) (by decide) ?_ ?_
          · have geometry : g2PrismBase 27 = g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SliceRoot true false) 1 2) 2 0) 2 0) 0 1 := by
              funext i j
              fin_cases i <;> fin_cases j <;>
                norm_num [g2PrismBase, g2Upper25Base, g2SliceRoot, g2Root,
                  g2Point, g2Lower, g2Upper, g2SplitTriangle, Function.update,
                  Pi.smul_apply, Pi.add_apply, smul_eq_mul]
            rw [← geometry]
            exact @rows 27
          · refine g2TriangleRows_of_bisect (i := 0) (j := 2) (by decide) ?_ ?_
            · have geometry : g2PrismBase 28 = g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SliceRoot true false) 1 2) 2 0) 2 0) 1 0) 0 2 := by
                funext i j
                fin_cases i <;> fin_cases j <;>
                  norm_num [g2PrismBase, g2Upper26Base, g2SliceRoot, g2Root,
                    g2Point, g2Lower, g2Upper, g2SplitTriangle, Function.update,
                    Pi.smul_apply, Pi.add_apply, smul_eq_mul]
              rw [← geometry]
              exact @rows 28
            · refine g2TriangleRows_of_bisect (i := 0) (j := 1) (by decide) ?_ ?_
              · have geometry : g2PrismBase 29 = g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SliceRoot true false) 1 2) 2 0) 2 0) 1 0) 2 0) 0 1 := by
                  funext i j
                  fin_cases i <;> fin_cases j <;>
                    norm_num [g2PrismBase, g2Upper27Base, g2SliceRoot, g2Root,
                      g2Point, g2Lower, g2Upper, g2SplitTriangle, Function.update,
                      Pi.smul_apply, Pi.add_apply, smul_eq_mul]
                rw [← geometry]
                exact @rows 29
              · refine g2TriangleRows_of_bisect (i := 0) (j := 2) (by decide) ?_ ?_
                · have geometry : g2PrismBase 30 = g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SliceRoot true false) 1 2) 2 0) 2 0) 1 0) 2 0) 1 0) 0 2 := by
                    funext i j
                    fin_cases i <;> fin_cases j <;>
                      norm_num [g2PrismBase, g2Upper28Base, g2SliceRoot, g2Root,
                        g2Point, g2Lower, g2Upper, g2SplitTriangle, Function.update,
                        Pi.smul_apply, Pi.add_apply, smul_eq_mul]
                  rw [← geometry]
                  exact @rows 30
                · have geometry : g2PrismBase 31 = g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SliceRoot true false) 1 2) 2 0) 2 0) 1 0) 2 0) 1 0) 2 0 := by
                    funext i j
                    fin_cases i <;> fin_cases j <;>
                      norm_num [g2PrismBase, g2Upper29Base, g2SliceRoot, g2Root,
                        g2Point, g2Lower, g2Upper, g2SplitTriangle, Function.update,
                        Pi.smul_apply, Pi.add_apply, smul_eq_mul]
                  rw [← geometry]
                  exact @rows 31
    · refine g2TriangleRows_of_bisect (i := 1) (j := 2) (by decide) ?_ ?_
      · refine g2TriangleRows_of_bisect (i := 0) (j := 2) (by decide) ?_ ?_
        · have geometry : g2PrismBase 32 = g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SliceRoot true false) 2 1) 1 2) 0 2 := by
            funext i j
            fin_cases i <;> fin_cases j <;>
              norm_num [g2PrismBase, g2Upper30Base, g2SliceRoot, g2Root,
                g2Point, g2Lower, g2Upper, g2SplitTriangle, Function.update,
                Pi.smul_apply, Pi.add_apply, smul_eq_mul]
          rw [← geometry]
          exact @rows 32
        · refine g2TriangleRows_of_bisect (i := 0) (j := 1) (by decide) ?_ ?_
          · have geometry : g2PrismBase 33 = g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SliceRoot true false) 2 1) 1 2) 2 0) 0 1 := by
              funext i j
              fin_cases i <;> fin_cases j <;>
                norm_num [g2PrismBase, g2Upper31Base, g2SliceRoot, g2Root,
                  g2Point, g2Lower, g2Upper, g2SplitTriangle, Function.update,
                  Pi.smul_apply, Pi.add_apply, smul_eq_mul]
            rw [← geometry]
            exact @rows 33
          · refine g2TriangleRows_of_bisect (i := 0) (j := 2) (by decide) ?_ ?_
            · have geometry : g2PrismBase 34 = g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SliceRoot true false) 2 1) 1 2) 2 0) 1 0) 0 2 := by
                funext i j
                fin_cases i <;> fin_cases j <;>
                  norm_num [g2PrismBase, g2Upper32Base, g2SliceRoot, g2Root,
                    g2Point, g2Lower, g2Upper, g2SplitTriangle, Function.update,
                    Pi.smul_apply, Pi.add_apply, smul_eq_mul]
              rw [← geometry]
              exact @rows 34
            · have geometry : g2PrismBase 35 = g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SliceRoot true false) 2 1) 1 2) 2 0) 1 0) 2 0 := by
                funext i j
                fin_cases i <;> fin_cases j <;>
                  norm_num [g2PrismBase, g2Upper33Base, g2SliceRoot, g2Root,
                    g2Point, g2Lower, g2Upper, g2SplitTriangle, Function.update,
                    Pi.smul_apply, Pi.add_apply, smul_eq_mul]
              rw [← geometry]
              exact @rows 35
      · refine g2TriangleRows_of_bisect (i := 1) (j := 2) (by decide) ?_ ?_
        · refine g2TriangleRows_of_bisect (i := 0) (j := 2) (by decide) ?_ ?_
          · have geometry : g2PrismBase 36 = g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SliceRoot true false) 2 1) 2 1) 1 2) 0 2 := by
              funext i j
              fin_cases i <;> fin_cases j <;>
                norm_num [g2PrismBase, g2Upper34Base, g2SliceRoot, g2Root,
                  g2Point, g2Lower, g2Upper, g2SplitTriangle, Function.update,
                  Pi.smul_apply, Pi.add_apply, smul_eq_mul]
            rw [← geometry]
            exact @rows 36
          · have geometry : g2PrismBase 37 = g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SliceRoot true false) 2 1) 2 1) 1 2) 2 0 := by
              funext i j
              fin_cases i <;> fin_cases j <;>
                norm_num [g2PrismBase, g2Upper35Base, g2SliceRoot, g2Root,
                  g2Point, g2Lower, g2Upper, g2SplitTriangle, Function.update,
                  Pi.smul_apply, Pi.add_apply, smul_eq_mul]
            rw [← geometry]
            exact @rows 37
        · have geometry : g2PrismBase 38 = g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SliceRoot true false) 2 1) 2 1) 2 1 := by
            funext i j
            fin_cases i <;> fin_cases j <;>
              norm_num [g2PrismBase, g2Upper36Base, g2SliceRoot, g2Root,
                g2Point, g2Lower, g2Upper, g2SplitTriangle, Function.update,
                Pi.smul_apply, Pi.add_apply, smul_eq_mul]
          rw [← geometry]
          exact @rows 38
  · refine g2TriangleRows_of_bisect (i := 0) (j := 2) (by decide) ?_ ?_
    · refine g2TriangleRows_of_bisect (i := 1) (j := 2) (by decide) ?_ ?_
      · refine g2TriangleRows_of_bisect (i := 0) (j := 2) (by decide) ?_ ?_
        · refine g2TriangleRows_of_bisect (i := 1) (j := 2) (by decide) ?_ ?_
          · have geometry : g2PrismBase 2 = g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SliceRoot true true) 0 2) 1 2) 0 2) 1 2 := by
              funext i j
              fin_cases i <;> fin_cases j <;>
                norm_num [g2PrismBase, g2Upper0Base, g2SliceRoot, g2Root,
                  g2Point, g2Lower, g2Upper, g2SplitTriangle, Function.update,
                  Pi.smul_apply, Pi.add_apply, smul_eq_mul]
            rw [← geometry]
            exact @rows 2
          · have geometry : g2PrismBase 3 = g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SliceRoot true true) 0 2) 1 2) 0 2) 2 1 := by
              funext i j
              fin_cases i <;> fin_cases j <;>
                norm_num [g2PrismBase, g2Upper1Base, g2SliceRoot, g2Root,
                  g2Point, g2Lower, g2Upper, g2SplitTriangle, Function.update,
                  Pi.smul_apply, Pi.add_apply, smul_eq_mul]
            rw [← geometry]
            exact @rows 3
        · have geometry : g2PrismBase 4 = g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SliceRoot true true) 0 2) 1 2) 2 0 := by
            funext i j
            fin_cases i <;> fin_cases j <;>
              norm_num [g2PrismBase, g2Upper2Base, g2SliceRoot, g2Root,
                g2Point, g2Lower, g2Upper, g2SplitTriangle, Function.update,
                Pi.smul_apply, Pi.add_apply, smul_eq_mul]
          rw [← geometry]
          exact @rows 4
      · refine g2TriangleRows_of_bisect (i := 1) (j := 2) (by decide) ?_ ?_
        · refine g2TriangleRows_of_bisect (i := 1) (j := 2) (by decide) ?_ ?_
          · have geometry : g2PrismBase 5 = g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SliceRoot true true) 0 2) 2 1) 1 2) 1 2 := by
              funext i j
              fin_cases i <;> fin_cases j <;>
                norm_num [g2PrismBase, g2Upper3Base, g2SliceRoot, g2Root,
                  g2Point, g2Lower, g2Upper, g2SplitTriangle, Function.update,
                  Pi.smul_apply, Pi.add_apply, smul_eq_mul]
            rw [← geometry]
            exact @rows 5
          · have geometry : g2PrismBase 6 = g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SliceRoot true true) 0 2) 2 1) 1 2) 2 1 := by
              funext i j
              fin_cases i <;> fin_cases j <;>
                norm_num [g2PrismBase, g2Upper4Base, g2SliceRoot, g2Root,
                  g2Point, g2Lower, g2Upper, g2SplitTriangle, Function.update,
                  Pi.smul_apply, Pi.add_apply, smul_eq_mul]
            rw [← geometry]
            exact @rows 6
        · refine g2TriangleRows_of_bisect (i := 0) (j := 1) (by decide) ?_ ?_
          · refine g2TriangleRows_of_bisect (i := 1) (j := 2) (by decide) ?_ ?_
            · have geometry : g2PrismBase 7 = g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SliceRoot true true) 0 2) 2 1) 2 1) 0 1) 1 2 := by
                funext i j
                fin_cases i <;> fin_cases j <;>
                  norm_num [g2PrismBase, g2Upper5Base, g2SliceRoot, g2Root,
                    g2Point, g2Lower, g2Upper, g2SplitTriangle, Function.update,
                    Pi.smul_apply, Pi.add_apply, smul_eq_mul]
              rw [← geometry]
              exact @rows 7
            · refine g2TriangleRows_of_bisect (i := 0) (j := 1) (by decide) ?_ ?_
              · have geometry : g2PrismBase 8 = g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SliceRoot true true) 0 2) 2 1) 2 1) 0 1) 2 1) 0 1 := by
                  funext i j
                  fin_cases i <;> fin_cases j <;>
                    norm_num [g2PrismBase, g2Upper6Base, g2SliceRoot, g2Root,
                      g2Point, g2Lower, g2Upper, g2SplitTriangle, Function.update,
                      Pi.smul_apply, Pi.add_apply, smul_eq_mul]
                rw [← geometry]
                exact @rows 8
              · have geometry : g2PrismBase 9 = g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SliceRoot true true) 0 2) 2 1) 2 1) 0 1) 2 1) 1 0 := by
                  funext i j
                  fin_cases i <;> fin_cases j <;>
                    norm_num [g2PrismBase, g2Upper7Base, g2SliceRoot, g2Root,
                      g2Point, g2Lower, g2Upper, g2SplitTriangle, Function.update,
                      Pi.smul_apply, Pi.add_apply, smul_eq_mul]
                rw [← geometry]
                exact @rows 9
          · refine g2TriangleRows_of_bisect (i := 0) (j := 1) (by decide) ?_ ?_
            · have geometry : g2PrismBase 10 = g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SliceRoot true true) 0 2) 2 1) 2 1) 1 0) 0 1 := by
                funext i j
                fin_cases i <;> fin_cases j <;>
                  norm_num [g2PrismBase, g2Upper8Base, g2SliceRoot, g2Root,
                    g2Point, g2Lower, g2Upper, g2SplitTriangle, Function.update,
                    Pi.smul_apply, Pi.add_apply, smul_eq_mul]
              rw [← geometry]
              exact @rows 10
            · have geometry : g2PrismBase 11 = g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SliceRoot true true) 0 2) 2 1) 2 1) 1 0) 1 0 := by
                funext i j
                fin_cases i <;> fin_cases j <;>
                  norm_num [g2PrismBase, g2Upper9Base, g2SliceRoot, g2Root,
                    g2Point, g2Lower, g2Upper, g2SplitTriangle, Function.update,
                    Pi.smul_apply, Pi.add_apply, smul_eq_mul]
              rw [← geometry]
              exact @rows 11
    · refine g2TriangleRows_of_bisect (i := 0) (j := 2) (by decide) ?_ ?_
      · refine g2TriangleRows_of_bisect (i := 1) (j := 2) (by decide) ?_ ?_
        · refine g2TriangleRows_of_bisect (i := 0) (j := 2) (by decide) ?_ ?_
          · refine g2TriangleRows_of_bisect (i := 1) (j := 2) (by decide) ?_ ?_
            · have geometry : g2PrismBase 12 = g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SliceRoot true true) 2 0) 0 2) 1 2) 0 2) 1 2 := by
                funext i j
                fin_cases i <;> fin_cases j <;>
                  norm_num [g2PrismBase, g2Upper10Base, g2SliceRoot, g2Root,
                    g2Point, g2Lower, g2Upper, g2SplitTriangle, Function.update,
                    Pi.smul_apply, Pi.add_apply, smul_eq_mul]
              rw [← geometry]
              exact @rows 12
            · have geometry : g2PrismBase 13 = g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SliceRoot true true) 2 0) 0 2) 1 2) 0 2) 2 1 := by
                funext i j
                fin_cases i <;> fin_cases j <;>
                  norm_num [g2PrismBase, g2Upper11Base, g2SliceRoot, g2Root,
                    g2Point, g2Lower, g2Upper, g2SplitTriangle, Function.update,
                    Pi.smul_apply, Pi.add_apply, smul_eq_mul]
              rw [← geometry]
              exact @rows 13
          · have geometry : g2PrismBase 14 = g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SliceRoot true true) 2 0) 0 2) 1 2) 2 0 := by
              funext i j
              fin_cases i <;> fin_cases j <;>
                norm_num [g2PrismBase, g2Upper12Base, g2SliceRoot, g2Root,
                  g2Point, g2Lower, g2Upper, g2SplitTriangle, Function.update,
                  Pi.smul_apply, Pi.add_apply, smul_eq_mul]
            rw [← geometry]
            exact @rows 14
        · refine g2TriangleRows_of_bisect (i := 1) (j := 2) (by decide) ?_ ?_
          · have geometry : g2PrismBase 15 = g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SliceRoot true true) 2 0) 0 2) 2 1) 1 2 := by
              funext i j
              fin_cases i <;> fin_cases j <;>
                norm_num [g2PrismBase, g2Upper13Base, g2SliceRoot, g2Root,
                  g2Point, g2Lower, g2Upper, g2SplitTriangle, Function.update,
                  Pi.smul_apply, Pi.add_apply, smul_eq_mul]
            rw [← geometry]
            exact @rows 15
          · refine g2TriangleRows_of_bisect (i := 0) (j := 1) (by decide) ?_ ?_
            · have geometry : g2PrismBase 16 = g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SliceRoot true true) 2 0) 0 2) 2 1) 2 1) 0 1 := by
                funext i j
                fin_cases i <;> fin_cases j <;>
                  norm_num [g2PrismBase, g2Upper14Base, g2SliceRoot, g2Root,
                    g2Point, g2Lower, g2Upper, g2SplitTriangle, Function.update,
                    Pi.smul_apply, Pi.add_apply, smul_eq_mul]
              rw [← geometry]
              exact @rows 16
            · have geometry : g2PrismBase 17 = g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SliceRoot true true) 2 0) 0 2) 2 1) 2 1) 1 0 := by
                funext i j
                fin_cases i <;> fin_cases j <;>
                  norm_num [g2PrismBase, g2Upper15Base, g2SliceRoot, g2Root,
                    g2Point, g2Lower, g2Upper, g2SplitTriangle, Function.update,
                    Pi.smul_apply, Pi.add_apply, smul_eq_mul]
              rw [← geometry]
              exact @rows 17
      · refine g2TriangleRows_of_bisect (i := 0) (j := 2) (by decide) ?_ ?_
        · refine g2TriangleRows_of_bisect (i := 1) (j := 2) (by decide) ?_ ?_
          · have geometry : g2PrismBase 18 = g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SliceRoot true true) 2 0) 2 0) 0 2) 1 2 := by
              funext i j
              fin_cases i <;> fin_cases j <;>
                norm_num [g2PrismBase, g2Upper16Base, g2SliceRoot, g2Root,
                  g2Point, g2Lower, g2Upper, g2SplitTriangle, Function.update,
                  Pi.smul_apply, Pi.add_apply, smul_eq_mul]
            rw [← geometry]
            exact @rows 18
          · have geometry : g2PrismBase 19 = g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SliceRoot true true) 2 0) 2 0) 0 2) 2 1 := by
              funext i j
              fin_cases i <;> fin_cases j <;>
                norm_num [g2PrismBase, g2Upper17Base, g2SliceRoot, g2Root,
                  g2Point, g2Lower, g2Upper, g2SplitTriangle, Function.update,
                  Pi.smul_apply, Pi.add_apply, smul_eq_mul]
            rw [← geometry]
            exact @rows 19
        · refine g2TriangleRows_of_bisect (i := 0) (j := 2) (by decide) ?_ ?_
          · have geometry : g2PrismBase 20 = g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SliceRoot true true) 2 0) 2 0) 2 0) 0 2 := by
              funext i j
              fin_cases i <;> fin_cases j <;>
                norm_num [g2PrismBase, g2Upper18Base, g2SliceRoot, g2Root,
                  g2Point, g2Lower, g2Upper, g2SplitTriangle, Function.update,
                  Pi.smul_apply, Pi.add_apply, smul_eq_mul]
            rw [← geometry]
            exact @rows 20
          · have geometry : g2PrismBase 21 = g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SliceRoot true true) 2 0) 2 0) 2 0) 2 0 := by
              funext i j
              fin_cases i <;> fin_cases j <;>
                norm_num [g2PrismBase, g2Upper19Base, g2SliceRoot, g2Root,
                  g2Point, g2Lower, g2Upper, g2SplitTriangle, Function.update,
                  Pi.smul_apply, Pi.add_apply, smul_eq_mul]
            rw [← geometry]
            exact @rows 21

/-- The entire deep-facet region from the cap and noncone real row estimates. -/
theorem rowAt_deepFacet_of_adaptive_prisms (hnumeric : ∀ p, G2NumericRows p)
    {t : Profile} (ht : OrderedInterior t) (hd : t 3 ≤ 1 / 500)
    (hf : facetCoord t ≤ 1 / 20) (hε : 1 / 8 ≤ vertexDepth t)
    (hσ : 1 / 5 ≤ sigma t) : RowAt criticalQ t := by
  apply rowAt_deepFacet_of_g2Band (t := t) (ht := ht) (hd := hd) (hf := hf) (hε := hε) (hσ := hσ)
  intro b d hb hd₀ hd'
  exact rowAt_g2Band_of_triangleRoots
    (g2TriangleRoots_of_prisms (g2PrismRows_of_numeric hnumeric)) hb hd₀ hd'

end

end HlawkaSchatten.BelowExponent
