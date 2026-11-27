/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Tangent.FineTable

/-! Per-vertex numerical corner checks for a fixed-weight facet prism. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

inductive RowTree where
  | splitA : RowTree → RowTree → RowTree
  | splitB : RowTree → RowTree → RowTree
  | box : Nat → Nat → RowTree

structure Prism where
  vertices : List TC.V4
  profileDen : Nat
  pi : List Nat
  slope : List Int
  radiusNum : Nat
  radiusDen : Nat

def ctx : TC.Ctx := TC.mkCtx {
  prof := TC.fine_prof, tab := TC.fine_tab, Dw := 2 ^ 30, KBOX := 30, CB := 10,
  rcN := 1, rcD := 500, etaN := 1, etaD := 500 }

def weightDen : Nat := 2 ^ 30

def inputNumerator (P : Prism) (v : TC.V4) (j : Nat) : Int :=
  ((weightDen : Int) - P.pi.getD 3 0 - P.pi.getD j 0) * P.profileDen +
    (2 * (P.pi.getD 3 0 : Int) - weightDen) * ([v.v0, v.v1, v.v2].getD j 0) +
    P.slope.getD j 0 * v.v3

def vertexInputs (P : Prism) (v : TC.V4) : List Int :=
  [inputNumerator P v 0, inputNumerator P v 1, inputNumerator P v 2]

def dataOK (P : Prism) : Bool :=
  P.vertices.length == 6 && P.pi.length == 4 && P.slope.length == 3 &&
  Nat.blt 0 P.profileDen && Nat.blt 0 P.radiusNum &&
  Nat.blt (2 * P.radiusNum) P.radiusDen && P.pi.sum == weightDen &&
  P.vertices.all fun v =>
    v.v0 + v.v1 + v.v2 + v.v3 == P.profileDen &&
      let g := vertexInputs P v
      g.all (fun numerator => decide (0 ≤ numerator)) &&
      Nat.ble (g.map Int.toNat).sum (weightDen * P.profileDen)

def chartFaces (P : Prism) (j k l : Nat) : List (Bool × TC.Face) :=
  let p := P.pi.map (· * P.profileDen)
  P.vertices.map fun v =>
    (v.v3 == 0, TC.mkFace ctx [v] P.profileDen p ((vertexInputs P v).map Int.toNat) j k l)

def isConeBox (P : Prism) (j A2 B1 B2 : Nat) : Bool :=
  let scale := P.radiusDen + P.radiusNum
  let bound := ctx.Da * P.radiusDen
  Nat.ble bound ((ctx.Da - A2) * scale) &&
    (if j = 0 then Nat.ble bound ((ctx.Da - B2) * scale)
     else Nat.ble bound ((B1 - ctx.Da) * scale))

def numericBoxOK (F : TC.Face) (A1 A2 B1 B2 ca cb : Nat) : Bool :=
  TC.leafOK ctx F A1 A2 B1 B2 ca cb
    (TC.lmaxAt ctx F A1 B1) (TC.lmaxAt ctx F A1 B2)
    (TC.lmaxAt ctx F A2 B1) (TC.lmaxAt ctx F A2 B2)

def checkTree (P : Prism) (j : Nat) (faces : List (Bool × TC.Face)) :
    RowTree → Nat → Nat → Nat → Nat → Bool
  | .splitA left right, A1, A2, B1, B2 =>
    let m := (A1 + A2) / 2
    Nat.blt A1 m && Nat.blt m A2 &&
      checkTree P j faces left A1 m B1 B2 && checkTree P j faces right m A2 B1 B2
  | .splitB left right, A1, A2, B1, B2 =>
    let m := (B1 + B2) / 2
    Nat.blt B1 m && Nat.blt m B2 &&
      checkTree P j faces left A1 A2 B1 m && checkTree P j faces right A1 A2 m B2
  | .box ca cb, A1, A2, B1, B2 =>
    let closedCone := isConeBox P j A2 B1 B2
    faces.all fun (onBase, F) =>
      (onBase && closedCone) || numericBoxOK F A1 A2 B1 B2 ca cb

def checkChart (P : Prism) (j k l : Nat) (tree : RowTree) : Bool :=
  checkTree P j (chartFaces P j k l) tree 0 (2 * ctx.Da) 0 (2 * ctx.Da)

end HlawkaSchatten.BelowExponent.FacetNumeric
