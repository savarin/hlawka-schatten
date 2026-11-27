/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetArchive.NearChecker

/-! Exact checks for the two imbalance halves at each weighted F knot. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FSlabCheck

open FacetNumeric Tangent

structure Band where
  knot : Fin 157
  weight : Nat
  high : Bool

def lengthNum (P : Band) : Nat := if P.knot.val < 156 then 74 + P.knot.val else 7
def lengthDen (P : Band) : Nat := if P.knot.val < 156 then 4096 else 125
def profileDen (P : Band) : Nat := 8 * lengthDen P
def commonDen (P : Band) : Nat := 800 * lengthDen P
def edgeNum (P : Band) (edge : Bool) : Nat := (if P.high then 1 else 0) + (if edge then 1 else 0)

def profile (P : Band) (edge : Bool) : TC.V4 :=
  let d := lengthDen P
  let m := lengthNum P
  let n := edgeNum P edge
  ⟨4*(d-m)+n*d, 4*(d-m)-n*d, 8*m, 0⟩

def pi (P : Band) (edge : Bool) : List Nat :=
  let d := lengthDen P
  let n := edgeNum P edge
  [P.weight*(4-n)*d, P.weight*(4+n)*d, (100-P.weight)*4*d, (100-P.weight)*4*d]

def gamma (P : Band) : List Nat :=
  let d := lengthDen P
  let m := lengthNum P
  let g := 4*(100*d-P.weight*(d-m))
  [g,g,8*P.weight*(d-m)]

def terms (P : Band) (j : Fin 3) (v p : Bool) : List TC.Tm :=
  TC.mkTms ctx.Da j.val (chartA j).val (chartB j).val (pi P p) (profile P v)

def groups (P : Band) (j : Fin 3) : Fin 3 → List TC.Tm :=
  ![terms P j false false ++ terms P j false false,
    terms P j true true ++ terms P j true true,
    terms P j false true ++ terms P j true false]

def face (P : Band) (j : Fin 3) : TC.Face :=
  let G := (gamma P).map (2*·)
  let F := TC.mkFace ctx [] (profileDen P) [] G j.val (chartA j).val (chartB j).val
  { F with terms := (List.finRange 3).map (groups P j) }

def radius : Prism := {
  vertices := [], profileDen := 1, pi := [], slope := [], radiusNum := 1, radiusDen := 64 }

def movement (P : Band) (A B : Nat) (t : TC.Tm) : ℚ :=
  |(TC.gInt t (Nat.ble ctx.Da A) (nearShiftedMag A) (Nat.ble ctx.Da B) (nearShiftedMag B) : ℚ) /
      ((profileDen P : ℚ) * ctx.Da)| - 1

def nearGroup (P : Band) (j : Fin 3) (A B : Nat) (r s : ℚ) (ts : List TC.Tm) : Bool :=
  let g i := ((gamma P).getD i 0 : ℚ)
  let input := 2*(g j.val + g (chartA j).val*(nearIntercept r-nearSlope r*nearMagnitude A) +
    g (chartB j).val*(nearIntercept s-nearSlope s*nearMagnitude B))
  let output := (ts.map fun t => (t.p : ℚ)*nearUpper (movement P A B t)).sum
  ts.all (fun t => decide (-1 < movement P A B t)) && decide (output ≤ input)

def nearCorners (P : Band) (j : Fin 3) (a₀ a₁ b₀ b₁ : Nat) : Bool :=
  let r := nearAnchor a₀ a₁
  let s := nearAnchor b₀ b₁
  nearAxis a₀ a₁ && nearAxis b₀ b₁ &&
    (List.finRange 3).all fun i =>
      let ts := groups P j i
      nearGroup P j a₀ b₀ r s ts && nearGroup P j a₀ b₁ r s ts &&
      nearGroup P j a₁ b₀ r s ts && nearGroup P j a₁ b₁ r s ts

def leafOK (P : Band) (j : Fin 3) (F : TC.Face) (ca cb a₀ a₁ b₀ b₁ : Nat) : Bool :=
  if ca = 10001 then isConeBox radius j.val a₁ b₀ b₁
  else if ca = 10000 then nearCorners P j a₀ a₁ b₀ b₁
  else numericBoxOK F a₀ a₁ b₀ b₁ ca cb

def checkTree (P : Band) (j : Fin 3) (F : TC.Face) : RowTree → Nat → Nat → Nat → Nat → Bool
  | .splitA left right, a₀,a₁,b₀,b₁ =>
    let m := (a₀+a₁)/2
    Nat.blt a₀ m && Nat.blt m a₁ &&
      checkTree P j F left a₀ m b₀ b₁ && checkTree P j F right m a₁ b₀ b₁
  | .splitB left right, a₀,a₁,b₀,b₁ =>
    let m := (b₀+b₁)/2
    Nat.blt b₀ m && Nat.blt m b₁ &&
      checkTree P j F left a₀ a₁ b₀ m && checkTree P j F right a₀ a₁ m b₁
  | .box ca cb, a₀,a₁,b₀,b₁ => leafOK P j F ca cb a₀ a₁ b₀ b₁

def checkChart (P : Band) (j : Fin 3) (tree : RowTree) : Bool :=
  checkTree P j (face P j) tree 0 (2*ctx.Da) 0 (2*ctx.Da)

end HlawkaSchatten.BelowExponent.FSlabCheck
