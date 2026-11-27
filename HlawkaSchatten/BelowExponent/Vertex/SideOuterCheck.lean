/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CornerPowerTables
public import HlawkaSchatten.BelowExponent.Vertex.SideCornerData.RowTables

/-! Closed SC row checks at a single shared parameter corner. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

def scOuterAxes (i : Fin 34) (e : Bool) : OuterAxisBounds :=
  (scOuterAxisCache.get i).get ⟨e.toNat, by cases e <;> decide⟩

def scOuterSkips (k : Fin 3) (i j : Fin 34) : Bool :=
  ((scOuterSkipCache.get k).get i).testBit j.val

def scOuterFirst (k : Fin 3) : Fin 3 := ![1,0,0] k
def scOuterSecond (k : Fin 3) : Fin 3 := ![2,2,1] k

def scOuterBoxOK (P : OuterPointBounds) (k : Fin 3) (i j : Fin 34) : Bool :=
  [false,true].all fun x => [false,true].all fun y =>
    P.endpointOK k (scOuterFirst k) (scOuterSecond k) i j x y scOuterAxes outerRpowChordUpper

def scOuterRangeOK (P : OuterPointBounds) (k : Fin 3) (rows : List (Fin 34)) : Bool :=
  rows.all fun i => (List.finRange 34).all fun j => scOuterSkips k i j || scOuterBoxOK P k i j

def scOuterFaceOK (P : OuterPointBounds) (k : Fin 3) : Bool :=
  scOuterRangeOK P k (List.finRange 34)

end HlawkaSchatten.BelowExponent.Vertex
