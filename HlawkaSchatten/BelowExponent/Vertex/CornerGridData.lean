/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.RadicalCheck

/-! Grid B and the rational tests for a rectangle contained in the side cone. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

def outerNodes : Vector ℚ 35 := #v[-1, -7/8, -3/4, -5/8, -1/2, -3/8, -1/4, -7/32,
  -3/16, -5/32, -1/8, -3/32, -1/16, -1/32, -1/64, -1/128, -1/256, 0,
  1/256, 1/128, 1/64, 1/32, 1/16, 3/32, 1/8, 5/32, 3/16, 7/32, 1/4, 3/8,
  1/2, 5/8, 3/4, 7/8, 1]

def outerInterval (i : Fin 34) : RatBounds := ⟨outerNodes.get i.castSucc, outerNodes.get i.succ⟩

def outerEndpoint (r : RatBounds) (i : Bool) : ℚ := if i then r.hi else r.lo

def outerChartRow {R : Type*} [One R] (k : Fin 3) (u v : R) : Fin 3 → R :=
  ![![1,u,v], ![u,1,v], ![u,v,1]] k

def sideConeNormal (j : Fin 5) : Fin 3 → ℤ :=
  ![![-3,-8,0], ![3,1,0], ![-1,0,-4], ![4,0,1], ![-11,-8,-8]] j

def outerLinear {R : Type*} [Add R] [Mul R] (c z : Fin 3 → R) : R :=
  c 0*z 0 + c 1*z 1 + c 2*z 2

def outerSideSign (k : Fin 3) (u v : RatBounds) : ℚ :=
  if 0 < outerChartRow k u.lo v.lo 0 then 1 else -1

def outerSideSkip (k : Fin 3) (i j : Fin 34) : Bool :=
  let u := outerInterval i
  let v := outerInterval j
  let sign := outerSideSign k u v
  [false,true].all fun x => [false,true].all fun y =>
    let z := outerChartRow k (outerEndpoint u x) (outerEndpoint v y)
    decide (0 < sign*z 0) && (List.finRange 5).all fun d =>
      decide (0 ≤ sign*outerLinear (fun n => (sideConeNormal d n : ℚ)) z)

def outerChartGrid : List (Fin 3 × Fin 34 × Fin 34) :=
  (List.finRange 3).flatMap fun k =>
    (List.finRange 34).flatMap fun i => (List.finRange 34).map fun j => (k,i,j)

def outerSideGrid : List (Fin 3 × Fin 34 × Fin 34) :=
  outerChartGrid.filter fun (k,i,j) => !outerSideSkip k i j

theorem outerChartGrid_length : outerChartGrid.length = 3468 := by decide +kernel

theorem mem_outerChartGrid (k : Fin 3) (i j : Fin 34) : (k,i,j) ∈ outerChartGrid :=
  List.mem_flatMap.mpr ⟨k, List.mem_finRange k,
    List.mem_flatMap.mpr ⟨i, List.mem_finRange i, List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩⟩⟩

theorem mem_outerSideGrid {k : Fin 3} {i j : Fin 34} :
    (k,i,j) ∈ outerSideGrid ↔ outerSideSkip k i j = false := by
  simp [outerSideGrid, mem_outerChartGrid]

set_option maxHeartbeats 0 in
theorem outerSideGrid_length : outerSideGrid.length = 3383 := by decide +kernel

end HlawkaSchatten.BelowExponent.Vertex
