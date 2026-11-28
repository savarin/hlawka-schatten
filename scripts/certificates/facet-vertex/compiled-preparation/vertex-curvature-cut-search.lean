module

private def roundUp (v : ℚ) (scale : ℕ) : ℚ := (⌈v * scale⌉ : ℤ) / (scale : ℚ)
private def roundDown (v : ℚ) (scale : ℕ) : ℚ := (⌊v * scale⌋ : ℤ) / (scale : ℚ)

structure Variant where
  grid : Nat × Nat × Nat
  caps : Vector (Vector ℚ 3) 3
  floor : ℚ
  margin : Vector ℚ 3
  volume : Nat
  fallback : Bool := false

structure Plan where
  input : CurvatureCutInput
  choices : List Variant

private def prepareVariant (input : CurvatureCutInput) (na nb nd : Nat) : Option Variant := do
  let axes := (input.cell.grid na nb nd).map fun box => Vector.ofFn fun k =>
    axisCoefficientIntervals box input.roots k
  let curv := fun (data : Vector AxisCoefficientIntervals 3) k i => curvatureInterval (data.get k) i
  let weight := fun (data : Vector AxisCoefficientIntervals 3) i => ((data.get 0).weight.get i).value
  let good := axes.all fun data =>
    (List.finRange 3).all (fun i => (weight data i).ok) &&
    (List.finRange 3).all (fun k => (List.finRange 3).all fun i => (curv data k i).ok)
  guard good
  let caps := Vector.ofFn fun k => Vector.ofFn fun i =>
    roundUp (axes.foldl (fun hi data => max hi (curv data k i).upper) 0) 100000000
  let lower := axes.foldl (fun lo data => (List.finRange 3).foldl
    (fun lo i => min lo (weight data i).lower) lo) (100 : ℚ)
  let floor := roundDown lower 100000000
  guard (0 < floor)
  let margin := Vector.ofFn fun j => roundUp (curvatureLoss input.cell
    (fun k i => (caps.get k).get i) j) 10000000000
  return ⟨(na,nb,nd), caps, floor, margin, na*nb*nd, false⟩

private def makePlan (input : CurvatureCutInput) : Plan :=
  let presets := [(1,1,1),(2,2,1),(2,2,2),(4,4,2),(8,8,2)]
  let possible := presets.filterMap fun (a,b,d) =>
    if a*b*d < input.oldVolume then prepareVariant input a b d else none
  let fallback : Variant := ⟨(0,0,0), #v[#v[0,0,0],#v[0,0,0],#v[0,0,0]], 0,
    input.oldMargins, input.oldVolume, true⟩
  ⟨input, possible ++ [fallback]⟩

private def newDemands (plans : Array Plan) (points : Array SideCornerEntry) : Array (Vector ℚ 3) := Id.run do
  let mut demands := points.map SideCornerEntry.margin
  for plan in plans do
    let some v := plan.choices.head? | continue
    for i in plan.input.corners.toList do
      let some old := demands[i]? | continue
      demands := demands.set! i (Vector.ofFn fun k => max (old.get k) (v.margin.get k))
  return demands

private def walkFailures (demands : Array (Vector ℚ 3)) (points : Array SideCornerEntry)
    (roots : Array (Fin 3 → RatBounds)) (side : Bool)
    (previous : Array ((Vector ℚ 3) × Bool)) : IO (Array ((Vector ℚ 3) × Bool) × Array Bool × Nat) := do
  let mut next := #[]
  let mut failed := #[]
  let mut replayed := 0
  let skip := if side then scOuterSkips else fun _ _ _ => false
  for i in [:points.size] do
    let some p := points[i]? | throw (IO.userError s!"Point {i} is missing")
    let some r := roots[i]? | throw (IO.userError s!"Root bounds {i} are missing")
    let some m := demands[i]? | throw (IO.userError s!"Budget {i} is missing")
    let possible ←
      if m == p.margin then pure true
      else if let some (earlier, verdict) := previous[i]? then
        if m == earlier then pure verdict
        else do
          replayed := replayed + 1
          pure (outerSearchQuadrants (outerWideRectOK (.atPoint p.a p.b p.eta m r)) skip).isSome
      else do
        replayed := replayed + 1
        pure (outerSearchQuadrants (outerWideRectOK (.atPoint p.a p.b p.eta m r)) skip).isSome
    next := next.push (m,possible)
    failed := failed.push (!possible)
  return (next,failed,replayed)

private def downgrade (plan : Plan) (failures : Array Bool) (demands : Array (Vector ℚ 3))
    (points : Array SideCornerEntry) : Plan :=
  match plan.choices with
  | active :: next :: rest =>
    let blocked (i : Nat) : Bool := Id.run do
      if !(failures[i]?.getD false) then return false
      let some p := points[i]? | return false
      let some m := demands[i]? | return false
      return (List.finRange 3).any fun j =>
        decide (active.margin.get j = m.get j ∧ p.margin.get j < m.get j)
    if plan.input.corners.toList.any blocked then {plan with choices := next :: rest}
    else plan
  | _ => plan

private def toTsv (plan : Plan) : String :=
  match plan.choices.head? with
  | none => s!"{plan.input.name}\tOPEN"
  | some v =>
    let caps := (List.finRange 3).flatMap fun k => (List.finRange 3).map fun i =>
      toString ((v.caps.get k).get i)
    let margins := v.margin.toList.map toString
    let fields := [plan.input.name, toString plan.input.oldVolume, toString v.volume,
       toString v.grid.1, toString v.grid.2.1, toString v.grid.2.2, toString v.fallback,
       toString v.floor] ++ caps ++ margins
    String.intercalate "\t" fields

private def runFamily (name : String) (side : Bool) (cells : Array CurvatureCutInput)
    (points : Array SideCornerEntry) (roots : Array (Fin 3 → RatBounds)) : IO (Array Plan) := do
  IO.println s!"{name}: preparing {cells.size} parent boxes"
  let mut plans := cells.map makePlan
  let mut previous := #[]
  let baseline := cells.foldl (fun n c => n + c.oldVolume) 0
  for round in [:30] do
    let current := plans.foldl (fun n p => n + ((p.choices.head?).map Variant.volume).getD 0) 0
    let fallbacks := plans.foldl (fun n p => n + (if (p.choices.head?.map Variant.fallback).getD true then 1 else 0)) 0
    let margins := newDemands plans points
    let (next,failed,replayed) ← walkFailures margins points roots side previous
    let nfail := failed.foldl (fun n bad => n + bad.toNat) 0
    IO.println s!"{name}: round {round}, {current}/{baseline} candidate curvature subcells, {fallbacks} original parents, {nfail} open corners, {replayed} comparator calls"
    if nfail == 0 then
      return plans
    previous := next
    plans := plans.map (fun p => downgrade p failed margins points)
  throw (IO.userError s!"{name}: backoff exhausted")

def main (args : List String) : IO Unit := do
  let [destination] := args | throw (IO.userError "Expected a TSV output path")
  let vc ← runFamily "VC" false vcCutCells vcOuterPoints vcCutRoots
  let sc ← runFamily "SC" true scCutCells scOuterPoints scOuterRootTable
  let results := (vc ++ sc).toList.map toTsv
  IO.FS.writeFile destination (String.intercalate "\n" results ++ "\n")
