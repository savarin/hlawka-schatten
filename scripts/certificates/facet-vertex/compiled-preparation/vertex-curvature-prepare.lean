module

public meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureCheck
public meta import HlawkaSchatten.BelowExponent.Vertex.RootData.VcM000
public meta import HlawkaSchatten.BelowExponent.Vertex.RootData.ScS000

/-! Candidate search only. `CurvaturePilotData` rechecks the displayed numbers in the kernel. -/

open HlawkaSchatten.BelowExponent.Vertex

meta def printCurvatureCandidate (name : String) (c : ParameterCell) (roots : Fin 3 → RatBounds)
    (na nb nη : ℕ) : IO Unit := do
  let rows := (c.grid na nb nη).map fun d => Vector.ofFn (axisCoefficientIntervals d roots)
  let indices := List.finRange 3
  let upper := fun k i => rows.foldl (fun a v => max a (curvatureInterval (v.get k) i).hi) 0
  let weights := rows.flatMap fun v => indices.map fun j => ((v.get 0).weight.get j).value
  let lower := weights.foldl (fun a b => min a b.lo) (10 * (DyadicBounds.units : ℤ))
  let fixedPoint (n : ℤ) : ℚ := (n : ℚ) / DyadicBounds.units
  let maxima := Vector.ofFn fun k => Vector.ofFn fun i =>
    (⌈fixedPoint (upper k i) * (10^8 : ℚ)⌉ : ℚ) / 10^8
  let caps := fun k i => (maxima.get k).get i
  let floor := (⌊fixedPoint lower * (10^8 : ℚ)⌋ : ℚ) / 10^8
  let margins := indices.map fun i => (⌈curvatureLoss c caps i * (10^10 : ℚ)⌉ : ℚ) / 10^10
  let ok := rows.all fun v => (indices.all fun j => ((v.get 0).weight.get j).value.lowerOK floor) &&
    (indices.all fun k => indices.all fun i => (curvatureInterval (v.get k) i).upperOK (caps k i))
  if !ok || decide (floor ≤ 0) then
    throw (IO.userError (name ++ " failed the interval guards or weight floor"))
  let number (x : ℚ) := s!"{x.num}/{x.den}"
  let columns := [name, toString na, toString nb, toString nη] ++
    (indices.flatMap fun k => indices.map (fun i => number (caps k i))) ++
    [number floor] ++ margins.map number
  IO.println (String.intercalate "\t" columns)

#eval printCurvatureCandidate "vcM0" vcM0Cell vcM0Roots 6 6 2
#eval printCurvatureCandidate "scS0" scS0Cell scS0Roots 6 6 2
