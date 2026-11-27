import HlawkaSchatten.BelowExponent.Vertex.CurvatureData.VcM58.Config

open HlawkaSchatten.BelowExponent.Vertex

/- Exact schedule preparation on VC-M 58. The written output is candidate data. -/

private def sigmaAt (a b : ℚ) : ℚ := a + b - a^2 - a*b - b^2

private def sigmaEndpoints (c : ParameterCell) : RatBounds :=
  ⟨sigmaAt c.a.lo c.b.lo, sigmaAt c.a.hi c.b.hi⟩

private def sigmaTight (c : ParameterCell) (k : Fin 3) : IntervalJet :=
  let old := radicalSigmaInterval c k
  { old with value := old.value.intersect (DyadicBounds.ofRat (sigmaEndpoints c)) }

private def radicalTight (c : ParameterCell) (roots : Fin 3 → RatBounds)
    (k j : Fin 3) : IntervalJet :=
  let a := radicalBaseInterval c k j
  let b := radicalOtherInterval c k j
  let s := sigmaTight c k
  let power := radicalPowerInterval a b s
  let r₀ := DyadicBounds.ofRat (roots j)
  let r₁ := r₀.refineRadical power
  let r₂ := r₁.refineRadical power
  let r₃ := r₂.refineRadical power
  IntervalJet.radical r₃ a b s

private def tightAxes (c : ParameterCell) (roots : Fin 3 → RatBounds) (k : Fin 3) :
    AxisCoefficientIntervals :=
  axisCoefficientsFromRadicals c k (Vector.ofFn (radicalTight c roots k))

private def roundUp (x : ℚ) (scale : ℕ) : ℚ := (⌈x * scale⌉ : ℤ) / (scale : ℚ)
private def roundDown (x : ℚ) (scale : ℕ) : ℚ := (⌊x * scale⌋ : ℤ) / (scale : ℚ)

private structure Result where
  caps : Vector (Vector ℚ 3) 3
  floor : ℚ
  margins : Vector ℚ 3
  excess : Vector ℚ 3

private def prepare
    (axes : ParameterCell → (Fin 3 → RatBounds) → Fin 3 → AxisCoefficientIntervals)
    (na nb nη : ℕ) : Option Result := do
  let indices := List.finRange 3
  let cells := vcM58Cell.grid na nb nη
  let checkSigma (d : ParameterCell) := decide
    (0 ≤ 1-2*d.a.hi-d.b.hi ∧ 0 ≤ 1-d.a.hi-2*d.b.hi)
  guard (cells.all checkSigma)
  let data := cells.map fun d => Vector.ofFn (axes d vcM58Roots)
  let curv := fun (row : Vector AxisCoefficientIntervals 3) k j => curvatureInterval (row.get k) j
  let weight := fun (row : Vector AxisCoefficientIntervals 3) j => ((row.get 0).weight.get j).value
  guard (data.all fun row => indices.all (fun j => (weight row j).ok) &&
    indices.all (fun k => indices.all (fun j => (curv row k j).ok)))
  let caps := Vector.ofFn fun k => Vector.ofFn fun j =>
    roundUp (data.foldl (fun hi row => max hi (curv row k j).upper) 0) 100000000
  let floor := roundDown (data.foldl (fun lo row => indices.foldl
    (fun lo j => min lo (weight row j).lower) lo) (100 : ℚ)) 100000000
  let margins := Vector.ofFn fun j => roundUp (curvatureLoss vcM58Cell
    (fun k j => (caps.get k).get j) j) 10000000000
  let excess := Vector.ofFn fun j => margins.get j - vcM58Margins j
  return ⟨caps, floor, margins, excess⟩

private def working (r : Result) : Bool :=
  decide (0 < r.floor) && (List.finRange 3).all fun i => decide (r.excess.get i ≤ 0)

private def formatValues (v : Vector ℚ 3) : List String := v.toList.map toString

private def ordinarySchedules : List (Nat × Nat × Nat) :=
  let counts := [1, 2, 4, 8, 10, 12, 14, 16]
  (counts.flatMap fun na => counts.flatMap fun nb =>
    [1, 2, 3, 4].map fun nη => (na, nb, nη)).filter fun (na, nb, nη) => na*nb*nη ≤ 512

private def finerOneDepthSchedules : List (Nat × Nat × Nat) :=
  [(16,17,1), (17,16,1), (16,18,1), (18,16,1), (17,17,1), (17,18,1), (18,17,1),
   (18,18,1), (18,19,1), (19,18,1), (19,19,1), (18,20,1), (20,18,1), (20,20,1), (22,22,1)]

def main (args : List String) : IO Unit := do
  let schedules ← match args with
    | [] => pure ordinarySchedules
    | ["fine-one-depth"] => pure finerOneDepthSchedules
    | _ => throw (IO.userError "Expected no option or fine-one-depth")
  let schedules := schedules.mergeSort fun (na, nb, nη) (ma, mb, mη) => na*nb*nη ≤ ma*mb*mη
  let original := (radicalSigmaInterval vcM58Cell 0).value
  let tight := (sigmaTight vcM58Cell 0).value
  IO.eprintln s!"original parent sigma interval {original.lower} {original.upper}"
  IO.eprintln s!"revised parent sigma interval {tight.lower} {tight.upper}"
  IO.eprintln s!"exact sigma endpoints {(sigmaEndpoints vcM58Cell).lo} {(sigmaEndpoints vcM58Cell).hi}"
  IO.eprintln s!"testing {schedules.length} matched schedules"
  IO.println "formula\tna\tnb\tnη\tsubcells\tstatus\tweightFloor\tmargin0\tmargin1\tmargin2\texcess0\texcess1\texcess2\tcap00\tcap01\tcap02\tcap10\tcap11\tcap12\tcap20\tcap21\tcap22"
  for (na, nb, nη) in schedules do
    for (label, axes) in [("original", axisCoefficientIntervals), ("sigmaEndpoints", tightAxes)] do
      let rowStart := [label, toString na, toString nb, toString nη, toString (na*nb*nη)]
      match prepare axes na nb nη with
      | none => IO.println (String.intercalate "\t" (rowStart ++ ["domain failed"]))
      | some r =>
        let status := if working r then "fits" else "excess"
        IO.println (String.intercalate "\t" (rowStart ++ [status, toString r.floor] ++
          formatValues r.margins ++ formatValues r.excess ++ r.caps.toList.flatMap formatValues))
