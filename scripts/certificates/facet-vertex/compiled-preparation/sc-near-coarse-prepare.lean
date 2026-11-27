import HlawkaSchatten.BelowExponent.Vertex.SideConeCoarseTree
import HlawkaSchatten.BelowExponent.Vertex.SideConeFastTree
import HlawkaSchatten.BelowExponent.Vertex.SideConeParameterGrid
import Std.Data.HashMap

/-! Prepare exact candidate witnesses. The generated sources replay every guard in the kernel. -/
open HlawkaSchatten.BelowExponent.Vertex

namespace SCPrepare

def upperIntegerRoot (target n : Nat) : Nat := Id.run do
  let mut lo := 0
  let mut hi := 1 <<< (Nat.log2 target / n + 1)
  while lo + 1 < hi do
    let mid := (lo + hi) / 2
    if mid ^ n ≤ target then lo := mid else hi := mid
  return lo

def powerBounds (x p : ℚ) : RatBounds :=
  let scale : Nat := 1 <<< 64
  let num := x.num.natAbs ^ p.num.natAbs * scale ^ p.den
  let den := x.den ^ p.num.natAbs
  let floor := upperIntegerRoot (num / den) p.den
  let upper := if floor ^ p.den * den = num then floor else floor + 1
  ⟨(floor : ℚ) / scale, (upper : ℚ) / scale⟩

def factors (P X : RatBounds) (increasing : Bool) : FactorSamples :=
  let l := argumentLower X increasing
  let h := argumentUpper X increasing
  ⟨powerBounds (1+l) (exponentLower P l), powerBounds (1+h) (exponentUpper P h)⟩

def roots (C : ParameterCell) (i : Fin 3) : RatBounds :=
  let A := C.base i
  let B := C.other i
  let S := C.sigma
  let l := powerBounds (A.lo^2 * B.lo^3 / S.hi^2) (1/5)
  let h := powerBounds (A.hi^2 * B.hi^3 / S.lo^2) (1/5)
  ⟨l.lo, h.hi⟩

def axis (I : RatBounds) : SideFastAxis :=
  let Q := sideNearExponent
  let R := Q.sub (RatBounds.point 1)
  let w : SideFastAxisSamples := ⟨factors R I false, factors Q I false, factors R I false⟩
  ⟨w, w.intervals I⟩

def grid : SideFastGrid :=
  let U := Vector.ofFn fun i => axis (sideURange i)
  let V := Vector.ofFn fun i => axis (sideVRange i)
  ⟨U.get,V.get⟩

def boundsText (I : RatBounds) := s!"⟨{I.lo}, {I.hi}⟩"

def cellText (C : ParameterCell) := s!"⟨{boundsText C.a}, {boundsText C.b}, {boundsText C.η}⟩"

def sampleText (W : FactorSamples) := s!"⟨{boundsText W.lowerPower}, {boundsText W.upperPower}⟩"

def dyadicText (I : DyadicBounds) := s!"⟨{I.lo}, {I.hi}, {I.ok}⟩"

def axisText (A : SideFastAxis) : String :=
  "⟨⟨" ++ String.intercalate ", " ([A.samples.first, A.samples.second, A.samples.slope].map sampleText) ++
    "⟩, ⟨" ++ String.intercalate ", " ([A.bounds.first, A.bounds.second, A.bounds.slope].map dyadicText) ++ "⟩⟩"

def diagText (D : SideFastDiagonalTerms) : String :=
  "⟨" ++ String.intercalate ", " ([D.d,D.first,D.slope,D.baseSquared,D.center].map dyadicText) ++ "⟩"

def termText (P : SideFastParameterTerms) : String :=
  "⟨" ++ String.intercalate ", " (
    [dyadicText P.value,dyadicText P.first,dyadicText P.second,dyadicText P.scale,
      diagText P.diagU,diagText P.diagV,dyadicText P.mixedU,dyadicText P.mixedV,dyadicText P.mixedBase]) ++ "⟩"

def parameterText (P : SideFastParameter) : String :=
  "⟨" ++ String.intercalate ", " (
    [cellText P.cell, "![" ++ String.intercalate ", " (List.ofFn fun i => boundsText (P.roots i)) ++ "]",
      sampleText P.first, sampleText P.slope, termText P.terms]) ++ "⟩"

def treeText : SideFastTree → String
  | .leaf i M => s!".leaf {i} {sampleText M}"
  | .bisect k l r => s!".bisect {k.val} ({treeText l}) ({treeText r})"

def treeSize : SideFastTree → Nat
  | .leaf .. => 1
  | .bisect _ l r => treeSize l + treeSize r

structure Cache where
  index : Std.HashMap String Nat := {}
  data : Array SideFastParameter := #[]

def parameter (C : ParameterCell) : SideFastParameter :=
  let base : SideNearBox := ⟨C, roots C, sideNearExponent, RatBounds.point 0, RatBounds.point 0⟩
  let P : SideFastParameter :=
    ⟨C, roots C, factors base.exponent base.baseShift true,
      factors base.slope base.baseShift false, defaultTerms⟩
  {P with terms := P.canonical}
where
  defaultTerms : SideFastParameterTerms :=
    let z : DyadicBounds := .ofNumerator 0
    let d : SideFastDiagonalTerms := ⟨z,z,z,z,z⟩
    ⟨z,z,z,z,d,d,z,z,z⟩

def getParameter (C : ParameterCell) : StateM Cache (Nat × SideFastParameter) := do
  let key := cellText C
  let cache ← get
  if let some i := cache.index[key]? then
    if let some P := cache.data[i]? then return (i,P)
  let P := parameter C
  let i := cache.data.size
  let updated : Cache := ⟨cache.index.insert key i,cache.data.push P⟩
  set updated
  return (i,P)

def tryLeaf (C : ParameterCell) (G : SideFastGrid) (row : Fin 27 × Fin 36) :
    StateM Cache (Option SideFastTree) := do
  let (i,P) ← getParameter C
  let u := sideURange row.1
  let v := sideVRange row.2
  let B := P.box u v
  let M := factors B.exponent B.argument false
  return if P.leafCheck u v (G.u row.1) (G.v row.2) M then some (.leaf i M) else none

def buildTree (G : SideFastGrid) (row : Fin 27 × Fin 36) (C : ParameterCell) (depth : Nat)
    (fuel : Nat) : StateM Cache (Option SideFastTree) := do
  if let some leaf ← tryLeaf C G row then return some leaf
  match fuel with
  | 0 => return none
  | fuel+1 =>
    -- Try each one-axis split before exploring a deeper subdivision.
    let order : List (Fin 3) := [⟨depth%3,Nat.mod_lt _ (by decide)⟩,
      ⟨(depth+1)%3,Nat.mod_lt _ (by decide)⟩, ⟨(depth+2)%3,Nat.mod_lt _ (by decide)⟩]
    let mut best := order.head!
    let mut bestScore := 0
    for k in order do
      let l ← tryLeaf (C.sideHalf k false) G row
      let r ← tryLeaf (C.sideHalf k true) G row
      if let (some l, some r) := (l,r) then return some (.bisect k l r)
      let score := l.isSome.toNat + r.isSome.toNat
      if score > bestScore then
        best := k
        bestScore := score
    let some l ← buildTree G row (C.sideHalf best false) (depth+1) fuel | return none
    let some r ← buildTree G row (C.sideHalf best true) (depth+1) fuel | return none
    return some (.bisect best l r)

structure TrialRect where
  ul : Nat
  uh : Nat
  vl : Nat
  vh : Nat
  deriving Repr

def TrialRect.uBounds (R : TrialRect) : RatBounds :=
  ⟨sideUNodes.get (Fin.ofNat 28 R.ul),sideUNodes.get (Fin.ofNat 28 R.uh)⟩

def TrialRect.vBounds (R : TrialRect) : RatBounds :=
  ⟨sideVNodes.get (Fin.ofNat 37 R.vl),sideVNodes.get (Fin.ofNat 37 R.vh)⟩

def trialLeaf (C : ParameterCell) (U V : RatBounds) (A B : SideFastAxis) :
    StateM Cache (Option SideFastTree) := do
  let (i,P) ← getParameter C
  let box := P.box U V
  let M := factors box.exponent box.argument false
  return if P.leafCheck U V A B M then some (.leaf i M) else none

def trialParam (U V : RatBounds) (A B : SideFastAxis) (C : ParameterCell) (depth : Nat)
    (fuel : Nat) : StateM Cache (Option SideFastTree) := do
  if let some w ← trialLeaf C U V A B then return some w
  match fuel with
  | 0 => return none
  | fuel+1 =>
    let order : List (Fin 3) := [⟨depth%3,Nat.mod_lt _ (by decide)⟩,
      ⟨(depth+1)%3,Nat.mod_lt _ (by decide)⟩, ⟨(depth+2)%3,Nat.mod_lt _ (by decide)⟩]
    let mut best := order.head!
    let mut bestScore := 0
    for k in order do
      let l ← trialLeaf (C.sideHalf k false) U V A B
      let r ← trialLeaf (C.sideHalf k true) U V A B
      if let (some l, some r) := (l,r) then return some (.bisect k l r)
      let score := l.isSome.toNat+r.isSome.toNat
      if score > bestScore then
        best := k
        bestScore := score
    let some l ← trialParam U V A B (C.sideHalf best false) (depth+1) fuel | return none
    let some r ← trialParam U V A B (C.sideHalf best true) (depth+1) fuel | return none
    return some (.bisect best l r)

inductive TrialRowTree
  | omitted
  | tile (rect : TrialRect) (parameters : SideFastTree)
  | cutU (left right : TrialRowTree)
  | cutV (left right : TrialRowTree)

partial def trialRows (C : ParameterCell) (R : TrialRect) (effort : Nat) :
    StateM Cache (Option TrialRowTree) := do
  let U := R.uBounds
  let V := R.vBounds
  if U.hi+V.hi ≤ -5/8 then return some .omitted
  let du := R.uh-R.ul
  let dv := R.vh-R.vl
  let fuel := if du == 1 && dv == 1 then 14 else effort
  let A := axis U
  let B := axis V
  if let some tree ← trialParam U V A B C 0 fuel then return some (.tile R tree)
  let splitU := decide (du > 1 && (dv ≤ 1 || V.hi-V.lo ≤ U.hi-U.lo))
  let (L, H) :=
    if splitU then
      let m := (R.ul+R.uh)/2
      ({R with uh := m},{R with ul := m})
    else if dv > 1 then
      let m := (R.vl+R.vh)/2
      ({R with vh := m},{R with vl := m})
    else (R,R)
  if du == 1 && dv == 1 then return none
  let some l ← trialRows C L effort | return none
  let some r ← trialRows C H effort | return none
  return some (if splitU then .cutU l r else .cutV l r)

def TrialRowTree.tiles : TrialRowTree → List (TrialRect × SideFastTree)
  | .omitted => []
  | .tile r p => [(r,p)]
  | .cutU l r | .cutV l r => l.tiles ++ r.tiles

def startRects : List TrialRect := [⟨8,27,9,36⟩,⟨8,27,0,9⟩,⟨0,8,9,36⟩,⟨0,8,0,9⟩]

def trialCell (target : Nat) : Option ParameterCell :=
  if target < 510 then scParameterGrid[target]?
  else if target == 521 then some ⟨⟨0,1/80⟩,⟨3/16,21/80⟩,⟨1/10,1/6⟩⟩
  else if target == 535 then some ⟨⟨1/80,1/40⟩,⟨33/80,1/2⟩,⟨1/10,1/6⟩⟩
  else none

def refs : SideFastTree → List Nat
  | .leaf idx _ => [idx]
  | .bisect _ l r => refs l ++ refs r

def treeDirectText (stem : String) : SideFastTree → String
  | .leaf i M => s!".leaf {stem}P{i} {stem}P{i}_checked {sampleText M}"
  | .bisect k l r => s!".bisect {k.val} ({treeDirectText stem l}) ({treeDirectText stem r})"

def uName (stem : String) (r : TrialRect) := s!"{stem}U{r.ul}_{r.uh}"
def vName (stem : String) (r : TrialRect) := s!"{stem}V{r.vl}_{r.vh}"

def rowTreeText (stem axisStem : String) : TrialRowTree → String
  | .omitted => ".omitted"
  | .tile R T => s!"(.tile ⟨{uName axisStem R}, {vName axisStem R}, {treeDirectText stem T}⟩)"
  | .cutU l r => s!"(.cutU {rowTreeText stem axisStem l} {rowTreeText stem axisStem r})"
  | .cutV l r => s!"(.cutV {rowTreeText stem axisStem l} {rowTreeText stem axisStem r})"

/-- A rational as an identifier fragment: `-3/4` becomes `m3d4`. -/
def ratIdent (q : ℚ) : String :=
  (if q < 0 then "m" else "") ++ toString q.num.natAbs ++ (if q.den = 1 then "" else s!"d{q.den}")

/-- The bank name of the axis on `I`. The packet `axis I` depends on `I` alone, so equal bounds share
one bank entry. -/
def bankName (I : RatBounds) : String := s!"sideAxisBank_{ratIdent I.lo}_{ratIdent I.hi}"

/-- `rowTreeText` citing bank axes by their bounds instead of cell-local axes. -/
def rowTreeTextBanked (stem : String) : TrialRowTree → String
  | .omitted => ".omitted"
  | .tile R T => s!"(.tile ⟨{bankName R.uBounds}, {bankName R.vBounds}, {treeDirectText stem T}⟩)"
  | .cutU l r => s!"(.cutU {rowTreeTextBanked stem l} {rowTreeTextBanked stem r})"
  | .cutV l r => s!"(.cutV {rowTreeTextBanked stem l} {rowTreeTextBanked stem r})"

partial def emitCheckedTree (stem : String) (banked : Bool) (R : TrialRect) (tree : TrialRowTree) :
    StateM (Array String) String := do
  let cost := tree.tiles.foldl (fun n tile => n + treeSize tile.2) 0
  let mut node := if banked then rowTreeTextBanked stem tree else rowTreeText stem stem tree
  let mut proof := "by decide +kernel"
  if cost > 40 then
    match tree with
    | .cutU l r =>
      let m := (R.ul+R.uh)/2
      let left ← emitCheckedTree stem banked {R with uh := m} l
      let right ← emitCheckedTree stem banked {R with ul := m} r
      node := s!".cutU {left} {right}"
      proof := s!"SideConeCoarseTree.cutU_checked {left}_checked {right}_checked"
    | .cutV l r =>
      let m := (R.vl+R.vh)/2
      let left ← emitCheckedTree stem banked {R with vh := m} l
      let right ← emitCheckedTree stem banked {R with vl := m} r
      node := s!".cutV {left} {right}"
      proof := s!"SideConeCoarseTree.cutV_checked {left}_checked {right}_checked"
    | _ => pure ()
  let chunks ← get
  let name := s!"{stem}Node{chunks.size}"
  let definition := s!"def {name} : SideConeCoarseTree := {node}\n\n"
  let header := s!"theorem {name}_checked : {name}.check {stem}Cell ⟨{R.ul}, {R.uh}⟩ ⟨{R.vl}, {R.vh}⟩ = true :=\n"
  set (chunks.push (definition ++ header ++ "  " ++ proof ++ "\n\n"))
  return name

def axisDecl (name : String) (bounds : RatBounds) : String :=
  s!"def {name} : SideCoarseAxis := ⟨{boundsText bounds}, {axisText (axis bounds)}, by decide +kernel⟩\n\n"

/-- `a/b` or `a` as a rational. -/
def parseRat (s : String) : Option ℚ :=
  match s.splitOn "/" with
  | [n] => n.toInt?.map (fun i => (i : ℚ))
  | [n, d] => do
    let i ← n.toInt?
    let j ← d.toNat?
    if j = 0 then none else some ((i : ℚ) / j)
  | _ => none

/-- One bank entry: the checked fact, then the axis citing it. Bounds and data text are exactly
those of `axisDecl` for the same bounds. -/
def bankDecl (I : RatBounds) : String :=
  let name := bankName I
  let data := axisText (axis I)
  s!"theorem {name}_checked : SideFastAxis.check {data} {boundsText I} = true := by decide +kernel\n" ++
    s!"def {name} : SideCoarseAxis := ⟨{boundsText I}, {data}, {name}_checked⟩\n\n"

/-- The bank for the production axes: one entry per distinct bounds listed in `boundsFile`
(lines `lo hi`), in file order. -/
def emitProductionBank (dst boundsFile : String) : IO Unit := do
  let lines := (← IO.FS.lines boundsFile).toList.filter (· ≠ "")
  let mut source := "module\n\npublic import HlawkaSchatten.BelowExponent.Vertex.SideConeCoarseRows\n\n"
  source := source ++ "@[expose] public section\n\nnamespace HlawkaSchatten.BelowExponent.Vertex\n\n"
  source := source ++ "-- Generated by scripts/certificates/facet-vertex/compiled-preparation/" ++
    "sc-near-coarse-prepare.lean --axis-bank-production.\n\n"
  let mut seen : Std.HashMap String Bool := {}
  for line in lines do
    let some (lo, hi) := (match line.splitOn " " with
      | [a, b] => do pure (← parseRat a, ← parseRat b)
      | _ => none) | throw (IO.userError s!"Bad bounds line {line}")
    let I : RatBounds := ⟨lo, hi⟩
    if seen[bankName I]?.isNone then
      seen := seen.insert (bankName I) true
      source := source ++ bankDecl I
  IO.FS.writeFile dst (source ++ "end HlawkaSchatten.BelowExponent.Vertex\n")
  IO.println s!"{seen.size} bank axes"

def bisectedSpans : Nat → Nat → Nat → List (Nat × Nat)
  | 0, _, _ => []
  | fuel+1, lo, hi =>
    if hi ≤ lo+1 then [(lo, hi)]
    else
      let mid := (lo+hi)/2
      (lo, hi) :: (bisectedSpans fuel lo mid ++ bisectedSpans fuel mid hi)

def emitAxisBank (dst : String) : IO Unit := do
  let u := startRects.flatMap (fun r => bisectedSpans 8 r.ul r.uh) |>.eraseDups
  let v := startRects.flatMap (fun r => bisectedSpans 8 r.vl r.vh) |>.eraseDups
  let mut source := "module\n\npublic import HlawkaSchatten.BelowExponent.Vertex.SideConeCoarseTree\n\n"
  source := source ++ "@[expose] public section\n\nnamespace HlawkaSchatten.BelowExponent.Vertex\n\n"
  source := source ++ "-- Generated by scripts/certificates/facet-vertex/compiled-preparation/sc-near-coarse-prepare.lean --axis-bank.\n\n"
  for (lo, hi) in u do
    let r : TrialRect := ⟨lo, hi, 0, 0⟩
    source := source ++ axisDecl (uName "scNearAxis" r) r.uBounds
  for (lo, hi) in v do
    let r : TrialRect := ⟨0, 0, lo, hi⟩
    source := source ++ axisDecl (vName "scNearAxis" r) r.vBounds
  IO.FS.writeFile dst (source ++ "end HlawkaSchatten.BelowExponent.Vertex\n")
  IO.println s!"{u.length} u spans and {v.length} v spans"

def prepare (C : ParameterCell) (effort : Nat) : IO (Array TrialRowTree × Cache) := do
  let mut cache : Cache := {}
  let mut quadrants : Array TrialRowTree := #[]
  for R in startRects do
    let (found, newCache) := (trialRows C R effort).run cache
    cache := newCache
    let some rows := found | throw (IO.userError s!"Open row quadrant {repr R}")
    quadrants := quadrants.push rows
  return (quadrants, cache)

def counts (effort : Nat) : IO Unit := do
  for target in [:510] do
    let some C := trialCell target | throw (IO.userError "Missing original cell")
    let (quadrants, cache) ← prepare C effort
    let tiles := quadrants.toList.flatMap TrialRowTree.tiles
    let leaves := tiles.foldl (fun n row => n + treeSize row.2) 0
    IO.println s!"TOTAL {target} effort{effort} {tiles.length} {leaves} {cache.data.size}"

def parameterLeaves : SideFastTree → List (Nat × FactorSamples)
  | .leaf n sample => [(n, sample)]
  | .bisect _ l r => parameterLeaves l ++ parameterLeaves r

def coefficientKey (I : SideLowerCoefficients) (cap : ℚ) : String :=
  String.intercalate "," ([I.value, I.first, I.second, I.diagonalFirst, I.mixed,
    I.diagonalSecond, cap].map toString)

def reflectCoefficients (I : SideLowerCoefficients) : SideLowerCoefficients :=
  let s : ℚ := if I.first < 0 then -1 else 1
  let t : ℚ := if I.second < 0 then -1 else 1
  let b := I.mixed * s * t
  let mixed := if I.first == 0 || I.second == 0 then |b| else b
  ⟨I.value, I.first * s, I.second * t, I.diagonalFirst, mixed, I.diagonalSecond⟩

def signedCoefficients (I : SideLowerCoefficients) (u v : Bool) : SideLowerCoefficients :=
  ⟨I.value, (if u then I.first else -I.first), (if v then I.second else -I.second),
    I.diagonalFirst, (if u == v then I.mixed else -I.mixed), I.diagonalSecond⟩

def coefficientwiseLE (a b : SideLowerCoefficients) : Bool :=
  decide (a.value ≤ b.value ∧ a.first ≤ b.first ∧ a.second ≤ b.second ∧
    a.diagonalFirst ≤ b.diagonalFirst ∧ a.mixed ≤ b.mixed ∧ a.diagonalSecond ≤ b.diagonalSecond)

def repeatTuples (targets : List String) : IO Unit := do
  let mut globalFull : Std.HashMap String Bool := {}
  let mut globalReflected : Std.HashMap String Bool := {}
  for text in targets do
    let target := text.toNat!
    let some C := trialCell target | throw (IO.userError s!"Missing original cell {target}")
    let (quadrants, cache) ← prepare C 2
    let tiles := quadrants.toList.flatMap TrialRowTree.tiles
    let mut full : Std.HashMap String Bool := {}
    let mut reflected : Std.HashMap String Bool := {}
    let mut horizontal : Std.HashMap String Bool := {}
    let mut vertical : Std.HashMap String Bool := {}
    let mut determinant := 0
    let mut rectangle := 0
    let mut front : Std.HashMap Nat (List SideLowerCoefficients) := {}
    let mut rectangleInputs : List (Nat × SideLowerCoefficients) := []
    for (R, tree) in tiles do
      let U := R.uBounds
      let V := R.vBounds
      let UA := axis U
      let VA := axis V
      for (n, sample) in parameterLeaves tree do
        let some P := cache.data[n]? | throw (IO.userError "Missing parameter")
        let F := P.mixedInterval U V sample
        let coefficient := P.terms.evaluate UA.bounds VA.bounds F
        let signU := sideAxisSign U
        let signV := sideAxisSign V
        let lower := coefficient.toRat.lower signU signV
        let signed := signedCoefficients lower signU signV
        horizontal := horizontal.insert s!"{n},{R.ul},{R.uh}" true
        vertical := vertical.insert s!"{n},{R.vl},{R.vh}" true
        if lower.detOK P.cell.a.hi then
          determinant := determinant + 1
          let exactKey := coefficientKey lower P.cell.a.hi
          let reflectionKey := coefficientKey (reflectCoefficients lower) P.cell.a.hi
          full := full.insert exactKey true
          reflected := reflected.insert reflectionKey true
          globalFull := globalFull.insert exactKey true
          globalReflected := globalReflected.insert reflectionKey true
          let active := (front.get? n).getD []
          unless active.any (fun corner => coefficientwiseLE corner signed) do
            front := front.insert n (signed :: active.filter (fun corner => !coefficientwiseLE signed corner))
        else
          rectangle := rectangle + 1
          rectangleInputs := (n, signed) :: rectangleInputs
    let minimal := front.toList.foldl (fun count (_, corners) => count + corners.length) 0
    let dominated := rectangleInputs.countP (fun (n, datum) =>
      ((front.get? n).getD []).any (fun corner => coefficientwiseLE corner datum))
    IO.println s!"{target}\t{determinant}\t{rectangle}\t{full.size}\t{reflected.size}\t{horizontal.size}\t{vertical.size}\t{minimal}\t{dominated}"
  IO.println s!"global determinant keys\t{globalFull.size}\t{globalReflected.size}"

def emitCell (target effort : Nat) (dst mode : String) : IO Unit := do
  let modeShared := mode == "tree-shared"
  let modeBanked := mode == "production-banked"
  let modeShards := mode == "shard-test" || mode == "production-packed" || modeBanked
  let modeTree := mode != ""
  let some C := trialCell target | throw (IO.userError "Unknown cell")
  let (quadrants, cache) ← prepare C effort
  let tiles := quadrants.toList.flatMap TrialRowTree.tiles
  let stem := if mode == "production" || mode == "production-packed" || modeBanked then
    s!"scCoarseProd{target}" else
    if mode == "shard-test" then s!"scCoarseSplit{target}" else
    if modeShared then s!"scCoarseShared{target}" else
    if modeTree then s!"scCoarseTree{target}" else s!"scCoarse{target}"
  let module := if modeShards then "SideConeCoarseShards" else
    if modeShared then "SideConeCoarseAxisBank" else
    if modeTree then "SideConeCoarseTree" else "SideConeCoarseRows"
  let bankImport := if modeBanked then "public import HlawkaSchatten.BelowExponent.Vertex.SideConeAxisBank\n" else ""
  let mut source := s!"module\n\npublic import HlawkaSchatten.BelowExponent.Vertex.{module}\n{bankImport}\n@[expose] public section\n\n"
  source := source ++ "namespace HlawkaSchatten.BelowExponent.Vertex\n\nset_option maxRecDepth 30000\nset_option maxHeartbeats 0\n\n"
  source := source ++ s!"def {stem}Cell : ParameterCell := {SCPrepare.cellText C}\n\n"
  let keys := (tiles.flatMap fun p => refs p.2).eraseDups
  for i in keys do
    let some P := cache.data[i]? | throw (IO.userError "Missing parameter")
    source := source ++ s!"def {stem}P{i} : SideFastParameter := {parameterText P}\n"
    source := source ++ s!"theorem {stem}P{i}_checked : {stem}P{i}.check = true := by decide +kernel\n\n"
  unless modeShared || modeBanked do
    let mut emitted : Std.HashMap String Bool := {}
    for (R,_) in tiles do
      for (name,bounds) in [(uName stem R,R.uBounds),(vName stem R,R.vBounds)] do
        if emitted[name]?.isNone then
          emitted := emitted.insert name true
          source := source ++ axisDecl name bounds
  let mut rootChecks := #[]
  if modeShards then
    let (names, chunks) := ((startRects.zip quadrants.toList).mapM fun (rect, tree) =>
      emitCheckedTree stem modeBanked rect tree).run #[]
    source := source ++ String.join chunks.toList
    rootChecks := names.toArray
  if modeTree then
    source := source ++ s!"def {stem}Trees : Bool → Bool → SideConeCoarseTree\n"
    for (i, s, t) in ([(0,true,true),(1,true,false),(2,false,true),(3,false,false)] : List (Nat × Bool × Bool)) do
      let some quadrant := quadrants[i]? | throw (IO.userError "Missing quadrant")
      let node := if modeShards then rootChecks[i]! else
        rowTreeText stem (if modeShared then "scNearAxis" else stem) quadrant
      source := source ++ s!"  | {s}, {t} => {node}\n"
    source := source ++ "\n"
  else
    let body := String.intercalate ",\n  " (tiles.map fun (R,T) =>
      s!"⟨{uName stem R}, {vName stem R}, {treeDirectText stem T}⟩")
    source := source ++ s!"def {stem}Tiles : List SideCoarseTile := [\n  {body}]\n\n"
  source := source ++ s!"theorem {stem}Near : ∀ row ∈ sideRowGrid,\n"
  source := source ++ s!"    SideConeOn {stem}Cell (sideURange row.1) (sideVRange row.2) :=\n"
  if modeShards then
    source := source ++ s!"  sideConeCoarseTrees_sound (trees := {stem}Trees) (by\n"
    source := source ++ "    intro s t\n    cases s <;> cases t\n"
    for name in rootChecks.toList.reverse do
      source := source ++ s!"    · exact {name}_checked\n"
    source := source ++ "  )\n"
  else if modeTree then
    source := source ++ s!"  sideConeCoarseTrees_sound (trees := {stem}Trees) (by decide +kernel)\n"
  else
    source := source ++ s!"  sideCoarseTiles_sound (tiles := {stem}Tiles) (by decide +kernel) (by decide +kernel)\n"
  source := source ++ "\nend HlawkaSchatten.BelowExponent.Vertex\n"
  IO.FS.writeFile dst source
  IO.println s!"{target}: {tiles.length} row rectangles, {tiles.foldl (fun n row => n+treeSize row.2) 0} leaves, {keys.length} parameters"

def pilot (args : List String) : IO Unit := do
  let cellText :: effortText :: dst :: flags := args |
    throw (IO.userError "CELL EFFORT OUTPUT [tree|tree-shared]")
  unless flags == [] || flags == ["tree"] || flags == ["tree-shared"] do
    throw (IO.userError "Expected optional tree or tree-shared mode")
  emitCell cellText.toNat! effortText.toNat! dst (flags.headD "")

def production (dst : System.FilePath) (first stop : Nat) (mode : String) : IO Unit := do
  unless first < stop && stop ≤ 510 do
    throw (IO.userError "Expected a half-open range within 0..510")
  IO.FS.createDirAll dst
  for target in [first:stop] do
    emitCell target 2 (dst / s!"Cell{target}.lean").toString mode

end SCPrepare

def main : List String → IO Unit
  | ["--counts", effort] => SCPrepare.counts effort.toNat!
  | "--repeat-tuples" :: targets => SCPrepare.repeatTuples targets
  | ["--axis-bank", dst] => SCPrepare.emitAxisBank dst
  | ["--production", dst, first, stop] =>
    SCPrepare.production (System.FilePath.mk dst) first.toNat! stop.toNat! "production"
  | ["--production-packed", dst, first, stop] =>
    SCPrepare.production (System.FilePath.mk dst) first.toNat! stop.toNat! "production-packed"
  | ["--production-banked", dst, first, stop] =>
    SCPrepare.production (System.FilePath.mk dst) first.toNat! stop.toNat! "production-banked"
  | ["--axis-bank-production", dst, boundsFile] => SCPrepare.emitProductionBank dst boundsFile
  | ["--shard-test", cell, dst] => SCPrepare.emitCell cell.toNat! 2 dst "shard-test"
  | args => SCPrepare.pilot args
