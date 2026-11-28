module

public meta import HlawkaSchatten.BelowExponent.Vertex.SideCutCorners.RootTable
public meta import HlawkaSchatten.BelowExponent.Vertex.SideOuterWidePrepare

public meta section

open HlawkaSchatten.BelowExponent.Vertex

def main : List String → IO Unit
  | "bounds" :: args => prepareSCOuterBounds "SideCutCorners" "scCutOuter" scCutOuterPoints scCutOuterRootTable args
  | "wide" :: args => prepareSCOuterWide "SideCutCorners" "scCutOuter" scCutOuterPoints scCutOuterRootTable args
  | _ => throw (IO.userError "Usage: sc-outer-cut-prepare.lean (bounds|wide) OUTPUT_DIRECTORY [INDEX ...]")
