import HlawkaSchatten.BelowExponent.Vertex.SideCutCorners.RootTable
import HlawkaSchatten.BelowExponent.Vertex.SideOuterWidePrepare

open HlawkaSchatten.BelowExponent.Vertex

def main : List String → IO Unit
  | "bounds" :: args => prepareSCOuterBounds "SideCutCorners" "scCutOuter" scCutOuterPoints scCutOuterRootTable args
  | "wide" :: args => prepareSCOuterWide "SideCutCorners" "scCutOuter" scCutOuterPoints scCutOuterRootTable args
  | _ => throw (IO.userError "Usage: sc-outer-cut-prepare.lean (bounds|wide) OUTPUT_DIRECTORY [INDEX ...]")
