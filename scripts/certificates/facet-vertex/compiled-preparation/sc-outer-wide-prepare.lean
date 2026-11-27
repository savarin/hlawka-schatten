import HlawkaSchatten.BelowExponent.Vertex.SideCornerData.RootTable
import HlawkaSchatten.BelowExponent.Vertex.SideOuterWidePrepare

open HlawkaSchatten.BelowExponent.Vertex

def main : List String → IO Unit :=
  prepareSCOuterWide "SideCornerData" "scOuter" scOuterPoints scOuterRootTable
