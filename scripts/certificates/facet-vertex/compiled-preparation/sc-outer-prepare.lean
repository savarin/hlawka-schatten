module

public meta import HlawkaSchatten.BelowExponent.Vertex.SideCornerData.RootTable
public meta import HlawkaSchatten.BelowExponent.Vertex.SideOuterWidePrepare

public meta section

open HlawkaSchatten.BelowExponent.Vertex

def main : List String → IO Unit :=
  prepareSCOuterBounds "SideCornerData" "scOuter" scOuterPoints scOuterRootTable
