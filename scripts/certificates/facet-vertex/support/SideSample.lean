module

public meta import SideCertificateSupport.RootTable
public meta import SideCertificateSupport.WidePrepare

public meta section

open HlawkaSchatten.BelowExponent.Vertex

def main (args : List String) : IO Unit :=
  prepareSCOuterWide "SideCutCorners" "scCutOuter" scCutOuterPoints scCutOuterRootTable args
