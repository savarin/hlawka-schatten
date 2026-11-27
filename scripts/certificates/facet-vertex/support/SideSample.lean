import SideCertificateSupport.RootTable
import SideCertificateSupport.WidePrepare

open HlawkaSchatten.BelowExponent.Vertex

def main (args : List String) : IO Unit :=
  prepareSCOuterWide "SideCutCorners" "scCutOuter" scCutOuterPoints scCutOuterRootTable args
